use std::collections::{HashMap, HashSet};

use luac_parser::{LuaChunk, LuaConstant, LuaNumber};

use crate::lua51::ast::*;
use crate::lua51::cfg::{BasicBlock, ControlFlowGraph, EdgeKind};
use crate::lua51::dominator::{find_loops, DominatorTree, LoopKind, NaturalLoop};
use crate::lua51::instruction::{is_k, index_k};
use crate::lua51::liveness::{compute_liveness, is_reg_live_after, LivenessInfo};
use crate::lua51::opcodes::OpCode;

/// Context for decompiling a single Lua function.
pub struct Lifter<'a> {
    chunk: &'a LuaChunk,
    cfg: ControlFlowGraph,
    _dom: DominatorTree,
    loops: Vec<NaturalLoop>,
    liveness: LivenessInfo,
    /// Register expressions: tracks what expression is currently held in each register.
    regs: Vec<Option<Expr>>,
    /// Pending tables being constructed (register -> accumulated fields).
    pending_tables: HashMap<u32, Vec<TableField>>,
    /// Stable references a register value has been assigned into.
    capture_aliases: HashMap<u32, Expr>,
    /// Registers that are updated from their own previous value across branches.
    accumulator_regs: HashSet<u32>,
    /// Blocks already visited to prevent infinite recursion.
    visited_blocks: HashSet<usize>,
    /// Local variable names assigned to registers (reg -> name).
    local_names: HashMap<u32, String>,
    /// Registers that have been declared as `local`.
    declared_locals: HashSet<u32>,
    /// Number of parameters (these registers are implicitly declared).
    num_params: u32,
    /// Whether this chunk has debug info (locals/upvalue names).
    has_debug_info: bool,
    /// Upvalue expressions resolved from the parent closure site.
    resolved_upvalues: Vec<Option<Expr>>,
    /// Loop exit block IDs for break detection.
    loop_exits: HashSet<usize>,
}

impl<'a> Lifter<'a> {
    pub fn decompile(chunk: &'a LuaChunk) -> Function {
        Self::decompile_with_upvalues(chunk, Vec::new())
    }

    fn decompile_with_upvalues(
        chunk: &'a LuaChunk,
        resolved_upvalues: Vec<Option<Expr>>,
    ) -> Function {
        let cfg = ControlFlowGraph::build(&chunk.instructions);
        let dom = DominatorTree::build(&cfg);
        let loops = find_loops(&cfg, &dom);
        let liveness = compute_liveness(&cfg, chunk.max_stack as usize);
        let has_debug_info = !chunk.locals.is_empty();

        // Collect loop exit blocks for break detection
        let mut loop_exits = HashSet::new();
        for lp in &loops {
            let max_body = lp.body.iter().copied().max().unwrap_or(lp.header);
            if max_body + 1 < cfg.num_blocks() {
                loop_exits.insert(max_body + 1);
            }
        }

        let max_stack = chunk.max_stack as usize;
        let mut lifter = Lifter {
            chunk,
            cfg,
            _dom: dom,
            loops,
            liveness,
            regs: vec![None; max_stack.max(256)],
            pending_tables: HashMap::new(),
            capture_aliases: HashMap::new(),
            accumulator_regs: HashSet::new(),
            visited_blocks: HashSet::new(),
            local_names: HashMap::new(),
            declared_locals: HashSet::new(),
            num_params: chunk.num_params as u32,
            has_debug_info,
            resolved_upvalues,
            loop_exits,
        };

        lifter.accumulator_regs = lifter.find_accumulator_regs();

        let params: Vec<String> = (0..chunk.num_params as u32)
            .map(|i| {
                let name = lifter.local_name(i, 0);
                lifter.local_names.insert(i, name.clone());
                lifter.declared_locals.insert(i);
                lifter.set_reg(i, Expr::Name(name.clone()));
                name
            })
            .collect();
        let is_vararg = chunk.is_vararg.is_some();

        let body = if lifter.cfg.num_blocks() > 0 {
            lifter.lift_block_range(0, lifter.cfg.num_blocks())
        } else {
            Vec::new()
        };

        Function {
            params,
            is_vararg,
            body,
        }
    }

    /// Lift a range of blocks into a statement list, handling control structures.
    fn lift_block_range(&mut self, start_block: usize, end_block: usize) -> Block {
        let mut stmts = Vec::new();
        let mut block_idx = start_block;

        while block_idx < end_block && block_idx < self.cfg.num_blocks() {
            // Prevent revisiting blocks
            if !self.visited_blocks.insert(block_idx) {
                block_idx += 1;
                continue;
            }

            // Check if this block is a loop header
            if let Some(lp) = self.find_loop_at(block_idx) {
                let lp = lp.clone();
                let next = self.lift_loop(&lp, &mut stmts);
                if next <= block_idx {
                    // Safety: avoid infinite loop
                    block_idx += 1;
                } else {
                    block_idx = next;
                }
                continue;
            }

            let block = self.cfg.blocks[block_idx].clone();
            let _last_pc = block.end;

            // Check for conditional (if/elseif/else)
            if self.is_conditional_block(&block) {
                let next = self.lift_conditional(block_idx, &mut stmts);
                if next <= block_idx {
                    // Safety: avoid infinite loop, lift as normal instructions
                    self.lift_instructions(block.start, block.end, &mut stmts);
                    block_idx += 1;
                } else {
                    block_idx = next;
                }
                continue;
            }

            // Normal block: lift instructions sequentially
            self.lift_instructions(block.start, block.end, &mut stmts);

            // Check if this block ends with a JMP to a loop exit (break)
            let last_inst = self.cfg.instructions[block.end];
            if last_inst.op == OpCode::Jmp && block.successors.len() == 1 {
                let target = block.successors[0];
                if self.loop_exits.contains(&target) {
                    stmts.push(Stat::Break);
                }
                // Follow unconditional JMP: skip ahead to target block
                // (blocks between here and target are only reachable via the target)
                if target > block_idx + 1 {
                    block_idx = target;
                    continue;
                }
            }

            block_idx += 1;
        }

        stmts
    }

    /// Lift a single loop structure.
    fn lift_loop(&mut self, lp: &NaturalLoop, stmts: &mut Block) -> usize {
        match lp.kind {
            LoopKind::NumericFor => self.lift_numeric_for(lp, stmts),
            LoopKind::GenericFor => self.lift_generic_for(lp, stmts),
            LoopKind::WhileRepeat => self.lift_while(lp, stmts),
        }
    }

    fn lift_numeric_for(&mut self, lp: &NaturalLoop, stmts: &mut Block) -> usize {
        let header = &self.cfg.blocks[lp.header].clone();

        // Find the FORPREP instruction: it's in the block preceding the header
        // or in the header itself.  The FORPREP's A register tells us the for-loop slots.
        let forprep_block = self.find_forprep_block(lp.header);
        let forprep_inst = if let Some(fb) = forprep_block {
            let b = &self.cfg.blocks[fb];
            self.cfg.instructions[b.end]
        } else {
            self.cfg.instructions[header.start]
        };

        let base = forprep_inst.a;
        let var_name = self.local_name(base + 3, header.start);

        // Lift the pre-loop setup to get init/limit/step
        if let Some(fb) = forprep_block {
            let b = &self.cfg.blocks[fb].clone();
            // Lift instructions before FORPREP to set up init/limit/step
            if b.end > b.start {
                self.lift_instructions(b.start, b.end - 1, stmts);
            }
        }

        let start_expr = self.reg_expr(base);
        let limit_expr = self.reg_expr(base + 1);
        let step_expr = self.reg_expr(base + 2);
        let step = if matches!(&step_expr, Expr::Number(NumLit::Int(1))) {
            None
        } else {
            Some(step_expr)
        };

        // Body: blocks between header and latch (exclusive of FORLOOP block)
        let body_start = lp.header + 1;
        let body_end = lp.latch;
        let body = if body_start < body_end {
            self.lift_block_range(body_start, body_end)
        } else {
            // Single-block body: the header IS the body (header contains FORLOOP at end)
            let hdr = self.cfg.blocks[lp.header].clone();
            if hdr.end > hdr.start {
                let mut body = Vec::new();
                self.lift_instructions(hdr.start, hdr.end - 1, &mut body);
                body
            } else {
                Vec::new()
            }
        };

        stmts.push(Stat::NumericFor {
            name: var_name,
            start: start_expr,
            limit: limit_expr,
            step,
            body,
        });

        // Return the block after the loop exit
        self.max_loop_block(lp) + 1
    }

    fn lift_generic_for(&mut self, lp: &NaturalLoop, stmts: &mut Block) -> usize {
        let header = &self.cfg.blocks[lp.header].clone();

        // Find TFORLOOP instruction in the header or latch block
        let mut tforloop_inst = None;
        for pc in header.start..=header.end {
            if self.cfg.instructions[pc].op == OpCode::TForLoop {
                tforloop_inst = Some(self.cfg.instructions[pc]);
                break;
            }
        }
        if tforloop_inst.is_none() {
            let latch_block = &self.cfg.blocks[lp.latch].clone();
            for pc in latch_block.start..=latch_block.end {
                if self.cfg.instructions[pc].op == OpCode::TForLoop {
                    tforloop_inst = Some(self.cfg.instructions[pc]);
                    break;
                }
            }
        }
        let tfl = tforloop_inst.unwrap_or(self.cfg.instructions[header.end]);

        let base = tfl.a;
        let num_vars = tfl.c();

        let names: Vec<String> = (0..num_vars)
            .map(|i| self.local_name(base + 3 + i, header.start))
            .collect();

        // Register loop variable names so the body can reference them
        for (i, name) in names.iter().enumerate() {
            let r = base + 3 + i as u32;
            self.local_names.insert(r, name.clone());
            self.declared_locals.insert(r);
            self.set_reg(r, Expr::Name(name.clone()));
        }

        let iter_expr = self.reg_expr(base);

        // Body: loop blocks excluding the header, sorted by block ID
        let mut body_blocks: Vec<usize> = lp.body.iter()
            .filter(|&&b| b != lp.header)
            .copied()
            .collect();
        body_blocks.sort();

        let body = if !body_blocks.is_empty() {
            let first = *body_blocks.first().unwrap();
            let last = *body_blocks.last().unwrap();
            self.lift_block_range(first, last + 1)
        } else {
            Vec::new()
        };

        stmts.push(Stat::GenericFor {
            names,
            iterators: vec![iter_expr],
            body,
        });

        self.max_loop_block(lp) + 1
    }

    fn lift_while(&mut self, lp: &NaturalLoop, stmts: &mut Block) -> usize {
        let _header = &self.cfg.blocks[lp.header].clone();

        // Try to extract condition from header block
        let cond = self.extract_condition(lp.header).unwrap_or(Expr::Bool(true));

        // Body: blocks in the loop excluding header
        let body_start = lp.header + 1;
        let body_end = lp.latch + 1;
        let body = self.lift_block_range(body_start, body_end);

        stmts.push(Stat::While { cond, body });

        self.max_loop_block(lp) + 1
    }

    /// Lift an if/elseif/else chain.
    fn lift_conditional(&mut self, block_idx: usize, stmts: &mut Block) -> usize {
        // Try to detect and lift OR/AND short-circuit chains first
        if let Some(next) = self.try_lift_or_and_chain(block_idx, stmts) {
            return next;
        }

        let block = self.cfg.blocks[block_idx].clone();

        // Lift any instructions before the test/JMP at the end of this block.
        // The test is typically the second-to-last instruction (before JMP).
        let test_pc = self.find_test_pc(&block);
        if let Some(tp) = test_pc {
            if tp > block.start {
                self.lift_instructions(block.start, tp - 1, stmts);
            }
        }

        let cond = self.extract_condition(block_idx).unwrap_or(Expr::Bool(true));

        // Find the two branches
        let succs = block.successors.clone();
        if succs.len() != 2 {
            // Not a proper conditional; just lift as normal
            self.lift_instructions(block.start, block.end, stmts);
            return block_idx + 1;
        }

        // The edge order: ConditionalFalse is added first, ConditionalTrue second
        // ConditionalFalse = the JMP target (condition NOT met)
        // ConditionalTrue = fallthrough after JMP (condition met, test passed -> skip JMP)
        let false_target = succs[0]; // Where JMP goes (condition false)
        let true_target = succs[1];  // Fallthrough past JMP (condition true)

        // Detect guard clause pattern: `if not cond then return end`
        // In Lua bytecode this is: TEST/EQ -> JMP past return -> RETURN -> continuation
        // The true_target block (condition true = skip JMP) is a small block ending in RETURN
        // and false_target is the continuation.
        // Only match if the return block is NOT a merge point (has only 1 predecessor).
        if self.is_return_block(true_target) && false_target > true_target
            && self.cfg.blocks[true_target].predecessors.len() <= 1
        {
            // Guard clause: the "true" path is just a return
            let guard_body = self.lift_block_range(true_target, true_target + 1);
            stmts.push(Stat::If {
                cond,
                then_block: guard_body,
                elseif_clauses: Vec::new(),
                else_block: None,
            });
            return false_target;
        }

        // Detect inverted guard: `if cond then <continue> else return end`
        // Here false_target is a return block and true_target is the continuation
        // Only match if the return block is NOT a merge point.
        if self.is_return_block(false_target) && true_target < false_target
            && self.cfg.blocks[false_target].predecessors.len() <= 1
        {
            let guard_body = self.lift_block_range(false_target, false_target + 1);
            let inv_cond = negate_expr(cond);
            stmts.push(Stat::If {
                cond: inv_cond,
                then_block: guard_body,
                elseif_clauses: Vec::new(),
                else_block: None,
            });
            return true_target;
        }

        // Find the merge point
        let merge = self.find_merge_point(block_idx, true_target, false_target);

        let then_end = merge.unwrap_or(false_target);
        let then_block = self.lift_block_range(true_target, then_end);

        let else_block = if let Some(merge) = merge {
            if false_target < merge {
                let eb = self.lift_block_range(false_target, merge);
                if eb.is_empty() { None } else { Some(eb) }
            } else {
                None
            }
        } else {
            None
        };

        stmts.push(Stat::If {
            cond,
            then_block,
            elseif_clauses: Vec::new(),
            else_block,
        });

        merge.unwrap_or(false_target.max(true_target) + 1)
    }

    /// Detect and lift OR/AND short-circuit conditional chains.
    ///
    /// OR pattern (`if a or b then T end`):
    ///   Block A: ConditionalFalse → T, ConditionalTrue → Block B
    ///   Block B: ConditionalTrue → T, ConditionalFalse → continuation
    ///   (Intermediate blocks: ConditionalFalse → T, ConditionalTrue → next)
    ///
    /// AND pattern (`if a and b then body end`):
    ///   Block A: ConditionalFalse → END, ConditionalTrue → Block B
    ///   Block B: ConditionalFalse → END, ConditionalTrue → body
    fn try_lift_or_and_chain(&mut self, start: usize, stmts: &mut Block) -> Option<usize> {
        let block = &self.cfg.blocks[start];
        if block.successors.len() != 2 { return None; }
        if self.block_contains_testset(start) {
            return None;
        }

        let _false0 = block.successors[0]; // ConditionalFalse (JMP target)
        let true0 = block.successors[1];  // ConditionalTrue (fallthrough)

        // true0 must be a conditional block (next test in chain)
        if true0 >= self.cfg.num_blocks() { return None; }
        if !self.is_conditional_block(&self.cfg.blocks[true0]) { return None; }
        if self.block_contains_testset(true0) {
            return None;
        }

        // Try OR chain detection
        if let Some(result) = self.try_or_chain(start, stmts) {
            return Some(result);
        }

        // Try AND chain detection
        if let Some(result) = self.try_and_chain(start, stmts) {
            return Some(result);
        }

        None
    }

    /// Detect and lift an OR chain: `if A or B or ... then T`.
    ///
    /// Pattern: intermediate blocks have ConditionalFalse → T (common body),
    /// last block has ConditionalTrue → T.
    fn try_or_chain(&mut self, start: usize, stmts: &mut Block) -> Option<usize> {
        let block = &self.cfg.blocks[start];
        let false0 = block.successors[0]; // ConditionalFalse = JMP target = T (body)
        let true0 = block.successors[1];  // ConditionalTrue = next test

        let body_target = false0;
        let mut chain = vec![start]; // blocks in the chain
        let mut current = true0;

        // Follow the chain
        loop {
            if current >= self.cfg.num_blocks() { return None; }
            if !self.is_conditional_block(&self.cfg.blocks[current]) { return None; }
            if self.block_contains_testset(current) { return None; }

            let cur_block = &self.cfg.blocks[current];
            let cur_false = cur_block.successors[0]; // ConditionalFalse
            let cur_true = cur_block.successors[1];  // ConditionalTrue

            if cur_false == body_target {
                // Intermediate block: false → T, true → next
                chain.push(current);
                current = cur_true;
            } else if cur_true == body_target {
                // Last block: true → T, false → continuation
                chain.push(current);
                let continuation = cur_false;

                // Build the combined OR condition
                return Some(self.emit_or_chain(&chain, body_target, continuation, stmts));
            } else {
                // Doesn't match the OR pattern
                return None;
            }
        }
    }

    /// Emit an OR chain as a single `if` statement.
    fn emit_or_chain(
        &mut self,
        chain: &[usize],
        body_target: usize,
        continuation: usize,
        stmts: &mut Block,
    ) -> usize {
        let mut parts = Vec::new();

        for (i, &block_idx) in chain.iter().enumerate() {
            let block = self.cfg.blocks[block_idx].clone();
            let test_pc = self.find_test_pc(&block);

            // Lift pre-test instructions (updates register state)
            if let Some(tp) = test_pc {
                if tp > block.start {
                    self.lift_instructions(block.start, tp - 1, stmts);
                }
            }

            let cond = self.extract_condition(block_idx).unwrap_or(Expr::Bool(true));
            self.visited_blocks.insert(block_idx);

            let is_last = i == chain.len() - 1;
            if is_last {
                // Last block: ConditionalTrue → body, condition as-is
                parts.push(cond);
            } else {
                // Intermediate block: ConditionalFalse → body, negate condition
                parts.push(negate_expr(cond));
            }
        }

        // Combine with OR
        let combined = parts.into_iter().reduce(|a, b| {
            Expr::BinOp(BinOp::Or, Box::new(a), Box::new(b))
        }).unwrap_or(Expr::Bool(true));

        // Lift the body (target T)
        // Check if body is a guard clause (return)
        if self.is_return_block(body_target) {
            let then_block = self.lift_block_range(body_target, body_target + 1);
            stmts.push(Stat::If {
                cond: combined,
                then_block,
                elseif_clauses: Vec::new(),
                else_block: None,
            });
            return continuation;
        }

        // Normal if: body with potential else
        let merge = if self.block_flows_to(body_target, continuation) {
            Some(continuation)
        } else {
            self.find_merge_point(
                *chain.first().unwrap(),
                body_target,
                continuation,
            )
        };
        let then_end = merge.unwrap_or(continuation);
        let then_block = self.lift_block_range(body_target, then_end);

        let else_block = if let Some(m) = merge {
            if continuation < m {
                let eb = self.lift_block_range(continuation, m);
                if eb.is_empty() { None } else { Some(eb) }
            } else {
                None
            }
        } else {
            None
        };

        stmts.push(Stat::If {
            cond: combined,
            then_block,
            elseif_clauses: Vec::new(),
            else_block,
        });

        merge.unwrap_or(continuation.max(body_target) + 1)
    }

    /// Detect and lift an AND chain: `if A and B and ... then body end`.
    ///
    /// Pattern: all blocks have ConditionalFalse → END (common else/end target),
    /// ConditionalTrue chains to next test, last true → body.
    fn try_and_chain(&mut self, start: usize, stmts: &mut Block) -> Option<usize> {
        let block = &self.cfg.blocks[start];
        let false0 = block.successors[0]; // ConditionalFalse = JMP target = END
        let true0 = block.successors[1];  // ConditionalTrue = next test

        let end_target = false0;
        let mut chain = vec![start];
        let mut current = true0;

        // Follow the chain
        loop {
            if current >= self.cfg.num_blocks() {
                // Reached the end of blocks; body is current
                break;
            }
            if !self.is_conditional_block(&self.cfg.blocks[current]) {
                // Non-conditional block = body
                break;
            }
            if self.block_contains_testset(current) {
                return None;
            }

            let cur_block = &self.cfg.blocks[current];
            let cur_false = cur_block.successors[0];
            let cur_true = cur_block.successors[1];

            if cur_false == end_target {
                // Another AND block: false → END, true → next
                chain.push(current);
                current = cur_true;
            } else {
                // Doesn't match AND pattern
                return None;
            }
        }

        // Need at least 2 blocks for a chain
        if chain.len() < 2 { return None; }

        let body_target = current;

        // Build and emit the AND chain
        let mut parts = Vec::new();

        for &block_idx in &chain {
            let block = self.cfg.blocks[block_idx].clone();
            let test_pc = self.find_test_pc(&block);

            if let Some(tp) = test_pc {
                if tp > block.start {
                    self.lift_instructions(block.start, tp - 1, stmts);
                }
            }

            let cond = self.extract_condition(block_idx).unwrap_or(Expr::Bool(true));
            self.visited_blocks.insert(block_idx);
            parts.push(cond);
        }

        // Combine with AND
        let combined = parts.into_iter().reduce(|a, b| {
            Expr::BinOp(BinOp::And, Box::new(a), Box::new(b))
        }).unwrap_or(Expr::Bool(true));

        // Lift body and else
        let merge = if self.block_flows_to(body_target, end_target) {
            Some(end_target)
        } else {
            self.find_merge_point(
                *chain.first().unwrap(),
                body_target,
                end_target,
            )
        };
        let then_end = merge.unwrap_or(end_target);
        let then_block = self.lift_block_range(body_target, then_end);

        let else_block = if let Some(m) = merge {
            if end_target < m {
                let eb = self.lift_block_range(end_target, m);
                if eb.is_empty() { None } else { Some(eb) }
            } else {
                None
            }
        } else {
            None
        };

        stmts.push(Stat::If {
            cond: combined,
            then_block,
            elseif_clauses: Vec::new(),
            else_block,
        });

        Some(merge.unwrap_or(end_target.max(body_target) + 1))
    }

    /// Lift a range of instructions into statements.
    fn lift_instructions(&mut self, start_pc: usize, end_pc: usize, stmts: &mut Block) {
        let mut pc = start_pc;
        while pc <= end_pc {
            let inst = self.cfg.instructions[pc];
            match inst.op {
                OpCode::Move => {
                    let src = self.reg_expr(inst.b());
                    self.assign_reg_expr(pc, inst.a, src, stmts);
                }
                OpCode::LoadK => {
                    let expr = self.const_expr(inst.bx());
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::LoadBool => {
                    self.assign_reg_expr(pc, inst.a, Expr::Bool(inst.b() != 0), stmts);
                    if inst.c() != 0 {
                        pc += 1; // skip next instruction
                    }
                }
                OpCode::LoadNil => {
                    for r in inst.a..=inst.b() {
                        self.assign_reg_expr(pc, r, Expr::Nil, stmts);
                    }
                }
                OpCode::GetUpval => {
                    let expr = self.upvalue_expr(inst.b());
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::GetGlobal => {
                    let name = self.const_string(inst.bx());
                    self.assign_reg_expr(pc, inst.a, Expr::Global(name), stmts);
                }
                OpCode::GetTable => {
                    let table = self.reg_expr(inst.b());
                    let key = self.rk_expr(inst.c());
                    let expr = make_index(table, key);
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::SetGlobal => {
                    self.flush_pending_table(inst.a);
                    let name = self.const_string(inst.bx());
                    let val = self.reg_expr(inst.a);
                    stmts.push(Stat::Assign {
                        targets: vec![Expr::Global(name)],
                        values: vec![val],
                    });
                    self.capture_aliases
                        .insert(inst.a, Expr::Global(self.const_string(inst.bx())));
                }
                OpCode::SetUpval => {
                    let val = self.reg_expr(inst.a);
                    let uv = self.upvalue_expr(inst.b());
                    stmts.push(Stat::Assign {
                        targets: vec![uv],
                        values: vec![val],
                    });
                }
                OpCode::SetTable => {
                    // Check if this is part of table construction
                    let is_pending = self.pending_tables.contains_key(&inst.a);
                    if is_pending {
                        let key = self.rk_expr(inst.b());
                        let val = self.rk_expr(inst.c());
                        let fields = self.pending_tables.get_mut(&inst.a).unwrap();
                        // If key is a string identifier, use NameField
                        if let Expr::StringLit(ref s) = key {
                            if let Ok(name) = std::str::from_utf8(s) {
                                if is_identifier(name) {
                                    fields.push(TableField::NameField(
                                        name.to_string(),
                                        val,
                                    ));
                                    pc += 1;
                                    continue;
                                }
                            }
                        }
                        fields.push(TableField::IndexField(key, val));
                        pc += 1;
                        continue;
                    }
                    // Flush any pending table first
                    self.flush_pending_table(inst.a);
                    let table = self.reg_expr(inst.a);
                    let key = self.rk_expr(inst.b());
                    let val = self.rk_expr(inst.c());
                    let target = make_index(table, key);
                    stmts.push(Stat::Assign {
                        targets: vec![target.clone()],
                        values: vec![val],
                    });
                    if !is_k(inst.c()) {
                        self.capture_aliases.insert(inst.c(), target);
                    }
                }
                OpCode::NewTable => {
                    self.assign_reg_expr(pc, inst.a, Expr::Table(Vec::new()), stmts);
                    self.pending_tables.insert(inst.a, Vec::new());
                }
                OpCode::Self_ => {
                    let table = self.reg_expr(inst.b());
                    let method = self.rk_expr(inst.c());
                    let method_ref = make_index(table.clone(), method);
                    self.assign_reg_expr(pc, inst.a + 1, table, stmts);
                    self.assign_reg_expr(pc, inst.a, method_ref, stmts);
                }
                OpCode::Add => {
                    let expr = Expr::BinOp(
                        BinOp::Add,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Sub => {
                    let expr = Expr::BinOp(
                        BinOp::Sub,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Mul => {
                    let expr = Expr::BinOp(
                        BinOp::Mul,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Div => {
                    let expr = Expr::BinOp(
                        BinOp::Div,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Mod => {
                    let expr = Expr::BinOp(
                        BinOp::Mod,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Pow => {
                    let expr = Expr::BinOp(
                        BinOp::Pow,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Unm => {
                    let expr = Expr::UnOp(UnOp::Neg, Box::new(self.reg_expr(inst.b())));
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Not => {
                    let expr = Expr::UnOp(UnOp::Not, Box::new(self.reg_expr(inst.b())));
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Len => {
                    let expr = Expr::UnOp(UnOp::Len, Box::new(self.reg_expr(inst.b())));
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Concat => {
                    let b = inst.b();
                    let c = inst.c();
                    let mut expr = self.reg_expr(b);
                    for r in (b + 1)..=c {
                        expr = Expr::BinOp(
                            BinOp::Concat,
                            Box::new(expr),
                            Box::new(self.reg_expr(r)),
                        );
                    }
                    self.assign_reg_expr(pc, inst.a, expr, stmts);
                }
                OpCode::Jmp => {
                    // Jumps are handled by the CFG; skip here
                }
                OpCode::Eq | OpCode::Lt | OpCode::Le => {
                    // Comparison tests: handled at block level for conditionals
                    pc += 1; // skip following JMP
                }
                OpCode::Test => {
                    // Handled at conditional level
                    pc += 1;
                }
                OpCode::TestSet => {
                    // R(A) := R(B) if R(B) <=> C, else skip
                    pc += 1;
                }
                OpCode::Call => {
                    let func = self.reg_expr(inst.a);
                    let num_args = if inst.b() == 0 {
                        0 // variable args - simplified
                    } else {
                        inst.b() - 1
                    };
                    let args: Vec<Expr> = (0..num_args)
                        .map(|i| self.reg_expr(inst.a + 1 + i))
                        .collect();
                    let call = CallExpr { func, args };

                    if inst.c() == 1 {
                        // C==1: no return values -> statement call
                        stmts.push(Stat::Call(call));
                    } else if inst.c() == 0 {
                        // C==0: variable return values (used by next CALL/RETURN/SETLIST)
                        self.set_reg(inst.a, Expr::FuncCall(Box::new(call)));
                    } else {
                        // C>=2: fixed return values (C-1 results)
                        let num_results = inst.c() - 1;
                        if num_results == 1 {
                            let call_expr = Expr::FuncCall(Box::new(call));
                            // Use liveness: only create a local if the result
                            // is used later
                            let live = is_reg_live_after(
                                &self.cfg, &self.liveness, pc, inst.a,
                            );
                            if live {
                                self.set_reg_local(inst.a, call_expr, stmts);
                            } else {
                                // Result not used -> emit as statement
                                if let Expr::FuncCall(c) = call_expr {
                                    stmts.push(Stat::Call(*c));
                                }
                            }
                        } else {
                            // Multiple fixed return values -> local multi-assign
                            let names: Vec<String> = (0..num_results)
                                .map(|i| {
                                    let r = inst.a + i;
                                    let name = self.make_local_name(r);
                                    self.local_names.insert(r, name.clone());
                                    self.declared_locals.insert(r);
                                    name
                                })
                                .collect();
                            stmts.push(Stat::LocalAssign {
                                names: names.clone(),
                                exprs: vec![Expr::FuncCall(Box::new(call))],
                            });
                            for (i, name) in names.iter().enumerate() {
                                let r = (inst.a + i as u32) as usize;
                                if r < self.regs.len() {
                                    self.regs[r] = Some(Expr::Name(name.clone()));
                                }
                            }
                        }
                    }
                }
                OpCode::TailCall => {
                    let func = self.reg_expr(inst.a);
                    let num_args = if inst.b() == 0 {
                        0
                    } else {
                        inst.b() - 1
                    };
                    let args: Vec<Expr> = (0..num_args)
                        .map(|i| self.reg_expr(inst.a + 1 + i))
                        .collect();
                    let call = CallExpr { func, args };
                    stmts.push(Stat::Return(vec![Expr::FuncCall(Box::new(call))]));
                }
                OpCode::Return => {
                    let num_ret = if inst.b() == 0 {
                        0
                    } else {
                        inst.b() - 1
                    };
                    if num_ret == 0 && inst.a == 0 {
                        // `return` with no values at end of function - may be implicit
                        if pc != end_pc || end_pc != self.cfg.instructions.len() - 1 {
                            stmts.push(Stat::Return(Vec::new()));
                        }
                    } else {
                        let vals: Vec<Expr> = (0..num_ret)
                            .map(|i| self.reg_expr(inst.a + i))
                            .collect();
                        stmts.push(Stat::Return(vals));
                    }
                }
                OpCode::ForLoop | OpCode::ForPrep => {
                    // Handled by loop lifting
                }
                OpCode::TForLoop => {
                    // Handled by loop lifting
                }
                OpCode::SetList => {
                    let table_reg = inst.a;
                    let num = if inst.b() == 0 { 0 } else { inst.b() };
                    // Items are in registers A+1 .. A+num
                    // Flush any pending subtables in those registers first
                    for i in 1..=num {
                        self.flush_pending_table(table_reg + i);
                    }
                    // Collect values
                    let values: Vec<Expr> = (1..=num)
                        .map(|i| self.reg_expr(table_reg + i))
                        .collect();
                    if let Some(fields) = self.pending_tables.get_mut(&table_reg) {
                        for val in values {
                            fields.push(TableField::Value(val));
                        }
                    }
                }
                OpCode::Close => {
                    // Internal VM operation, no visible effect in source
                }
                OpCode::Closure => {
                    let closure_pc = pc;
                    let proto_idx = inst.bx() as usize;
                    let sub_func = if proto_idx < self.chunk.prototypes.len() {
                        let sub_chunk = &self.chunk.prototypes[proto_idx];
                        let resolved = self.resolve_closure_upvalues(pc, sub_chunk, stmts);
                        Lifter::decompile_with_upvalues(sub_chunk, resolved)
                    } else {
                        Function {
                            params: Vec::new(),
                            is_vararg: false,
                            body: Vec::new(),
                        }
                    };
                    if proto_idx < self.chunk.prototypes.len() {
                        pc += self.chunk.prototypes[proto_idx].num_upvalues as usize;
                    }
                    self.assign_reg_expr(
                        closure_pc,
                        inst.a,
                        Expr::FunctionDef(Box::new(sub_func)),
                        stmts,
                    );
                }
                OpCode::VarArg => {
                    self.assign_reg_expr(pc, inst.a, Expr::VarArg, stmts);
                }
            }
            pc += 1;
        }
    }

    // -- Helper methods --

    fn set_reg(&mut self, reg: u32, expr: Expr) {
        let r = reg as usize;
        if r < self.regs.len() {
            self.regs[r] = Some(expr);
        }
        // Clear local name mapping so reg_expr returns the actual expression
        // instead of the old local name. The local is now dead (overwritten).
        self.local_names.remove(&reg);
        // Clear any pending table — the register is being overwritten with
        // a completely new value, so any table construction for this register
        // is finished (or abandoned).
        self.pending_tables.remove(&reg);
        self.capture_aliases.remove(&reg);
    }

    /// Set a register and potentially emit a `local` declaration if this is a
    /// new local variable (register above params, first assignment).
    fn set_reg_local(&mut self, reg: u32, expr: Expr, stmts: &mut Block) {
        if reg >= self.num_params && !self.declared_locals.contains(&reg) {
            // First assignment to this register -> declare local
            self.declared_locals.insert(reg);
            let name = self.make_local_name_for_expr(reg, &expr);
            self.local_names.insert(reg, name.clone());
            let r = reg as usize;
            if r < self.regs.len() {
                self.regs[r] = Some(Expr::Name(name.clone()));
            }
            stmts.push(Stat::LocalAssign {
                names: vec![name],
                exprs: vec![expr],
            });
        } else if let Some(name) = self.local_names.get(&reg).cloned() {
            // Already declared -> emit assignment
            let r = reg as usize;
            if r < self.regs.len() {
                self.regs[r] = Some(Expr::Name(name.clone()));
            }
            stmts.push(Stat::Assign {
                targets: vec![Expr::Name(name)],
                values: vec![expr],
            });
        } else {
            // Parameter register -> just update
            let r = reg as usize;
            if r < self.regs.len() {
                self.regs[r] = Some(expr);
            }
        }
    }

    fn assign_reg_expr(&mut self, pc: usize, reg: u32, expr: Expr, stmts: &mut Block) {
        let block_id = self.cfg.block_of(pc);
        let live_out_of_block = (reg as usize) < self.liveness.max_reg
            && self.liveness.live_out[block_id][reg as usize];

        if self.accumulator_regs.contains(&reg)
            && reg >= self.num_params
            && live_out_of_block
        {
            self.set_reg_local(reg, expr, stmts);
        } else {
            self.set_reg(reg, expr);
        }
    }

    fn resolve_closure_upvalues(
        &mut self,
        pc: usize,
        sub_chunk: &LuaChunk,
        stmts: &mut Block,
    ) -> Vec<Option<Expr>> {
        let num_upvalues = sub_chunk.num_upvalues as usize;
        let mut resolved = Vec::with_capacity(num_upvalues);

        for offset in 0..num_upvalues {
            let capture_pc = pc + 1 + offset;
            if capture_pc >= self.cfg.instructions.len() {
                resolved.push(None);
                continue;
            }

            let capture = self.cfg.instructions[capture_pc];
            let expr = match capture.op {
                OpCode::Move => Some(self.capture_stack_upvalue(capture.b(), capture_pc, stmts)),
                OpCode::GetUpval => Some(self.upvalue_expr(capture.b())),
                _ => None,
            };
            resolved.push(expr);
        }

        resolved
    }

    fn capture_stack_upvalue(&mut self, reg: u32, pc: usize, stmts: &mut Block) -> Expr {
        if let Some(name) = self.local_names.get(&reg).cloned() {
            return Expr::Name(name);
        }

        if reg < self.num_params {
            let name = self.local_name(reg, pc);
            self.local_names.insert(reg, name.clone());
            let r = reg as usize;
            if r < self.regs.len() {
                self.regs[r] = Some(Expr::Name(name.clone()));
            }
            return Expr::Name(name);
        }

        if let Some(alias) = self.capture_aliases.get(&reg).cloned() {
            return alias;
        }

        match self.reg_expr(reg) {
            Expr::Name(name) => Expr::Name(name),
            Expr::Global(name) => Expr::Global(name),
            Expr::Upvalue(idx) => self.upvalue_expr(idx),
            Expr::Field(table, field) => Expr::Field(table, field),
            expr => {
                let name = self.local_name(reg, pc);
                self.local_names.insert(reg, name.clone());
                self.declared_locals.insert(reg);
                let r = reg as usize;
                if r < self.regs.len() {
                    self.regs[r] = Some(Expr::Name(name.clone()));
                }
                self.pending_tables.remove(&reg);
                self.capture_aliases.remove(&reg);
                stmts.push(Stat::LocalAssign {
                    names: vec![name.clone()],
                    exprs: vec![expr],
                });
                Expr::Name(name)
            }
        }
    }

    fn reg_expr(&self, reg: u32) -> Expr {
        // If this register has a local name, return the name reference
        if let Some(name) = self.local_names.get(&reg) {
            return Expr::Name(name.clone());
        }
        // If this register has a pending table with accumulated fields, return them
        if let Some(fields) = self.pending_tables.get(&reg) {
            if !fields.is_empty() {
                return Expr::Table(fields.clone());
            }
        }
        let r = reg as usize;
        if r < self.regs.len() {
            self.regs[r].clone().unwrap_or(Expr::Register(reg))
        } else {
            Expr::Register(reg)
        }
    }

    fn rk_expr(&self, rk: u32) -> Expr {
        if is_k(rk) {
            self.const_expr(index_k(rk))
        } else {
            self.reg_expr(rk)
        }
    }

    fn const_expr(&self, idx: u32) -> Expr {
        let i = idx as usize;
        if i >= self.chunk.constants.len() {
            return Expr::Nil;
        }
        match &self.chunk.constants[i] {
            LuaConstant::Null => Expr::Nil,
            LuaConstant::Bool(b) => Expr::Bool(*b),
            LuaConstant::Number(n) => match n {
                LuaNumber::Integer(v) => Expr::Number(NumLit::Int(*v)),
                LuaNumber::Float(v) => Expr::Number(NumLit::Float(*v)),
            },
            LuaConstant::String(s) => Expr::StringLit(s.as_ref().to_vec()),
            _ => Expr::Nil,
        }
    }

    fn const_string(&self, idx: u32) -> String {
        let i = idx as usize;
        if i < self.chunk.constants.len() {
            if let LuaConstant::String(s) = &self.chunk.constants[i] {
                return String::from_utf8_lossy(s.as_ref()).into_owned();
            }
        }
        format!("_K{}", idx)
    }

    fn upvalue_expr(&self, idx: u32) -> Expr {
        let i = idx as usize;
        if i < self.resolved_upvalues.len() {
            if let Some(expr) = &self.resolved_upvalues[i] {
                return expr.clone();
            }
        }
        if i < self.chunk.upvalue_names.len() {
            let name = String::from_utf8_lossy(&self.chunk.upvalue_names[i]).into_owned();
            if !name.is_empty() {
                return Expr::Name(name);
            }
        }
        Expr::Upvalue(idx)
    }

    fn local_name(&self, reg: u32, pc: usize) -> String {
        // Try debug info: locals are ordered by register assignment
        // In standard Lua 5.1 bytecode, the i-th local in the array corresponds
        // to register i (for the scope range start_pc..end_pc)
        for (i, local) in self.chunk.locals.iter().enumerate() {
            if i == reg as usize
                && local.start_pc as usize <= pc + 1
                && pc < local.end_pc as usize
            {
                if !local.name.is_empty() && !local.name.starts_with('(') {
                    return local.name.clone();
                }
            }
        }
        // Also scan all locals for any that match this register
        for local in &self.chunk.locals {
            if local.start_pc as usize <= pc + 1 && pc < local.end_pc as usize {
                // Use locals array index as register mapping
            }
        }
        // Fall back to matching by position in locals array for params
        let r = reg as usize;
        if r < self.chunk.locals.len() {
            let name = &self.chunk.locals[r].name;
            if !name.is_empty() && !name.starts_with('(') {
                return name.clone();
            }
        }
        self.make_local_name(reg)
    }

    fn make_local_name(&self, reg: u32) -> String {
        let current_expr = self.regs.get(reg as usize).and_then(|e| e.as_ref());
        self.make_local_name_from_known_expr(reg, current_expr)
    }

    fn make_local_name_for_expr(&self, reg: u32, expr: &Expr) -> String {
        self.make_local_name_from_known_expr(reg, Some(expr))
    }

    fn make_local_name_from_known_expr(&self, reg: u32, current_expr: Option<&Expr>) -> String {
        if reg < self.num_params {
            if self.has_debug_info {
                return self.local_name(reg, 0);
            }
            return format!("a{}", reg);
        }
        if let Some(name) = self.infer_accumulator_name(reg, current_expr) {
            return self.uniquify_local_name(name);
        }
        if let Some(fields) = self.pending_tables.get(&reg) {
            if !fields.is_empty() {
                if let Some(name) = self.infer_table_local_name(fields) {
                    return self.uniquify_local_name(name);
                }
            }
        }
        // For stripped bytecode, try to infer a meaningful name from context.
        // Look at what was last stored in this register.
        if let Some(expr) = current_expr {
            match expr {
                Expr::Table(fields) => {
                    if let Some(name) = self.infer_table_local_name(fields) {
                        return self.uniquify_local_name(name);
                    }
                }
                // If it's a global function call, name after the function
                Expr::FuncCall(call) => {
                    if let Some(name) = self.infer_call_local_name(call) {
                        return self.uniquify_local_name(name);
                    }
                    if let Expr::Global(name) = &call.func {
                        let short = normalize_call_name(name);
                        if short.len() <= 20 {
                            return self.uniquify_local_name(short);
                        }
                    }
                    // Method call: use method name
                    if let Expr::Field(_, method) = &call.func {
                        return self.uniquify_local_name(normalize_call_name(method));
                    }
                }
                _ => {}
            }
        }
        format!("l_{}", reg)
    }

    fn infer_accumulator_name(&self, reg: u32, expr: Option<&Expr>) -> Option<String> {
        if !self.accumulator_regs.contains(&reg) || !self.is_returned_reg(reg) {
            return None;
        }

        match expr {
            Some(Expr::Number(_)) | None => Some("result".to_string()),
            _ => None,
        }
    }

    fn infer_call_local_name(&self, call: &CallExpr) -> Option<String> {
        let method = match &call.func {
            Expr::Field(_, method) => method.as_str(),
            Expr::Global(name) => name.as_str(),
            _ => return None,
        };

        let first_int_arg = match call.args.first() {
            Some(Expr::Number(NumLit::Int(value))) => Some(*value),
            Some(Expr::Number(NumLit::Float(value))) if value.fract() == 0.0 => Some(*value as i64),
            _ => None,
        };

        match method {
            "IsHaveBuff" => Some(match first_int_arg {
                Some(id) => format!("has_buff_{}", id),
                None => "has_buff".to_string(),
            }),
            "GetBuff" | "GetBuffByOwner" => Some(match first_int_arg {
                Some(id) => format!("buff_{}", id),
                None => "buff".to_string(),
            }),
            "GetSkillLevel" => first_int_arg.map(|id| format!("skill_{}", id)),
            "GetEndTime" => Some("end_time".to_string()),
            "GetLogicFrameCount" => Some("logic_frame_count".to_string()),
            _ => None,
        }
    }

    fn is_returned_reg(&self, reg: u32) -> bool {
        self.cfg.instructions.iter().any(|inst| {
            inst.op == OpCode::Return && inst.a == reg && inst.b() == 2
        })
    }

    fn uniquify_local_name(&self, base: String) -> String {
        if !self.local_names.values().any(|name| name == &base) {
            return base;
        }

        let mut suffix = 1;
        loop {
            let candidate = format!("{}_{}", base, suffix);
            if !self.local_names.values().any(|name| name == &candidate) {
                return candidate;
            }
            suffix += 1;
        }
    }

    fn infer_table_local_name(&self, fields: &[TableField]) -> Option<String> {
        if fields.is_empty() {
            return None;
        }

        if fields.iter().all(|field| matches!(field, TableField::IndexField(_, Expr::Bool(true)))) {
            if fields.iter().any(|field| {
                matches!(field, TableField::IndexField(key, _) if self.expr_mentions_field(key, "ENUM"))
            }) {
                return Some("enum_lookup".to_string());
            }
            return Some("lookup".to_string());
        }

        if fields.iter().all(|field| matches!(field, TableField::NameField(_, Expr::Number(_)))) {
            let keys: Vec<&str> = fields
                .iter()
                .filter_map(|field| match field {
                    TableField::NameField(name, _) => Some(name.as_str()),
                    _ => None,
                })
                .collect();
            if keys.iter().any(|name| name.contains("NOT_")) {
                return Some("penalties".to_string());
            }
            if keys.iter().all(|name| is_upper_ident(name)) {
                return Some("modifiers".to_string());
            }
        }

        None
    }

    fn expr_mentions_field(&self, expr: &Expr, field_name: &str) -> bool {
        match expr {
            Expr::Field(table, field) => field == field_name || self.expr_mentions_field(table, field_name),
            Expr::Index(table, key) => {
                self.expr_mentions_field(table, field_name)
                    || self.expr_mentions_field(key, field_name)
            }
            Expr::MethodCall(call) | Expr::FuncCall(call) => {
                self.expr_mentions_field(&call.func, field_name)
                    || call.args.iter().any(|arg| self.expr_mentions_field(arg, field_name))
            }
            Expr::BinOp(_, lhs, rhs) => {
                self.expr_mentions_field(lhs, field_name)
                    || self.expr_mentions_field(rhs, field_name)
            }
            Expr::UnOp(_, inner) => self.expr_mentions_field(inner, field_name),
            Expr::Table(fields) => fields.iter().any(|field| match field {
                TableField::IndexField(key, value) => {
                    self.expr_mentions_field(key, field_name)
                        || self.expr_mentions_field(value, field_name)
                }
                TableField::NameField(_, value) | TableField::Value(value) => {
                    self.expr_mentions_field(value, field_name)
                }
            }),
            _ => false,
        }
    }

    /// Flush the pending table construction for a specific register.
    fn flush_pending_table(&mut self, reg: u32) {
        if let Some(fields) = self.pending_tables.remove(&reg) {
            self.set_reg(reg, Expr::Table(fields));
        }
    }

    /// Check if a block consists of only a RETURN (or RETURN with values).
    fn is_return_block(&self, block_idx: usize) -> bool {
        if block_idx >= self.cfg.num_blocks() {
            return false;
        }
        let block = &self.cfg.blocks[block_idx];
        let last = self.cfg.instructions[block.end];
        matches!(last.op, OpCode::Return | OpCode::TailCall)
            && block.successors.is_empty()
    }

    /// Find the PC of the test instruction in a conditional block.
    fn find_test_pc(&self, block: &BasicBlock) -> Option<usize> {
        for pc in block.start..=block.end {
            let inst = self.cfg.instructions[pc];
            if matches!(
                inst.op,
                OpCode::Eq | OpCode::Lt | OpCode::Le | OpCode::Test | OpCode::TestSet
            ) {
                return Some(pc);
            }
        }
        None
    }

    fn find_loop_at(&self, block_idx: usize) -> Option<&NaturalLoop> {
        self.loops.iter().find(|l| l.header == block_idx)
    }

    fn find_forprep_block(&self, header: usize) -> Option<usize> {
        // Look for a predecessor of the header that ends with FORPREP
        for &pred in &self.cfg.blocks[header].predecessors {
            let pred_block = &self.cfg.blocks[pred];
            let last = self.cfg.instructions[pred_block.end];
            if last.op == OpCode::ForPrep {
                return Some(pred);
            }
        }
        // Also check if it's one block before header
        if header > 0 {
            let prev = &self.cfg.blocks[header - 1];
            let last = self.cfg.instructions[prev.end];
            if last.op == OpCode::ForPrep {
                return Some(header - 1);
            }
        }
        None
    }

    fn max_loop_block(&self, lp: &NaturalLoop) -> usize {
        lp.body.iter().copied().max().unwrap_or(lp.header)
    }

    fn is_conditional_block(&self, block: &BasicBlock) -> bool {
        block.successors.len() == 2
            && self.cfg.edges.iter().any(|e| {
                e.from == block.id
                    && matches!(
                        e.kind,
                        EdgeKind::ConditionalTrue | EdgeKind::ConditionalFalse
                    )
            })
    }

    fn block_contains_testset(&self, block_idx: usize) -> bool {
        if block_idx >= self.cfg.num_blocks() {
            return false;
        }
        let block = &self.cfg.blocks[block_idx];
        (block.start..=block.end).any(|pc| self.cfg.instructions[pc].op == OpCode::TestSet)
    }

    fn block_flows_to(&self, from_block: usize, target_block: usize) -> bool {
        if from_block >= self.cfg.num_blocks() || target_block >= self.cfg.num_blocks() {
            return false;
        }
        self.cfg.blocks[from_block].successors.iter().all(|&succ| succ == target_block)
    }

    fn find_accumulator_regs(&self) -> HashSet<u32> {
        let mut regs = HashSet::new();

        for inst in &self.cfg.instructions {
            match inst.op {
                OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div | OpCode::Mod | OpCode::Pow => {
                    let uses_target = (!is_k(inst.b()) && inst.a == inst.b())
                        || (!is_k(inst.c()) && inst.a == inst.c());
                    if uses_target {
                        regs.insert(inst.a);
                    }
                }
                OpCode::Concat => {
                    if inst.a >= inst.b() && inst.a <= inst.c() {
                        regs.insert(inst.a);
                    }
                }
                _ => {}
            }
        }

        regs
    }

    fn extract_condition(&self, block_idx: usize) -> Option<Expr> {
        let block = &self.cfg.blocks[block_idx];
        // Look for the test instruction (second-to-last, before JMP)
        for pc in block.start..=block.end {
            let inst = self.cfg.instructions[pc];
            match inst.op {
                OpCode::Eq => {
                    let lhs = self.rk_expr(inst.b());
                    let rhs = self.rk_expr(inst.c());
                    return Some(if inst.a == 0 {
                        Expr::BinOp(BinOp::Eq, Box::new(lhs), Box::new(rhs))
                    } else {
                        Expr::BinOp(BinOp::Ne, Box::new(lhs), Box::new(rhs))
                    });
                }
                OpCode::Lt => {
                    let lhs = self.rk_expr(inst.b());
                    let rhs = self.rk_expr(inst.c());
                    return Some(if inst.a == 0 {
                        Expr::BinOp(BinOp::Lt, Box::new(lhs), Box::new(rhs))
                    } else {
                        Expr::BinOp(BinOp::Ge, Box::new(lhs), Box::new(rhs))
                    });
                }
                OpCode::Le => {
                    let lhs = self.rk_expr(inst.b());
                    let rhs = self.rk_expr(inst.c());
                    return Some(if inst.a == 0 {
                        Expr::BinOp(BinOp::Le, Box::new(lhs), Box::new(rhs))
                    } else {
                        Expr::BinOp(BinOp::Gt, Box::new(lhs), Box::new(rhs))
                    });
                }
                OpCode::Test => {
                    let expr = self.reg_expr(inst.a);
                    return Some(if inst.c() == 0 {
                        expr
                    } else {
                        Expr::UnOp(UnOp::Not, Box::new(expr))
                    });
                }
                OpCode::TestSet => {
                    let expr = self.reg_expr(inst.b());
                    return Some(if inst.c() == 0 {
                        expr
                    } else {
                        Expr::UnOp(UnOp::Not, Box::new(expr))
                    });
                }
                _ => {}
            }
        }
        None
    }

    fn find_merge_point(
        &self,
        cond_block: usize,
        true_block: usize,
        false_block: usize,
    ) -> Option<usize> {
        if false_block < self.cfg.num_blocks() {
            let false_preds = &self.cfg.blocks[false_block].predecessors;
            if false_preds.len() >= 3
                && false_preds.contains(&cond_block)
                && false_preds
                    .iter()
                    .any(|&pred| pred != cond_block && pred >= true_block && pred < false_block)
            {
                return Some(false_block);
            }
        }

        // Simple heuristic: the merge point is the smallest block ID
        // that is a successor of both branches (or the false_block if
        // the true block falls through to it).
        let max_branch = true_block.max(false_block);

        // Look for a block after both branches where control re-merges.
        for b in (max_branch + 1)..self.cfg.num_blocks() {
            let block = &self.cfg.blocks[b];
            if block.predecessors.len() >= 2 {
                return Some(b);
            }
            if !block
                .predecessors
                .iter()
                .all(|&p| p >= true_block && p <= max_branch)
                && block.predecessors.iter().any(|&p| p >= true_block)
            {
                return Some(b);
            }
        }

        if false_block > true_block && false_block > cond_block {
            return Some(false_block);
        }

        None
    }
}

/// Build a field access or index expression.
fn make_index(table: Expr, key: Expr) -> Expr {
    // If key is a string that's a valid identifier, use Field syntax
    if let Expr::StringLit(ref s) = key {
        if let Ok(name) = std::str::from_utf8(s) {
            if is_identifier(name) {
                return Expr::Field(Box::new(table), name.to_string());
            }
        }
    }
    Expr::Index(Box::new(table), Box::new(key))
}

/// Check if a string is a valid Lua identifier.
fn is_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let mut chars = s.chars();
    let first = chars.next().unwrap();
    if !first.is_ascii_alphabetic() && first != '_' {
        return false;
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !is_lua_keyword(s)
}

fn is_upper_ident(s: &str) -> bool {
    !s.is_empty()
        && s
            .chars()
            .all(|c| c == '_' || c.is_ascii_uppercase() || c.is_ascii_digit())
}

fn normalize_call_name(name: &str) -> String {
    let snake = camel_to_snake(name);
    snake
        .strip_prefix("get_")
        .or_else(|| snake.strip_prefix("is_"))
        .map(ToOwned::to_owned)
        .unwrap_or(snake)
}

fn camel_to_snake(name: &str) -> String {
    let mut out = String::new();
    for (idx, ch) in name.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if idx != 0 {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

fn is_lua_keyword(s: &str) -> bool {
    matches!(
        s,
        "and"
            | "break"
            | "do"
            | "else"
            | "elseif"
            | "end"
            | "false"
            | "for"
            | "function"
            | "if"
            | "in"
            | "local"
            | "nil"
            | "not"
            | "or"
            | "repeat"
            | "return"
            | "then"
            | "true"
            | "until"
            | "while"
    )
}

/// Negate an expression (for inverting conditions).
fn negate_expr(expr: Expr) -> Expr {
    match expr {
        Expr::UnOp(UnOp::Not, inner) => *inner,
        Expr::BinOp(BinOp::Eq, a, b) => Expr::BinOp(BinOp::Ne, a, b),
        Expr::BinOp(BinOp::Ne, a, b) => Expr::BinOp(BinOp::Eq, a, b),
        Expr::BinOp(BinOp::Lt, a, b) => Expr::BinOp(BinOp::Ge, a, b),
        Expr::BinOp(BinOp::Ge, a, b) => Expr::BinOp(BinOp::Lt, a, b),
        Expr::BinOp(BinOp::Le, a, b) => Expr::BinOp(BinOp::Gt, a, b),
        Expr::BinOp(BinOp::Gt, a, b) => Expr::BinOp(BinOp::Le, a, b),
        Expr::Bool(b) => Expr::Bool(!b),
        other => Expr::UnOp(UnOp::Not, Box::new(other)),
    }
}
