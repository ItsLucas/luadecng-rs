use std::collections::{HashMap, HashSet};

use luac_parser::LuaChunk;

use crate::lua51::ast::*;
use crate::lua51::cfg::ControlFlowGraph;
use crate::lua51::dominator::{find_loops, DominatorTree, LoopKind, NaturalLoop};
use crate::lua51::liveness::{compute_liveness, LivenessInfo};
use crate::lua51::opcodes::OpCode;

mod instruction;
mod naming;
mod or_and;
mod register;
mod util;

use util::negate_expr;

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
    /// Active loop headers being lifted to avoid re-entering the same loop.
    active_loop_headers: Vec<usize>,
    /// Exit blocks for active loops, innermost last.
    active_loop_exits: Vec<usize>,
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
            active_loop_headers: Vec::new(),
            active_loop_exits: Vec::new(),
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
            if self.visited_blocks.contains(&block_idx) {
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

            self.visited_blocks.insert(block_idx);

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
                if self.current_loop_exit() == Some(target) {
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
        let loop_exit = self.max_loop_block(lp) + 1;

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
            if !self.visited_blocks.contains(&fb) {
                let b = &self.cfg.blocks[fb].clone();
                self.visited_blocks.insert(fb);
                // Lift instructions before FORPREP to set up init/limit/step
                if b.end > b.start {
                    self.lift_instructions(b.start, b.end - 1, stmts);
                }
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

        self.active_loop_headers.push(lp.header);
        self.active_loop_exits.push(loop_exit);
        let body = self.lift_block_range(lp.header, lp.latch + 1);
        self.active_loop_exits.pop();
        self.active_loop_headers.pop();

        stmts.push(Stat::NumericFor {
            name: var_name,
            start: start_expr,
            limit: limit_expr,
            step,
            body,
        });

        // Return the block after the loop exit
        loop_exit
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

        self.active_loop_headers.push(lp.header);
        self.active_loop_exits.push(self.max_loop_block(lp) + 1);
        let body = if !body_blocks.is_empty() {
            let first = *body_blocks.first().unwrap();
            let last = *body_blocks.last().unwrap();
            self.lift_block_range(first, last + 1)
        } else {
            Vec::new()
        };
        self.active_loop_exits.pop();
        self.active_loop_headers.pop();

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
        self.active_loop_headers.push(lp.header);
        self.active_loop_exits.push(self.max_loop_block(lp) + 1);
        let body_start = lp.header + 1;
        let body_end = lp.latch + 1;
        let body = self.lift_block_range(body_start, body_end);
        self.active_loop_exits.pop();
        self.active_loop_headers.pop();

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
}
