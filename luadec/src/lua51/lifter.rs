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
    dom: DominatorTree,
    loops: Vec<NaturalLoop>,
    liveness: LivenessInfo,
    /// Register expressions: tracks what expression is currently held in each register.
    regs: Vec<Option<Expr>>,
    /// Pending tables being constructed (register -> accumulated fields).
    pending_tables: HashMap<u32, Vec<TableField>>,
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
    /// Loop exit block IDs for break detection.
    loop_exits: HashSet<usize>,
}

impl<'a> Lifter<'a> {
    pub fn decompile(chunk: &'a LuaChunk) -> Function {
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
            dom,
            loops,
            liveness,
            regs: vec![None; max_stack.max(256)],
            pending_tables: HashMap::new(),
            visited_blocks: HashSet::new(),
            local_names: HashMap::new(),
            declared_locals: HashSet::new(),
            num_params: chunk.num_params as u32,
            has_debug_info,
            loop_exits,
        };

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

        // Find TFORLOOP instruction in the latch block
        let latch_block = &self.cfg.blocks[lp.latch].clone();
        let mut tforloop_inst = None;
        for pc in latch_block.start..=latch_block.end {
            if self.cfg.instructions[pc].op == OpCode::TForLoop {
                tforloop_inst = Some(self.cfg.instructions[pc]);
                break;
            }
        }
        let tfl = tforloop_inst.unwrap_or(self.cfg.instructions[latch_block.end]);

        let base = tfl.a;
        let num_vars = tfl.c();

        let names: Vec<String> = (0..num_vars)
            .map(|i| self.local_name(base + 3 + i, header.start))
            .collect();
        let iter_expr = self.reg_expr(base);

        let body_start = lp.header;
        let body_end = lp.latch;
        let body = if body_start < body_end {
            self.lift_block_range(body_start, body_end)
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
        if self.is_return_block(true_target) && false_target > true_target {
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
        if self.is_return_block(false_target) && true_target < false_target {
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

    /// Lift a range of instructions into statements.
    fn lift_instructions(&mut self, start_pc: usize, end_pc: usize, stmts: &mut Block) {
        let mut pc = start_pc;
        while pc <= end_pc {
            let inst = self.cfg.instructions[pc];
            match inst.op {
                OpCode::Move => {
                    let src = self.reg_expr(inst.b());
                    self.set_reg(inst.a, src);
                }
                OpCode::LoadK => {
                    let expr = self.const_expr(inst.bx());
                    self.set_reg(inst.a, expr);
                }
                OpCode::LoadBool => {
                    self.set_reg(inst.a, Expr::Bool(inst.b() != 0));
                    if inst.c() != 0 {
                        pc += 1; // skip next instruction
                    }
                }
                OpCode::LoadNil => {
                    for r in inst.a..=inst.b() {
                        self.set_reg(r, Expr::Nil);
                    }
                }
                OpCode::GetUpval => {
                    let expr = self.upvalue_expr(inst.b());
                    self.set_reg(inst.a, expr);
                }
                OpCode::GetGlobal => {
                    let name = self.const_string(inst.bx());
                    self.set_reg(inst.a, Expr::Global(name));
                }
                OpCode::GetTable => {
                    let table = self.reg_expr(inst.b());
                    let key = self.rk_expr(inst.c());
                    let expr = make_index(table, key);
                    self.set_reg(inst.a, expr);
                }
                OpCode::SetGlobal => {
                    self.flush_pending_table(inst.a);
                    let name = self.const_string(inst.bx());
                    let val = self.reg_expr(inst.a);
                    stmts.push(Stat::Assign {
                        targets: vec![Expr::Global(name)],
                        values: vec![val],
                    });
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
                        targets: vec![target],
                        values: vec![val],
                    });
                }
                OpCode::NewTable => {
                    self.set_reg(inst.a, Expr::Table(Vec::new()));
                    self.pending_tables.insert(inst.a, Vec::new());
                }
                OpCode::Self_ => {
                    let table = self.reg_expr(inst.b());
                    let method = self.rk_expr(inst.c());
                    let method_ref = make_index(table.clone(), method);
                    self.set_reg(inst.a + 1, table);
                    self.set_reg(inst.a, method_ref);
                }
                OpCode::Add => {
                    let expr = Expr::BinOp(
                        BinOp::Add,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.set_reg(inst.a, expr);
                }
                OpCode::Sub => {
                    let expr = Expr::BinOp(
                        BinOp::Sub,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.set_reg(inst.a, expr);
                }
                OpCode::Mul => {
                    let expr = Expr::BinOp(
                        BinOp::Mul,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.set_reg(inst.a, expr);
                }
                OpCode::Div => {
                    let expr = Expr::BinOp(
                        BinOp::Div,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.set_reg(inst.a, expr);
                }
                OpCode::Mod => {
                    let expr = Expr::BinOp(
                        BinOp::Mod,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.set_reg(inst.a, expr);
                }
                OpCode::Pow => {
                    let expr = Expr::BinOp(
                        BinOp::Pow,
                        Box::new(self.rk_expr(inst.b())),
                        Box::new(self.rk_expr(inst.c())),
                    );
                    self.set_reg(inst.a, expr);
                }
                OpCode::Unm => {
                    let expr = Expr::UnOp(UnOp::Neg, Box::new(self.reg_expr(inst.b())));
                    self.set_reg(inst.a, expr);
                }
                OpCode::Not => {
                    let expr = Expr::UnOp(UnOp::Not, Box::new(self.reg_expr(inst.b())));
                    self.set_reg(inst.a, expr);
                }
                OpCode::Len => {
                    let expr = Expr::UnOp(UnOp::Len, Box::new(self.reg_expr(inst.b())));
                    self.set_reg(inst.a, expr);
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
                    self.set_reg(inst.a, expr);
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
                    let proto_idx = inst.bx() as usize;
                    let sub_func = if proto_idx < self.chunk.prototypes.len() {
                        let sub_chunk = &self.chunk.prototypes[proto_idx];
                        Lifter::decompile(sub_chunk)
                    } else {
                        Function {
                            params: Vec::new(),
                            is_vararg: false,
                            body: Vec::new(),
                        }
                    };
                    self.set_reg(inst.a, Expr::FunctionDef(Box::new(sub_func)));
                }
                OpCode::VarArg => {
                    self.set_reg(inst.a, Expr::VarArg);
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
    }

    /// Set a register and potentially emit a `local` declaration if this is a
    /// new local variable (register above params, first assignment).
    fn set_reg_local(&mut self, reg: u32, expr: Expr, stmts: &mut Block) {
        if reg >= self.num_params && !self.declared_locals.contains(&reg) {
            // First assignment to this register -> declare local
            self.declared_locals.insert(reg);
            let name = self.make_local_name(reg);
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

    fn reg_expr(&self, reg: u32) -> Expr {
        // If this register has a local name, return the name reference
        if let Some(name) = self.local_names.get(&reg) {
            return Expr::Name(name.clone());
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
        if reg < self.num_params {
            if self.has_debug_info {
                return self.local_name(reg, 0);
            }
            return format!("a{}", reg);
        }
        // For stripped bytecode, try to infer a meaningful name from context.
        // Look at what was last stored in this register.
        if let Some(expr) = self.regs.get(reg as usize).and_then(|e| e.as_ref()) {
            match expr {
                // If it's a global function call, name after the function
                Expr::FuncCall(call) => {
                    if let Expr::Global(name) = &call.func {
                        let short = name.to_ascii_lowercase();
                        if short.len() <= 20 {
                            return short;
                        }
                    }
                    // Method call: use method name
                    if let Expr::Field(_, method) = &call.func {
                        return method.to_ascii_lowercase();
                    }
                }
                _ => {}
            }
        }
        format!("l_{}", reg)
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
        _cond_block: usize,
        true_block: usize,
        false_block: usize,
    ) -> Option<usize> {
        // Simple heuristic: the merge point is the smallest block ID
        // that is a successor of both branches (or the false_block if
        // the true block falls through to it).
        let max_branch = true_block.max(false_block);

        // Look for a block after both branches where control re-merges
        for b in (max_branch + 1)..self.cfg.num_blocks() {
            let block = &self.cfg.blocks[b];
            if block.predecessors.len() >= 2 {
                return Some(b);
            }
            // If this block has no predecessors from within the if branches,
            // it's likely the merge.
            if !block.predecessors.iter().all(|&p| {
                p >= true_block && p <= max_branch
            }) && block.predecessors.iter().any(|&p| p >= true_block) {
                return Some(b);
            }
        }

        // Fallback: if false_block > true_block, false might be the merge
        if false_block > true_block {
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
