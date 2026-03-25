use crate::lua51::ast::*;
use crate::lua51::liveness::is_reg_live_after;
use crate::lua51::opcodes::OpCode;
use super::Lifter;
use super::util::{make_index, is_identifier};

impl<'a> Lifter<'a> {
    /// Lift a range of instructions into statements.
    pub(super) fn lift_instructions(&mut self, start_pc: usize, end_pc: usize, stmts: &mut Block) {
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
                    if !crate::lua51::instruction::is_k(inst.c()) {
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
}
