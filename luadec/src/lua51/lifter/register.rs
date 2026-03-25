use luac_parser::{LuaChunk, LuaConstant, LuaNumber};

use crate::lua51::ast::*;
use crate::lua51::instruction::{is_k, index_k};
use crate::lua51::opcodes::OpCode;
use super::Lifter;

impl<'a> Lifter<'a> {
    pub(super) fn set_reg(&mut self, reg: u32, expr: Expr) {
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
    pub(super) fn set_reg_local(&mut self, reg: u32, expr: Expr, stmts: &mut Block) {
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

    pub(super) fn assign_reg_expr(&mut self, pc: usize, reg: u32, expr: Expr, stmts: &mut Block) {
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

    pub(super) fn resolve_closure_upvalues(
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

    pub(super) fn reg_expr(&self, reg: u32) -> Expr {
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

    pub(super) fn rk_expr(&self, rk: u32) -> Expr {
        if is_k(rk) {
            self.const_expr(index_k(rk))
        } else {
            self.reg_expr(rk)
        }
    }

    pub(super) fn const_expr(&self, idx: u32) -> Expr {
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

    pub(super) fn const_string(&self, idx: u32) -> String {
        let i = idx as usize;
        if i < self.chunk.constants.len() {
            if let LuaConstant::String(s) = &self.chunk.constants[i] {
                return String::from_utf8_lossy(s.as_ref()).into_owned();
            }
        }
        format!("_K{}", idx)
    }

    pub(super) fn upvalue_expr(&self, idx: u32) -> Expr {
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
}
