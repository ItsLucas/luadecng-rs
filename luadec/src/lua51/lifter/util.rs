use std::collections::HashSet;

use crate::lua51::ast::*;
use crate::lua51::cfg::{BasicBlock, EdgeKind};
use crate::lua51::dominator::NaturalLoop;
use crate::lua51::instruction::is_k;
use crate::lua51::opcodes::OpCode;
use super::Lifter;

impl<'a> Lifter<'a> {
    /// Flush the pending table construction for a specific register.
    pub(super) fn flush_pending_table(&mut self, reg: u32) {
        if let Some(fields) = self.pending_tables.remove(&reg) {
            self.set_reg(reg, Expr::Table(fields));
        }
    }

    /// Check if a block consists of only a RETURN (or RETURN with values).
    pub(super) fn is_return_block(&self, block_idx: usize) -> bool {
        if block_idx >= self.cfg.num_blocks() {
            return false;
        }
        let block = &self.cfg.blocks[block_idx];
        let last = self.cfg.instructions[block.end];
        matches!(last.op, OpCode::Return | OpCode::TailCall)
            && block.successors.is_empty()
    }

    /// Find the PC of the test instruction in a conditional block.
    pub(super) fn find_test_pc(&self, block: &BasicBlock) -> Option<usize> {
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

    pub(super) fn find_loop_at(&self, block_idx: usize) -> Option<&NaturalLoop> {
        if self.active_loop_headers.contains(&block_idx) {
            return None;
        }
        self.loops.iter().find(|l| l.header == block_idx)
    }

    pub(super) fn current_loop_exit(&self) -> Option<usize> {
        self.active_loop_exits.last().copied()
    }

    pub(super) fn find_forprep_block(&self, header: usize) -> Option<usize> {
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

    pub(super) fn max_loop_block(&self, lp: &NaturalLoop) -> usize {
        lp.body.iter().copied().max().unwrap_or(lp.header)
    }

    pub(super) fn is_conditional_block(&self, block: &BasicBlock) -> bool {
        block.successors.len() == 2
            && self.cfg.edges.iter().any(|e| {
                e.from == block.id
                    && matches!(
                        e.kind,
                        EdgeKind::ConditionalTrue | EdgeKind::ConditionalFalse
                    )
            })
    }

    pub(super) fn block_contains_testset(&self, block_idx: usize) -> bool {
        if block_idx >= self.cfg.num_blocks() {
            return false;
        }
        let block = &self.cfg.blocks[block_idx];
        (block.start..=block.end).any(|pc| self.cfg.instructions[pc].op == OpCode::TestSet)
    }

    pub(super) fn block_flows_to(&self, from_block: usize, target_block: usize) -> bool {
        if from_block >= self.cfg.num_blocks() || target_block >= self.cfg.num_blocks() {
            return false;
        }
        self.cfg.blocks[from_block].successors.iter().all(|&succ| succ == target_block)
    }

    pub(super) fn find_accumulator_regs(&self) -> HashSet<u32> {
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

    pub(super) fn extract_condition(&self, block_idx: usize) -> Option<Expr> {
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

    pub(super) fn find_merge_point(
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
pub(super) fn make_index(table: Expr, key: Expr) -> Expr {
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
pub(super) fn is_identifier(s: &str) -> bool {
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

pub(super) fn is_lua_keyword(s: &str) -> bool {
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
pub(super) fn negate_expr(expr: Expr) -> Expr {
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
