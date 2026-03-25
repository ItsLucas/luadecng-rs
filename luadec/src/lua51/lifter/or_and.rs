use crate::lua51::ast::*;
use super::Lifter;
use super::util::negate_expr;

impl<'a> Lifter<'a> {
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
    pub(super) fn try_lift_or_and_chain(&mut self, start: usize, stmts: &mut Block) -> Option<usize> {
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
}
