use std::collections::BTreeSet;
use std::fmt;

use crate::lua51::instruction::Instruction;
use crate::lua51::opcodes::OpCode;

/// Type of edge connecting two basic blocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeKind {
    /// Sequential fallthrough to next block.
    Fallthrough,
    /// Unconditional jump (JMP).
    Jump,
    /// Conditional true branch (condition met, skip next instruction).
    ConditionalTrue,
    /// Conditional false branch (condition not met, fallthrough to JMP).
    ConditionalFalse,
    /// FORLOOP back-edge (loop continues).
    ForLoopBack,
    /// FORLOOP exit (loop finished).
    ForLoopExit,
    /// FORPREP jump to loop body end (to FORLOOP).
    ForPrep,
    /// TFORLOOP continue (iterator returned non-nil).
    TForLoopBack,
    /// TFORLOOP exit (iterator returned nil).
    TForLoopExit,
}

/// A directed edge in the control flow graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edge {
    pub from: usize,
    pub to: usize,
    pub kind: EdgeKind,
}

/// A basic block: a maximal sequence of instructions with single entry / single exit.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: usize,
    /// First instruction index (inclusive).
    pub start: usize,
    /// Last instruction index (inclusive).
    pub end: usize,
    /// Successor block IDs.
    pub successors: Vec<usize>,
    /// Predecessor block IDs.
    pub predecessors: Vec<usize>,
}

/// Control flow graph for a single Lua function/chunk.
#[derive(Debug)]
pub struct ControlFlowGraph {
    pub blocks: Vec<BasicBlock>,
    pub edges: Vec<Edge>,
    pub instructions: Vec<Instruction>,
    /// Map from instruction index to block ID (for quick lookup).
    inst_to_block: Vec<usize>,
}

impl ControlFlowGraph {
    /// Build a CFG from a slice of raw 32-bit Lua 5.1 instructions.
    pub fn build(raw_instructions: &[u32]) -> Self {
        let instructions: Vec<Instruction> = raw_instructions
            .iter()
            .map(|&raw| Instruction::decode(raw).expect("invalid instruction"))
            .collect();

        if instructions.is_empty() {
            return ControlFlowGraph {
                blocks: Vec::new(),
                edges: Vec::new(),
                instructions,
                inst_to_block: Vec::new(),
            };
        }

        // Phase 1: Identify block leaders (first instruction of each block).
        let leaders = find_leaders(&instructions);

        // Phase 2: Create basic blocks from leader set.
        let blocks = create_blocks(&leaders, instructions.len());

        // Phase 3: Build inst_to_block map.
        let mut inst_to_block = vec![0usize; instructions.len()];
        for (block_id, block) in blocks.iter().enumerate() {
            for pc in block.start..=block.end {
                inst_to_block[pc] = block_id;
            }
        }

        // Phase 4: Build edges.
        let edges = build_edges(&blocks, &instructions, &inst_to_block);

        // Phase 5: Fill in successor/predecessor lists.
        let mut blocks = blocks;
        for edge in &edges {
            blocks[edge.from].successors.push(edge.to);
            blocks[edge.to].predecessors.push(edge.from);
        }

        ControlFlowGraph {
            blocks,
            edges,
            instructions,
            inst_to_block,
        }
    }

    /// Get the block ID that contains the given instruction index.
    pub fn block_of(&self, pc: usize) -> usize {
        self.inst_to_block[pc]
    }

    /// Get a block by its ID.
    pub fn block(&self, id: usize) -> &BasicBlock {
        &self.blocks[id]
    }

    /// Get instructions in a block.
    pub fn block_instructions(&self, block: &BasicBlock) -> &[Instruction] {
        &self.instructions[block.start..=block.end]
    }

    /// Number of basic blocks.
    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }
}

/// Identify all leader instruction indices.
///
/// Leaders are:
/// - Index 0 (entry point)
/// - Jump targets (pc + 1 + sBx for JMP/FORLOOP/FORPREP)
/// - Instruction after a jump/branch/return (fallthrough point)
/// - Instruction after a test opcode's following JMP target
fn find_leaders(instructions: &[Instruction]) -> BTreeSet<usize> {
    let len = instructions.len();
    let mut leaders = BTreeSet::new();
    leaders.insert(0);

    for (pc, inst) in instructions.iter().enumerate() {
        match inst.op {
            // Unconditional jump
            OpCode::Jmp => {
                let target = (pc as i32 + 1 + inst.sbx()) as usize;
                if target < len {
                    leaders.insert(target);
                }
                // Instruction after JMP is a leader (if reachable)
                if pc + 1 < len {
                    leaders.insert(pc + 1);
                }
            }

            // Comparison tests: EQ, LT, LE skip next instruction (which must be JMP)
            // The conditional creates two paths:
            //   - condition true: skip the JMP, go to pc+2
            //   - condition false: execute the JMP at pc+1
            OpCode::Eq | OpCode::Lt | OpCode::Le | OpCode::Test | OpCode::TestSet => {
                // pc+1 should be a JMP; its target is a leader
                if pc + 1 < len {
                    let next = &instructions[pc + 1];
                    debug_assert_eq!(next.op, OpCode::Jmp, "test at pc={} not followed by JMP", pc);
                    let jmp_target = (pc as i32 + 2 + next.sbx()) as usize;
                    if jmp_target < len {
                        leaders.insert(jmp_target);
                    }
                }
                // pc+2 is the fallthrough after skipping the JMP
                if pc + 2 < len {
                    leaders.insert(pc + 2);
                }
            }

            // Numeric for loop: FORLOOP jumps back if loop continues
            OpCode::ForLoop => {
                let target = (pc as i32 + 1 + inst.sbx()) as usize;
                if target < len {
                    leaders.insert(target);
                }
                if pc + 1 < len {
                    leaders.insert(pc + 1);
                }
            }

            // FORPREP: jump forward to FORLOOP
            OpCode::ForPrep => {
                let target = (pc as i32 + 1 + inst.sbx()) as usize;
                if target < len {
                    leaders.insert(target);
                }
            }

            // Generic for loop: TFORLOOP either continues or exits
            OpCode::TForLoop => {
                // TFORLOOP is followed by a JMP (back-edge)
                if pc + 1 < len {
                    let next = &instructions[pc + 1];
                    debug_assert_eq!(
                        next.op,
                        OpCode::Jmp,
                        "TFORLOOP at pc={} not followed by JMP",
                        pc
                    );
                    let jmp_target = (pc as i32 + 2 + next.sbx()) as usize;
                    if jmp_target < len {
                        leaders.insert(jmp_target);
                    }
                }
                if pc + 2 < len {
                    leaders.insert(pc + 2);
                }
            }

            // Return terminates the block; next instruction (if any) starts a new one
            OpCode::Return | OpCode::TailCall => {
                if pc + 1 < len {
                    leaders.insert(pc + 1);
                }
            }

            _ => {}
        }
    }

    leaders
}

/// Create BasicBlock structs from the sorted leader set.
fn create_blocks(leaders: &BTreeSet<usize>, num_instructions: usize) -> Vec<BasicBlock> {
    let leader_vec: Vec<usize> = leaders.iter().copied().collect();
    let mut blocks = Vec::with_capacity(leader_vec.len());

    for (i, &start) in leader_vec.iter().enumerate() {
        let end = if i + 1 < leader_vec.len() {
            leader_vec[i + 1] - 1
        } else {
            num_instructions - 1
        };
        blocks.push(BasicBlock {
            id: i,
            start,
            end,
            successors: Vec::new(),
            predecessors: Vec::new(),
        });
    }

    blocks
}

/// Build edges between blocks based on the last instruction of each block.
fn build_edges(
    blocks: &[BasicBlock],
    instructions: &[Instruction],
    inst_to_block: &[usize],
) -> Vec<Edge> {
    let mut edges = Vec::new();
    let len = instructions.len();

    for block in blocks {
        let last_pc = block.end;
        let last = &instructions[last_pc];
        let block_id = block.id;

        match last.op {
            OpCode::Jmp => {
                let target = (last_pc as i32 + 1 + last.sbx()) as usize;

                // Check if this JMP is preceded by a test opcode (EQ/LT/LE/TEST/TESTSET)
                // within the same block - making this a conditional branch.
                let is_conditional = last_pc > block.start && {
                    let prev = &instructions[last_pc - 1];
                    matches!(
                        prev.op,
                        OpCode::Eq
                            | OpCode::Lt
                            | OpCode::Le
                            | OpCode::Test
                            | OpCode::TestSet
                    )
                };

                let is_tforloop = last_pc > block.start
                    && instructions[last_pc - 1].op == OpCode::TForLoop;

                if is_conditional {
                    // False branch: follow the JMP
                    if target < len {
                        edges.push(Edge {
                            from: block_id,
                            to: inst_to_block[target],
                            kind: EdgeKind::ConditionalFalse,
                        });
                    }
                    // True branch: skip the JMP, go to pc+1
                    if last_pc + 1 < len {
                        edges.push(Edge {
                            from: block_id,
                            to: inst_to_block[last_pc + 1],
                            kind: EdgeKind::ConditionalTrue,
                        });
                    }
                } else if is_tforloop {
                    // Back-edge: jump back to iterator call
                    if target < len {
                        edges.push(Edge {
                            from: block_id,
                            to: inst_to_block[target],
                            kind: EdgeKind::TForLoopBack,
                        });
                    }
                    // Exit: fall through past the JMP
                    if last_pc + 1 < len {
                        edges.push(Edge {
                            from: block_id,
                            to: inst_to_block[last_pc + 1],
                            kind: EdgeKind::TForLoopExit,
                        });
                    }
                } else {
                    if target < len {
                        edges.push(Edge {
                            from: block_id,
                            to: inst_to_block[target],
                            kind: EdgeKind::Jump,
                        });
                    }
                }
            }

            // Test opcodes where the JMP is NOT in this block (rare edge case)
            OpCode::Eq | OpCode::Lt | OpCode::Le | OpCode::Test | OpCode::TestSet => {
                let jmp_pc = last_pc + 1;
                if jmp_pc < len {
                    edges.push(Edge {
                        from: block_id,
                        to: inst_to_block[jmp_pc],
                        kind: EdgeKind::Fallthrough,
                    });
                }
            }

            OpCode::ForLoop => {
                // Back-edge: loop continues, jump to loop body start
                let target = (last_pc as i32 + 1 + last.sbx()) as usize;
                if target < len {
                    edges.push(Edge {
                        from: block_id,
                        to: inst_to_block[target],
                        kind: EdgeKind::ForLoopBack,
                    });
                }
                // Exit: loop ends, fall through
                if last_pc + 1 < len {
                    edges.push(Edge {
                        from: block_id,
                        to: inst_to_block[last_pc + 1],
                        kind: EdgeKind::ForLoopExit,
                    });
                }
            }

            OpCode::ForPrep => {
                // Jump to FORLOOP
                let target = (last_pc as i32 + 1 + last.sbx()) as usize;
                if target < len {
                    edges.push(Edge {
                        from: block_id,
                        to: inst_to_block[target],
                        kind: EdgeKind::ForPrep,
                    });
                }
            }

            OpCode::TForLoop => {
                // TFORLOOP at last_pc, but normally the block also contains
                // the following JMP. Check if last_pc is actually the block end
                // (the JMP case is handled in the Jmp arm when preceded by TFORLOOP).
                let jmp_pc = last_pc + 1;
                if jmp_pc < len {
                    edges.push(Edge {
                        from: block_id,
                        to: inst_to_block[jmp_pc],
                        kind: EdgeKind::Fallthrough,
                    });
                }
            }

            OpCode::Return | OpCode::TailCall => {
                // No successors (terminal block)
            }

            _ => {
                // Default: fallthrough to next block
                if last_pc + 1 < len {
                    edges.push(Edge {
                        from: block_id,
                        to: inst_to_block[last_pc + 1],
                        kind: EdgeKind::Fallthrough,
                    });
                }
            }
        }
    }

    edges
}

impl fmt::Display for ControlFlowGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for block in &self.blocks {
            writeln!(
                f,
                "Block {} [pc {}..{}] pred={:?} succ={:?}",
                block.id, block.start, block.end, block.predecessors, block.successors
            )?;
            for pc in block.start..=block.end {
                writeln!(f, "  [{:4}] {}", pc, self.instructions[pc])?;
            }
        }
        if !self.edges.is_empty() {
            writeln!(f, "Edges:")?;
            for edge in &self.edges {
                writeln!(f, "  B{} -> B{} ({:?})", edge.from, edge.to, edge.kind)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lua51::instruction::{encode_abc, encode_abx, encode_asbx};
    use crate::lua51::opcodes::OpCode;

    #[test]
    fn linear_code() {
        // LOADK 0 0; LOADK 1 1; RETURN 0 1
        let code = vec![
            encode_abx(OpCode::LoadK, 0, 0),
            encode_abx(OpCode::LoadK, 1, 1),
            encode_abc(OpCode::Return, 0, 1, 0),
        ];
        let cfg = ControlFlowGraph::build(&code);
        assert_eq!(cfg.num_blocks(), 1);
        assert_eq!(cfg.blocks[0].start, 0);
        assert_eq!(cfg.blocks[0].end, 2);
        assert!(cfg.edges.is_empty());
    }

    #[test]
    fn simple_jump() {
        // [0] JMP +1      -> jumps to [2]
        // [1] LOADK 0 0
        // [2] RETURN 0 1
        let code = vec![
            encode_asbx(OpCode::Jmp, 0, 1),
            encode_abx(OpCode::LoadK, 0, 0),
            encode_abc(OpCode::Return, 0, 1, 0),
        ];
        let cfg = ControlFlowGraph::build(&code);
        // Leaders: 0, 1, 2 -> 3 blocks
        assert_eq!(cfg.num_blocks(), 3);
        // Block 0 jumps to block 2
        assert!(cfg.edges.iter().any(|e| e.from == 0
            && e.to == 2
            && e.kind == EdgeKind::Jump));
    }

    #[test]
    fn conditional_branch() {
        // [0] EQ 0 0 1     -- if R(0) == R(1)
        // [1] JMP +1       -- jump to [3] if condition false
        // [2] LOADK 2 0    -- condition true path
        // [3] RETURN 0 1
        let code = vec![
            encode_abc(OpCode::Eq, 0, 0, 1),
            encode_asbx(OpCode::Jmp, 0, 1),
            encode_abx(OpCode::LoadK, 2, 0),
            encode_abc(OpCode::Return, 0, 1, 0),
        ];
        let cfg = ControlFlowGraph::build(&code);
        // Leaders: 0, 2, 3 -> 3 blocks
        // Block 0: [0,1] (EQ + JMP)
        assert_eq!(cfg.num_blocks(), 3);
        assert_eq!(cfg.blocks[0].start, 0);
        assert_eq!(cfg.blocks[0].end, 1);
        // Should have ConditionalTrue -> block 1 (pc=2) and ConditionalFalse -> block 2 (pc=3)
        assert!(cfg
            .edges
            .iter()
            .any(|e| e.from == 0 && e.kind == EdgeKind::ConditionalTrue));
        assert!(cfg
            .edges
            .iter()
            .any(|e| e.from == 0 && e.kind == EdgeKind::ConditionalFalse));
    }

    #[test]
    fn numeric_for_loop() {
        // [0] LOADK 0 0      -- init
        // [1] LOADK 1 1      -- limit
        // [2] LOADK 2 2      -- step
        // [3] FORPREP 0 +1   -- jump to [5] (FORLOOP)
        // [4] LOADK 4 0      -- loop body
        // [5] FORLOOP 0 -2   -- jump back to [4] if loop continues
        // [6] RETURN 0 1
        let code = vec![
            encode_abx(OpCode::LoadK, 0, 0),
            encode_abx(OpCode::LoadK, 1, 1),
            encode_abx(OpCode::LoadK, 2, 2),
            encode_asbx(OpCode::ForPrep, 0, 1),
            encode_abx(OpCode::LoadK, 4, 0),
            encode_asbx(OpCode::ForLoop, 0, -2),
            encode_abc(OpCode::Return, 0, 1, 0),
        ];
        let cfg = ControlFlowGraph::build(&code);
        // FORLOOP has back-edge and exit edge
        assert!(cfg
            .edges
            .iter()
            .any(|e| e.kind == EdgeKind::ForLoopBack));
        assert!(cfg
            .edges
            .iter()
            .any(|e| e.kind == EdgeKind::ForLoopExit));
        assert!(cfg.edges.iter().any(|e| e.kind == EdgeKind::ForPrep));
    }

    #[test]
    fn empty_function() {
        let cfg = ControlFlowGraph::build(&[]);
        assert_eq!(cfg.num_blocks(), 0);
        assert!(cfg.edges.is_empty());
    }
}
