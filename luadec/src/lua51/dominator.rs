use crate::lua51::cfg::{ControlFlowGraph, EdgeKind};
use crate::lua51::opcodes::OpCode;

/// Dominator tree for a control flow graph.
///
/// Uses the iterative data-flow algorithm (Cooper, Harvey, Kennedy):
/// simple, correct, and fast enough for the small CFGs produced by Lua functions.
#[derive(Debug)]
pub struct DominatorTree {
    /// Immediate dominator of each block. `idom[entry] == entry`.
    idom: Vec<usize>,
    /// Children in the dominator tree (blocks immediately dominated).
    children: Vec<Vec<usize>>,
    /// Dominance frontier for each block.
    frontier: Vec<Vec<usize>>,
    /// Number of blocks.
    num_blocks: usize,
}

impl DominatorTree {
    /// Build the dominator tree from a CFG. Entry block is assumed to be block 0.
    pub fn build(cfg: &ControlFlowGraph) -> Self {
        let n = cfg.num_blocks();
        if n == 0 {
            return DominatorTree {
                idom: Vec::new(),
                children: Vec::new(),
                frontier: Vec::new(),
                num_blocks: 0,
            };
        }

        // Compute reverse postorder (RPO) numbering via DFS.
        let rpo = compute_rpo(cfg, n);
        let rpo_order = &rpo.order; // block IDs in RPO
        let rpo_num = &rpo.number; // block ID -> RPO number

        // Iterative dominator computation (Cooper, Harvey, Kennedy 2001).
        const UNDEF: usize = usize::MAX;
        let mut idom = vec![UNDEF; n];
        idom[0] = 0; // entry dominates itself

        let intersect = |idom: &[usize], rpo_num: &[usize], mut b1: usize, mut b2: usize| -> usize {
            while b1 != b2 {
                while rpo_num[b1] > rpo_num[b2] {
                    b1 = idom[b1];
                }
                while rpo_num[b2] > rpo_num[b1] {
                    b2 = idom[b2];
                }
            }
            b1
        };

        let mut changed = true;
        while changed {
            changed = false;
            // Process in RPO, skipping entry (index 0 in rpo_order).
            for &b in &rpo_order[1..] {
                let preds = &cfg.blocks[b].predecessors;
                // Find first processed predecessor.
                let mut new_idom = UNDEF;
                for &p in preds {
                    if idom[p] != UNDEF {
                        new_idom = p;
                        break;
                    }
                }
                if new_idom == UNDEF {
                    continue; // unreachable block
                }
                // Intersect with remaining processed predecessors.
                for &p in preds {
                    if p != new_idom && idom[p] != UNDEF {
                        new_idom = intersect(&idom, rpo_num, p, new_idom);
                    }
                }
                if idom[b] != new_idom {
                    idom[b] = new_idom;
                    changed = true;
                }
            }
        }

        // Build children lists.
        let mut children = vec![Vec::new(); n];
        for b in 0..n {
            if idom[b] != b && idom[b] != UNDEF {
                children[idom[b]].push(b);
            }
        }

        // Compute dominance frontiers.
        let frontier = compute_dominance_frontiers(&idom, cfg, n);

        DominatorTree {
            idom,
            children,
            frontier,
            num_blocks: n,
        }
    }

    /// Immediate dominator of block `b`.
    pub fn idom(&self, b: usize) -> usize {
        self.idom[b]
    }

    /// Children of block `b` in the dominator tree.
    pub fn children(&self, b: usize) -> &[usize] {
        &self.children[b]
    }

    /// Dominance frontier of block `b`.
    pub fn frontier(&self, b: usize) -> &[usize] {
        &self.frontier[b]
    }

    /// Check if block `a` dominates block `b`.
    pub fn dominates(&self, a: usize, b: usize) -> bool {
        const UNDEF: usize = usize::MAX;
        let mut cur = b;
        loop {
            if cur == a {
                return true;
            }
            let idom = self.idom[cur];
            if idom == UNDEF || idom == cur {
                return false; // unreachable or reached entry without finding a
            }
            cur = idom;
        }
    }

    /// Number of blocks.
    pub fn num_blocks(&self) -> usize {
        self.num_blocks
    }
}

impl std::fmt::Display for DominatorTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Dominator Tree:")?;
        for b in 0..self.num_blocks {
            writeln!(
                f,
                "  B{}: idom=B{}, children={:?}, frontier={:?}",
                b, self.idom[b], self.children[b], self.frontier[b]
            )?;
        }
        Ok(())
    }
}

// --- Natural loop detection ---

/// A natural loop identified from back-edges in the CFG.
#[derive(Debug, Clone)]
pub struct NaturalLoop {
    /// The loop header block (target of back-edge, dominates all loop blocks).
    pub header: usize,
    /// The block containing the back-edge to the header.
    pub latch: usize,
    /// All blocks in the loop body (including header and latch).
    pub body: Vec<usize>,
    /// The kind of loop, if identifiable from Lua patterns.
    pub kind: LoopKind,
}

/// Classification of Lua loop constructs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopKind {
    /// `for i = init, limit, step do ... end` (FORPREP/FORLOOP)
    NumericFor,
    /// `for k, v in iter do ... end` (TFORLOOP)
    GenericFor,
    /// `while cond do ... end` or `repeat ... until cond`
    WhileRepeat,
}

/// Find all natural loops in the CFG using dominator information.
///
/// A back-edge is an edge N -> H where H dominates N. Each back-edge
/// defines a natural loop whose body is the set of blocks that can reach N
/// without going through H.
pub fn find_loops(cfg: &ControlFlowGraph, dom: &DominatorTree) -> Vec<NaturalLoop> {
    let mut loops = Vec::new();

    for edge in &cfg.edges {
        let target_block = &cfg.blocks[edge.to];
        let target_ends_with_forloop = matches!(
            cfg.instructions[target_block.end].op,
            OpCode::ForLoop | OpCode::TForLoop
        );

        // Numeric/generic for loops have explicit back-edge kinds and do not
        // satisfy the normal dominance check because FORPREP jumps directly to
        // the FORLOOP block before entering the body.
        let is_explicit_loop_back = matches!(edge.kind, EdgeKind::ForLoopBack | EdgeKind::TForLoopBack);
        let is_natural_back_edge = dom.dominates(edge.to, edge.from)
            && !(target_ends_with_forloop && !is_explicit_loop_back);

        if is_explicit_loop_back || is_natural_back_edge {
            let header = edge.to;
            let latch = edge.from;

            // Collect loop body: all blocks that can reach `latch` without
            // going through `header`.
            let mut body = collect_loop_body(cfg, header, latch);
            if edge.kind == EdgeKind::ForLoopBack {
                body.retain(|&block_id| {
                    let block = &cfg.blocks[block_id];
                    cfg.instructions[block.end].op != OpCode::ForPrep
                });
            }

            // Classify the loop kind based on the edge type and instructions.
            let kind = classify_loop(cfg, edge.kind, header);

            loops.push(NaturalLoop {
                header,
                latch,
                body,
                kind,
            });
        }
    }

    // Sort loops by header for deterministic ordering.
    loops.sort_by_key(|l| (l.header, l.latch));
    loops
}

/// Collect all blocks in the natural loop defined by the back-edge latch -> header.
fn collect_loop_body(cfg: &ControlFlowGraph, header: usize, latch: usize) -> Vec<usize> {
    let mut body = vec![false; cfg.num_blocks()];
    body[header] = true;

    if header == latch {
        return vec![header];
    }

    body[latch] = true;
    let mut stack = vec![latch];

    // Work backwards from latch, adding predecessors until we reach header.
    while let Some(b) = stack.pop() {
        for &pred in &cfg.blocks[b].predecessors {
            if !body[pred] {
                body[pred] = true;
                stack.push(pred);
            }
        }
    }

    body.iter()
        .enumerate()
        .filter_map(|(i, &in_loop)| if in_loop { Some(i) } else { None })
        .collect()
}

/// Classify a loop based on the back-edge kind and header instructions.
fn classify_loop(cfg: &ControlFlowGraph, edge_kind: EdgeKind, header: usize) -> LoopKind {
    match edge_kind {
        EdgeKind::ForLoopBack => LoopKind::NumericFor,
        EdgeKind::TForLoopBack => LoopKind::GenericFor,
        _ => {
            // Check if header block contains FORLOOP or TFORLOOP
            let block = &cfg.blocks[header];
            use crate::lua51::opcodes::OpCode;
            for pc in block.start..=block.end {
                match cfg.instructions[pc].op {
                    OpCode::ForLoop => return LoopKind::NumericFor,
                    OpCode::TForLoop => return LoopKind::GenericFor,
                    _ => {}
                }
            }
            LoopKind::WhileRepeat
        }
    }
}

// --- RPO computation ---

struct Rpo {
    /// Block IDs in reverse postorder.
    order: Vec<usize>,
    /// RPO number for each block ID.
    number: Vec<usize>,
}

fn compute_rpo(cfg: &ControlFlowGraph, n: usize) -> Rpo {
    let mut visited = vec![false; n];
    let mut postorder = Vec::with_capacity(n);

    fn dfs(
        b: usize,
        cfg: &ControlFlowGraph,
        visited: &mut Vec<bool>,
        postorder: &mut Vec<usize>,
    ) {
        visited[b] = true;
        for &succ in &cfg.blocks[b].successors {
            if !visited[succ] {
                dfs(succ, cfg, visited, postorder);
            }
        }
        postorder.push(b);
    }

    dfs(0, cfg, &mut visited, &mut postorder);

    // Reverse postorder
    postorder.reverse();
    let mut number = vec![0usize; n];
    for (i, &b) in postorder.iter().enumerate() {
        number[b] = i;
    }

    Rpo {
        order: postorder,
        number,
    }
}

/// Compute dominance frontiers using the algorithm from
/// Cooper, Harvey, Kennedy (2001).
fn compute_dominance_frontiers(idom: &[usize], cfg: &ControlFlowGraph, n: usize) -> Vec<Vec<usize>> {
    let mut frontiers = vec![Vec::new(); n];

    for b in 0..n {
        let preds = &cfg.blocks[b].predecessors;
        if preds.len() >= 2 {
            for &p in preds {
                let mut runner = p;
                while runner != idom[b] && runner != usize::MAX {
                    if !frontiers[runner].contains(&b) {
                        frontiers[runner].push(b);
                    }
                    if runner == idom[runner] {
                        break;
                    }
                    runner = idom[runner];
                }
            }
        }
    }

    frontiers
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lua51::cfg::ControlFlowGraph;
    use crate::lua51::instruction::{encode_abc, encode_abx, encode_asbx};
    use crate::lua51::opcodes::OpCode;

    #[test]
    fn dominator_linear() {
        // Linear code: single block, entry dominates itself
        let code = vec![
            encode_abx(OpCode::LoadK, 0, 0),
            encode_abc(OpCode::Return, 0, 1, 0),
        ];
        let cfg = ControlFlowGraph::build(&code);
        let dom = DominatorTree::build(&cfg);
        assert_eq!(dom.idom(0), 0);
        assert!(dom.dominates(0, 0));
    }

    #[test]
    fn dominator_diamond() {
        // Diamond CFG:
        // [0] EQ 0 0 1      block 0: [0,1]
        // [1] JMP +1         -> block 2 (false), block 1 (true)
        // [2] LOADK 2 0      block 1: [2]
        // [3] LOADK 3 0      block 2: [3]
        // [4] RETURN 0 1     block 2 continues: [3,4] -- wait, 3 is a leader
        //
        // Actually let me lay this out more carefully:
        // [0] EQ 0 0 1       -- test
        // [1] JMP +2         -- if false, jump to [4]
        // [2] LOADK 2 0      -- true path
        // [3] JMP +0         -- jump to [4]
        // [4] RETURN 0 1     -- merge point
        let code = vec![
            encode_abc(OpCode::Eq, 0, 0, 1),
            encode_asbx(OpCode::Jmp, 0, 2),
            encode_abx(OpCode::LoadK, 2, 0),
            encode_asbx(OpCode::Jmp, 0, 0),
            encode_abc(OpCode::Return, 0, 1, 0),
        ];
        let cfg = ControlFlowGraph::build(&code);
        let dom = DominatorTree::build(&cfg);

        // Block 0 dominates all blocks
        for b in 0..cfg.num_blocks() {
            assert!(dom.dominates(0, b), "block 0 should dominate block {}", b);
        }
    }

    #[test]
    fn detect_numeric_for_loop() {
        // [0] LOADK 0 0      -- init
        // [1] LOADK 1 1      -- limit
        // [2] LOADK 2 2      -- step
        // [3] FORPREP 0 +1   -- jump to [5]
        // [4] LOADK 4 0      -- loop body
        // [5] FORLOOP 0 -2   -- back to [4]
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
        let dom = DominatorTree::build(&cfg);
        let loops = find_loops(&cfg, &dom);

        assert_eq!(loops.len(), 1);
        assert_eq!(loops[0].kind, LoopKind::NumericFor);
        assert!(loops[0].body.len() >= 1);
    }

    #[test]
    fn detect_while_loop() {
        // Simple while-style loop:
        // [0] EQ 0 0 1       -- while condition test
        // [1] JMP +2         -- if false, exit to [4]
        // [2] LOADK 2 0      -- loop body
        // [3] JMP -4         -- jump back to [0]
        // [4] RETURN 0 1
        let code = vec![
            encode_abc(OpCode::Eq, 0, 0, 1),
            encode_asbx(OpCode::Jmp, 0, 2),
            encode_abx(OpCode::LoadK, 2, 0),
            encode_asbx(OpCode::Jmp, 0, -4),
            encode_abc(OpCode::Return, 0, 1, 0),
        ];
        let cfg = ControlFlowGraph::build(&code);
        let dom = DominatorTree::build(&cfg);
        let loops = find_loops(&cfg, &dom);

        assert_eq!(loops.len(), 1);
        assert_eq!(loops[0].kind, LoopKind::WhileRepeat);
    }

    #[test]
    fn empty_cfg_dominator() {
        let cfg = ControlFlowGraph::build(&[]);
        let dom = DominatorTree::build(&cfg);
        assert_eq!(dom.num_blocks(), 0);
        let loops = find_loops(&cfg, &dom);
        assert!(loops.is_empty());
    }
}
