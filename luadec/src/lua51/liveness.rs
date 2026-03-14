use crate::lua51::cfg::ControlFlowGraph;
use crate::lua51::instruction::{is_k, Instruction};
use crate::lua51::opcodes::OpCode;

/// Per-instruction register usage info.
#[derive(Debug, Clone, Default)]
pub struct RegUsage {
    /// Registers defined (written) by this instruction.
    pub defs: Vec<u32>,
    /// Registers used (read) by this instruction.
    pub uses: Vec<u32>,
}

/// Compute register defs/uses for a single instruction.
pub fn instruction_reg_usage(inst: &Instruction) -> RegUsage {
    let mut u = RegUsage::default();
    let a = inst.a;

    match inst.op {
        OpCode::Move => {
            u.defs.push(a);
            u.uses.push(inst.b());
        }
        OpCode::LoadK | OpCode::LoadBool => {
            u.defs.push(a);
        }
        OpCode::LoadNil => {
            for r in a..=inst.b() {
                u.defs.push(r);
            }
        }
        OpCode::GetUpval => {
            u.defs.push(a);
        }
        OpCode::GetGlobal => {
            u.defs.push(a);
        }
        OpCode::GetTable => {
            u.defs.push(a);
            u.uses.push(inst.b());
            if !is_k(inst.c()) { u.uses.push(inst.c()); }
        }
        OpCode::SetGlobal => {
            u.uses.push(a);
        }
        OpCode::SetUpval => {
            u.uses.push(a);
        }
        OpCode::SetTable => {
            u.uses.push(a);
            if !is_k(inst.b()) { u.uses.push(inst.b()); }
            if !is_k(inst.c()) { u.uses.push(inst.c()); }
        }
        OpCode::NewTable => {
            u.defs.push(a);
        }
        OpCode::Self_ => {
            u.defs.push(a);
            u.defs.push(a + 1);
            u.uses.push(inst.b());
            if !is_k(inst.c()) { u.uses.push(inst.c()); }
        }
        OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div
        | OpCode::Mod | OpCode::Pow => {
            u.defs.push(a);
            if !is_k(inst.b()) { u.uses.push(inst.b()); }
            if !is_k(inst.c()) { u.uses.push(inst.c()); }
        }
        OpCode::Unm | OpCode::Not | OpCode::Len => {
            u.defs.push(a);
            u.uses.push(inst.b());
        }
        OpCode::Concat => {
            u.defs.push(a);
            for r in inst.b()..=inst.c() {
                u.uses.push(r);
            }
        }
        OpCode::Jmp => {}
        OpCode::Eq | OpCode::Lt | OpCode::Le => {
            if !is_k(inst.b()) { u.uses.push(inst.b()); }
            if !is_k(inst.c()) { u.uses.push(inst.c()); }
        }
        OpCode::Test => {
            u.uses.push(a);
        }
        OpCode::TestSet => {
            u.defs.push(a);
            u.uses.push(inst.b());
        }
        OpCode::Call => {
            // Function in R(A), args in R(A+1)..R(A+B-1)
            let num_args = if inst.b() == 0 { 0 } else { inst.b() - 1 };
            u.uses.push(a);
            for i in 1..=num_args {
                u.uses.push(a + i);
            }
            // Results in R(A)..R(A+C-2)
            let num_results = if inst.c() == 0 { 1 } else { inst.c() - 1 };
            for i in 0..num_results {
                u.defs.push(a + i);
            }
        }
        OpCode::TailCall => {
            let num_args = if inst.b() == 0 { 0 } else { inst.b() - 1 };
            u.uses.push(a);
            for i in 1..=num_args {
                u.uses.push(a + i);
            }
        }
        OpCode::Return => {
            let num_ret = if inst.b() == 0 { 0 } else { inst.b() - 1 };
            for i in 0..num_ret {
                u.uses.push(a + i);
            }
        }
        OpCode::ForLoop => {
            // Uses and modifies loop control vars
            u.uses.push(a);
            u.uses.push(a + 1);
            u.uses.push(a + 2);
            u.defs.push(a);
            u.defs.push(a + 3);
        }
        OpCode::ForPrep => {
            u.uses.push(a);
            u.uses.push(a + 2);
            u.defs.push(a);
        }
        OpCode::TForLoop => {
            u.uses.push(a);
            u.uses.push(a + 1);
            u.uses.push(a + 2);
            let num_vars = inst.c();
            for i in 0..=num_vars {
                u.defs.push(a + 3 + i);
            }
        }
        OpCode::SetList => {
            let num = if inst.b() == 0 { 0 } else { inst.b() };
            u.uses.push(a);
            for i in 1..=num {
                u.uses.push(a + i);
            }
        }
        OpCode::Close => {}
        OpCode::Closure => {
            u.defs.push(a);
        }
        OpCode::VarArg => {
            let num = if inst.b() == 0 { 1 } else { inst.b() - 1 };
            for i in 0..num {
                u.defs.push(a + i);
            }
        }
    }
    u
}

/// Liveness information for a CFG.
#[derive(Debug)]
pub struct LivenessInfo {
    /// For each block: set of registers live at entry.
    pub live_in: Vec<Vec<bool>>,
    /// For each block: set of registers live at exit.
    pub live_out: Vec<Vec<bool>>,
    /// Maximum register index seen.
    pub max_reg: usize,
}

/// Compute liveness analysis for the given CFG.
/// Returns per-block live-in and live-out sets.
pub fn compute_liveness(cfg: &ControlFlowGraph, max_stack: usize) -> LivenessInfo {
    let n = cfg.num_blocks();
    let nregs = max_stack;
    if n == 0 {
        return LivenessInfo {
            live_in: Vec::new(),
            live_out: Vec::new(),
            max_reg: nregs,
        };
    }

    // Compute per-block use_set (used before def) and kill (defined) sets.
    let mut use_set = vec![vec![false; nregs]; n];
    let mut kill = vec![vec![false; nregs]; n];

    for (bid, block) in cfg.blocks.iter().enumerate() {
        for pc in block.start..=block.end {
            let inst = &cfg.instructions[pc];
            let usage = instruction_reg_usage(inst);
            // use_set: used but not yet killed in this block
            for &r in &usage.uses {
                let r = r as usize;
                if r < nregs && !kill[bid][r] {
                    use_set[bid][r] = true;
                }
            }
            // kill: defined in this block
            for &r in &usage.defs {
                let r = r as usize;
                if r < nregs {
                    kill[bid][r] = true;
                }
            }
        }
    }

    // Iterative dataflow: live_out[B] = union of live_in[S] for all successors S
    // live_in[B] = use_set[B] | (live_out[B] - kill[B])
    let mut live_in = vec![vec![false; nregs]; n];
    let mut live_out = vec![vec![false; nregs]; n];

    let mut changed = true;
    while changed {
        changed = false;
        // Process in reverse order for faster convergence
        for bid in (0..n).rev() {
            // live_out = union of live_in of successors
            for r in 0..nregs {
                let mut out = false;
                for &succ in &cfg.blocks[bid].successors {
                    if succ < n && live_in[succ][r] {
                        out = true;
                        break;
                    }
                }
                live_out[bid][r] = out;
            }

            // live_in = use_set | (live_out - kill)
            for r in 0..nregs {
                let new_in = use_set[bid][r] || (live_out[bid][r] && !kill[bid][r]);
                if new_in != live_in[bid][r] {
                    live_in[bid][r] = new_in;
                    changed = true;
                }
            }
        }
    }

    LivenessInfo { live_in, live_out, max_reg: nregs }
}

/// Check if a register is live at a given pc within a block.
/// This does a local scan from end of block backwards.
pub fn is_reg_live_after(
    cfg: &ControlFlowGraph,
    liveness: &LivenessInfo,
    pc: usize,
    reg: u32,
) -> bool {
    let r = reg as usize;
    if r >= liveness.max_reg {
        return false;
    }
    let block_id = cfg.block_of(pc);
    let block = &cfg.blocks[block_id];

    // Start with live_out of the block
    let mut live = liveness.live_out[block_id][r];

    // Scan backwards from end of block to pc+1
    for scan_pc in (pc + 1..=block.end).rev() {
        let inst = &cfg.instructions[scan_pc];
        let usage = instruction_reg_usage(inst);
        // If defined here, not live before this point
        if usage.defs.contains(&reg) {
            live = false;
        }
        // If used here, live before this point
        if usage.uses.contains(&reg) {
            live = true;
        }
    }

    live
}
