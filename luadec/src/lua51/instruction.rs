use crate::lua51::opcodes::{OpCode, OpMode};

/// Bit layout of a Lua 5.1 instruction (32-bit unsigned):
///
/// ```text
///  MSB                                                         LSB
///  +--------+---------+---------+--------+--------+
///  |   B(9) |   C(9)  |   A(8)  | OpCode(6)      |
///  +--------+---------+---------+--------+--------+
///  31    23  22    14  13      6  5             0
///
///  For ABx/AsBx format, B and C are merged into Bx (18 bits).
/// ```

const SIZE_OP: u32 = 6;
const SIZE_A: u32 = 8;
const SIZE_C: u32 = 9;
const SIZE_B: u32 = 9;
const SIZE_BX: u32 = SIZE_C + SIZE_B; // 18

const POS_OP: u32 = 0;
const POS_A: u32 = POS_OP + SIZE_OP; // 6
const POS_C: u32 = POS_A + SIZE_A; // 14
const POS_B: u32 = POS_C + SIZE_C; // 23
const POS_BX: u32 = POS_C; // 14

const MAXARG_BX: u32 = (1 << SIZE_BX) - 1; // 262143
const MAXARG_SBX: i32 = (MAXARG_BX >> 1) as i32; // 131071

/// Bit 8 of a B/C field indicates a constant index rather than a register.
pub const BITRK: u32 = 1 << (SIZE_B - 1); // 256

/// Check whether a B/C value refers to a constant (vs register).
#[inline]
pub fn is_k(x: u32) -> bool {
    x & BITRK != 0
}

/// Extract the constant index from an RK value.
#[inline]
pub fn index_k(x: u32) -> u32 {
    x & !BITRK
}

/// Number of list items to accumulate before a SETLIST instruction.
pub const LFIELDS_PER_FLUSH: u32 = 50;

/// A decoded Lua 5.1 instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instruction {
    pub raw: u32,
    pub op: OpCode,
    pub a: u32,
    pub fields: InstructionFields,
}

/// The variable part of a decoded instruction, depending on the opcode format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionFields {
    ABC { b: u32, c: u32 },
    ABx { bx: u32 },
    AsBx { sbx: i32 },
}

#[inline]
fn mask(n: u32) -> u32 {
    (1u32 << n) - 1
}

impl Instruction {
    /// Decode a raw 32-bit value into a structured `Instruction`.
    pub fn decode(raw: u32) -> Option<Instruction> {
        let opcode_val = (raw >> POS_OP) & mask(SIZE_OP);
        let op = OpCode::from_u8(opcode_val as u8)?;
        let a = (raw >> POS_A) & mask(SIZE_A);

        let fields = match op.props().mode {
            OpMode::ABC => {
                let b = (raw >> POS_B) & mask(SIZE_B);
                let c = (raw >> POS_C) & mask(SIZE_C);
                InstructionFields::ABC { b, c }
            }
            OpMode::ABx => {
                let bx = (raw >> POS_BX) & mask(SIZE_BX);
                InstructionFields::ABx { bx }
            }
            OpMode::AsBx => {
                let bx = (raw >> POS_BX) & mask(SIZE_BX);
                let sbx = bx as i32 - MAXARG_SBX;
                InstructionFields::AsBx { sbx }
            }
        };

        Some(Instruction {
            raw,
            op,
            a,
            fields,
        })
    }

    /// Get the B field (only valid for ABC format).
    pub fn b(&self) -> u32 {
        match self.fields {
            InstructionFields::ABC { b, .. } => b,
            _ => panic!("b() called on non-ABC instruction"),
        }
    }

    /// Get the C field (only valid for ABC format).
    pub fn c(&self) -> u32 {
        match self.fields {
            InstructionFields::ABC { c, .. } => c,
            _ => panic!("c() called on non-ABC instruction"),
        }
    }

    /// Get the Bx field (only valid for ABx format).
    pub fn bx(&self) -> u32 {
        match self.fields {
            InstructionFields::ABx { bx } => bx,
            _ => panic!("bx() called on non-ABx instruction"),
        }
    }

    /// Get the sBx field (only valid for AsBx format).
    pub fn sbx(&self) -> i32 {
        match self.fields {
            InstructionFields::AsBx { sbx } => sbx,
            _ => panic!("sbx() called on non-AsBx instruction"),
        }
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.fields {
            InstructionFields::ABC { b, c } => {
                write!(f, "{:<12} {} {} {}", self.op, self.a, b, c)
            }
            InstructionFields::ABx { bx } => {
                write!(f, "{:<12} {} {}", self.op, self.a, bx)
            }
            InstructionFields::AsBx { sbx } => {
                write!(f, "{:<12} {} {}", self.op, self.a, sbx)
            }
        }
    }
}

/// Encode helpers (useful for testing)
pub fn encode_abc(op: OpCode, a: u32, b: u32, c: u32) -> u32 {
    ((op as u32) << POS_OP) | (a << POS_A) | (b << POS_B) | (c << POS_C)
}

pub fn encode_abx(op: OpCode, a: u32, bx: u32) -> u32 {
    ((op as u32) << POS_OP) | (a << POS_A) | (bx << POS_BX)
}

pub fn encode_asbx(op: OpCode, a: u32, sbx: i32) -> u32 {
    let bx = (sbx + MAXARG_SBX) as u32;
    ((op as u32) << POS_OP) | (a << POS_A) | (bx << POS_BX)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_move() {
        // MOVE A=1 B=2
        let raw = encode_abc(OpCode::Move, 1, 2, 0);
        let inst = Instruction::decode(raw).unwrap();
        assert_eq!(inst.op, OpCode::Move);
        assert_eq!(inst.a, 1);
        assert_eq!(inst.b(), 2);
        assert_eq!(inst.c(), 0);
    }

    #[test]
    fn decode_loadk() {
        // LOADK A=5 Bx=100
        let raw = encode_abx(OpCode::LoadK, 5, 100);
        let inst = Instruction::decode(raw).unwrap();
        assert_eq!(inst.op, OpCode::LoadK);
        assert_eq!(inst.a, 5);
        assert_eq!(inst.bx(), 100);
    }

    #[test]
    fn decode_jmp() {
        // JMP sBx=10
        let raw = encode_asbx(OpCode::Jmp, 0, 10);
        let inst = Instruction::decode(raw).unwrap();
        assert_eq!(inst.op, OpCode::Jmp);
        assert_eq!(inst.sbx(), 10);

        // JMP sBx=-5
        let raw = encode_asbx(OpCode::Jmp, 0, -5);
        let inst = Instruction::decode(raw).unwrap();
        assert_eq!(inst.op, OpCode::Jmp);
        assert_eq!(inst.sbx(), -5);
    }

    #[test]
    fn decode_add() {
        // ADD A=0 B=256(K0) C=1
        let raw = encode_abc(OpCode::Add, 0, BITRK, 1);
        let inst = Instruction::decode(raw).unwrap();
        assert_eq!(inst.op, OpCode::Add);
        assert_eq!(inst.a, 0);
        assert!(is_k(inst.b()));
        assert_eq!(index_k(inst.b()), 0);
        assert!(!is_k(inst.c()));
    }

    #[test]
    fn roundtrip_all_formats() {
        // ABC
        let raw = encode_abc(OpCode::Call, 3, 2, 1);
        let inst = Instruction::decode(raw).unwrap();
        assert_eq!(inst.raw, raw);
        assert_eq!(inst.op, OpCode::Call);
        assert_eq!(inst.a, 3);
        assert_eq!(inst.b(), 2);
        assert_eq!(inst.c(), 1);

        // ABx
        let raw = encode_abx(OpCode::Closure, 0, 42);
        let inst = Instruction::decode(raw).unwrap();
        assert_eq!(inst.raw, raw);
        assert_eq!(inst.bx(), 42);

        // AsBx
        let raw = encode_asbx(OpCode::ForLoop, 2, -100);
        let inst = Instruction::decode(raw).unwrap();
        assert_eq!(inst.raw, raw);
        assert_eq!(inst.sbx(), -100);
    }

    #[test]
    fn invalid_opcode() {
        // Opcode 38 doesn't exist
        let raw = 38u32;
        assert!(Instruction::decode(raw).is_none());
    }

    #[test]
    fn display_format() {
        let raw = encode_abc(OpCode::Move, 1, 2, 0);
        let inst = Instruction::decode(raw).unwrap();
        let s = format!("{}", inst);
        assert!(s.contains("MOVE"));
        assert!(s.contains("1"));
        assert!(s.contains("2"));
    }
}
