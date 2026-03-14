/// Lua 5.1 opcodes, matching the enum order in lopcodes.h
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum OpCode {
    Move = 0,      // A B     R(A) := R(B)
    LoadK = 1,     // A Bx    R(A) := Kst(Bx)
    LoadBool = 2,  // A B C   R(A) := (Bool)B; if (C) pc++
    LoadNil = 3,   // A B     R(A) := ... := R(B) := nil
    GetUpval = 4,  // A B     R(A) := UpValue[B]
    GetGlobal = 5, // A Bx    R(A) := Gbl[Kst(Bx)]
    GetTable = 6,  // A B C   R(A) := R(B)[RK(C)]
    SetGlobal = 7, // A Bx    Gbl[Kst(Bx)] := R(A)
    SetUpval = 8,  // A B     UpValue[B] := R(A)
    SetTable = 9,  // A B C   R(A)[RK(B)] := RK(C)
    NewTable = 10, // A B C   R(A) := {} (size = B,C)
    Self_ = 11,    // A B C   R(A+1) := R(B); R(A) := R(B)[RK(C)]
    Add = 12,      // A B C   R(A) := RK(B) + RK(C)
    Sub = 13,      // A B C   R(A) := RK(B) - RK(C)
    Mul = 14,      // A B C   R(A) := RK(B) * RK(C)
    Div = 15,      // A B C   R(A) := RK(B) / RK(C)
    Mod = 16,      // A B C   R(A) := RK(B) % RK(C)
    Pow = 17,      // A B C   R(A) := RK(B) ^ RK(C)
    Unm = 18,      // A B     R(A) := -R(B)
    Not = 19,      // A B     R(A) := not R(B)
    Len = 20,      // A B     R(A) := length of R(B)
    Concat = 21,   // A B C   R(A) := R(B).. ... ..R(C)
    Jmp = 22,      // sBx     pc+=sBx
    Eq = 23,       // A B C   if ((RK(B) == RK(C)) ~= A) then pc++
    Lt = 24,       // A B C   if ((RK(B) <  RK(C)) ~= A) then pc++
    Le = 25,       // A B C   if ((RK(B) <= RK(C)) ~= A) then pc++
    Test = 26,     // A C     if not (R(A) <=> C) then pc++
    TestSet = 27,  // A B C   if (R(B) <=> C) then R(A) := R(B) else pc++
    Call = 28,     // A B C   R(A), ... ,R(A+C-2) := R(A)(R(A+1), ... ,R(A+B-1))
    TailCall = 29, // A B C   return R(A)(R(A+1), ... ,R(A+B-1))
    Return = 30,   // A B     return R(A), ... ,R(A+B-2)
    ForLoop = 31,  // A sBx   R(A)+=R(A+2); if R(A) <?= R(A+1) then { pc+=sBx; R(A+3)=R(A) }
    ForPrep = 32,  // A sBx   R(A)-=R(A+2); pc+=sBx
    TForLoop = 33, // A C     R(A+3), ... ,R(A+3+C) := R(A)(R(A+1), R(A+2));
    SetList = 34,  // A B C   R(A)[(C-1)*FPF+i] := R(A+i), 1 <= i <= B
    Close = 35,    // A       close all variables in the stack up to (>=) R(A)
    Closure = 36,  // A Bx    R(A) := closure(KPROTO[Bx], R(A), ... ,R(A+n))
    VarArg = 37,   // A B     R(A), R(A+1), ..., R(A+B-1) = vararg
}

pub const NUM_OPCODES: usize = 38;

impl OpCode {
    pub fn from_u8(v: u8) -> Option<OpCode> {
        if v < NUM_OPCODES as u8 {
            // SAFETY: OpCode is repr(u8) with contiguous values 0..37
            Some(unsafe { std::mem::transmute(v) })
        } else {
            None
        }
    }

    pub fn name(self) -> &'static str {
        OPCODE_NAMES[self as usize]
    }
}

impl std::fmt::Display for OpCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// Opcode name table, corresponding to luaP_opnames in lopcodes.c
const OPCODE_NAMES: [&str; NUM_OPCODES] = [
    "MOVE", "LOADK", "LOADBOOL", "LOADNIL", "GETUPVAL", "GETGLOBAL", "GETTABLE", "SETGLOBAL",
    "SETUPVAL", "SETTABLE", "NEWTABLE", "SELF", "ADD", "SUB", "MUL", "DIV", "MOD", "POW", "UNM",
    "NOT", "LEN", "CONCAT", "JMP", "EQ", "LT", "LE", "TEST", "TESTSET", "CALL", "TAILCALL",
    "RETURN", "FORLOOP", "FORPREP", "TFORLOOP", "SETLIST", "CLOSE", "CLOSURE", "VARARG",
];

/// Instruction format
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpMode {
    ABC,
    ABx,
    AsBx,
}

/// Argument mode mask
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpArgMask {
    /// Argument is not used
    N,
    /// Argument is used
    U,
    /// Argument is a register or jump offset
    R,
    /// Argument is a constant or register/constant
    K,
}

/// Opcode metadata
#[derive(Debug, Clone, Copy)]
pub struct OpProp {
    pub mode: OpMode,
    pub b_mode: OpArgMask,
    pub c_mode: OpArgMask,
    pub sets_a: bool,
    pub is_test: bool,
}

/// Opcode property table, matching luaP_opmodes in lopcodes.c
pub const OP_PROPS: [OpProp; NUM_OPCODES] = {
    use OpArgMask::*;
    use OpMode::*;
    const fn p(is_test: bool, sets_a: bool, b: OpArgMask, c: OpArgMask, mode: OpMode) -> OpProp {
        OpProp {
            mode,
            b_mode: b,
            c_mode: c,
            sets_a,
            is_test,
        }
    }
    [
        //              T      A     B  C   mode
        p(false, true,  R, N, ABC),  // MOVE
        p(false, true,  K, N, ABx),  // LOADK
        p(false, true,  U, U, ABC),  // LOADBOOL
        p(false, true,  R, N, ABC),  // LOADNIL
        p(false, true,  U, N, ABC),  // GETUPVAL
        p(false, true,  K, N, ABx),  // GETGLOBAL
        p(false, true,  R, K, ABC),  // GETTABLE
        p(false, false, K, N, ABx),  // SETGLOBAL
        p(false, false, U, N, ABC),  // SETUPVAL
        p(false, false, K, K, ABC),  // SETTABLE
        p(false, true,  U, U, ABC),  // NEWTABLE
        p(false, true,  R, K, ABC),  // SELF
        p(false, true,  K, K, ABC),  // ADD
        p(false, true,  K, K, ABC),  // SUB
        p(false, true,  K, K, ABC),  // MUL
        p(false, true,  K, K, ABC),  // DIV
        p(false, true,  K, K, ABC),  // MOD
        p(false, true,  K, K, ABC),  // POW
        p(false, true,  R, N, ABC),  // UNM
        p(false, true,  R, N, ABC),  // NOT
        p(false, true,  R, N, ABC),  // LEN
        p(false, true,  R, R, ABC),  // CONCAT
        p(false, false, R, N, AsBx), // JMP
        p(true,  false, K, K, ABC),  // EQ
        p(true,  false, K, K, ABC),  // LT
        p(true,  false, K, K, ABC),  // LE
        p(true,  true,  R, U, ABC),  // TEST
        p(true,  true,  R, U, ABC),  // TESTSET
        p(false, true,  U, U, ABC),  // CALL
        p(false, true,  U, U, ABC),  // TAILCALL
        p(false, false, U, N, ABC),  // RETURN
        p(false, true,  R, N, AsBx), // FORLOOP
        p(false, true,  R, N, AsBx), // FORPREP
        p(true,  false, N, U, ABC),  // TFORLOOP
        p(false, false, U, U, ABC),  // SETLIST
        p(false, false, N, N, ABC),  // CLOSE
        p(false, true,  U, N, ABx),  // CLOSURE
        p(false, true,  U, N, ABC),  // VARARG
    ]
};

impl OpCode {
    pub fn props(self) -> &'static OpProp {
        &OP_PROPS[self as usize]
    }
}
