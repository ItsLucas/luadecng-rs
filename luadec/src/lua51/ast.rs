/// Lua AST node types for decompiled output.

/// A complete Lua function body (chunk).
#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub params: Vec<String>,
    pub is_vararg: bool,
    pub body: Block,
}

/// A sequence of statements.
pub type Block = Vec<Stat>;

/// Lua statement.
#[derive(Debug, Clone, PartialEq)]
pub enum Stat {
    /// `local var1, var2 = expr1, expr2`
    LocalAssign {
        names: Vec<String>,
        exprs: Vec<Expr>,
    },
    /// `var1, var2 = expr1, expr2`
    Assign {
        targets: Vec<Expr>,
        values: Vec<Expr>,
    },
    /// `expr(args)` (function call as statement)
    Call(CallExpr),
    /// `do ... end`
    DoBlock(Block),
    /// `while cond do ... end`
    While {
        cond: Expr,
        body: Block,
    },
    /// `repeat ... until cond`
    Repeat {
        body: Block,
        cond: Expr,
    },
    /// `if cond then ... elseif ... else ... end`
    If {
        cond: Expr,
        then_block: Block,
        elseif_clauses: Vec<(Expr, Block)>,
        else_block: Option<Block>,
    },
    /// `for name = start, limit, step do ... end`
    NumericFor {
        name: String,
        start: Expr,
        limit: Expr,
        step: Option<Expr>,
        body: Block,
    },
    /// `for name1, name2 in iter do ... end`
    GenericFor {
        names: Vec<String>,
        iterators: Vec<Expr>,
        body: Block,
    },
    /// `return expr1, expr2, ...`
    Return(Vec<Expr>),
    /// `break`
    Break,
    /// Comment (for readability of decompiled output).
    Comment(String),
}

/// Lua expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// `nil`
    Nil,
    /// `true` / `false`
    Bool(bool),
    /// Numeric literal
    Number(NumLit),
    /// String literal (raw bytes; emitter handles encoding)
    StringLit(Vec<u8>),
    /// `...`
    VarArg,
    /// Variable reference by name
    Name(String),
    /// `table[key]` or `table.field`
    Index(Box<Expr>, Box<Expr>),
    /// `table.name` (syntactic sugar for Index with string key)
    Field(Box<Expr>, String),
    /// `prefix:method(args)` (syntactic sugar)
    MethodCall(Box<CallExpr>),
    /// Function call `f(args)`
    FuncCall(Box<CallExpr>),
    /// Binary operation
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    /// Unary operation
    UnOp(UnOp, Box<Expr>),
    /// `function(...) ... end`
    FunctionDef(Box<Function>),
    /// Table constructor `{ ... }`
    Table(Vec<TableField>),
    /// Placeholder for registers not yet resolved.
    Register(u32),
    /// Upvalue reference by index.
    Upvalue(u32),
    /// Global variable reference.
    Global(String),
}

/// Numeric literal (preserves integer vs float distinction).
#[derive(Debug, Clone, PartialEq)]
pub enum NumLit {
    Int(i64),
    Float(f64),
}

/// Function/method call.
#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub func: Expr,
    pub args: Vec<Expr>,
}

/// Table constructor field.
#[derive(Debug, Clone, PartialEq)]
pub enum TableField {
    /// `[expr] = expr`
    IndexField(Expr, Expr),
    /// `name = expr`
    NameField(String, Expr),
    /// Positional value
    Value(Expr),
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Concat,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    Len,
}

/// Operator precedence (higher = binds tighter).
impl BinOp {
    pub fn precedence(self) -> u8 {
        match self {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 3,
            BinOp::Concat => 4,
            BinOp::Add | BinOp::Sub => 5,
            BinOp::Mul | BinOp::Div | BinOp::Mod => 6,
            BinOp::Pow => 7,
        }
    }

    /// Whether the operator is right-associative.
    pub fn is_right_assoc(self) -> bool {
        matches!(self, BinOp::Pow | BinOp::Concat)
    }

    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Pow => "^",
            BinOp::Concat => "..",
            BinOp::Eq => "==",
            BinOp::Ne => "~=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "and",
            BinOp::Or => "or",
        }
    }
}

impl UnOp {
    pub fn precedence(self) -> u8 {
        8 // all unary ops have higher precedence than any binary op
    }

    pub fn symbol(self) -> &'static str {
        match self {
            UnOp::Neg => "-",
            UnOp::Not => "not ",
            UnOp::Len => "#",
        }
    }
}
