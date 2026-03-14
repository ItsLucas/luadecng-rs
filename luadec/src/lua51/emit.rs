use std::fmt::Write;

use crate::lua51::ast::*;

/// Emit a Lua function as source code.
pub fn emit_function(func: &Function) -> String {
    let mut out = String::new();
    let body = fold_elseif_chain(&func.body);
    emit_block(&body, &mut out, 0);
    out
}

/// Emit a complete chunk (wrapping the main function body).
pub fn emit_chunk(func: &Function) -> String {
    let mut out = String::new();
    let body = fold_elseif_chain(&func.body);
    emit_block(&body, &mut out, 0);
    // Remove trailing blank lines
    while out.ends_with("\n\n") {
        out.pop();
    }
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Fold nested if-else chains into elseif clauses.
/// Transforms: `if A then B else if C then D else E end end`
/// into:       `if A then B elseif C then D else E end`
fn fold_elseif_chain(block: &Block) -> Block {
    block.iter().map(|stat| fold_stat(stat)).collect()
}

fn fold_stat(stat: &Stat) -> Stat {
    match stat {
        Stat::If {
            cond,
            then_block,
            elseif_clauses,
            else_block,
        } => {
            let then_block = fold_elseif_chain(then_block);
            let mut new_elseifs: Vec<(Expr, Block)> = elseif_clauses
                .iter()
                .map(|(c, b)| (c.clone(), fold_elseif_chain(b)))
                .collect();

            // Try to flatten: if else_block is a single `if` statement, merge it
            let new_else = if let Some(eb) = else_block {
                let folded = fold_elseif_chain(eb);
                if folded.len() == 1 {
                    if let Stat::If {
                        cond: inner_cond,
                        then_block: inner_then,
                        elseif_clauses: inner_elseifs,
                        else_block: inner_else,
                    } = &folded[0]
                    {
                        // Merge into elseif
                        new_elseifs.push((inner_cond.clone(), inner_then.clone()));
                        new_elseifs.extend(inner_elseifs.iter().cloned());
                        inner_else.clone()
                    } else {
                        Some(folded)
                    }
                } else {
                    Some(folded)
                }
            } else {
                None
            };

            Stat::If {
                cond: cond.clone(),
                then_block,
                elseif_clauses: new_elseifs,
                else_block: new_else,
            }
        }
        Stat::While { cond, body } => Stat::While {
            cond: cond.clone(),
            body: fold_elseif_chain(body),
        },
        Stat::Repeat { body, cond } => Stat::Repeat {
            body: fold_elseif_chain(body),
            cond: cond.clone(),
        },
        Stat::NumericFor { name, start, limit, step, body } => Stat::NumericFor {
            name: name.clone(),
            start: start.clone(),
            limit: limit.clone(),
            step: step.clone(),
            body: fold_elseif_chain(body),
        },
        Stat::GenericFor { names, iterators, body } => Stat::GenericFor {
            names: names.clone(),
            iterators: iterators.clone(),
            body: fold_elseif_chain(body),
        },
        Stat::DoBlock(body) => Stat::DoBlock(fold_elseif_chain(body)),
        other => other.clone(),
    }
}

fn emit_block(block: &Block, out: &mut String, indent: usize) {
    for (i, stat) in block.iter().enumerate() {
        // Add blank lines between top-level logical groups
        if indent == 0 && i > 0 {
            let prev = &block[i - 1];
            if should_separate(prev, stat) {
                out.push('\n');
            }
        }
        emit_stat(stat, out, indent);
    }
}

/// Decide whether to insert a blank line between two consecutive top-level statements.
fn should_separate(prev: &Stat, curr: &Stat) -> bool {
    // Always separate after a function definition
    if is_func_def(prev) {
        return true;
    }
    // Separate before a function definition
    if is_func_def(curr) {
        return true;
    }
    // Separate between different "kinds" of statements
    // (e.g., after a block of assignments before a call, or vice versa)
    false
}

fn is_func_def(stat: &Stat) -> bool {
    match stat {
        Stat::Assign { values, .. } => {
            values.len() == 1 && matches!(&values[0], Expr::FunctionDef(_))
        }
        Stat::LocalAssign { exprs, .. } => {
            exprs.len() == 1 && matches!(&exprs[0], Expr::FunctionDef(_))
        }
        _ => false,
    }
}

fn emit_stat(stat: &Stat, out: &mut String, indent: usize) {
    let pad = "  ".repeat(indent);
    match stat {
        Stat::LocalAssign { names, exprs } => {
            write!(out, "{}local {}", pad, names.join(", ")).unwrap();
            if !exprs.is_empty() {
                out.push_str(" = ");
                emit_expr_list(exprs, out);
            }
            out.push('\n');
        }
        Stat::Assign { targets, values } => {
            // Pretty-print `name = function(...) end` as `function name(...) end`
            if targets.len() == 1 && values.len() == 1 {
                if let Expr::FunctionDef(func) = &values[0] {
                    let name = match &targets[0] {
                        Expr::Global(n) => Some(n.clone()),
                        Expr::Name(n) => Some(n.clone()),
                        Expr::Field(table, field) => {
                            // t.method = function(...) -> function t.method(...)
                            let mut s = String::new();
                            emit_expr(table, &mut s, 10);
                            s.push('.');
                            s.push_str(field);
                            Some(s)
                        }
                        _ => None,
                    };
                    if let Some(fname) = name {
                        write!(out, "{}function {}(", pad, fname).unwrap();
                        let mut params = func.params.join(", ");
                        if func.is_vararg {
                            if !params.is_empty() {
                                params.push_str(", ");
                            }
                            params.push_str("...");
                        }
                        out.push_str(&params);
                        out.push_str(")\n");
                        emit_block(&func.body, out, indent + 1);
                        writeln!(out, "{}end", pad).unwrap();
                        return;
                    }
                }
            }
            write!(out, "{}", pad).unwrap();
            emit_expr_list(targets, out);
            out.push_str(" = ");
            emit_expr_list(values, out);
            out.push('\n');
        }
        Stat::Call(call) => {
            write!(out, "{}", pad).unwrap();
            emit_call(call, out);
            out.push('\n');
        }
        Stat::DoBlock(body) => {
            writeln!(out, "{}do", pad).unwrap();
            emit_block(body, out, indent + 1);
            writeln!(out, "{}end", pad).unwrap();
        }
        Stat::While { cond, body } => {
            write!(out, "{}while ", pad).unwrap();
            emit_expr(cond, out, 0);
            out.push_str(" do\n");
            emit_block(body, out, indent + 1);
            writeln!(out, "{}end", pad).unwrap();
        }
        Stat::Repeat { body, cond } => {
            writeln!(out, "{}repeat", pad).unwrap();
            emit_block(body, out, indent + 1);
            write!(out, "{}until ", pad).unwrap();
            emit_expr(cond, out, 0);
            out.push('\n');
        }
        Stat::If {
            cond,
            then_block,
            elseif_clauses,
            else_block,
        } => {
            write!(out, "{}if ", pad).unwrap();
            emit_expr(cond, out, 0);
            out.push_str(" then\n");
            emit_block(then_block, out, indent + 1);
            for (ec, eb) in elseif_clauses {
                write!(out, "{}elseif ", pad).unwrap();
                emit_expr(ec, out, 0);
                out.push_str(" then\n");
                emit_block(eb, out, indent + 1);
            }
            if let Some(eb) = else_block {
                writeln!(out, "{}else", pad).unwrap();
                emit_block(eb, out, indent + 1);
            }
            writeln!(out, "{}end", pad).unwrap();
        }
        Stat::NumericFor {
            name,
            start,
            limit,
            step,
            body,
        } => {
            write!(out, "{}for {} = ", pad, name).unwrap();
            emit_expr(start, out, 0);
            out.push_str(", ");
            emit_expr(limit, out, 0);
            if let Some(s) = step {
                out.push_str(", ");
                emit_expr(s, out, 0);
            }
            out.push_str(" do\n");
            emit_block(body, out, indent + 1);
            writeln!(out, "{}end", pad).unwrap();
        }
        Stat::GenericFor {
            names,
            iterators,
            body,
        } => {
            write!(out, "{}for {} in ", pad, names.join(", ")).unwrap();
            emit_expr_list(iterators, out);
            out.push_str(" do\n");
            emit_block(body, out, indent + 1);
            writeln!(out, "{}end", pad).unwrap();
        }
        Stat::Return(exprs) => {
            write!(out, "{}return", pad).unwrap();
            if !exprs.is_empty() {
                out.push(' ');
                emit_expr_list(exprs, out);
            }
            out.push('\n');
        }
        Stat::Break => {
            writeln!(out, "{}break", pad).unwrap();
        }
        Stat::Comment(text) => {
            writeln!(out, "{}-- {}", pad, text).unwrap();
        }
    }
}

fn emit_expr_list(exprs: &[Expr], out: &mut String) {
    for (i, e) in exprs.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        emit_expr(e, out, 0);
    }
}

/// Emit an expression, handling operator precedence and parenthesization.
/// `parent_prec` is the precedence of the enclosing operator (0 = no enclosing op).
fn emit_expr(expr: &Expr, out: &mut String, parent_prec: u8) {
    match expr {
        Expr::Nil => out.push_str("nil"),
        Expr::Bool(true) => out.push_str("true"),
        Expr::Bool(false) => out.push_str("false"),
        Expr::Number(n) => emit_number(n, out),
        Expr::StringLit(s) => emit_string(s, out),
        Expr::VarArg => out.push_str("..."),
        Expr::Name(n) => out.push_str(n),
        Expr::Global(n) => out.push_str(n),
        Expr::Register(r) => write!(out, "r{}", r).unwrap(),
        Expr::Upvalue(u) => write!(out, "upval{}", u).unwrap(),
        Expr::Index(table, key) => {
            emit_expr(table, out, 10);
            out.push('[');
            emit_expr(key, out, 0);
            out.push(']');
        }
        Expr::Field(table, field) => {
            emit_expr(table, out, 10);
            out.push('.');
            out.push_str(field);
        }
        Expr::BinOp(op, lhs, rhs) => {
            let prec = op.precedence();
            let needs_parens = prec < parent_prec;
            if needs_parens {
                out.push('(');
            }
            emit_expr(lhs, out, prec);
            write!(out, " {} ", op.symbol()).unwrap();
            // Right-associative: right child needs prec+1 to avoid unnecessary parens
            let rhs_prec = if op.is_right_assoc() { prec } else { prec + 1 };
            emit_expr(rhs, out, rhs_prec);
            if needs_parens {
                out.push(')');
            }
        }
        Expr::UnOp(op, operand) => {
            let prec = op.precedence();
            let needs_parens = prec < parent_prec;
            if needs_parens {
                out.push('(');
            }
            out.push_str(op.symbol());
            emit_expr(operand, out, prec);
            if needs_parens {
                out.push(')');
            }
        }
        Expr::FuncCall(call) => {
            emit_call(call, out);
        }
        Expr::MethodCall(call) => {
            emit_call(call, out);
        }
        Expr::FunctionDef(func) => {
            emit_function_def(func, out, false);
        }
        Expr::Table(fields) => {
            emit_table(fields, out);
        }
    }
}

fn emit_call(call: &CallExpr, out: &mut String) {
    emit_expr(&call.func, out, 10);
    out.push('(');
    emit_expr_list(&call.args, out);
    out.push(')');
}

fn emit_function_def(func: &Function, out: &mut String, _as_stat: bool) {
    out.push_str("function(");
    let mut params = func.params.join(", ");
    if func.is_vararg {
        if !params.is_empty() {
            params.push_str(", ");
        }
        params.push_str("...");
    }
    out.push_str(&params);
    out.push_str(")\n");

    // Estimate current indent from trailing whitespace
    let current_indent = count_trailing_indent(out);
    emit_block(&func.body, out, current_indent + 1);

    let pad = "  ".repeat(current_indent);
    write!(out, "{}end", pad).unwrap();
}

fn emit_table(fields: &[TableField], out: &mut String) {
    if fields.is_empty() {
        out.push_str("{}");
        return;
    }

    // Estimate inline length to decide single-line vs multi-line
    let current_indent = count_trailing_indent(out);
    let inline = emit_table_inline(fields);
    // Use multi-line if: inline is too long, or has nested tables, or many fields
    let use_multiline = inline.len() > 80 || fields.len() > 4 && inline.len() > 60;

    if !use_multiline {
        out.push_str(&inline);
        return;
    }

    // Multi-line format
    let inner_pad = "  ".repeat(current_indent + 1);
    let outer_pad = "  ".repeat(current_indent);
    out.push_str("{\n");
    for (i, field) in fields.iter().enumerate() {
        out.push_str(&inner_pad);
        match field {
            TableField::IndexField(key, val) => {
                out.push('[');
                emit_expr(key, out, 0);
                out.push_str("] = ");
                emit_expr(val, out, 0);
            }
            TableField::NameField(name, val) => {
                out.push_str(name);
                out.push_str(" = ");
                emit_expr(val, out, 0);
            }
            TableField::Value(val) => {
                emit_expr(val, out, 0);
            }
        }
        if i + 1 < fields.len() {
            out.push(',');
        }
        out.push('\n');
    }
    write!(out, "{}}}", outer_pad).unwrap();
}

/// Emit a table as a single-line string (for length estimation).
fn emit_table_inline(fields: &[TableField]) -> String {
    let mut s = String::new();
    s.push('{');
    for (i, field) in fields.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        match field {
            TableField::IndexField(key, val) => {
                s.push('[');
                emit_expr(key, &mut s, 0);
                s.push_str("] = ");
                emit_expr(val, &mut s, 0);
            }
            TableField::NameField(name, val) => {
                s.push_str(name);
                s.push_str(" = ");
                emit_expr(val, &mut s, 0);
            }
            TableField::Value(val) => {
                emit_expr(val, &mut s, 0);
            }
        }
    }
    s.push('}');
    s
}

fn emit_number(n: &NumLit, out: &mut String) {
    match n {
        NumLit::Int(v) => write!(out, "{}", v).unwrap(),
        NumLit::Float(v) => {
            if v.fract() == 0.0 && v.abs() < 1e15 {
                // Emit as integer-looking float if it has no fractional part
                write!(out, "{}", *v as i64).unwrap();
            } else {
                write!(out, "{}", v).unwrap();
            }
        }
    }
}

/// Emit a string literal with proper escaping.
/// Supports multi-line string detection, GBK decoding, and non-UTF-8 byte escapes.
fn emit_string(bytes: &[u8], out: &mut String) {
    // Try UTF-8 first
    if let Ok(s) = std::str::from_utf8(bytes) {
        emit_string_content(s, bytes, out);
        return;
    }

    // Try GBK decoding (common in JX3 Lua scripts)
    let (decoded, _, had_errors) = encoding_rs::GBK.decode(bytes);
    if !had_errors {
        emit_string_content(&decoded, bytes, out);
        return;
    }

    // Fallback: emit with byte escapes for non-ASCII
    out.push('"');
    for &b in bytes {
        emit_byte_escaped(b, out);
    }
    out.push('"');
}

/// Emit a string that has been successfully decoded to text.
fn emit_string_content(text: &str, raw: &[u8], out: &mut String) {
    let has_newlines = text.contains('\n');
    let has_long_bracket_close = text.contains("]]");
    let is_printable = text.chars().all(|c| !c.is_control() || c == '\n' || c == '\r' || c == '\t');

    if has_newlines && !has_long_bracket_close && is_printable {
        // Use [[...]] long string
        out.push_str("[[");
        if text.starts_with('\n') {
            out.push('\n');
        }
        out.push_str(text);
        out.push_str("]]");
        return;
    }

    // Use quoted string with escapes
    out.push('"');
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            '\x07' => out.push_str("\\a"),
            '\x08' => out.push_str("\\b"),
            '\x0C' => out.push_str("\\f"),
            '\x0B' => out.push_str("\\v"),
            c if c >= ' ' && c <= '~' => out.push(c),
            c if !c.is_control() => out.push(c), // printable Unicode (incl. CJK)
            c => {
                // Control character: emit as byte escapes
                let mut buf = [0u8; 4];
                let s = c.encode_utf8(&mut buf);
                for &b in s.as_bytes() {
                    write!(out, "\\{}", b).unwrap();
                }
            }
        }
    }
    out.push('"');
}

fn emit_byte_escaped(b: u8, out: &mut String) {
    match b {
        b'\\' => out.push_str("\\\\"),
        b'"' => out.push_str("\\\""),
        b'\n' => out.push_str("\\n"),
        b'\r' => out.push_str("\\r"),
        b'\t' => out.push_str("\\t"),
        b'\0' => out.push_str("\\0"),
        0x07 => out.push_str("\\a"),
        0x08 => out.push_str("\\b"),
        0x0C => out.push_str("\\f"),
        0x0B => out.push_str("\\v"),
        0x20..=0x7E => out.push(b as char),
        _ => {
            write!(out, "\\{}", b).unwrap();
        }
    }
}

fn count_trailing_indent(s: &str) -> usize {
    // Count indent level from last newline
    if let Some(last_nl) = s.rfind('\n') {
        let after = &s[last_nl + 1..];
        let spaces = after.len() - after.trim_start().len();
        spaces / 2
    } else {
        0
    }
}
