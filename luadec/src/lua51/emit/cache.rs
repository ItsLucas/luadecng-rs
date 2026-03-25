use crate::lua51::ast::*;
use super::normalize::simplify_expr;

// ---- Repeated trailing getter caching ----

pub(super) fn cache_repeated_trailing_getter_call(cond: &Expr, then_block: &Block) -> Option<Block> {
    let mut terms = Vec::new();
    collect_and_terms(cond, &mut terms);
    let last_term = terms.last()?.clone();
    let call_expr = match &last_term {
        Expr::FuncCall(call) if is_cacheable_getter_call(call) => last_term.clone(),
        _ => return None,
    };

    if !block_contains_expr(then_block, &call_expr) {
        return None;
    }

    let cache_name = uniquify_cache_name(suggest_cached_call_name(&call_expr), cond, then_block);
    let outer_terms = &terms[..terms.len() - 1];
    let rewritten_then = replace_exprs_in_block(then_block, &call_expr, &Expr::Name(cache_name.clone()));
    let inner_if = Stat::If {
        cond: Expr::Name(cache_name.clone()),
        then_block: rewritten_then,
        elseif_clauses: Vec::new(),
        else_block: None,
    };
    let cached_local = Stat::LocalAssign {
        names: vec![cache_name.clone()],
        exprs: vec![call_expr],
    };

    if outer_terms.is_empty() {
        return Some(vec![Stat::DoBlock(vec![cached_local, inner_if])]);
    }

    Some(vec![Stat::If {
        cond: combine_and_terms(outer_terms),
        then_block: vec![cached_local, inner_if],
        elseif_clauses: Vec::new(),
        else_block: None,
    }])
}

// ---- Shared negated getter caching ----

pub(super) fn cache_shared_negated_getter_calls(block: &Block) -> Block {
    let mut out = Vec::new();
    let mut index = 0;

    while index < block.len() {
        let Some((shared_call, mut group)) = collect_negated_getter_group(block, index) else {
            out.push(block[index].clone());
            index += 1;
            continue;
        };

        let group_len = group.len();
        if group_len < 2 {
            out.push(block[index].clone());
            index += 1;
            continue;
        }

        let cache_name = uniquify_cache_name(suggest_cached_call_name(&shared_call), &Expr::Bool(false), block);
        let replacement = Expr::UnOp(UnOp::Not, Box::new(Expr::Name(cache_name.clone())));
        let prefixes: Vec<Expr> = group
            .iter()
            .filter_map(|(prefix, _)| prefix.clone())
            .collect();

        let rewritten_ifs: Block = group
            .drain(..)
            .map(|(prefix, stat)| rewrite_grouped_if(prefix, stat, &replacement))
            .collect();

        let mut outer_body = Vec::with_capacity(rewritten_ifs.len() + 1);
        outer_body.push(Stat::LocalAssign {
            names: vec![cache_name],
            exprs: vec![shared_call],
        });
        outer_body.extend(rewritten_ifs);

        if prefixes.len() == group_len && !prefixes.is_empty() {
            out.push(Stat::If {
                cond: combine_or_terms(&prefixes),
                then_block: outer_body,
                elseif_clauses: Vec::new(),
                else_block: None,
            });
        } else {
            out.push(Stat::DoBlock(outer_body));
        }

        index += group_len;
    }

    out
}

fn collect_negated_getter_group(block: &Block, start: usize) -> Option<(Expr, Vec<(Option<Expr>, Stat)>)> {
    let (shared_call, first_prefix) = extract_negated_trailing_getter_from_if(block.get(start)?)?;
    let mut group = vec![(first_prefix, block[start].clone())];
    let mut index = start + 1;

    while let Some((other_call, other_prefix)) = block.get(index).and_then(extract_negated_trailing_getter_from_if) {
        if other_call != shared_call {
            break;
        }
        group.push((other_prefix, block[index].clone()));
        index += 1;
    }

    Some((shared_call, group))
}

fn extract_negated_trailing_getter_from_if(stat: &Stat) -> Option<(Expr, Option<Expr>)> {
    let Stat::If {
        cond,
        then_block: _,
        elseif_clauses,
        else_block,
    } = stat else {
        return None;
    };
    if !elseif_clauses.is_empty() || else_block.is_some() {
        return None;
    }

    match cond {
        Expr::BinOp(BinOp::And, prefix, tail) => match &**tail {
            Expr::UnOp(UnOp::Not, inner) => match &**inner {
                Expr::FuncCall(call) if is_cacheable_getter_call(call) => {
                    Some((*inner.clone(), Some(*prefix.clone())))
                }
                _ => None,
            },
            _ => None,
        },
        Expr::UnOp(UnOp::Not, inner) => match &**inner {
            Expr::FuncCall(call) if is_cacheable_getter_call(call) => Some((*inner.clone(), None)),
            _ => None,
        },
        _ => None,
    }
}

fn rewrite_grouped_if(
    prefix: Option<Expr>,
    stat: Stat,
    replacement: &Expr,
) -> Stat {
    let Stat::If {
        cond: _,
        then_block,
        elseif_clauses: _,
        else_block: _,
    } = stat else {
        unreachable!();
    };

    let cond = match prefix {
        Some(prefix) => simplify_expr(Expr::BinOp(
            BinOp::And,
            Box::new(prefix),
            Box::new(replacement.clone()),
        )),
        None => replacement.clone(),
    };

    Stat::If {
        cond,
        then_block,
        elseif_clauses: Vec::new(),
        else_block: None,
    }
}

// ---- Expression term helpers ----

fn combine_or_terms(terms: &[Expr]) -> Expr {
    terms
        .iter()
        .cloned()
        .reduce(|lhs, rhs| simplify_expr(Expr::BinOp(BinOp::Or, Box::new(lhs), Box::new(rhs))))
        .unwrap_or(Expr::Bool(true))
}

fn collect_and_terms<'a>(expr: &'a Expr, out: &mut Vec<Expr>) {
    match expr {
        Expr::BinOp(BinOp::And, lhs, rhs) => {
            collect_and_terms(lhs, out);
            collect_and_terms(rhs, out);
        }
        _ => out.push(expr.clone()),
    }
}

fn combine_and_terms(terms: &[Expr]) -> Expr {
    terms
        .iter()
        .cloned()
        .reduce(|lhs, rhs| simplify_expr(Expr::BinOp(BinOp::And, Box::new(lhs), Box::new(rhs))))
        .unwrap_or(Expr::Bool(true))
}

// ---- Cacheable getter detection ----

fn is_cacheable_getter_call(call: &CallExpr) -> bool {
    match &call.func {
        Expr::Field(_, method) => matches!(method.as_str(), "GetBuffByOwner" | "GetBuff"),
        _ => false,
    }
}

fn suggest_cached_call_name(expr: &Expr) -> String {
    let Expr::FuncCall(call) = expr else {
        return "cached_value".to_string();
    };
    let Expr::Field(_, method) = &call.func else {
        return "cached_value".to_string();
    };

    if matches!(method.as_str(), "GetBuffByOwner" | "GetBuff") {
        if let Some(expr) = call.args.first() {
            match expr {
                Expr::Number(NumLit::Int(buff_id)) => {
                    return format!("buff_{}", buff_id);
                }
                Expr::Number(NumLit::Float(buff_id)) if buff_id.fract() == 0.0 => {
                    return format!("buff_{}", *buff_id as i64);
                }
                _ => {}
            }
        }
    }

    camel_to_snake(method)
}

fn camel_to_snake(name: &str) -> String {
    let mut out = String::new();
    for (idx, ch) in name.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if idx != 0 {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

fn uniquify_cache_name(base: String, cond: &Expr, block: &Block) -> String {
    if !expr_contains_name(cond, &base) && !block_contains_name(block, &base) {
        return base;
    }

    let mut suffix = 1;
    loop {
        let candidate = format!("{}_{}", base, suffix);
        if !expr_contains_name(cond, &candidate) && !block_contains_name(block, &candidate) {
            return candidate;
        }
        suffix += 1;
    }
}

// ---- AST contains/name checks ----

fn block_contains_name(block: &Block, name: &str) -> bool {
    block.iter().any(|stat| stat_contains_name(stat, name))
}

fn stat_contains_name(stat: &Stat, name: &str) -> bool {
    match stat {
        Stat::LocalAssign { names, exprs } => {
            names.iter().any(|existing| existing == name)
                || exprs.iter().any(|expr| expr_contains_name(expr, name))
        }
        Stat::Assign { targets, values } => {
            targets.iter().any(|expr| expr_contains_name(expr, name))
                || values.iter().any(|expr| expr_contains_name(expr, name))
        }
        Stat::Call(call) => call_contains_name(call, name),
        Stat::DoBlock(body) => block_contains_name(body, name),
        Stat::While { cond, body } => expr_contains_name(cond, name) || block_contains_name(body, name),
        Stat::Repeat { body, cond } => block_contains_name(body, name) || expr_contains_name(cond, name),
        Stat::If { cond, then_block, elseif_clauses, else_block } => {
            expr_contains_name(cond, name)
                || block_contains_name(then_block, name)
                || elseif_clauses.iter().any(|(expr, block)| expr_contains_name(expr, name) || block_contains_name(block, name))
                || else_block.as_ref().is_some_and(|block| block_contains_name(block, name))
        }
        Stat::NumericFor { name: loop_name, start, limit, step, body } => {
            loop_name == name
                || expr_contains_name(start, name)
                || expr_contains_name(limit, name)
                || step.as_ref().is_some_and(|expr| expr_contains_name(expr, name))
                || block_contains_name(body, name)
        }
        Stat::GenericFor { names, iterators, body } => {
            names.iter().any(|existing| existing == name)
                || iterators.iter().any(|expr| expr_contains_name(expr, name))
                || block_contains_name(body, name)
        }
        Stat::Return(exprs) => exprs.iter().any(|expr| expr_contains_name(expr, name)),
        Stat::Break | Stat::Comment(_) => false,
    }
}

fn expr_contains_name(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Name(existing) => existing == name,
        Expr::Index(table, key) => expr_contains_name(table, name) || expr_contains_name(key, name),
        Expr::Field(table, _) => expr_contains_name(table, name),
        Expr::MethodCall(call) | Expr::FuncCall(call) => call_contains_name(call, name),
        Expr::BinOp(_, lhs, rhs) => expr_contains_name(lhs, name) || expr_contains_name(rhs, name),
        Expr::UnOp(_, inner) => expr_contains_name(inner, name),
        Expr::FunctionDef(func) => block_contains_name(&func.body, name),
        Expr::Table(fields) => fields.iter().any(|field| match field {
            TableField::IndexField(key, value) => expr_contains_name(key, name) || expr_contains_name(value, name),
            TableField::NameField(_, value) | TableField::Value(value) => expr_contains_name(value, name),
        }),
        _ => false,
    }
}

fn call_contains_name(call: &CallExpr, name: &str) -> bool {
    expr_contains_name(&call.func, name) || call.args.iter().any(|arg| expr_contains_name(arg, name))
}

// ---- AST contains/expr checks ----

fn block_contains_expr(block: &Block, target: &Expr) -> bool {
    block.iter().any(|stat| stat_contains_expr(stat, target))
}

fn stat_contains_expr(stat: &Stat, target: &Expr) -> bool {
    match stat {
        Stat::LocalAssign { exprs, .. } => exprs.iter().any(|expr| expr_contains_expr(expr, target)),
        Stat::Assign { targets, values } => {
            targets.iter().any(|expr| expr_contains_expr(expr, target))
                || values.iter().any(|expr| expr_contains_expr(expr, target))
        }
        Stat::Call(call) => expr_contains_expr(&Expr::FuncCall(Box::new(call.clone())), target),
        Stat::DoBlock(body) => block_contains_expr(body, target),
        Stat::While { cond, body } => expr_contains_expr(cond, target) || block_contains_expr(body, target),
        Stat::Repeat { body, cond } => block_contains_expr(body, target) || expr_contains_expr(cond, target),
        Stat::If { cond, then_block, elseif_clauses, else_block } => {
            expr_contains_expr(cond, target)
                || block_contains_expr(then_block, target)
                || elseif_clauses.iter().any(|(expr, block)| expr_contains_expr(expr, target) || block_contains_expr(block, target))
                || else_block.as_ref().is_some_and(|block| block_contains_expr(block, target))
        }
        Stat::NumericFor { start, limit, step, body, .. } => {
            expr_contains_expr(start, target)
                || expr_contains_expr(limit, target)
                || step.as_ref().is_some_and(|expr| expr_contains_expr(expr, target))
                || block_contains_expr(body, target)
        }
        Stat::GenericFor { iterators, body, .. } => {
            iterators.iter().any(|expr| expr_contains_expr(expr, target))
                || block_contains_expr(body, target)
        }
        Stat::Return(exprs) => exprs.iter().any(|expr| expr_contains_expr(expr, target)),
        Stat::Break | Stat::Comment(_) => false,
    }
}

fn expr_contains_expr(expr: &Expr, target: &Expr) -> bool {
    if expr == target {
        return true;
    }

    match expr {
        Expr::Index(table, key) => expr_contains_expr(table, target) || expr_contains_expr(key, target),
        Expr::Field(table, _) => expr_contains_expr(table, target),
        Expr::MethodCall(call) | Expr::FuncCall(call) => {
            expr_contains_expr(&call.func, target)
                || call.args.iter().any(|arg| expr_contains_expr(arg, target))
        }
        Expr::BinOp(_, lhs, rhs) => expr_contains_expr(lhs, target) || expr_contains_expr(rhs, target),
        Expr::UnOp(_, inner) => expr_contains_expr(inner, target),
        Expr::FunctionDef(func) => block_contains_expr(&func.body, target),
        Expr::Table(fields) => fields.iter().any(|field| match field {
            TableField::IndexField(key, value) => expr_contains_expr(key, target) || expr_contains_expr(value, target),
            TableField::NameField(_, value) | TableField::Value(value) => expr_contains_expr(value, target),
        }),
        _ => false,
    }
}

// ---- AST expression replacement ----

fn replace_exprs_in_block(block: &Block, target: &Expr, replacement: &Expr) -> Block {
    block.iter().map(|stat| replace_exprs_in_stat(stat, target, replacement)).collect()
}

fn replace_exprs_in_stat(stat: &Stat, target: &Expr, replacement: &Expr) -> Stat {
    match stat {
        Stat::LocalAssign { names, exprs } => Stat::LocalAssign {
            names: names.clone(),
            exprs: exprs.iter().map(|expr| replace_expr(expr, target, replacement)).collect(),
        },
        Stat::Assign { targets, values } => Stat::Assign {
            targets: targets.iter().map(|expr| replace_expr(expr, target, replacement)).collect(),
            values: values.iter().map(|expr| replace_expr(expr, target, replacement)).collect(),
        },
        Stat::Call(call) => match replace_expr(&Expr::FuncCall(Box::new(call.clone())), target, replacement) {
            Expr::FuncCall(updated) => Stat::Call(*updated),
            expr => Stat::Call(CallExpr { func: expr, args: Vec::new() }),
        },
        Stat::DoBlock(body) => Stat::DoBlock(replace_exprs_in_block(body, target, replacement)),
        Stat::While { cond, body } => Stat::While {
            cond: replace_expr(cond, target, replacement),
            body: replace_exprs_in_block(body, target, replacement),
        },
        Stat::Repeat { body, cond } => Stat::Repeat {
            body: replace_exprs_in_block(body, target, replacement),
            cond: replace_expr(cond, target, replacement),
        },
        Stat::If { cond, then_block, elseif_clauses, else_block } => Stat::If {
            cond: replace_expr(cond, target, replacement),
            then_block: replace_exprs_in_block(then_block, target, replacement),
            elseif_clauses: elseif_clauses
                .iter()
                .map(|(expr, block)| {
                    (
                        replace_expr(expr, target, replacement),
                        replace_exprs_in_block(block, target, replacement),
                    )
                })
                .collect(),
            else_block: else_block
                .as_ref()
                .map(|block| replace_exprs_in_block(block, target, replacement)),
        },
        Stat::NumericFor { name, start, limit, step, body } => Stat::NumericFor {
            name: name.clone(),
            start: replace_expr(start, target, replacement),
            limit: replace_expr(limit, target, replacement),
            step: step.as_ref().map(|expr| replace_expr(expr, target, replacement)),
            body: replace_exprs_in_block(body, target, replacement),
        },
        Stat::GenericFor { names, iterators, body } => Stat::GenericFor {
            names: names.clone(),
            iterators: iterators.iter().map(|expr| replace_expr(expr, target, replacement)).collect(),
            body: replace_exprs_in_block(body, target, replacement),
        },
        Stat::Return(exprs) => Stat::Return(
            exprs.iter().map(|expr| replace_expr(expr, target, replacement)).collect(),
        ),
        Stat::Break => Stat::Break,
        Stat::Comment(text) => Stat::Comment(text.clone()),
    }
}

fn replace_expr(expr: &Expr, target: &Expr, replacement: &Expr) -> Expr {
    if expr == target {
        return replacement.clone();
    }

    match expr {
        Expr::Index(table, key) => Expr::Index(
            Box::new(replace_expr(table, target, replacement)),
            Box::new(replace_expr(key, target, replacement)),
        ),
        Expr::Field(table, field) => Expr::Field(
            Box::new(replace_expr(table, target, replacement)),
            field.clone(),
        ),
        Expr::MethodCall(call) => Expr::MethodCall(Box::new(replace_call(call, target, replacement))),
        Expr::FuncCall(call) => Expr::FuncCall(Box::new(replace_call(call, target, replacement))),
        Expr::BinOp(op, lhs, rhs) => Expr::BinOp(
            *op,
            Box::new(replace_expr(lhs, target, replacement)),
            Box::new(replace_expr(rhs, target, replacement)),
        ),
        Expr::UnOp(op, inner) => Expr::UnOp(*op, Box::new(replace_expr(inner, target, replacement))),
        Expr::FunctionDef(func) => Expr::FunctionDef(Box::new(Function {
            params: func.params.clone(),
            is_vararg: func.is_vararg,
            body: replace_exprs_in_block(&func.body, target, replacement),
        })),
        Expr::Table(fields) => Expr::Table(
            fields.iter().map(|field| match field {
                TableField::IndexField(key, value) => TableField::IndexField(
                    replace_expr(key, target, replacement),
                    replace_expr(value, target, replacement),
                ),
                TableField::NameField(name, value) => {
                    TableField::NameField(name.clone(), replace_expr(value, target, replacement))
                }
                TableField::Value(value) => TableField::Value(replace_expr(value, target, replacement)),
            }).collect(),
        ),
        other => other.clone(),
    }
}

fn replace_call(call: &CallExpr, target: &Expr, replacement: &Expr) -> CallExpr {
    CallExpr {
        func: replace_expr(&call.func, target, replacement),
        args: call.args.iter().map(|arg| replace_expr(arg, target, replacement)).collect(),
    }
}
