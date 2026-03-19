use std::fmt::Write;

use crate::lua51::ast::*;

/// Emit a Lua function as source code.
pub fn emit_function(func: &Function) -> String {
    let mut out = String::new();
    let body = normalize_block(&func.body);
    let body = fold_elseif_chain(&body);
    emit_block(&body, &mut out, 0);
    out
}

/// Emit a complete chunk (wrapping the main function body).
pub fn emit_chunk(func: &Function) -> String {
    let mut out = String::new();
    let body = normalize_block(&func.body);
    let body = fold_elseif_chain(&body);
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

fn normalize_block(block: &Block) -> Block {
    let mut out = Vec::new();
    for stat in block {
        out.extend(normalize_stat(stat));
    }
    let out = cache_shared_negated_getter_calls(&out);
    collapse_nested_table_assignments(&out)
}

fn collapse_nested_table_assignments(block: &Block) -> Block {
    let mut out = Vec::new();
    let mut index = 0;

    while index < block.len() {
        let Some((seed, base_expr, mut base_fields)) = extract_table_assignment_seed(&block[index]) else {
            out.push(block[index].clone());
            index += 1;
            continue;
        };

        let mut next = index + 1;
        while next < block.len() {
            let Some((field_name, value)) = extract_nested_table_assignment(&block[next], &base_expr) else {
                break;
            };
            base_fields.push(TableField::NameField(field_name, value));
            next += 1;
        }

        if next == index + 1 {
            out.push(block[index].clone());
            index += 1;
            continue;
        }

        out.push(rebuild_table_assignment_seed(seed, base_fields));
        index = next;
    }

    out
}

enum TableAssignmentSeed {
    Assign(Expr),
    LocalAssign(String),
}

fn extract_table_assignment_seed(
    stat: &Stat,
) -> Option<(TableAssignmentSeed, Expr, Vec<TableField>)> {
    match stat {
        Stat::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
            let Expr::Table(fields) = &values[0] else {
                return None;
            };
            let base = targets[0].clone();
            let fields = fields.clone();
            Some((TableAssignmentSeed::Assign(base.clone()), base, fields))
        }
        Stat::LocalAssign { names, exprs } if names.len() == 1 && exprs.len() == 1 => {
            let Expr::Table(fields) = &exprs[0] else {
                return None;
            };
            let local_name = names[0].clone();
            let fields = fields.clone();
            Some((
                TableAssignmentSeed::LocalAssign(local_name.clone()),
                Expr::Name(local_name),
                fields,
            ))
        }
        _ => None,
    }
}

fn rebuild_table_assignment_seed(seed: TableAssignmentSeed, fields: Vec<TableField>) -> Stat {
    match seed {
        TableAssignmentSeed::Assign(target) => Stat::Assign {
            targets: vec![target],
            values: vec![Expr::Table(fields)],
        },
        TableAssignmentSeed::LocalAssign(name) => Stat::LocalAssign {
            names: vec![name],
            exprs: vec![Expr::Table(fields)],
        },
    }
}

fn extract_nested_table_assignment(stat: &Stat, base_expr: &Expr) -> Option<(String, Expr)> {
    let Stat::Assign { targets, values } = stat else {
        return None;
    };
    if targets.len() != 1 || values.len() != 1 {
        return None;
    }
    let Expr::Table(_) = &values[0] else {
        return None;
    };

    let field_name = match &targets[0] {
        Expr::Field(table, field) if table.as_ref() == base_expr => field.clone(),
        Expr::Index(table, key) if table.as_ref() == base_expr => match key.as_ref() {
            Expr::StringLit(bytes) => {
                let field = std::str::from_utf8(bytes).ok()?;
                if !is_identifier(field) {
                    return None;
                }
                field.to_string()
            }
            _ => return None,
        },
        _ => return None,
    };

    Some((field_name, values[0].clone()))
}

fn is_identifier(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    let mut chars = name.chars();
    let first = chars.next().unwrap();
    if !first.is_ascii_alphabetic() && first != '_' {
        return false;
    }
    chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_') && !is_lua_keyword(name)
}

fn is_lua_keyword(name: &str) -> bool {
    matches!(
        name,
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

fn normalize_stat(stat: &Stat) -> Block {
    match stat {
        Stat::LocalAssign { names, exprs } => vec![Stat::LocalAssign {
            names: names.clone(),
            exprs: exprs.iter().cloned().map(simplify_expr).collect(),
        }],
        Stat::Assign { targets, values } => vec![Stat::Assign {
            targets: targets.iter().cloned().map(simplify_expr).collect(),
            values: values.iter().cloned().map(simplify_expr).collect(),
        }],
        Stat::Call(call) => vec![Stat::Call(simplify_call(call.clone()))],
        Stat::DoBlock(body) => vec![Stat::DoBlock(normalize_block(body))],
        Stat::While { cond, body } => vec![Stat::While {
            cond: simplify_expr(cond.clone()),
            body: normalize_block(body),
        }],
        Stat::Repeat { body, cond } => vec![Stat::Repeat {
            body: normalize_block(body),
            cond: simplify_expr(cond.clone()),
        }],
        Stat::If {
            cond,
            then_block,
            elseif_clauses,
            else_block,
        } => normalize_if(cond, then_block, elseif_clauses, else_block),
        Stat::NumericFor {
            name,
            start,
            limit,
            step,
            body,
        } => vec![Stat::NumericFor {
            name: name.clone(),
            start: simplify_expr(start.clone()),
            limit: simplify_expr(limit.clone()),
            step: step.clone().map(simplify_expr),
            body: normalize_block(body),
        }],
        Stat::GenericFor { names, iterators, body } => vec![Stat::GenericFor {
            names: names.clone(),
            iterators: iterators.iter().cloned().map(simplify_expr).collect(),
            body: normalize_block(body),
        }],
        Stat::Return(exprs) => vec![Stat::Return(
            exprs.iter().cloned().map(simplify_expr).collect(),
        )],
        Stat::Break => vec![Stat::Break],
        Stat::Comment(text) => vec![Stat::Comment(text.clone())],
    }
}

fn normalize_if(
    cond: &Expr,
    then_block: &Block,
    elseif_clauses: &[(Expr, Block)],
    else_block: &Option<Block>,
) -> Block {
    let cond = simplify_expr(cond.clone());
    let then_block = normalize_block(then_block);
    let mut elseif_clauses: Vec<(Expr, Block)> = elseif_clauses
        .iter()
        .map(|(expr, block)| (simplify_expr(expr.clone()), normalize_block(block)))
        .collect();
    let mut else_block = else_block.as_ref().map(normalize_block);

    loop {
        let Some(block) = else_block.as_ref() else {
            break;
        };
        if block.len() != 1 {
            break;
        }
        let Stat::If {
            cond: inner_cond,
            then_block: inner_then,
            elseif_clauses: inner_elseifs,
            else_block: inner_else,
        } = &block[0] else {
            break;
        };

        elseif_clauses.push((simplify_expr(inner_cond.clone()), inner_then.clone()));
        elseif_clauses.extend(inner_elseifs.iter().cloned());
        else_block = inner_else.clone();
    }

    if then_block.is_empty() && elseif_clauses.is_empty() {
        if let Some(else_block) = else_block.as_ref() {
            if !else_block.is_empty() {
                return vec![Stat::If {
                    cond: negate_condition(cond),
                    then_block: else_block.clone(),
                    elseif_clauses: Vec::new(),
                    else_block: None,
                }];
            }
        }
    }

    if elseif_clauses.is_empty() && else_block.is_none() && then_block.len() == 1 {
        if let Stat::If {
            cond: inner_cond,
            then_block: inner_then,
            elseif_clauses: inner_elseifs,
            else_block: inner_else,
        } = &then_block[0]
        {
            let merged_terms = count_and_terms(&cond) + count_and_terms(inner_cond);
            if inner_elseifs.is_empty() && inner_else.is_none() && !inner_then.is_empty() && merged_terms <= 3 {
                return vec![Stat::If {
                    cond: simplify_expr(Expr::BinOp(
                        BinOp::And,
                        Box::new(cond),
                        Box::new(inner_cond.clone()),
                    )),
                    then_block: inner_then.clone(),
                    elseif_clauses: Vec::new(),
                    else_block: None,
                }];
            }
        }
    }

    if elseif_clauses.is_empty() && else_block.is_none() && then_block.len() > 1 {
        if let Stat::If {
            cond: inner_cond,
            then_block: inner_then,
            elseif_clauses: inner_elseifs,
            else_block: inner_else,
        } = &then_block[0]
        {
            let merged_terms = count_and_terms(&cond) + count_and_terms(inner_cond);
            if inner_elseifs.is_empty()
                && inner_else.is_none()
                && block_ends_with_terminator(inner_then)
                && merged_terms <= 3
            {
                let mut out = vec![Stat::If {
                    cond: simplify_expr(Expr::BinOp(
                        BinOp::And,
                        Box::new(cond),
                        Box::new(inner_cond.clone()),
                    )),
                    then_block: inner_then.clone(),
                    elseif_clauses: Vec::new(),
                    else_block: None,
                }];
                out.extend(then_block[1..].iter().cloned());
                return out;
            }
        }
    }

    if else_block.is_none()
        && !then_block.is_empty()
        && !elseif_clauses.is_empty()
        && elseif_clauses.iter().all(|(_, block)| *block == then_block)
    {
        let merged_cond = elseif_clauses.iter().fold(cond.clone(), |acc, (expr, _)| {
            simplify_expr(Expr::BinOp(BinOp::Or, Box::new(acc), Box::new(expr.clone())))
        });
        return vec![Stat::If {
            cond: merged_cond,
            then_block,
            elseif_clauses: Vec::new(),
            else_block: None,
        }];
    }

    if elseif_clauses.is_empty() && else_block.is_none() {
        if let Some(rewritten) = cache_repeated_trailing_getter_call(&cond, &then_block) {
            return rewritten;
        }
    }

    let (trimmed_then, trailing_then) = split_trailing_terminator_tail(&then_block);
    if trailing_then.is_empty() {
        return vec![Stat::If {
            cond,
            then_block,
            elseif_clauses,
            else_block,
        }];
    }

    if !elseif_clauses.is_empty() || else_block.is_some() {
        return vec![Stat::If {
            cond,
            then_block: trimmed_then,
            elseif_clauses,
            else_block,
        }];
    }

    let mut out = vec![Stat::If {
        cond,
        then_block: trimmed_then,
        elseif_clauses,
        else_block,
    }];
    out.extend(trailing_then);
    out
}

fn split_trailing_terminator_tail(block: &Block) -> (Block, Block) {
    for (index, stat) in block.iter().enumerate() {
        if is_terminator(stat) {
            let prefix = block[..=index].to_vec();
            let tail = block[index + 1..].to_vec();
            return (prefix, tail);
        }
    }
    (block.clone(), Vec::new())
}

fn block_ends_with_terminator(block: &Block) -> bool {
    block.last().is_some_and(is_terminator)
}

fn is_terminator(stat: &Stat) -> bool {
    matches!(stat, Stat::Return(_) | Stat::Break)
}

fn count_and_terms(expr: &Expr) -> usize {
    match expr {
        Expr::BinOp(BinOp::And, lhs, rhs) => count_and_terms(lhs) + count_and_terms(rhs),
        _ => 1,
    }
}

fn simplify_expr(expr: Expr) -> Expr {
    match expr {
        Expr::Index(table, key) => Expr::Index(
            Box::new(simplify_expr(*table)),
            Box::new(simplify_expr(*key)),
        ),
        Expr::Field(table, field) => Expr::Field(Box::new(simplify_expr(*table)), field),
        Expr::MethodCall(call) => Expr::MethodCall(Box::new(simplify_call(*call))),
        Expr::FuncCall(call) => Expr::FuncCall(Box::new(simplify_call(*call))),
        Expr::BinOp(op, lhs, rhs) => {
            let lhs = simplify_expr(*lhs);
            let rhs = simplify_expr(*rhs);
            match (op, &lhs) {
                (BinOp::And, Expr::Bool(true)) => rhs,
                (BinOp::And, Expr::Bool(false)) => Expr::Bool(false),
                (BinOp::Or, Expr::Bool(false)) => rhs,
                (BinOp::Or, Expr::Bool(true)) => Expr::Bool(true),
                _ => Expr::BinOp(op, Box::new(lhs), Box::new(rhs)),
            }
        }
        Expr::UnOp(UnOp::Not, operand) => {
            let operand = simplify_expr(*operand);
            match operand {
                Expr::Bool(value) => Expr::Bool(!value),
                Expr::UnOp(UnOp::Not, inner) => Expr::UnOp(UnOp::Not, inner),
                other => Expr::UnOp(UnOp::Not, Box::new(other)),
            }
        }
        Expr::UnOp(op, operand) => Expr::UnOp(op, Box::new(simplify_expr(*operand))),
        Expr::FunctionDef(func) => Expr::FunctionDef(Box::new(Function {
            params: func.params.clone(),
            is_vararg: func.is_vararg,
            body: normalize_block(&func.body),
        })),
        Expr::Table(fields) => Expr::Table(
            fields
                .into_iter()
                .map(|field| match field {
                    TableField::IndexField(key, value) => {
                        TableField::IndexField(simplify_expr(key), simplify_expr(value))
                    }
                    TableField::NameField(name, value) => {
                        TableField::NameField(name, simplify_expr(value))
                    }
                    TableField::Value(value) => TableField::Value(simplify_expr(value)),
                })
                .collect(),
        ),
        other => other,
    }
}

fn simplify_call(call: CallExpr) -> CallExpr {
    CallExpr {
        func: simplify_expr(call.func),
        args: call.args.into_iter().map(simplify_expr).collect(),
    }
}

fn negate_condition(expr: Expr) -> Expr {
    match expr {
        Expr::Bool(value) => Expr::Bool(!value),
        Expr::UnOp(UnOp::Not, inner) => simplify_expr(*inner),
        other => Expr::UnOp(UnOp::Not, Box::new(other)),
    }
}

fn cache_repeated_trailing_getter_call(cond: &Expr, then_block: &Block) -> Option<Block> {
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

fn cache_shared_negated_getter_calls(block: &Block) -> Block {
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
fn emit_string_content(text: &str, _raw: &[u8], out: &mut String) {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn emit_single(stat: Stat) -> String {
        emit_chunk(&Function {
            params: Vec::new(),
            is_vararg: false,
            body: vec![stat],
        })
    }

    #[test]
    fn flattens_linear_nested_ifs() {
        let source = emit_single(Stat::If {
            cond: Expr::Name("a".to_string()),
            then_block: vec![Stat::If {
                cond: Expr::Name("b".to_string()),
                then_block: vec![Stat::Return(vec![])],
                elseif_clauses: Vec::new(),
                else_block: None,
            }],
            elseif_clauses: Vec::new(),
            else_block: None,
        });

        assert!(source.contains("if a and b then"));
        assert!(!source.contains("if b then"));
    }

    #[test]
    fn inverts_empty_then_branch() {
        let source = emit_single(Stat::If {
            cond: Expr::Name("a".to_string()),
            then_block: Vec::new(),
            elseif_clauses: Vec::new(),
            else_block: Some(vec![Stat::Return(vec![])]),
        });

        assert!(source.contains("if not a then"));
        assert!(!source.contains("else"));
    }

    #[test]
    fn simplifies_true_and_condition() {
        let source = emit_single(Stat::If {
            cond: Expr::BinOp(
                BinOp::And,
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Name("ready".to_string())),
            ),
            then_block: vec![Stat::Return(vec![])],
            elseif_clauses: Vec::new(),
            else_block: None,
        });

        assert!(source.contains("if ready then"));
        assert!(!source.contains("true and"));
    }

    #[test]
    fn hoists_guard_tail_out_of_outer_if() {
        let source = emit_chunk(&Function {
            params: Vec::new(),
            is_vararg: false,
            body: vec![Stat::If {
                cond: Expr::Name("a".to_string()),
                then_block: vec![
                    Stat::If {
                        cond: Expr::Name("b".to_string()),
                        then_block: vec![Stat::Return(vec![])],
                        elseif_clauses: Vec::new(),
                        else_block: None,
                    },
                    Stat::Call(CallExpr {
                        func: Expr::Name("next_step".to_string()),
                        args: Vec::new(),
                    }),
                ],
                elseif_clauses: Vec::new(),
                else_block: None,
            }],
        });

        assert!(source.contains("if a and b then"));
        assert!(source.contains("end\nnext_step()"));
    }

    #[test]
    fn folds_else_if_to_elseif() {
        let source = emit_single(Stat::If {
            cond: Expr::Name("a".to_string()),
            then_block: vec![Stat::Call(CallExpr {
                func: Expr::Name("left".to_string()),
                args: Vec::new(),
            })],
            elseif_clauses: Vec::new(),
            else_block: Some(vec![Stat::If {
                cond: Expr::Name("b".to_string()),
                then_block: vec![Stat::Call(CallExpr {
                    func: Expr::Name("right".to_string()),
                    args: Vec::new(),
                })],
                elseif_clauses: Vec::new(),
                else_block: None,
            }]),
        });

        assert!(source.contains("elseif b then"));
        assert!(!source.contains("else\n  if b then"));
    }

    #[test]
    fn merges_identical_elseif_bodies() {
        let body = vec![Stat::Call(CallExpr {
            func: Expr::Name("apply".to_string()),
            args: Vec::new(),
        })];
        let source = emit_single(Stat::If {
            cond: Expr::Name("left".to_string()),
            then_block: body.clone(),
            elseif_clauses: vec![
                (Expr::Name("right".to_string()), body.clone()),
                (Expr::Name("extra".to_string()), body),
            ],
            else_block: None,
        });

        assert!(source.contains("if left or right or extra then"));
        assert!(!source.contains("elseif"));
    }

    #[test]
    fn caches_repeated_getter_call_inside_if() {
        let buff_call = Expr::FuncCall(Box::new(CallExpr {
            func: Expr::Field(Box::new(Expr::Name("a1".to_string())), "GetBuffByOwner".to_string()),
            args: vec![
                Expr::Number(NumLit::Int(30349)),
                Expr::Number(NumLit::Int(0)),
                Expr::Field(Box::new(Expr::Name("a0".to_string())), "dwID".to_string()),
            ],
        }));
        let source = emit_single(Stat::If {
            cond: Expr::BinOp(
                BinOp::And,
                Box::new(Expr::Name("ready".to_string())),
                Box::new(buff_call.clone()),
            ),
            then_block: vec![Stat::Assign {
                targets: vec![Expr::Name("damage".to_string())],
                values: vec![Expr::Field(Box::new(buff_call), "nStackNum".to_string())],
            }],
            elseif_clauses: Vec::new(),
            else_block: None,
        });

        assert!(source.contains("if ready then"));
        assert!(source.contains("local buff_30349 = a1.GetBuffByOwner(30349, 0, a0.dwID)"));
        assert!(source.contains("if buff_30349 then"));
        assert!(source.contains("damage = buff_30349.nStackNum"));
    }

    #[test]
    fn caches_shared_negated_getter_across_sibling_ifs() {
        let guard_call = Expr::FuncCall(Box::new(CallExpr {
            func: Expr::Field(Box::new(Expr::Name("a1".to_string())), "GetBuffByOwner".to_string()),
            args: vec![
                Expr::Number(NumLit::Int(4706)),
                Expr::Number(NumLit::Int(1)),
                Expr::Field(Box::new(Expr::Name("a0".to_string())), "dwID".to_string()),
            ],
        }));
        let source = emit_chunk(&Function {
            params: Vec::new(),
            is_vararg: false,
            body: vec![
                Stat::If {
                    cond: Expr::BinOp(
                        BinOp::And,
                        Box::new(Expr::Name("left".to_string())),
                        Box::new(Expr::UnOp(UnOp::Not, Box::new(guard_call.clone()))),
                    ),
                    then_block: vec![Stat::Call(CallExpr {
                        func: Expr::Name("first".to_string()),
                        args: Vec::new(),
                    })],
                    elseif_clauses: Vec::new(),
                    else_block: None,
                },
                Stat::If {
                    cond: Expr::BinOp(
                        BinOp::And,
                        Box::new(Expr::Name("right".to_string())),
                        Box::new(Expr::UnOp(UnOp::Not, Box::new(guard_call))),
                    ),
                    then_block: vec![Stat::Call(CallExpr {
                        func: Expr::Name("second".to_string()),
                        args: Vec::new(),
                    })],
                    elseif_clauses: Vec::new(),
                    else_block: None,
                },
            ],
        });

        assert!(source.contains("if left or right then"));
        assert!(source.contains("local buff_4706 = a1.GetBuffByOwner(4706, 1, a0.dwID)"));
        assert!(source.contains("if left and not buff_4706 then"));
        assert!(source.contains("if right and not buff_4706 then"));
    }
}
