use crate::lua51::ast::*;
use super::cache::{cache_repeated_trailing_getter_call, cache_shared_negated_getter_calls};

pub(super) fn normalize_block(block: &Block) -> Block {
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

pub(super) fn simplify_expr(expr: Expr) -> Expr {
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

pub(super) fn simplify_call(call: CallExpr) -> CallExpr {
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
