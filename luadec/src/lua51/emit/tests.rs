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
