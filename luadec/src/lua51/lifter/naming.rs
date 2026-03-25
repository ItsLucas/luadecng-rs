use crate::lua51::ast::*;
use crate::lua51::opcodes::OpCode;
use super::Lifter;

fn normalize_call_name(name: &str) -> String {
    let snake = camel_to_snake(name);
    snake
        .strip_prefix("get_")
        .or_else(|| snake.strip_prefix("is_"))
        .map(ToOwned::to_owned)
        .unwrap_or(snake)
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

fn is_upper_ident(s: &str) -> bool {
    !s.is_empty()
        && s
            .chars()
            .all(|c| c == '_' || c.is_ascii_uppercase() || c.is_ascii_digit())
}

impl<'a> Lifter<'a> {
    pub(super) fn local_name(&self, reg: u32, pc: usize) -> String {
        // Try debug info: locals are ordered by register assignment
        // In standard Lua 5.1 bytecode, the i-th local in the array corresponds
        // to register i (for the scope range start_pc..end_pc)
        for (i, local) in self.chunk.locals.iter().enumerate() {
            if i == reg as usize
                && local.start_pc as usize <= pc + 1
                && pc < local.end_pc as usize
            {
                if !local.name.is_empty() && !local.name.starts_with('(') {
                    return local.name.clone();
                }
            }
        }
        // Also scan all locals for any that match this register
        for local in &self.chunk.locals {
            if local.start_pc as usize <= pc + 1 && pc < local.end_pc as usize {
                // Use locals array index as register mapping
            }
        }
        // Fall back to matching by position in locals array for params
        let r = reg as usize;
        if r < self.chunk.locals.len() {
            let name = &self.chunk.locals[r].name;
            if !name.is_empty() && !name.starts_with('(') {
                return name.clone();
            }
        }
        self.make_local_name(reg)
    }

    pub(super) fn make_local_name(&self, reg: u32) -> String {
        let current_expr = self.regs.get(reg as usize).and_then(|e| e.as_ref());
        self.make_local_name_from_known_expr(reg, current_expr)
    }

    pub(super) fn make_local_name_for_expr(&self, reg: u32, expr: &Expr) -> String {
        self.make_local_name_from_known_expr(reg, Some(expr))
    }

    fn make_local_name_from_known_expr(&self, reg: u32, current_expr: Option<&Expr>) -> String {
        if reg < self.num_params {
            if self.has_debug_info {
                return self.local_name(reg, 0);
            }
            return format!("a{}", reg);
        }
        if let Some(name) = self.infer_accumulator_name(reg, current_expr) {
            return self.uniquify_local_name(name);
        }
        if let Some(fields) = self.pending_tables.get(&reg) {
            if !fields.is_empty() {
                if let Some(name) = self.infer_table_local_name(fields) {
                    return self.uniquify_local_name(name);
                }
            }
        }
        // For stripped bytecode, try to infer a meaningful name from context.
        // Look at what was last stored in this register.
        if let Some(expr) = current_expr {
            match expr {
                Expr::Table(fields) => {
                    if let Some(name) = self.infer_table_local_name(fields) {
                        return self.uniquify_local_name(name);
                    }
                }
                // If it's a global function call, name after the function
                Expr::FuncCall(call) => {
                    if let Some(name) = self.infer_call_local_name(call) {
                        return self.uniquify_local_name(name);
                    }
                    if let Expr::Global(name) = &call.func {
                        let short = normalize_call_name(name);
                        if short.len() <= 20 {
                            return self.uniquify_local_name(short);
                        }
                    }
                    // Method call: use method name
                    if let Expr::Field(_, method) = &call.func {
                        return self.uniquify_local_name(normalize_call_name(method));
                    }
                }
                _ => {}
            }
        }
        format!("l_{}", reg)
    }

    fn infer_accumulator_name(&self, reg: u32, expr: Option<&Expr>) -> Option<String> {
        if !self.accumulator_regs.contains(&reg) || !self.is_returned_reg(reg) {
            return None;
        }

        match expr {
            Some(Expr::Number(_)) | None => Some("result".to_string()),
            _ => None,
        }
    }

    fn infer_call_local_name(&self, call: &CallExpr) -> Option<String> {
        let method = match &call.func {
            Expr::Field(_, method) => method.as_str(),
            Expr::Global(name) => name.as_str(),
            _ => return None,
        };

        let first_int_arg = match call.args.first() {
            Some(Expr::Number(NumLit::Int(value))) => Some(*value),
            Some(Expr::Number(NumLit::Float(value))) if value.fract() == 0.0 => Some(*value as i64),
            _ => None,
        };

        match method {
            "IsHaveBuff" => Some(match first_int_arg {
                Some(id) => format!("has_buff_{}", id),
                None => "has_buff".to_string(),
            }),
            "GetBuff" | "GetBuffByOwner" => Some(match first_int_arg {
                Some(id) => format!("buff_{}", id),
                None => "buff".to_string(),
            }),
            "GetSkillLevel" => first_int_arg.map(|id| format!("skill_{}", id)),
            "GetEndTime" => Some("end_time".to_string()),
            "GetLogicFrameCount" => Some("logic_frame_count".to_string()),
            _ => None,
        }
    }

    fn is_returned_reg(&self, reg: u32) -> bool {
        self.cfg.instructions.iter().any(|inst| {
            inst.op == OpCode::Return && inst.a == reg && inst.b() == 2
        })
    }

    fn uniquify_local_name(&self, base: String) -> String {
        if !self.local_names.values().any(|name| name == &base) {
            return base;
        }

        let mut suffix = 1;
        loop {
            let candidate = format!("{}_{}", base, suffix);
            if !self.local_names.values().any(|name| name == &candidate) {
                return candidate;
            }
            suffix += 1;
        }
    }

    fn infer_table_local_name(&self, fields: &[TableField]) -> Option<String> {
        if fields.is_empty() {
            return None;
        }

        if fields.iter().all(|field| matches!(field, TableField::IndexField(_, Expr::Bool(true)))) {
            if fields.iter().any(|field| {
                matches!(field, TableField::IndexField(key, _) if self.expr_mentions_field(key, "ENUM"))
            }) {
                return Some("enum_lookup".to_string());
            }
            return Some("lookup".to_string());
        }

        if fields.iter().all(|field| matches!(field, TableField::NameField(_, Expr::Number(_)))) {
            let keys: Vec<&str> = fields
                .iter()
                .filter_map(|field| match field {
                    TableField::NameField(name, _) => Some(name.as_str()),
                    _ => None,
                })
                .collect();
            if keys.iter().any(|name| name.contains("NOT_")) {
                return Some("penalties".to_string());
            }
            if keys.iter().all(|name| is_upper_ident(name)) {
                return Some("modifiers".to_string());
            }
        }

        None
    }

    fn expr_mentions_field(&self, expr: &Expr, field_name: &str) -> bool {
        match expr {
            Expr::Field(table, field) => field == field_name || self.expr_mentions_field(table, field_name),
            Expr::Index(table, key) => {
                self.expr_mentions_field(table, field_name)
                    || self.expr_mentions_field(key, field_name)
            }
            Expr::MethodCall(call) | Expr::FuncCall(call) => {
                self.expr_mentions_field(&call.func, field_name)
                    || call.args.iter().any(|arg| self.expr_mentions_field(arg, field_name))
            }
            Expr::BinOp(_, lhs, rhs) => {
                self.expr_mentions_field(lhs, field_name)
                    || self.expr_mentions_field(rhs, field_name)
            }
            Expr::UnOp(_, inner) => self.expr_mentions_field(inner, field_name),
            Expr::Table(fields) => fields.iter().any(|field| match field {
                TableField::IndexField(key, value) => {
                    self.expr_mentions_field(key, field_name)
                        || self.expr_mentions_field(value, field_name)
                }
                TableField::NameField(_, value) | TableField::Value(value) => {
                    self.expr_mentions_field(value, field_name)
                }
            }),
            _ => false,
        }
    }
}
