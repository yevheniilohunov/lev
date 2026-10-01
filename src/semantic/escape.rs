use super::hir::{HirAllocationKind, HirBlock, HirExpr, HirExprKind, HirProgram, HirStmt};
use super::symbols::LocalId;

pub fn analyze(program: &mut HirProgram) {
    for function in &mut program.functions {
        let mut escaping_locals = Vec::new();

        collect_escaping_locals(&function.body, &mut escaping_locals);

        // Propagate:
        //
        //   let a = new Foo();
        //   let b = a;
        //   return b;
        //
        // from b back to a.
        loop {
            let before = escaping_locals.len();

            collect_escape_aliases(&function.body, &mut escaping_locals);

            if escaping_locals.len() == before {
                break;
            }
        }

        mark_allocations(&mut function.body, &escaping_locals);
    }
}

fn collect_escaping_locals(block: &HirBlock, escaping: &mut Vec<LocalId>) {
    for statement in &block.statements {
        match statement {
            HirStmt::Return { value } => {
                if let Some(value) = value {
                    collect_escaping_expr(value, escaping);
                }
            }

            HirStmt::AssignField { value, .. } => {
                collect_escaping_expr(value, escaping);
            }

            HirStmt::Expr(expr) => {
                collect_escaping_expr(expr, escaping);
            }

            HirStmt::If {
                then_block,
                else_block,
                ..
            } => {
                collect_escaping_locals(then_block, escaping);

                if let Some(else_block) = else_block {
                    collect_escaping_locals(else_block, escaping);
                }
            }

            HirStmt::While { body, .. } => {
                collect_escaping_locals(body, escaping);
            }

            HirStmt::Assign { .. }
            | HirStmt::Let { .. }
            | HirStmt::Const { .. }
            | HirStmt::Break
            | HirStmt::Continue => {}
        }
    }
}

fn collect_escaping_expr(expr: &HirExpr, escaping: &mut Vec<LocalId>) {
    match &expr.kind {
        HirExprKind::Local(local) => {
            add_escaping_local(*local, escaping);
        }

        // A value passed to an ordinary function may escape the current
        // function, so all local values used as arguments are escaping.
        HirExprKind::Call { arguments, .. } => {
            for argument in arguments {
                collect_escaping_expr(argument, escaping);
            }
        }

        // Constructor self is handled separately by the lowering rules.
        // Constructor arguments, however, are ordinary values and may escape.
        HirExprKind::ConstructorCall { arguments, .. } => {
            for argument in arguments {
                collect_escaping_expr(argument, escaping);
            }
        }

        HirExprKind::Binary { left, right, .. } => {
            collect_escaping_expr(left, escaping);
            collect_escaping_expr(right, escaping);
        }

        HirExprKind::Field { receiver, .. } => {
            collect_escaping_expr(receiver, escaping);
        }

        HirExprKind::StructInit { arguments, .. } => {
            for argument in arguments {
                collect_escaping_expr(argument, escaping);
            }
        }

        HirExprKind::Integer(_) | HirExprKind::String(_) | HirExprKind::Bool(_) => {}
    }
}

fn collect_escape_aliases(block: &HirBlock, escaping: &mut Vec<LocalId>) {
    for statement in &block.statements {
        match statement {
            HirStmt::Assign { local, value }
            | HirStmt::Let { local, value }
            | HirStmt::Const { local, value } => {
                if escaping.contains(local) {
                    collect_value_locals(value, escaping);
                }
            }

            HirStmt::If {
                then_block,
                else_block,
                ..
            } => {
                collect_escape_aliases(then_block, escaping);

                if let Some(else_block) = else_block {
                    collect_escape_aliases(else_block, escaping);
                }
            }

            HirStmt::While { body, .. } => {
                collect_escape_aliases(body, escaping);
            }

            HirStmt::AssignField { .. }
            | HirStmt::Return { .. }
            | HirStmt::Expr(_)
            | HirStmt::Break
            | HirStmt::Continue => {}
        }
    }
}

fn collect_value_locals(expr: &HirExpr, escaping: &mut Vec<LocalId>) {
    match &expr.kind {
        HirExprKind::Local(local) => {
            add_escaping_local(*local, escaping);
        }

        HirExprKind::StructInit { arguments, .. } => {
            for argument in arguments {
                collect_value_locals(argument, escaping);
            }
        }

        HirExprKind::Binary { left, right, .. } => {
            collect_value_locals(left, escaping);
            collect_value_locals(right, escaping);
        }

        HirExprKind::Field { receiver, .. } => {
            collect_value_locals(receiver, escaping);
        }

        HirExprKind::Call { arguments, .. } | HirExprKind::ConstructorCall { arguments, .. } => {
            for argument in arguments {
                collect_value_locals(argument, escaping);
            }
        }

        HirExprKind::Integer(_) | HirExprKind::String(_) | HirExprKind::Bool(_) => {}
    }
}

fn mark_allocations(block: &mut HirBlock, escaping_locals: &[LocalId]) {
    for statement in &mut block.statements {
        match statement {
            HirStmt::Assign { local, value }
            | HirStmt::Let { local, value }
            | HirStmt::Const { local, value } => {
                mark_value(
                    value,
                    if escaping_locals.contains(local) {
                        AllocationContext::Escaping
                    } else {
                        AllocationContext::Local
                    },
                    escaping_locals,
                );
            }

            HirStmt::AssignField {
                receiver, value, ..
            } => {
                mark_value(receiver, AllocationContext::Local, escaping_locals);
                mark_value(value, AllocationContext::Escaping, escaping_locals);
            }

            HirStmt::Return { value } => {
                if let Some(value) = value {
                    mark_value(value, AllocationContext::Escaping, escaping_locals);
                }
            }

            HirStmt::Expr(expr) => {
                mark_value(expr, AllocationContext::Local, escaping_locals);
            }

            HirStmt::If {
                condition,
                then_block,
                else_block,
            } => {
                mark_value(condition, AllocationContext::Local, escaping_locals);
                mark_allocations(then_block, escaping_locals);

                if let Some(else_block) = else_block {
                    mark_allocations(else_block, escaping_locals);
                }
            }

            HirStmt::While { condition, body } => {
                mark_value(condition, AllocationContext::Local, escaping_locals);
                mark_allocations(body, escaping_locals);
            }

            HirStmt::Break | HirStmt::Continue => {}
        }
    }
}

#[derive(Clone, Copy)]
enum AllocationContext {
    Local,
    Escaping,
}

fn mark_value(expr: &mut HirExpr, context: AllocationContext, escaping_locals: &[LocalId]) {
    match &mut expr.kind {
        HirExprKind::StructInit {
            allocation,
            arguments,
            ..
        } => {
            *allocation = match context {
                AllocationContext::Local => HirAllocationKind::Stack,
                AllocationContext::Escaping => HirAllocationKind::Heap,
            };

            for argument in arguments {
                mark_value(argument, AllocationContext::Local, escaping_locals);
            }
        }

        HirExprKind::Call { arguments, .. } => {
            for argument in arguments {
                mark_value(argument, AllocationContext::Escaping, escaping_locals);
            }
        }

        HirExprKind::ConstructorCall { arguments, .. } => {
            for argument in arguments {
                mark_value(argument, AllocationContext::Escaping, escaping_locals);
            }
        }

        HirExprKind::Binary { left, right, .. } => {
            mark_value(left, AllocationContext::Local, escaping_locals);
            mark_value(right, AllocationContext::Local, escaping_locals);
        }

        HirExprKind::Field { receiver, .. } => {
            mark_value(receiver, AllocationContext::Local, escaping_locals);
        }

        HirExprKind::Local(local) => {
            // A local which has already been identified as escaping does not
            // itself create a new allocation here. Its original StructInit
            // is handled at its definition.
            let _ = escaping_locals.contains(local);
        }

        HirExprKind::Integer(_) | HirExprKind::String(_) | HirExprKind::Bool(_) => {}
    }
}

fn add_escaping_local(local: LocalId, escaping: &mut Vec<LocalId>) {
    if !escaping.contains(&local) {
        escaping.push(local);
    }
}
