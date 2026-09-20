use crate::{ compiler::error::CompilerError, semantic::{ hir::*, types::Type } };

use super::ir::*;

pub fn lower_to_ir(program: HirProgram) -> Result<IrProgram, Vec<CompilerError>> {
    let structs = program.structs
        .iter()
        .map(|structure| IrStruct {
            id: structure.id,
            name: structure.name.clone(),
            fields: structure.fields
                .iter()
                .map(|field| IrField {
                    name: field.name.clone(),
                    ty: IrType::from(&field.ty),
                })
                .collect(),
        })
        .collect();

    let functions = program.functions.iter().map(lower_function).collect();

    Ok(IrProgram {
        structs,
        functions,
    })
}

fn lower_function(function: &HirFunction) -> IrFunction {
    let parameters = function.params
        .iter()
        .map(|param| IrLocal {
            id: param.local,
            name: param.name.clone(),
            ty: IrType::from(&param.ty),
        })
        .collect();

    let locals = function.locals
        .iter()
        .map(|local| IrLocal {
            id: local.id,
            name: local.name.clone(),
            ty: IrType::from(&local.ty),
        })
        .collect();

    let mut builder = FunctionBuilder::new();

    /*
     * Parameters are definitions of their corresponding locals.
     *
     * They must be emitted before the normal function body so SSA
     * construction has an initial definition for every parameter.
     */
    for parameter in &function.params {
        let destination = builder.new_value();

        builder.emit(IrInstruction::Parameter {
            destination,
            local: parameter.local,
        });
    }

    builder.lower_block(&function.body);
    builder.finish();

    IrFunction {
        id: function.id,
        name: function.name.clone(),
        owner: function.owner,
        parameters,
        locals,
        return_type: IrType::from(&function.return_type),
        entry: BlockId(0),
        blocks: builder.blocks,
    }
}

struct FunctionBuilder {
    next_value: usize,
    blocks: Vec<BasicBlock>,
    current_block: BlockId,
    loop_targets: Vec<LoopTargets>,
}

struct LoopTargets {
    condition: BlockId,
    exit: BlockId,
}

impl FunctionBuilder {
    fn new() -> Self {
        Self {
            next_value: 0,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: Vec::new(),
                terminator: Terminator::Unreachable,
            }],
            current_block: BlockId(0),
            loop_targets: Vec::new(),
        }
    }

    fn new_value(&mut self) -> ValueId {
        let value = ValueId(self.next_value);
        self.next_value += 1;
        value
    }

    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len());

        self.blocks.push(BasicBlock {
            id,
            instructions: Vec::new(),
            terminator: Terminator::Unreachable,
        });

        id
    }

    fn set_current(&mut self, block: BlockId) {
        self.current_block = block;
    }

    fn current(&mut self) -> &mut BasicBlock {
        &mut self.blocks[self.current_block.0]
    }

    fn is_terminated(&self) -> bool {
        !matches!(self.blocks[self.current_block.0].terminator, Terminator::Unreachable)
    }

    fn emit(&mut self, instruction: IrInstruction) {
        if !self.is_terminated() {
            self.current().instructions.push(instruction);
        }
    }

    fn terminate(&mut self, terminator: Terminator) {
        if !self.is_terminated() {
            self.blocks[self.current_block.0].terminator = terminator;
        }
    }

    fn ensure_open_block(&mut self) {
        if self.is_terminated() {
            let block = self.new_block();
            self.set_current(block);
        }
    }

    fn finish(&mut self) {
        if !self.is_terminated() {
            self.terminate(Terminator::Unreachable);
        }
    }

    fn lower_block(&mut self, block: &HirBlock) {
        for statement in &block.statements {
            self.ensure_open_block();
            self.lower_stmt(statement);
        }
    }

    fn lower_stmt(&mut self, statement: &HirStmt) {
        match statement {
            HirStmt::Let { local, value } => {
                if let Some(value) = self.lower_value_for_local(value) {
                    self.emit(IrInstruction::StoreLocal {
                        local: *local,
                        value,
                    });
                }
            }

            HirStmt::Const { local, value } => {
                if let Some(value) = self.lower_value_for_local(value) {
                    self.emit(IrInstruction::StoreLocal {
                        local: *local,
                        value,
                    });
                }
            }

            HirStmt::Assign { local, value } => {
                if let Some(value) = self.lower_value_for_local(value) {
                    self.emit(IrInstruction::StoreLocal {
                        local: *local,
                        value,
                    });
                }
            }

            HirStmt::Return { value } => {
                let value = value.as_ref().and_then(|expr| self.lower_expr(expr));

                self.terminate(Terminator::Return { value });
            }

            HirStmt::Expr(expr) => {
                let _ = self.lower_expr(expr);
            }

            HirStmt::If { condition, then_block, else_block } => {
                self.lower_if(condition, then_block, else_block.as_ref());
            }

            HirStmt::While { condition, body } => {
                self.lower_while(condition, body);
            }

            HirStmt::Break => {
                if let Some(targets) = self.loop_targets.last() {
                    self.terminate(Terminator::Jump(targets.exit));
                }
            }

            HirStmt::Continue => {
                if let Some(targets) = self.loop_targets.last() {
                    self.terminate(Terminator::Jump(targets.condition));
                }
            }
        }
    }

    fn lower_value_for_local(&mut self, expr: &HirExpr) -> Option<ValueId> {
        let value = self.lower_expr(expr)?;

        if let Type::Struct(struct_id) = expr.ty {
            // A struct constructor already creates its own object.
            if matches!(expr.kind, HirExprKind::StructInit { .. }) {
                return Some(value);
            }

            let destination = self.new_value();

            self.emit(IrInstruction::StructCopy {
                destination,
                source: value,
                struct_id,
            });

            Some(destination)
        } else {
            Some(value)
        }
    }

    fn lower_if(
        &mut self,
        condition: &HirExpr,
        then_block: &HirBlock,
        else_block: Option<&HirBlock>
    ) {
        let Some(condition) = self.lower_expr(condition) else {
            return;
        };

        let then_id = self.new_block();
        let else_id = self.new_block();
        let merge_id = self.new_block();

        self.terminate(Terminator::Branch {
            condition,
            then_block: then_id,
            else_block: else_id,
        });

        self.set_current(then_id);
        self.lower_block(then_block);

        if !self.is_terminated() {
            self.terminate(Terminator::Jump(merge_id));
        }

        self.set_current(else_id);

        if let Some(else_block) = else_block {
            self.lower_block(else_block);
        }

        if !self.is_terminated() {
            self.terminate(Terminator::Jump(merge_id));
        }

        self.set_current(merge_id);
    }

    fn lower_while(&mut self, condition: &HirExpr, body: &HirBlock) {
        let condition_id = self.new_block();
        let body_id = self.new_block();
        let exit_id = self.new_block();

        self.terminate(Terminator::Jump(condition_id));

        self.set_current(condition_id);

        let Some(condition_value) = self.lower_expr(condition) else {
            self.terminate(Terminator::Jump(exit_id));
            self.set_current(exit_id);
            return;
        };

        self.terminate(Terminator::Branch {
            condition: condition_value,
            then_block: body_id,
            else_block: exit_id,
        });

        self.set_current(body_id);

        self.loop_targets.push(LoopTargets {
            condition: condition_id,
            exit: exit_id,
        });

        self.lower_block(body);

        self.loop_targets.pop();

        if !self.is_terminated() {
            self.terminate(Terminator::Jump(condition_id));
        }

        self.set_current(exit_id);
    }

    fn lower_expr(&mut self, expr: &HirExpr) -> Option<ValueId> {
        match &expr.kind {
            HirExprKind::Integer(value) => {
                let destination = self.new_value();

                self.emit(IrInstruction::ConstInt {
                    destination,
                    value: *value,
                });

                Some(destination)
            }

            HirExprKind::String(value) => {
                let destination = self.new_value();

                self.emit(IrInstruction::ConstString {
                    destination,
                    value: value.clone(),
                });

                Some(destination)
            }

            HirExprKind::Bool(value) => {
                let destination = self.new_value();

                self.emit(IrInstruction::ConstBool {
                    destination,
                    value: *value,
                });

                Some(destination)
            }

            HirExprKind::Local(local) => {
                let destination = self.new_value();

                self.emit(IrInstruction::LoadLocal {
                    destination,
                    local: *local,
                });

                Some(destination)
            }

            HirExprKind::Binary { left, op, right } => {
                let left = self.lower_expr(left)?;
                let right = self.lower_expr(right)?;

                let destination = self.new_value();

                let op = match op {
                    HirBinaryOp::Add => IrBinaryOp::Add,
                    HirBinaryOp::Subtract => IrBinaryOp::Subtract,
                    HirBinaryOp::Multiply => IrBinaryOp::Multiply,
                    HirBinaryOp::Divide => IrBinaryOp::Divide,
                    HirBinaryOp::Equal => IrBinaryOp::Equal,
                };

                self.emit(IrInstruction::Binary {
                    destination,
                    op,
                    left,
                    right,
                });

                Some(destination)
            }

            HirExprKind::Call { function, arguments } => {
                let mut values = Vec::with_capacity(arguments.len());

                for argument in arguments {
                    values.push(self.lower_expr(argument)?);
                }

                let destination = match &expr.ty {
                    Type::Void => None,
                    _ => Some(self.new_value()),
                };

                self.emit(IrInstruction::Call {
                    destination,
                    function: *function,
                    arguments: values,
                });

                destination
            }
            HirExprKind::Field { receiver, field } => {
                let receiver_value = self.lower_expr(receiver)?;
                let destination = self.new_value();

                self.emit(IrInstruction::LoadField {
                    destination,
                    receiver: receiver_value,
                    field: *field,
                });

                Some(destination)
            }
            HirExprKind::StructInit { struct_id, arguments } => {
                let destination = self.new_value();

                self.emit(IrInstruction::AllocStruct {
                    destination,
                    struct_id: *struct_id,
                });

                for (field, argument) in arguments.iter().enumerate() {
                    let value = self.lower_expr(argument)?;

                    self.emit(IrInstruction::StoreField {
                        receiver: destination,
                        field,
                        value,
                    });
                }

                Some(destination)
            }
        }
    }
}
