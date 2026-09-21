use std::collections::HashSet;

use crate::compiler::error::CompilerError;
use crate::compiler::source::SourceFile;
use crate::compiler::{ source::Span };

use crate::parser::ast::*;
use crate::semantic::modifiers::Visibility;

use super::{ hir::*, scope::Scope, symbols::*, types::Type };

pub fn analyze(program: Program, source: SourceFile) -> Result<HirProgram, Vec<CompilerError>> {
    let mut analyzer = Analyzer::new(&source);

    analyzer.collect_struct_names(&program);
    analyzer.resolve_struct_bases(&program);
    analyzer.collect_function_signatures(&program);
    analyzer.collect_struct_fields(&program);

    if !analyzer.errors.is_empty() {
        return Err(analyzer.errors);
    }

    let hir = analyzer.analyze_program(program);

    if analyzer.errors.is_empty() {
        Ok(hir)
    } else {
        Err(analyzer.errors)
    }
}

struct Analyzer<'a> {
    source: &'a SourceFile,
    symbols: SymbolTable,
    errors: Vec<CompilerError>,
    current_owner: Option<StructId>,
}

impl<'a> Analyzer<'a> {
    fn new(source: &'a SourceFile) -> Self {
        Self {
            source,
            symbols: SymbolTable::new(),
            errors: Vec::new(),
            current_owner: None,
        }
    }

    fn error_at(&self, message: impl Into<String>, span: Span) -> CompilerError {
        CompilerError::new(&self.source.text, message, span.to_source_span())
    }

    // ---------------------------------------------------------------------
    // Symbol collection
    // ---------------------------------------------------------------------

    fn collect_struct_names(&mut self, program: &Program) {
        for structure in &program.structs {
            if let Err(error) = self.symbols.add_struct(structure.name.clone()) {
                self.errors.push(self.error_at(error, structure.span));
            }
        }
    }

    fn collect_function_signatures(&mut self, program: &Program) {
        for function in &program.functions {
            self.collect_function_signature(function, None);
        }

        // Register methods declared inside structs.
        for struct_decl in &program.structs {
            let Some(struct_id) = self.symbols.find_struct(&struct_decl.name) else {
                continue;
            };
            for method in &struct_decl.methods {
                self.collect_function_signature(method, Some(struct_id));
            }
        }
    }

    fn collect_function_signature(&mut self, function: &FunctionDecl, owner: Option<StructId>) {
        let mut parameters = Vec::new();
        let mut seen_parameters = HashSet::new();
        for parameter in &function.params {
            if !seen_parameters.insert(parameter.name.clone()) {
                self.errors.push(
                    self.error_at(
                        format!("parameter '{}' is duplicated", parameter.name),
                        parameter.span
                    )
                );
                continue;
            }
            if let Some(ty) = self.resolve_type(&parameter.ty, parameter.span) {
                parameters.push(ParameterSymbol { name: parameter.name.clone(), ty });
            }
        }
        let return_type = self
            .resolve_type(&function.return_type, function.span)
            .unwrap_or(Type::Void);
        let result = match owner {
            Some(struct_id) =>
                self.symbols.add_method(struct_id, function.name.clone(), parameters, return_type),
            None => self.symbols.add_function(function.name.clone(), parameters, return_type),
        };
        if let Err(error) = result {
            self.errors.push(self.error_at(error, function.span));
        }
    }

    fn collect_struct_fields(&mut self, program: &Program) {
        for structure in &program.structs {
            let Some(struct_id) = self.symbols.find_struct(&structure.name) else {
                continue;
            };

            let mut fields = Vec::new();

            for field in &structure.fields {
                let ty = self.resolve_type(&field.ty, field.span);

                if fields.iter().any(|existing: &FieldSymbol| existing.name == field.name) {
                    self.errors.push(
                        self.error_at(
                            format!(
                                "field '{}' is already declared in struct '{}'",
                                field.name,
                                structure.name
                            ),
                            field.span
                        )
                    );
                    continue;
                }

                if let Some(ty) = ty {
                    fields.push(FieldSymbol {
                        name: field.name.clone(),
                        ty,
                        visibility: field.visibility,
                        owner: struct_id,
                    });
                }
            }

            self.symbols.set_struct_fields(struct_id, fields);
        }
    }

    // ---------------------------------------------------------------------
    // Type resolution
    // ---------------------------------------------------------------------

    fn resolve_type(&mut self, ty: &TypeName, span: Span) -> Option<Type> {
        if let Some(type_) = Type::from_ast_builtin(ty) {
            return Some(type_);
        }

        let TypeName::Named(name) = ty else {
            return None;
        };

        if let Some(struct_id) = self.symbols.find_struct(name) {
            return Some(Type::Struct(struct_id));
        }

        self.errors.push(self.error_at(format!("unknown type '{}'", name), span));

        None
    }

    // ---------------------------------------------------------------------
    // Program
    // ---------------------------------------------------------------------

    fn analyze_program(&mut self, program: Program) -> HirProgram {
        let mut hir_structs = Vec::new();
        let mut hir_functions = Vec::new();

        for struct_decl in &program.structs {
            let Some(struct_id) = self.symbols.find_struct(&struct_decl.name) else {
                continue;
            };

            let struct_symbol = self.symbols.struct_symbol(struct_id);

            let fields = struct_symbol.fields
                .iter()
                .map(|field| HirField {
                    name: field.name.clone(),
                    ty: field.ty.clone(),
                })
                .collect();

            hir_structs.push(HirStruct {
                id: struct_id,
                name: struct_symbol.name.clone(),
                base: struct_symbol.base,
                fields,
            });

            for method in &struct_decl.methods {
                let Some(function_id) = self.symbols.find_method(struct_id, &method.name) else {
                    continue;
                };

                let hir_function = self.analyze_function(method, function_id);
                hir_functions.push(hir_function);
            }
        }

        for function in &program.functions {
            let Some(function_id) = self.symbols.find_function(&function.name) else {
                continue;
            };

            let hir_function = self.analyze_function(function, function_id);
            hir_functions.push(hir_function);
        }

        HirProgram {
            structs: hir_structs,
            functions: hir_functions,
        }
    }

    // ---------------------------------------------------------------------
    // Functions
    // ---------------------------------------------------------------------
    fn analyze_function(
        &mut self,
        function: &FunctionDecl,
        function_id: FunctionId
    ) -> HirFunction {
        let symbol = self.symbols.function_symbol(function_id).clone();

        self.current_owner = symbol.owner;

        let mut scope = Scope::new();
        let mut params = Vec::new();

        if let Some(owner) = symbol.owner {
            let receiver_name = "self".to_string();
            let receiver_type = Type::Struct(owner);

            match scope.declare(receiver_name.clone(), receiver_type.clone(), true) {
                Ok(local) => {
                    params.push(HirParam {
                        local,
                        name: receiver_name,
                        ty: receiver_type,
                    });
                }
                Err(error) => {
                    self.errors.push(self.error_at(error, function.span));
                }
            }
        }

        for parameter in &symbol.parameters {
            match scope.declare(parameter.name.clone(), parameter.ty.clone(), true) {
                Ok(local) => {
                    params.push(HirParam {
                        local,
                        name: parameter.name.clone(),
                        ty: parameter.ty.clone(),
                    });
                }
                Err(error) => {
                    self.errors.push(self.error_at(error, function.span));
                }
            }
        }

        let body = match self.analyze_block(&function.body, &mut scope, &symbol.return_type, 0) {
            Ok(body) => body,

            Err(errors) => {
                self.errors.extend(errors);

                HirBlock {
                    statements: Vec::new(),
                }
            }
        };

        let locals = scope
            .locals()
            .iter()
            .filter(|(id, _, _, _)| { !params.iter().any(|param| param.local == *id) })
            .map(|(id, name, ty, _)| HirLocal {
                id: *id,
                name: name.clone(),
                ty: ty.clone(),
            })
            .collect();

        self.current_owner = None;

        HirFunction {
            id: function_id,
            name: symbol.name,
            owner: symbol.owner,
            params,
            locals,
            return_type: symbol.return_type,
            body,
        }
    }

    fn can_access_field(&self, field: &FieldSymbol) -> bool {
        match field.visibility {
            Visibility::Public => true,

            Visibility::Private => { self.current_owner == Some(field.owner) }

            Visibility::Protected => {
                let Some(current_owner) = self.current_owner else {
                    return false;
                };

                self.is_same_or_derived(current_owner, field.owner)
            }
        }
    }

    fn is_same_or_derived(&self, current: StructId, target: StructId) -> bool {
        let mut current = Some(current);

        while let Some(struct_id) = current {
            if struct_id == target {
                return true;
            }

            current = self.symbols.struct_base(struct_id);
        }

        false
    }

    // ---------------------------------------------------------------------
    // Blocks
    // ---------------------------------------------------------------------

    fn analyze_block(
        &mut self,
        statement: &Stmt,
        scope: &mut Scope,
        return_type: &Type,
        loop_depth: usize
    ) -> Result<HirBlock, Vec<CompilerError>> {
        let Stmt::Block { statements, .. } = statement else {
            return Err(vec![CompilerError::internal("internal error: expected block statement")]);
        };

        scope.push_scope();

        let mut hir_stmnt = Vec::new();
        let mut errors = Vec::new();

        for statement in statements {
            match self.analyze_statement(statement, scope, return_type, loop_depth) {
                Ok(statement) => hir_stmnt.push(statement),

                Err(mut statement_errors) => {
                    errors.append(&mut statement_errors);
                }
            }
        }

        scope.pop_scope();

        if errors.is_empty() {
            Ok(HirBlock {
                statements: hir_stmnt,
            })
        } else {
            Err(errors)
        }
    }

    // ---------------------------------------------------------------------
    // Statements
    // ---------------------------------------------------------------------

    fn analyze_statement(
        &mut self,
        statement: &Stmt,
        scope: &mut Scope,
        return_type: &Type,
        loop_depth: usize
    ) -> Result<HirStmt, Vec<CompilerError>> {
        match statement {
            Stmt::Assign { name, value, span } => {
                let local = match scope.lookup(name) {
                    Some(local) => local,

                    None => {
                        return Err(
                            vec![self.error_at(format!("unknown variable '{}'", name), *span)]
                        );
                    }
                };

                if !scope.is_mutable(local) {
                    return Err(
                        vec![
                            self.error_at(
                                format!("cannot assign to immutable variable '{}'", name),
                                *span
                            )
                        ]
                    );
                }

                let expected = match scope.type_of(local) {
                    Some(ty) => ty.clone(),

                    None => {
                        return Err(
                            vec![self.error_at("internal error: missing type for local", *span)]
                        );
                    }
                };

                let value = self.analyze_expr(value, scope);

                if value.ty != expected {
                    return Err(
                        vec![
                            self.error_at(
                                format!(
                                    "cannot assign {:?} to variable '{}' of type {:?}",
                                    value.ty,
                                    name,
                                    expected
                                ),
                                *span
                            )
                        ]
                    );
                }

                Ok(HirStmt::Assign { local, value })
            }

            Stmt::Block { .. } =>
                Err(
                    vec![
                        CompilerError::internal("internal error: unexpected nested block statement")
                    ]
                ),

            Stmt::Let { name, ty, value, span } => {
                let declared_type = match self.resolve_type(ty, *span) {
                    Some(ty) => ty,

                    None => {
                        return Err(
                            vec![
                                self.error_at(
                                    "cannot determine type of variable declaration",
                                    *span
                                )
                            ]
                        );
                    }
                };

                let value = self.analyze_expr(value, scope);

                if value.ty != declared_type {
                    return Err(
                        vec![
                            self.error_at(
                                format!(
                                    "cannot initialize variable '{}' of type {:?} with value of type {:?}",
                                    name,
                                    declared_type,
                                    value.ty
                                ),
                                *span
                            )
                        ]
                    );
                }

                let local = match scope.declare(name.clone(), declared_type, true) {
                    Ok(local) => local,

                    Err(error) => {
                        return Err(vec![self.error_at(error, *span)]);
                    }
                };

                Ok(HirStmt::Let { local, value })
            }

            Stmt::Return { value, span } => {
                match (return_type, value) {
                    (Type::Void, None) => { Ok(HirStmt::Return { value: None }) }

                    (Type::Void, Some(expression)) => {
                        let value = self.analyze_expr(expression, scope);

                        Err(
                            vec![
                                self.error_at(
                                    format!(
                                        "void function cannot return a value of type {:?}",
                                        value.ty
                                    ),
                                    *span
                                )
                            ]
                        )
                    }

                    (expected, None) => {
                        Err(
                            vec![
                                self.error_at(
                                    format!("function must return a value of type {:?}", expected),
                                    *span
                                )
                            ]
                        )
                    }

                    (expected, Some(expression)) => {
                        let value = self.analyze_expr(expression, scope);

                        if value.ty != *expected {
                            return Err(
                                vec![
                                    self.error_at(
                                        format!(
                                            "cannot return value of type {:?} from function returning {:?}",
                                            value.ty,
                                            expected
                                        ),
                                        *span
                                    )
                                ]
                            );
                        }

                        Ok(HirStmt::Return {
                            value: Some(value),
                        })
                    }
                }
            }

            Stmt::Expr { expr, .. } => {
                let expr = self.analyze_expr(expr, scope);

                Ok(HirStmt::Expr(expr))
            }

            Stmt::If { condition, then_block, else_block, span } => {
                let condition = self.analyze_expr(condition, scope);

                if condition.ty != Type::Bool {
                    return Err(
                        vec![
                            self.error_at(
                                format!("if condition must be bool, found {:?}", condition.ty),
                                *span
                            )
                        ]
                    );
                }

                let then_block = match
                    self.analyze_block(then_block, scope, return_type, loop_depth)
                {
                    Ok(block) => block,

                    Err(errors) => {
                        return Err(errors);
                    }
                };

                let else_block = match else_block {
                    Some(block) => Some(self.analyze_block(block, scope, return_type, loop_depth)?),

                    None => None,
                };

                Ok(HirStmt::If {
                    condition,
                    then_block,
                    else_block,
                })
            }

            Stmt::While { condition, body, span } => {
                let condition = self.analyze_expr(condition, scope);

                if condition.ty != Type::Bool {
                    return Err(
                        vec![
                            self.error_at(
                                format!("while condition must be bool, found {:?}", condition.ty),
                                *span
                            )
                        ]
                    );
                }

                let body = self.analyze_block(body, scope, return_type, loop_depth + 1)?;

                Ok(HirStmt::While {
                    condition,
                    body,
                })
            }

            Stmt::Break { span } => {
                if loop_depth == 0 {
                    return Err(vec![self.error_at("'break' is only valid inside a loop", *span)]);
                }

                Ok(HirStmt::Break)
            }

            Stmt::Continue { span } => {
                if loop_depth == 0 {
                    return Err(
                        vec![self.error_at("'continue' is only valid inside a loop", *span)]
                    );
                }

                Ok(HirStmt::Continue)
            }

            Stmt::Const { name, ty, value, span } => {
                let declared_type = match self.resolve_type(ty, *span) {
                    Some(ty) => ty,

                    None => {
                        return Err(
                            vec![
                                self.error_at(
                                    "cannot determine type of variable declaration",
                                    *span
                                )
                            ]
                        );
                    }
                };

                let value = self.analyze_expr(value, scope);

                if value.ty != declared_type {
                    return Err(
                        vec![
                            self.error_at(
                                format!(
                                    "cannot initialize variable '{}' of type {:?} with value of type {:?}",
                                    name,
                                    declared_type,
                                    value.ty
                                ),
                                *span
                            )
                        ]
                    );
                }

                let local = match scope.declare(name.clone(), declared_type, false) {
                    Ok(local) => local,

                    Err(error) => {
                        return Err(vec![self.error_at(error, *span)]);
                    }
                };

                Ok(HirStmt::Const { local, value })
            }
        }
    }

    // ---------------------------------------------------------------------
    // Expressions
    // ---------------------------------------------------------------------

    fn analyze_expr(&mut self, expression: &Expr, scope: &Scope) -> HirExpr {
        match expression {
            Expr::Integer { value, span } =>
                HirExpr {
                    kind: HirExprKind::Integer(*value),
                    ty: Type::Int,
                    span: *span,
                },

            Expr::String { value, span } =>
                HirExpr {
                    kind: HirExprKind::String(value.clone()),
                    ty: Type::String,
                    span: *span,
                },

            Expr::Bool { value, span } =>
                HirExpr {
                    kind: HirExprKind::Bool(*value),
                    ty: Type::Bool,
                    span: *span,
                },

            Expr::Identifier { name, span } => {
                match scope.lookup(name) {
                    Some(local) => {
                        let ty = match scope.type_of(local) {
                            Some(ty) => ty.clone(),

                            None => {
                                self.errors.push(
                                    self.error_at("internal error: missing type for local", *span)
                                );

                                Type::Int
                            }
                        };

                        HirExpr {
                            kind: HirExprKind::Local(local),
                            ty,
                            span: *span,
                        }
                    }

                    None => {
                        self.errors.push(
                            self.error_at(format!("unknown variable '{}'", name), *span)
                        );

                        HirExpr {
                            kind: HirExprKind::Integer(0),
                            ty: Type::Int,
                            span: *span,
                        }
                    }
                }
            }

            Expr::Binary { op, left, right, span } => {
                let left = self.analyze_expr(left, scope);
                let right = self.analyze_expr(right, scope);

                match op {
                    BinaryOp::Add | BinaryOp::Subtract | BinaryOp::Multiply | BinaryOp::Divide => {
                        if left.ty != Type::Int || right.ty != Type::Int {
                            self.errors.push(
                                self.error_at(
                                    format!(
                                        "arithmetic operator requires int operands, found {:?} and {:?}",
                                        left.ty,
                                        right.ty
                                    ),
                                    *span
                                )
                            );

                            return HirExpr {
                                kind: HirExprKind::Integer(0),
                                ty: Type::Int,
                                span: *span,
                            };
                        }

                        let op = match op {
                            BinaryOp::Add => HirBinaryOp::Add,
                            BinaryOp::Subtract => HirBinaryOp::Subtract,
                            BinaryOp::Multiply => HirBinaryOp::Multiply,
                            BinaryOp::Divide => HirBinaryOp::Divide,
                            BinaryOp::Equal => unreachable!(),
                        };

                        HirExpr {
                            kind: HirExprKind::Binary {
                                left: Box::new(left),
                                op,
                                right: Box::new(right),
                            },
                            ty: Type::Int,
                            span: *span,
                        }
                    }

                    BinaryOp::Equal => {
                        if left.ty != right.ty {
                            self.errors.push(
                                self.error_at(
                                    format!(
                                        "cannot compare values of different types: {:?} and {:?}",
                                        left.ty,
                                        right.ty
                                    ),
                                    *span
                                )
                            );

                            return HirExpr {
                                kind: HirExprKind::Bool(false),
                                ty: Type::Bool,
                                span: *span,
                            };
                        }

                        HirExpr {
                            kind: HirExprKind::Binary {
                                left: Box::new(left),
                                op: HirBinaryOp::Equal,
                                right: Box::new(right),
                            },
                            ty: Type::Bool,
                            span: *span,
                        }
                    }
                }
            }

            Expr::Call { receiver, name, arguments, span } => {
                if let Some(receiver_expression) = receiver {
                    let analyzed_receiver = self.analyze_expr(receiver_expression, scope);

                    let Type::Struct(struct_id) = analyzed_receiver.ty.clone() else {
                        self.errors.push(
                            self.error_at(
                                format!(
                                    "cannot call method '{}' on value of type {:?}",
                                    name,
                                    analyzed_receiver.ty
                                ),
                                *span
                            )
                        );

                        return HirExpr {
                            kind: HirExprKind::Integer(0),
                            ty: Type::Int,
                            span: *span,
                        };
                    };

                    let Some(method_id) = self.symbols.find_method(struct_id, name) else {
                        self.errors.push(
                            self.error_at(
                                format!(
                                    "struct '{}' has no method '{}'",
                                    self.symbols.struct_symbol(struct_id).name,
                                    name
                                ),
                                *span
                            )
                        );

                        return HirExpr {
                            kind: HirExprKind::Integer(0),
                            ty: Type::Int,
                            span: *span,
                        };
                    };

                    let method = self.symbols.function_symbol(method_id).clone();

                    if arguments.len() != method.parameters.len() {
                        self.errors.push(
                            self.error_at(
                                format!(
                                    "method '{}.{}' expects {} argument(s), found {}",
                                    self.symbols.struct_symbol(struct_id).name,
                                    name,
                                    method.parameters.len(),
                                    arguments.len()
                                ),
                                *span
                            )
                        );
                    }

                    let mut analyzed_arguments = Vec::with_capacity(arguments.len() + 1);

                    // The receiver is passed as the first argument.
                    analyzed_arguments.push(analyzed_receiver);

                    for (index, argument) in arguments.iter().enumerate() {
                        let value = self.analyze_expr(argument, scope);

                        if let Some(parameter) = method.parameters.get(index) {
                            if value.ty != parameter.ty {
                                self.errors.push(
                                    self.error_at(
                                        format!(
                                            "argument {} of method '{}.{}' has type {:?}, expected {:?}",
                                            index + 1,
                                            self.symbols.struct_symbol(struct_id).name,
                                            name,
                                            value.ty,
                                            parameter.ty
                                        ),
                                        value.span
                                    )
                                );
                            }
                        }

                        analyzed_arguments.push(value);
                    }

                    HirExpr {
                        kind: HirExprKind::Call {
                            function: method_id,
                            arguments: analyzed_arguments,
                        },
                        ty: method.return_type,
                        span: *span,
                    }
                } else {
                    // A call whose name is a struct name is a struct constructor.
                    if let Some(struct_id) = self.symbols.find_struct(name) {
                        let structure = self.symbols.struct_symbol(struct_id).clone();

                        if arguments.len() != structure.fields.len() {
                            self.errors.push(
                                self.error_at(
                                    format!(
                                        "constructor '{}' expects {} argument(s), found {}",
                                        name,
                                        structure.fields.len(),
                                        arguments.len()
                                    ),
                                    *span
                                )
                            );
                        }

                        let mut analyzed_arguments = Vec::with_capacity(arguments.len());

                        for (index, argument) in arguments.iter().enumerate() {
                            let value = self.analyze_expr(argument, scope);

                            if let Some(field) = structure.fields.get(index) {
                                if value.ty != field.ty {
                                    self.errors.push(
                                        self.error_at(
                                            format!(
                                                "argument {} of constructor '{}' has type {:?}, expected {:?}",
                                                index + 1,
                                                name,
                                                value.ty,
                                                field.ty
                                            ),
                                            value.span
                                        )
                                    );
                                }
                            }

                            analyzed_arguments.push(value);
                        }

                        return HirExpr {
                            kind: HirExprKind::StructInit {
                                struct_id,
                                arguments: analyzed_arguments,
                            },
                            ty: Type::Struct(struct_id),
                            span: *span,
                        };
                    }

                    let Some(function_id) = self.symbols.find_function(name) else {
                        self.errors.push(
                            self.error_at(format!("unknown function '{}'", name), *span)
                        );

                        return HirExpr {
                            kind: HirExprKind::Integer(0),
                            ty: Type::Int,
                            span: *span,
                        };
                    };

                    let function = self.symbols.function_symbol(function_id).clone();

                    if arguments.len() != function.parameters.len() {
                        self.errors.push(
                            self.error_at(
                                format!(
                                    "function '{}' expects {} argument(s), found {}",
                                    name,
                                    function.parameters.len(),
                                    arguments.len()
                                ),
                                *span
                            )
                        );
                    }

                    let mut analyzed_arguments = Vec::with_capacity(arguments.len());

                    for (index, argument) in arguments.iter().enumerate() {
                        let value = self.analyze_expr(argument, scope);

                        if let Some(parameter) = function.parameters.get(index) {
                            if value.ty != parameter.ty {
                                self.errors.push(
                                    self.error_at(
                                        format!(
                                            "argument {} of '{}' has type {:?}, expected {:?}",
                                            index + 1,
                                            name,
                                            value.ty,
                                            parameter.ty
                                        ),
                                        value.span
                                    )
                                );
                            }
                        }

                        analyzed_arguments.push(value);
                    }

                    HirExpr {
                        kind: HirExprKind::Call {
                            function: function_id,
                            arguments: analyzed_arguments,
                        },
                        ty: function.return_type,
                        span: *span,
                    }
                }
            }
            Expr::Member { receiver, name, span } => {
                let analyzed_receiver = self.analyze_expr(receiver, scope);

                let Type::Struct(struct_id) = analyzed_receiver.ty else {
                    let receiver_type = analyzed_receiver.ty.clone();

                    self.errors.push(
                        self.error_at(format!("type {:?} has no fields", receiver_type), *span)
                    );

                    return HirExpr {
                        kind: HirExprKind::Integer(0),
                        ty: Type::Int,
                        span: *span,
                    };
                };

                let Some((field_index, field)) = self.symbols.find_field(struct_id, name) else {
                    let struct_name = self.symbols.struct_symbol(struct_id).name.clone();

                    self.errors.push(
                        self.error_at(
                            format!("struct '{}' has no field '{}'", struct_name, name),
                            *span
                        )
                    );

                    return HirExpr {
                        kind: HirExprKind::Integer(0),
                        ty: Type::Int,
                        span: *span,
                    };
                };

                if !self.can_access_field(field) {
                    let visibility = match field.visibility {
                        Visibility::Public => "public",
                        Visibility::Protected => "protected",
                        Visibility::Private => "private",
                    };

                    let struct_name = self.symbols.struct_symbol(struct_id).name.clone();

                    self.errors.push(
                        self.error_at(
                            format!(
                                "cannot access {} field '{}' of struct '{}'",
                                visibility,
                                name,
                                struct_name
                            ),
                            *span
                        )
                    );

                    return HirExpr {
                        kind: HirExprKind::Integer(0),
                        ty: Type::Int,
                        span: *span,
                    };
                }

                HirExpr {
                    kind: HirExprKind::Field {
                        receiver: Box::new(analyzed_receiver),
                        struct_id: field.owner,
                        field: field_index,
                    },
                    ty: field.ty.clone(),
                    span: *span,
                }
            }
        }
    }

    fn resolve_struct_bases(&mut self, program: &Program) {
        for structure in &program.structs {
            let Some(struct_id) = self.symbols.find_struct(&structure.name) else {
                continue;
            };

            let Some(base_name) = &structure.base else {
                continue;
            };

            let Some(base_id) = self.symbols.find_struct(base_name) else {
                self.errors.push(
                    self.error_at(
                        format!(
                            "struct '{}' extends unknown struct '{}'",
                            structure.name,
                            base_name
                        ),
                        structure.span
                    )
                );

                continue;
            };

            if struct_id == base_id {
                self.errors.push(
                    self.error_at(
                        format!("struct '{}' cannot extend itself", structure.name),
                        structure.span
                    )
                );

                continue;
            }

            self.symbols.set_struct_base(struct_id, base_id);
        }

        for structure in &program.structs {
            let Some(struct_id) = self.symbols.find_struct(&structure.name) else {
                continue;
            };

            if self.has_inheritance_cycle(struct_id) {
                self.errors.push(
                    self.error_at(
                        format!("inheritance cycle involving struct '{}'", structure.name),
                        structure.span
                    )
                );
            }
        }
    }

    fn has_inheritance_cycle(&self, start: StructId) -> bool {
        let mut visited = HashSet::new();
        let mut current = Some(start);

        while let Some(struct_id) = current {
            if !visited.insert(struct_id) {
                return true;
            }

            current = self.symbols.struct_base(struct_id);
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::source::Span;
    use crate::parser::ast::{ BinaryOp, Expr, FunctionDecl, Program, Stmt, TypeName };

    fn span() -> Span {
        Span::new(0, 1)
    }

    fn int(value: i64) -> Expr {
        Expr::Integer {
            value,
            span: span(),
        }
    }

    fn string(value: &str) -> Expr {
        Expr::String {
            value: value.to_string(),
            span: span(),
        }
    }

    fn boolean(value: bool) -> Expr {
        Expr::Bool {
            value,
            span: span(),
        }
    }

    fn identifier(name: &str) -> Expr {
        Expr::Identifier {
            name: name.to_string(),
            span: span(),
        }
    }

    fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
        Expr::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
            span: span(),
        }
    }

    fn block(statements: Vec<Stmt>) -> Stmt {
        Stmt::Block {
            statements,
            span: span(),
        }
    }

    fn function(name: &str, return_type: TypeName, statements: Vec<Stmt>) -> FunctionDecl {
        FunctionDecl {
            name: name.to_string(),
            params: Vec::new(),
            return_type,
            body: block(statements),
            span: span(),
        }
    }

    fn program(functions: Vec<FunctionDecl>) -> Program {
        Program {
            structs: Vec::new(),
            functions,
        }
    }

    #[test]
    fn analyzes_integer_return() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![Stmt::Return {
                        value: Some(int(42)),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_ok(), "expected successful analysis: {result:?}");

        let hir = result.unwrap();
        assert_eq!(hir.functions.len(), 1);
        assert_eq!(hir.functions[0].name, "main");
        assert_eq!(hir.functions[0].return_type, Type::Int);
    }

    #[test]
    fn rejects_return_type_mismatch() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![Stmt::Return {
                        value: Some(string("wrong")),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_err());

        let errors = result.unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains("return")),
            "expected return-type diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn rejects_unknown_variable() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![Stmt::Return {
                        value: Some(identifier("missing")),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_err());

        let errors = result.unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains("unknown variable")),
            "expected unknown-variable diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn analyzes_local_variable_and_assignment() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![
                        Stmt::Let {
                            name: "x".to_string(),
                            ty: TypeName::Int,
                            value: int(10),
                            span: span(),
                        },
                        Stmt::Assign {
                            name: "x".to_string(),
                            value: int(20),
                            span: span(),
                        },
                        Stmt::Return {
                            value: Some(identifier("x")),
                            span: span(),
                        }
                    ]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_ok(), "expected successful analysis: {result:?}");

        let hir = result.unwrap();
        let function = &hir.functions[0];

        assert_eq!(function.locals.len(), 1);
        assert_eq!(function.locals[0].name, "x");
        assert_eq!(function.locals[0].ty, Type::Int);
    }

    #[test]
    fn rejects_assignment_type_mismatch() {
        let source = SourceFile::new("");
        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![
                        Stmt::Let {
                            name: "x".to_string(),
                            ty: TypeName::Int,
                            value: int(10),
                            span: span(),
                        },
                        Stmt::Assign {
                            name: "x".to_string(),
                            value: string("wrong"),
                            span: span(),
                        },
                        Stmt::Return {
                            value: Some(identifier("x")),
                            span: span(),
                        }
                    ]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_err());

        let errors = result.unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains("cannot assign")),
            "expected assignment diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn analyzes_integer_binary_expression() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![Stmt::Return {
                        value: Some(binary(BinaryOp::Add, int(2), int(3))),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_ok(), "expected successful analysis: {result:?}");
    }

    #[test]
    fn rejects_non_integer_arithmetic() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![Stmt::Return {
                        value: Some(binary(BinaryOp::Add, string("left"), string("right"))),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_err());

        let errors = result.unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains("arithmetic")),
            "expected arithmetic diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn analyzes_boolean_condition() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![Stmt::If {
                        condition: boolean(true),
                        then_block: Box::new(
                            block(
                                vec![Stmt::Return {
                                    value: Some(int(1)),
                                    span: span(),
                                }]
                            )
                        ),
                        else_block: Some(
                            Box::new(
                                block(
                                    vec![Stmt::Return {
                                        value: Some(int(2)),
                                        span: span(),
                                    }]
                                )
                            )
                        ),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_ok(), "expected successful analysis: {result:?}");
    }

    #[test]
    fn rejects_non_boolean_condition() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Int,
                    vec![Stmt::If {
                        condition: int(1),
                        then_block: Box::new(
                            block(
                                vec![Stmt::Return {
                                    value: Some(int(1)),
                                    span: span(),
                                }]
                            )
                        ),
                        else_block: None,
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_err());

        let errors = result.unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains("condition")),
            "expected condition diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn rejects_break_outside_loop() {
        let source = SourceFile::new("");

        let program = program(
            vec![function("main", TypeName::Void, vec![Stmt::Break { span: span() }])]
        );

        let result = analyze(program, source);

        assert!(result.is_err());

        let errors = result.unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains("break")),
            "expected break diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn rejects_continue_outside_loop() {
        let source = SourceFile::new("");

        let program = program(
            vec![function("main", TypeName::Void, vec![Stmt::Continue { span: span() }])]
        );

        let result = analyze(program, source);

        assert!(result.is_err());

        let errors = result.unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains("continue")),
            "expected continue diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn allows_break_inside_loop() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Void,
                    vec![Stmt::While {
                        condition: boolean(true),
                        body: Box::new(block(vec![Stmt::Break { span: span() }])),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_ok(), "expected successful analysis: {result:?}");
    }

    #[test]
    fn analyzes_equality_expression() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Bool,
                    vec![Stmt::Return {
                        value: Some(binary(BinaryOp::Equal, int(1), int(1))),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_ok(), "expected successful analysis: {result:?}");
    }

    #[test]
    fn rejects_equality_between_different_types() {
        let source = SourceFile::new("");

        let program = program(
            vec![
                function(
                    "main",
                    TypeName::Bool,
                    vec![Stmt::Return {
                        value: Some(binary(BinaryOp::Equal, int(1), string("one"))),
                        span: span(),
                    }]
                )
            ]
        );

        let result = analyze(program, source);

        assert!(result.is_err(), "expected equality between different types to fail");
    }
}
