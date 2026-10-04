use crate::{
    compiler::{
        error::CompilerError,
        source::{SourceFile, Span},
    },
    parser::ast::ConstructorDecl,
    semantic::modifiers::Visibility,
};

use super::ast::{
    BinaryOp, Expr, FieldDecl, FunctionDecl, Param, Program, Stmt, StructDecl, TypeName,
};

use crate::lexer::token::{Token, TokenKind};

pub fn parse(source: &SourceFile, tokens: &[Token]) -> Result<Program, Vec<CompilerError>> {
    let mut parser = Parser::new(source, tokens);
    parser.parse_program()
}

struct Parser<'a> {
    source: &'a SourceFile,
    tokens: &'a [Token],
    position: usize,
}

impl<'a> Parser<'a> {
    fn new(source: &'a SourceFile, tokens: &'a [Token]) -> Self {
        Self {
            source,
            tokens,
            position: 0,
        }
    }

    fn parse_program(&mut self) -> Result<Program, Vec<CompilerError>> {
        let mut structs = Vec::new();
        let mut functions = Vec::new();
        let mut errors = Vec::new();

        while !self.check(&TokenKind::Eof) {
            if self.check(&TokenKind::Struct) {
                match self.parse_struct() {
                    Ok(value) => structs.push(value),
                    Err(error) => errors.push(error),
                }
            } else if self.check(&TokenKind::Fn) {
                match self.parse_function() {
                    Ok(value) => functions.push(value),
                    Err(error) => errors.push(error),
                }
            } else {
                errors.push(self.error_here("expected 'struct' or 'fn'"));
                self.advance();
            }
        }

        if errors.is_empty() {
            Ok(Program { structs, functions })
        } else {
            Err(errors)
        }
    }

    fn parse_struct(&mut self) -> Result<StructDecl, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::Struct, "expected 'struct'")?;

        let name = self.expect_identifier("expected struct name")?;

        let base = if self.consume(&TokenKind::Extends) {
            Some(self.expect_identifier("expected base struct name")?)
        } else {
            None
        };

        self.expect(&TokenKind::LeftBrace, "expected '{'")?;

        let mut fields = Vec::new();
        let mut constructors = Vec::new();
        let mut methods = Vec::new();

        while !self.check(&TokenKind::RightBrace) && !self.check(&TokenKind::Eof) {
            if self.check(&TokenKind::Constructor) {
                let constructor = self.parse_constructor()?;
                constructors.push(constructor);
            } else if self.check(&TokenKind::Fn) {
                let method = self.parse_function()?;
                methods.push(method);
            } else {
                let field = self.parse_struct_field()?;
                fields.push(field);
            }
        }

        self.expect(&TokenKind::RightBrace, "expected '}'")?;

        Ok(StructDecl {
            name,
            base,
            fields,
            methods,
            constructors,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_constructor(&mut self) -> Result<ConstructorDecl, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::Constructor, "expected 'constructor'")?;

        self.expect(&TokenKind::LeftParen, "expected '(' after 'constructor'")?;

        let mut params = Vec::new();

        if !self.check(&TokenKind::RightParen) {
            loop {
                let param_start = self.current_span().start;

                let param_name = self.expect_identifier("expected parameter name")?;

                self.expect(&TokenKind::Colon, "expected ':' after parameter name")?;

                let ty = self.parse_type()?;

                params.push(Param {
                    name: param_name,
                    ty,
                    span: Span::new(param_start, self.previous_span().end),
                });

                if !self.consume(&TokenKind::Comma) {
                    break;
                }
            }
        }

        self.expect(&TokenKind::RightParen, "expected ')'")?;

        let base_arguments = if self.consume(&TokenKind::Colon) {
            self.expect(&TokenKind::Base, "expected 'base' after ':'")?;

            self.expect(&TokenKind::LeftParen, "expected '(' after 'base'")?;

            let arguments = self.parse_call_arguments()?;

            arguments
        } else {
            Vec::new()
        };

        let body = self.parse_block()?;

        Ok(ConstructorDecl {
            params,
            base_arguments,
            body,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_struct_field(&mut self) -> Result<FieldDecl, CompilerError> {
        let start = self.current_span().start;

        let visibility = if self.consume(&TokenKind::Protected) {
            Visibility::Protected
        } else if self.consume(&TokenKind::Private) {
            Visibility::Private
        } else if self.consume(&TokenKind::Public) {
            Visibility::Public
        } else {
            Visibility::Public
        };

        let name = self.expect_identifier("expected field name")?;

        self.expect(&TokenKind::Colon, "expected ':' after field name")?;

        let ty = self.parse_type()?;

        self.expect(
            &TokenKind::Semicolon,
            "expected ';' after field declaration",
        )?;

        let end = self.previous_span().end;

        Ok(FieldDecl {
            name,
            ty,
            visibility,
            span: Span::new(start, end),
        })
    }

    fn parse_function(&mut self) -> Result<FunctionDecl, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::Fn, "expected 'fn'")?;

        let name = self.expect_identifier("expected function name")?;

        self.expect(&TokenKind::LeftParen, "expected '('")?;

        let mut params = Vec::new();

        if !self.check(&TokenKind::RightParen) {
            loop {
                let param_start = self.current_span().start;

                let param_name = self.expect_identifier("expected parameter name")?;

                self.expect(&TokenKind::Colon, "expected ':' after parameter name")?;

                let ty = self.parse_type()?;

                params.push(Param {
                    name: param_name,
                    ty,
                    span: Span::new(param_start, self.previous_span().end),
                });

                if !self.consume(&TokenKind::Comma) {
                    break;
                }
            }
        }

        self.expect(&TokenKind::RightParen, "expected ')'")?;

        self.expect(&TokenKind::Colon, "expected ':' before return type")?;

        let return_type = self.parse_type()?;

        let body = self.parse_block()?;

        Ok(FunctionDecl {
            name,
            params,
            return_type,
            body,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_block(&mut self) -> Result<Stmt, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::LeftBrace, "expected '{'")?;

        let mut statements = Vec::new();

        while !self.check(&TokenKind::RightBrace) && !self.check(&TokenKind::Eof) {
            statements.push(self.parse_statement()?);
        }

        self.expect(&TokenKind::RightBrace, "expected '}'")?;

        Ok(Stmt::Block {
            statements,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_statement(&mut self) -> Result<Stmt, CompilerError> {
        if self.check(&TokenKind::Let) {
            return self.parse_let_statement();
        }

        if self.check(&TokenKind::Const) {
            return self.parse_const_statement();
        }

        if self.check(&TokenKind::Return) {
            return self.parse_return_statement();
        }

        if self.check(&TokenKind::If) {
            return self.parse_if_statement();
        }

        if self.check(&TokenKind::While) {
            return self.parse_while_statement();
        }

        if self.check(&TokenKind::Break) {
            let start = self.current_span().start;

            self.advance();

            self.expect(&TokenKind::Semicolon, "expected ';' after 'break'")?;

            return Ok(Stmt::Break {
                span: Span::new(start, self.previous_span().end),
            });
        }

        if self.check(&TokenKind::Continue) {
            let start = self.current_span().start;

            self.advance();

            self.expect(&TokenKind::Semicolon, "expected ';' after 'continue'")?;

            return Ok(Stmt::Continue {
                span: Span::new(start, self.previous_span().end),
            });
        }

        /*
         * Assignment must be detected before parsing a normal expression.
         *
         * We recognize:
         *
         *     identifier = expression;
         *
         * but NOT:
         *
         *     identifier(...);
         */
        if self.is_assignment_statement() {
            return self.parse_assignment_statement();
        }

        let start = self.current_span().start;

        let expr = self.parse_expression()?;

        self.expect(&TokenKind::Semicolon, "expected ';' after expression")?;

        Ok(Stmt::Expr {
            expr,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_let_statement(&mut self) -> Result<Stmt, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::Let, "expected 'let'")?;

        let name = self.expect_identifier("expected variable name")?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let value = if self.check(&TokenKind::Equal) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        if ty.is_none() && value.is_none() {
            return Err(self.error_at(
                "variable declaration requires a type or initializer",
                self.previous_span(),
            ));
        }

        self.expect(
            &TokenKind::Semicolon,
            "expected ';' after variable declaration",
        )?;

        Ok(Stmt::Let {
            name,
            ty,
            value,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_const_statement(&mut self) -> Result<Stmt, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::Const, "expected 'const'")?;

        let name = self.expect_identifier("expected variable name")?;

        self.expect(&TokenKind::Colon, "expected ':' after variable name")?;

        let ty = self.parse_type()?;

        self.expect(&TokenKind::Equal, "expected '=' in variable declaration")?;

        let value = self.parse_expression()?;

        self.expect(
            &TokenKind::Semicolon,
            "expected ';' after variable declaration",
        )?;

        Ok(Stmt::Const {
            name,
            ty,
            value,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_assignment_statement(&mut self) -> Result<Stmt, CompilerError> {
        let start = self.current_span().start;

        let target = self.parse_assignment_target()?;

        self.expect(&TokenKind::Equal, "expected '=' in assignment")?;

        let value = self.parse_expression()?;

        self.expect(&TokenKind::Semicolon, "expected ';' after assignment")?;

        Ok(Stmt::Assign {
            target,
            value,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_assignment_target(&mut self) -> Result<Expr, CompilerError> {
        let start = self.current_span().start;

        let name = self.expect_identifier("expected assignment target")?;

        let mut target = Expr::Identifier {
            name,
            span: Span::new(start, self.previous_span().end),
        };

        while self.consume(&TokenKind::Dot) {
            let name = self.expect_identifier("expected member name after '.'")?;

            let end = self.previous_span().end;

            target = Expr::Member {
                receiver: Box::new(target),
                name,
                span: Span::new(start, end),
            };
        }

        Ok(target)
    }

    fn parse_return_statement(&mut self) -> Result<Stmt, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::Return, "expected 'return'")?;

        let value = if self.check(&TokenKind::Semicolon) {
            None
        } else {
            Some(self.parse_expression()?)
        };

        self.expect(&TokenKind::Semicolon, "expected ';' after return")?;

        Ok(Stmt::Return {
            value,
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_if_statement(&mut self) -> Result<Stmt, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::If, "expected 'if'")?;

        self.expect(&TokenKind::LeftParen, "expected '(' after 'if'")?;

        let condition = self.parse_expression()?;

        self.expect(&TokenKind::RightParen, "expected ')' after condition")?;

        let then_block = self.parse_block()?;

        let else_block = if self.consume(&TokenKind::Else) {
            Some(self.parse_block()?)
        } else {
            None
        };

        Ok(Stmt::If {
            condition,
            then_block: Box::new(then_block),
            else_block: else_block.map(Box::new),
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_while_statement(&mut self) -> Result<Stmt, CompilerError> {
        let start = self.current_span().start;

        self.expect(&TokenKind::While, "expected 'while'")?;

        self.expect(&TokenKind::LeftParen, "expected '(' after 'while'")?;

        let condition = self.parse_expression()?;

        self.expect(&TokenKind::RightParen, "expected ')' after condition")?;

        let body = self.parse_block()?;

        Ok(Stmt::While {
            condition,
            body: Box::new(body),
            span: Span::new(start, self.previous_span().end),
        })
    }

    fn parse_type(&mut self) -> Result<TypeName, CompilerError> {
        let token = self.advance();

        match token.kind {
            TokenKind::Int => Ok(TypeName::Int),
            TokenKind::StringType => Ok(TypeName::String),
            TokenKind::Bool => Ok(TypeName::Bool),
            TokenKind::Void => Ok(TypeName::Void),
            TokenKind::Identifier(name) => Ok(TypeName::Named(name)),
            _ => Err(self.error_at("expected type", token.span)),
        }
    }

    fn parse_expression(&mut self) -> Result<Expr, CompilerError> {
        self.parse_equality()
    }

    fn parse_equality(&mut self) -> Result<Expr, CompilerError> {
        let mut expr = self.parse_additive()?;

        while self.consume(&TokenKind::EqualEqual) {
            let right = self.parse_additive()?;

            let span = Span::new(expression_start(&expr), expression_end(&right));

            expr = Expr::Binary {
                op: BinaryOp::Equal,
                left: Box::new(expr),
                right: Box::new(right),
                span,
            };
        }

        Ok(expr)
    }

    fn parse_additive(&mut self) -> Result<Expr, CompilerError> {
        let mut expr = self.parse_multiplicative()?;

        loop {
            let op = if self.consume(&TokenKind::Plus) {
                Some(BinaryOp::Add)
            } else if self.consume(&TokenKind::Minus) {
                Some(BinaryOp::Subtract)
            } else {
                None
            };

            let Some(op) = op else {
                break;
            };

            let right = self.parse_multiplicative()?;

            let span = Span::new(expression_start(&expr), expression_end(&right));

            expr = Expr::Binary {
                op,
                left: Box::new(expr),
                right: Box::new(right),
                span,
            };
        }

        Ok(expr)
    }

    fn parse_multiplicative(&mut self) -> Result<Expr, CompilerError> {
        let mut expr = self.parse_primary()?;

        loop {
            let op = if self.consume(&TokenKind::Star) {
                Some(BinaryOp::Multiply)
            } else if self.consume(&TokenKind::Slash) {
                Some(BinaryOp::Divide)
            } else {
                None
            };

            let Some(op) = op else {
                break;
            };

            let right = self.parse_primary()?;

            let span = Span::new(expression_start(&expr), expression_end(&right));

            expr = Expr::Binary {
                op,
                left: Box::new(expr),
                right: Box::new(right),
                span,
            };
        }

        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr, CompilerError> {
        let token = self.advance();

        let mut expression = match token.kind {
            TokenKind::New => {
                let name = self.expect_identifier("expected struct name after 'new'")?;

                self.expect(&TokenKind::LeftParen, "expected '(' after struct name")?;

                let arguments = self.parse_call_arguments()?;

                Expr::New {
                    name,
                    arguments,
                    span: Span::new(token.span.start, self.previous_span().end),
                }
            }
            TokenKind::Integer(value) => Expr::Integer {
                value,
                span: token.span,
            },

            TokenKind::String(value) => Expr::String {
                value,
                span: token.span,
            },

            TokenKind::True => Expr::Bool {
                value: true,
                span: token.span,
            },

            TokenKind::False => Expr::Bool {
                value: false,
                span: token.span,
            },

            TokenKind::Identifier(name) => Expr::Identifier {
                name,
                span: token.span,
            },

            TokenKind::LeftParen => {
                let expression = self.parse_expression()?;
                self.expect(&TokenKind::RightParen, "expected ')'")?;
                expression
            }

            _ => {
                return Err(self.error_at("expected expression", token.span));
            }
        };

        loop {
            if self.consume(&TokenKind::LeftParen) {
                let arguments = self.parse_call_arguments()?;

                let Expr::Identifier { name, span } = expression else {
                    return Err(self.error_at(
                        "only function names can be called directly",
                        expression.span(),
                    ));
                };

                expression = Expr::Call {
                    receiver: None,
                    name,
                    arguments,
                    span: Span::new(span.start, self.previous_span().end),
                };

                continue;
            }

            if self.consume(&TokenKind::Dot) {
                let member_name = self.expect_identifier("expected name after '.'")?;

                if self.consume(&TokenKind::LeftParen) {
                    let arguments = self.parse_call_arguments()?;

                    expression = Expr::Call {
                        receiver: Some(Box::new(expression)),
                        name: member_name,
                        arguments,
                        span: Span::new(token.span.start, self.previous_span().end),
                    };
                } else {
                    expression = Expr::Member {
                        receiver: Box::new(expression),
                        name: member_name,
                        span: Span::new(token.span.start, self.previous_span().end),
                    };
                }

                continue;
            }

            break;
        }

        Ok(expression)
    }

    fn parse_call_arguments(&mut self) -> Result<Vec<Expr>, CompilerError> {
        let mut arguments = Vec::new();

        if !self.check(&TokenKind::RightParen) {
            loop {
                arguments.push(self.parse_expression()?);

                if !self.consume(&TokenKind::Comma) {
                    break;
                }
            }
        }

        self.expect(&TokenKind::RightParen, "expected ')' after arguments")?;

        Ok(arguments)
    }

    fn is_assignment_statement(&self) -> bool {
        let mut position = self.position;

        // Assignment must start with an expression that can be a target.
        match self.tokens.get(position).map(|token| &token.kind) {
            Some(TokenKind::Identifier(_)) => {
                position += 1;
            }

            _ => {
                return false;
            }
        }

        // Allow member access:
        //
        // identifier.name = ...
        //
        // This also allows:
        //
        // this.name = ...
        // object.field = ...
        //
        loop {
            let is_dot = matches!(
                self.tokens.get(position).map(|token| &token.kind),
                Some(TokenKind::Dot)
            );

            if !is_dot {
                break;
            }

            position += 1;

            if !matches!(
                self.tokens.get(position).map(|token| &token.kind),
                Some(TokenKind::Identifier(_))
            ) {
                return false;
            }

            position += 1;
        }

        matches!(
            self.tokens.get(position).map(|token| &token.kind),
            Some(TokenKind::Equal)
        )
    }

    fn expect_identifier(&mut self, message: &str) -> Result<String, CompilerError> {
        let token = self.advance();

        match token.kind {
            TokenKind::Identifier(name) => Ok(name),
            _ => Err(self.error_at(message, token.span)),
        }
    }

    fn expect(&mut self, expected: &TokenKind, message: &str) -> Result<Token, CompilerError> {
        if self.check(expected) {
            Ok(self.advance())
        } else {
            Err(self.error_here(message))
        }
    }

    fn consume(&mut self, kind: &TokenKind) -> bool {
        if self.check(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.peek().kind) == std::mem::discriminant(kind)
    }

    fn advance(&mut self) -> Token {
        let token = self.tokens.get(self.position).cloned().unwrap_or_else(|| {
            self.tokens
                .last()
                .cloned()
                .expect("parser requires at least EOF token")
        });

        if self.position < self.tokens.len() {
            self.position += 1;
        }

        token
    }

    fn peek(&self) -> &Token {
        self.tokens
            .get(self.position)
            .unwrap_or_else(|| self.tokens.last().expect("missing EOF token"))
    }

    fn current_span(&self) -> Span {
        self.peek().span
    }

    fn previous_span(&self) -> Span {
        if self.position == 0 {
            self.current_span()
        } else {
            self.tokens[self.position - 1].span
        }
    }

    fn error_here(&self, message: &str) -> CompilerError {
        self.error_at(message, self.current_span())
    }

    fn error_at(&self, message: impl Into<String>, span: Span) -> CompilerError {
        CompilerError::new(&self.source.text, message, span.to_source_span())
    }
}

fn expression_start(expr: &Expr) -> usize {
    match expr {
        Expr::Integer { span, .. }
        | Expr::String { span, .. }
        | Expr::Bool { span, .. }
        | Expr::Identifier { span, .. }
        | Expr::Binary { span, .. }
        | Expr::Member { span, .. }
        | Expr::New { span, .. }
        | Expr::Call { span, .. } => span.start,
    }
}

fn expression_end(expr: &Expr) -> usize {
    match expr {
        Expr::Integer { span, .. }
        | Expr::String { span, .. }
        | Expr::Bool { span, .. }
        | Expr::Identifier { span, .. }
        | Expr::Binary { span, .. }
        | Expr::Member { span, .. }
        | Expr::New { span, .. }
        | Expr::Call { span, .. } => span.end,
    }
}
