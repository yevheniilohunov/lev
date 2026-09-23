use crate::compiler::{ error::CompilerError, source::{ SourceFile, Span } };

use super::token::{ Token, TokenKind };

pub fn lex(source: &SourceFile) -> Result<Vec<Token>, Vec<CompilerError>> {
    let mut lexer = Lexer::new(source);
    lexer.run();

    if lexer.errors.is_empty() {
        Ok(lexer.tokens)
    } else {
        Err(lexer.errors)
    }
}

struct Lexer<'a> {
    source: &'a SourceFile,
    position: usize,

    tokens: Vec<Token>,
    errors: Vec<CompilerError>,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a SourceFile) -> Self {
        Self {
            source,
            position: 0,
            tokens: Vec::new(),
            errors: Vec::new(),
        }
    }

    fn run(&mut self) {
        while self.position < self.source.text.len() {
            self.skip_whitespace_and_comments();

            if self.position >= self.source.text.len() {
                break;
            }

            self.scan_token();
        }

        self.tokens.push(Token {
            kind: TokenKind::Eof,
            span: Span::new(self.position, self.position),
        });
    }

    fn scan_token(&mut self) {
        let start = self.position;

        let c = self.current_char();

        match c {
            '{' => self.simple(TokenKind::LeftBrace),
            '}' => self.simple(TokenKind::RightBrace),

            '(' => self.simple(TokenKind::LeftParen),
            ')' => self.simple(TokenKind::RightParen),

            ':' => self.simple(TokenKind::Colon),
            ';' => self.simple(TokenKind::Semicolon),
            ',' => self.simple(TokenKind::Comma),
            '.' => self.simple(TokenKind::Dot),

            '+' => self.simple(TokenKind::Plus),
            '-' => self.simple(TokenKind::Minus),
            '*' => self.simple(TokenKind::Star),

            '/' => self.simple(TokenKind::Slash),

            '=' => {
                self.advance();

                if self.current_char() == '=' {
                    self.advance();

                    self.tokens.push(Token {
                        kind: TokenKind::EqualEqual,
                        span: Span::new(start, self.position),
                    });
                } else {
                    self.tokens.push(Token {
                        kind: TokenKind::Equal,
                        span: Span::new(start, self.position),
                    });
                }
            }

            '"' => self.scan_string(),

            c if c.is_ascii_digit() => {
                self.scan_number();
            }

            c if is_identifier_start(c) => {
                self.scan_identifier();
            }

            _ => {
                self.errors.push(
                    CompilerError::new(
                        &self.source.text,
                        format!("unexpected character '{}'", c),
                        Span::new(start, start + c.len_utf8()).to_source_span()
                    )
                );

                self.advance();
            }
        }
    }

    fn scan_number(&mut self) {
        let start = self.position;

        while self.position < self.source.text.len() && self.current_char().is_ascii_digit() {
            self.advance();
        }

        let text = self.source.slice(start, self.position);

        match text.parse::<i64>() {
            Ok(value) => {
                self.tokens.push(Token {
                    kind: TokenKind::Integer(value),
                    span: Span::new(start, self.position),
                });
            }

            Err(_) => {
                self.errors.push(
                    CompilerError::new(
                        &self.source.text,
                        "integer literal is too large",
                        Span::new(start, self.position).to_source_span()
                    )
                );
            }
        }
    }

    fn scan_string(&mut self) {
        let start = self.position;

        self.advance();

        let mut value = String::new();

        while self.position < self.source.text.len() {
            let c = self.current_char();

            if c == '"' {
                self.advance();

                self.tokens.push(Token {
                    kind: TokenKind::String(value),
                    span: Span::new(start, self.position),
                });

                return;
            }

            if c == '\\' {
                self.advance();

                if self.position >= self.source.text.len() {
                    break;
                }

                let escaped = self.current_char();

                match escaped {
                    'n' => value.push('\n'),
                    't' => value.push('\t'),
                    '"' => value.push('"'),
                    '\\' => value.push('\\'),

                    _ => {
                        self.errors.push(
                            CompilerError::new(
                                &self.source.text,
                                format!("unknown escape sequence '\\{}'", escaped),
                                Span::new(self.position - 1, self.position + 1).to_source_span()
                            )
                        );
                    }
                }

                self.advance();
            } else {
                value.push(c);
                self.advance();
            }
        }

        self.errors.push(
            CompilerError::new(
                    &self.source.text,"unterminated string literal", Span::new(start, self.position).to_source_span())
        );
    }

    fn scan_identifier(&mut self) {
        let start = self.position;

        while self.position < self.source.text.len() && is_identifier_continue(self.current_char()) {
            self.advance();
        }

        let text = self.source.slice(start, self.position);

        let kind = match text {
            "extends"  => TokenKind::Extends,
            "struct" => TokenKind::Struct,
            "fn" => TokenKind::Fn,
            "constructor" => TokenKind::Constructor,
            "base" => TokenKind::Base,
            "let" => TokenKind::Let,
            "const" => TokenKind::Const,
            "return" => TokenKind::Return,

            "true" => TokenKind::True,
            "false" => TokenKind::False,

            "int" => TokenKind::Int,
            "string" => TokenKind::StringType,
            "bool" => TokenKind::Bool,
            "void" => TokenKind::Void,

            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "while" => TokenKind::While,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,

            "public" => TokenKind::Public,
            "private" => TokenKind::Private,
            "protected" => TokenKind::Protected,

            "new" => TokenKind::New,

            _ => TokenKind::Identifier(text.to_string()),
        };

        self.tokens.push(Token {
            kind,
            span: Span::new(start, self.position),
        });
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            while self.position < self.source.text.len() && self.current_char().is_whitespace() {
                self.advance();
            }

            if
                self.position + 1 < self.source.text.len() &&
                self.current_char() == '/' &&
                self.peek_char() == '/'
            {
                while self.position < self.source.text.len() && self.current_char() != '\n' {
                    self.advance();
                }

                continue;
            }

            break;
        }
    }

    fn simple(&mut self, kind: TokenKind) {
        let start = self.position;
        self.advance();

        self.tokens.push(Token {
            kind,
            span: Span::new(start, self.position),
        });
    }

    fn current_char(&self) -> char {
        self.source.text.as_bytes().get(self.position).copied().map(char::from).unwrap_or('\0')
    }

    fn peek_char(&self) -> char {
        self.source.text
            .as_bytes()
            .get(self.position + 1)
            .copied()
            .map(char::from)
            .unwrap_or('\0')
    }

    fn advance(&mut self) {
        self.position += 1;
    }
}

fn is_identifier_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_identifier_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}
