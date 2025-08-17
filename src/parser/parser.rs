use ariadne::{Color, ColorGenerator, Label, ReportKind};

use super::lexer;
use crate::{File, arena::Id};

pub(crate) type Result<T> = std::result::Result<T, ()>;

pub type Report<'a> = ariadne::Report<'a, lexer::Loc>;
pub type ReportBuilder<'a> = ariadne::ReportBuilder<'a, lexer::Loc>;

pub struct ErrorBuilder<'p, 'a> {
    parser: &'p mut Parser<'a>,
    builder: Option<ReportBuilder<'a>>,
    colors: ColorGenerator,
}

impl Drop for ErrorBuilder<'_, '_> {
    fn drop(&mut self) {
        let builder = self.builder.take().unwrap();
        self.parser.errors.push(builder.finish())
    }
}

impl<'p, 'a> ErrorBuilder<'p, 'a> {
    pub fn new(parser: &'p mut Parser<'a>, loc: lexer::Loc, message: impl ToString) -> Self {
        let builder = Report::build(ReportKind::Error, loc).with_message(message);
        Self {
            parser,
            builder: Some(builder),
            colors: ColorGenerator::new(),
        }
    }

    pub fn label(&mut self, loc: lexer::Loc, message: impl ToString) -> Color {
        let color = self.colors.next();
        if let Some(builder) = self.builder.as_mut() {
            builder.add_label(Label::new(loc).with_message(message).with_color(color))
        }
        color
    }

    pub fn note(&mut self, message: impl ToString) -> &mut Self {
        if let Some(builder) = self.builder.as_mut() {
            builder.add_note(message)
        }
        self
    }
}

pub struct Parser<'a> {
    lexer: std::iter::Peekable<lexer::Lexer<'a>>,
    file: Id<File>,
    text: &'a str,
    errors: Vec<Report<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(file: Id<File>, text: &'a str) -> Self {
        Parser {
            lexer: lexer::Lexer::new(file, text).peekable(),
            file,
            text,
            errors: Vec::new(),
        }
    }

    pub fn take_errors(self) -> Vec<Report<'a>> {
        self.errors
    }

    pub fn error<'p>(
        &'p mut self,
        loc: lexer::Loc,
        message: impl ToString,
    ) -> ErrorBuilder<'p, 'a> {
        ErrorBuilder::new(self, loc, message)
    }

    pub fn parse_error<T>(&mut self, loc: lexer::Loc, message: impl ToString) -> Result<T> {
        self.error(loc, "Parse error").label(loc, message);
        Result::Err(())
    }

    fn expected<T>(&mut self, loc: lexer::Loc, expected: &str, found: &str) -> Result<T> {
        self.parse_error(
            loc,
            format!("Expected `{}`, but found `{}` instead", expected, found),
        )
    }

    fn expected_atom<T>(&mut self, loc: lexer::Loc, expected: &str, found: &str) -> Result<T> {
        self.parse_error(
            loc,
            format!(
                "Expected atom `{}`, but found `{}` instead",
                expected, found
            ),
        )
    }

    pub fn text(&self, loc: lexer::Loc) -> &str {
        loc.text(self.text)
    }

    pub fn peek(&mut self) -> Result<lexer::Lexeme> {
        match self.lexer.peek() {
            Some(lex) => Result::Ok(lex.clone()),
            None => self.parse_error(
                lexer::Loc::end(self.file, self.text),
                "Unexpected end of input".to_owned(),
            ),
        }
    }

    pub fn consume(&mut self) -> Result<lexer::Lexeme> {
        match self.lexer.next() {
            Some(lex) => Result::Ok(lex),
            None => self.parse_error(
                lexer::Loc::end(self.file, self.text),
                "Unexpected end of input".to_owned(),
            ),
        }
    }

    pub fn next_is(&mut self, token: lexer::Token) -> Result<bool> {
        let next = self.peek()?;
        Result::Ok(next.token == token)
    }

    pub fn expect(&mut self, token: lexer::Token) -> Result<lexer::Lexeme> {
        let next = self.consume()?;
        if next.token != token {
            return self.parse_error(
                lexer::Loc::end(self.file, self.text),
                format!("Unexpected: {}", self.text(next.loc)),
            );
        }
        Result::Ok(next)
    }

    pub fn token(&mut self, token: lexer::Token) -> Result<lexer::Lexeme> {
        let next = self.consume()?;
        if next.token != token {
            let found = next.loc.text(self.text);
            return self.expected(next.loc, "atom", found);
        }

        Result::Ok(next)
    }

    pub fn atom(&mut self) -> Result<&str> {
        self.token(lexer::Token::Atom)
            .map(|lex| lex.loc.text(self.text))
    }

    /// Succeeds if the next token parsed is an atom with the same name given.
    pub fn keyword(&mut self, expected: &str) -> Result<()> {
        let next = self.consume()?;
        let found = next.loc.text(self.text);
        if next.token != lexer::Token::Atom || found != expected {
            return self.expected_atom(next.loc, expected, found);
        }

        Result::Ok(())
    }

    pub fn list<T>(&mut self, body: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let start = self.consume()?;
        if start.token != lexer::Token::LParen {
            self.error(start.loc, "Parse error")
                .label(start.loc, "Expected a `(`");
            return Result::Err(());
        }
        let res = body(self)?;
        let end = self.consume()?;
        if end.token != lexer::Token::RParen {
            let mut e = self.error(end.loc, "Parse error");
            e.label(start.loc, "Opening paren here");
            e.label(end.loc, "Expected a `)`");
            return Result::Err(());
        }
        Result::Ok(res)
    }
}
