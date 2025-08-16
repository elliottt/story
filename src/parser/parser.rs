use ariadne::{ColorGenerator, Label, ReportKind};

use super::lexer;

pub(crate) type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Error {
    loc: lexer::Loc,
    message: String,
}

pub type Report<'a> = ariadne::Report<'a, (&'a str, std::ops::Range<usize>)>;
pub type ReportBuilder<'a> = ariadne::ReportBuilder<'a, (&'a str, std::ops::Range<usize>)>;

impl Error {
    pub fn new(loc: lexer::Loc, message: String) -> Self {
        Error { loc, message }
    }

    pub fn report<'a>(self, file: &'a str) -> Report<'a> {
        Report::build(ReportKind::Error, (file, self.loc.range()))
            .with_label(Label::new((file, self.loc.range())))
            .with_message(self.message)
            .finish()
    }
}

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
    pub fn new(parser: &'p mut Parser<'a>, loc: lexer::Loc) -> Self {
        let builder = Report::build(ReportKind::Error, (parser.file, loc.range()));
        Self {
            parser,
            builder: Some(builder),
            colors: ColorGenerator::new(),
        }
    }

    pub fn label(&mut self, loc: lexer::Loc, message: String) -> &mut Self {
        if let Some(builder) = self.builder.as_mut() {
            builder.add_label(
                Label::new((self.parser.file, loc.range()))
                    .with_message(message)
                    .with_color(self.colors.next()),
            )
        }
        self
    }
}

pub struct Parser<'a> {
    lexer: std::iter::Peekable<lexer::Lexer<'a>>,
    file: &'a str,
    text: &'a str,
    errors: Vec<Report<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(file: &'a str, text: &'a str) -> Self {
        Parser {
            lexer: lexer::Lexer::new(text).peekable(),
            file,
            text,
            errors: Vec::new(),
        }
    }

    pub fn take_errors(self) -> Vec<Report<'a>> {
        self.errors
    }

    pub fn error<'p>(&'p mut self, loc: lexer::Loc, message: String) -> ErrorBuilder<'p, 'a> {
        let mut builder = ErrorBuilder::new(self, loc);
        builder.label(loc, message);
        builder
    }

    pub fn parse_error<T>(&self, loc: lexer::Loc, message: String) -> Result<T> {
        Result::Err(Error::new(loc, message))
    }

    fn expected<T>(&self, loc: lexer::Loc, expected: &str, found: &str) -> Result<T> {
        self.parse_error(
            loc,
            format!("Expected `{}`, but found `{}` instead", expected, found),
        )
    }

    fn expected_atom<T>(&self, loc: lexer::Loc, expected: &str, found: &str) -> Result<T> {
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
                lexer::Loc::end(self.text),
                "Unexpected end of input".to_owned(),
            ),
        }
    }

    pub fn consume(&mut self) -> Result<lexer::Lexeme> {
        match self.lexer.next() {
            Some(lex) => Result::Ok(lex),
            None => self.parse_error(
                lexer::Loc::end(self.text),
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
                lexer::Loc::end(self.text),
                format!("Unexpected: {}", self.text(next.loc)),
            );
        }
        Result::Ok(next)
    }

    pub fn lparen(&mut self) -> Result<()> {
        let next = self.consume()?;
        if next.token != lexer::Token::LParen {
            return self.expected(next.loc, "(", next.loc.text(self.text));
        }

        Result::Ok(())
    }

    pub fn rparen(&mut self) -> Result<()> {
        let next = self.consume()?;
        if next.token != lexer::Token::RParen {
            return self.expected(next.loc, ")", next.loc.text(self.text));
        }

        Result::Ok(())
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
        self.lparen()?;
        let res = body(self)?;
        self.rparen()?;
        Result::Ok(res)
    }
}
