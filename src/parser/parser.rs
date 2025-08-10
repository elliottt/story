use super::lexer;

pub(crate) type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Error {
    loc: lexer::Loc,
    message: String,
}

impl Error {
    fn new(loc: lexer::Loc, message: String) -> Self {
        Error { loc, message }
    }

    fn expected<T>(loc: lexer::Loc, expected: &str, found: &str) -> Result<T> {
        Result::Err(Error::new(
            loc,
            format!("Expected `{}`, but found `{}` instead", expected, found),
        ))
    }

    fn expected_atom<T>(loc: lexer::Loc, expected: &str, found: &str) -> Result<T> {
        Result::Err(Error::new(
            loc,
            format!(
                "Expected atom `{}`, but found `{}` instead",
                expected, found
            ),
        ))
    }
}

pub struct Parser<'a> {
    lexer: std::iter::Peekable<lexer::Lexer<'a>>,
    text: &'a str,
}

impl<'a> Parser<'a> {
    pub fn new(text: &'a str) -> Self {
        Parser {
            lexer: lexer::Lexer::new(text).peekable(),
            text,
        }
    }

    pub fn peek(&mut self) -> Result<lexer::Lexeme> {
        match self.lexer.peek() {
            Some(lex) => Result::Ok(lex.clone()),
            None => Result::Err(Error::new(
                lexer::Loc::end(self.text),
                "Unexpected end of input".to_owned(),
            )),
        }
    }

    pub fn consume(&mut self) -> Result<lexer::Lexeme> {
        match self.lexer.next() {
            Some(lex) => Result::Ok(lex),
            None => Result::Err(Error::new(
                lexer::Loc::end(self.text),
                "Unexpected end of input".to_owned(),
            )),
        }
    }

    pub fn lparen(&mut self) -> Result<()> {
        let next = self.consume()?;
        if next.token != lexer::Token::LParen {
            return Error::expected(next.loc, "(", next.loc.text(self.text));
        }

        Result::Ok(())
    }

    pub fn rparen(&mut self) -> Result<()> {
        let next = self.consume()?;
        if next.token != lexer::Token::RParen {
            return Error::expected(next.loc, "(", next.loc.text(self.text));
        }

        Result::Ok(())
    }

    pub fn atom(&mut self) -> Result<&str> {
        let next = self.consume()?;
        let found = next.loc.text(self.text);
        if next.token != lexer::Token::Atom {
            return Error::expected(next.loc, "atom", found);
        }

        Result::Ok(found)
    }

    /// Succeeds if the next token parsed is an atom with the same name given.
    pub fn keyword(&mut self, expected: &str) -> Result<()> {
        let next = self.consume()?;
        let found = next.loc.text(self.text);
        if next.token != lexer::Token::Atom || found != expected {
            return Error::expected_atom(next.loc, expected, found);
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
