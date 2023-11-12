use super::{types::Problem, Error, Lexeme, Lexer, Token};

pub struct Parser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(text: &'a str) -> Self {
        Self {
            lexer: Lexer::new(text),
        }
    }

    pub fn expect(&mut self, expected: Token) -> super::Result<Lexeme> {
        if let Some(lex) = self.lexer.next() {
            if lex.token == expected {
                return Ok(lex);
            }

            return Err(Error::ExpectedToken {
                expected,
                loc: lex.loc,
            });
        }

        Err(Error::UnexpectedEof)
    }

    pub fn atom(&mut self) -> super::Result<String> {
        let lex = self.expect(Token::Atom)?;
        Ok(lex.text(self.lexer.text).to_string())
    }

    pub fn list<F, R>(&mut self, body: F) -> super::Result<R>
    where
        F: FnOnce(&mut Self) -> super::Result<R>,
    {
        self.expect(Token::LParen)?;
        let r = body(self)?;
        self.expect(Token::RParen)?;
        Ok(r)
    }

    pub fn decl<F, R>(&mut self, name: &str, body: F) -> super::Result<R>
    where
        F: FnOnce(&mut Self) -> super::Result<R>,
    {
        self.list(|this| {
            let lex = this.expect(Token::Atom)?;

            if lex.text(self.lexer.text) != name {
                return Err(Error::ExpectedAtom {
                    expected: name.to_string(),
                    loc: lex.loc,
                });
            }

            body(this)
        })
    }

    pub fn problem(&mut self) -> super::Result<Problem> {
        self.decl("define", |this| {
            let name = this.decl("problem", Self::atom)?;

            // I'm not sure if it's reasonable to require that `:domain` occurs here, but it does
            // simplify parsing.
            let domain = this.decl(":domain", Self::atom)?;

            Ok(Problem { name, domain })
        })
    }
}
