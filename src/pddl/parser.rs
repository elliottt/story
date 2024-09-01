use super::{
    types::{Problem, Typed},
    Error, Lexeme, Lexer, Token,
};

use std::sync::Arc;

pub struct Parser<'a> {
    text: &'a str,
    lexer: std::iter::Peekable<Lexer<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(text: &'a str) -> Self {
        Self {
            text,
            lexer: Lexer::new(text).peekable(),
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
        Ok(lex.text(self.text).to_string())
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

    /// Parse a list of the form:
    ///
    /// > (<name> ...)
    ///
    /// Where `...` is parsed by the `body` closure provided.
    pub fn decl<F, R>(&mut self, name: &str, body: F) -> super::Result<R>
    where
        F: FnOnce(&mut Self) -> super::Result<R>,
    {
        self.list(|this| {
            let lex = this.expect(Token::Atom)?;

            if lex.text(self.text) != name {
                return Err(Error::ExpectedAtom {
                    expected: name.to_string(),
                    loc: lex.loc,
                });
            }

            body(this)
        })
    }

    pub fn typed_atoms(&mut self) -> super::Result<Vec<Typed<String>>> {
        let mut res: Vec<Typed<_>> = Vec::new();

        let mut start = 0;

        while let Some(lex) = self.lexer.peek() {
            // We're about to parse an annotation
            if lex.token == Token::Atom {
                if lex.text(self.text) == "-" {
                    // eat the token
                    self.lexer.next();

                    let ty = Arc::new(self.atom()?);

                    for entry in &mut res[start..] {
                        entry.ty.replace(ty.clone());
                    }

                    start = res.len();
                } else {
                    let atom = self.atom()?;
                    res.push(Typed::new(atom));
                }
            } else {
                break;
            }
        }

        Ok(res)
    }

    pub fn problem(&mut self) -> super::Result<Problem> {
        self.decl("define", |this| {
            let name = this.decl("problem", Self::atom)?;

            // I'm not sure if it's reasonable to require that `:domain` occurs here, but it does
            // simplify parsing.
            let domain = this.decl(":domain", Self::atom)?;

            let objects = this.decl(":objects", Self::typed_atoms)?;

            Ok(Problem { name, domain, objects })
        })
    }
}

#[test]
fn test_typed_atoms() {
    let text = "a b c - t e - j";
    let mut p = Parser::new(text);
    let atoms = p.typed_atoms().expect("typed atoms parse");

    assert_eq!(atoms.len(), 4);

    for atom in &atoms[0..2] {
        assert!(atom.ty.is_some());
        assert_eq!(**atom.ty.as_ref().unwrap(), "t");
    }

    assert!(atoms[3].ty.is_some());
    assert_eq!(**atoms[3].ty.as_ref().unwrap(), "j");
}
