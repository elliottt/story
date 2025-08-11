mod lexer;
mod parser;
pub use lexer::Loc;

use crate::ir::{Arena, Id, Type};
use lexer::Token;
use parser::{Error, Parser, Result};

pub fn lexer<'a>(bytes: &'a str) -> impl Iterator<Item = lexer::Lexeme> + 'a {
    lexer::Lexer::new(bytes)
}

pub fn parse_types(p: &mut Parser<'_>, types: &mut Arena<Type>) -> Result<()> {
    // As this is called within the context of a `list`, we terminate when we find a RParen.
    let mut buffer = Vec::new();
    let mut handling_supertype = false;
    println!("types");
    loop {
        if p.peek()?.token != Token::Atom {
            break;
        }

        let next = p.consume()?;
        match p.text(next.loc) {
            "-" => {
                handling_supertype = true;
                continue;
            }

            text if handling_supertype => {
                let super_type = types.add(Type {
                    loc: next.loc,
                    name: text.to_owned(),
                    super_type: Id::none(),
                });
                for ty in buffer.drain(..) {
                    // TODO: error if super_type is not none
                    types[ty].super_type = super_type;
                }
            }

            text => buffer.push(types.add(Type {
                loc: next.loc,
                name: text.to_owned(),
                super_type: Id::none(),
            })),
        }
    }

    Result::Ok(())
}

/// Parse a domain specification out of the bytes given.
pub fn parse_domain<'a>(bytes: &'a str) -> Result<crate::ir::Domain> {
    let mut parser = Parser::new(bytes);

    let mut domain = crate::ir::Domain::default();

    parser.list(|p| {
        p.keyword("define")?;

        p.list(|p| {
            p.keyword("domain")?;
            domain.name = String::from(p.atom()?);
            Result::Ok(())
        })?;

        while p.peek()?.token != lexer::Token::RParen {
            p.list(|p| {
                let case = p.token(lexer::Token::Atom)?;
                match p.text(case.loc) {
                    ":types" => parse_types(p, &mut domain.types)?,

                    _ => {
                        return Result::Err(Error::new(
                            case.loc,
                            format!("Expected a declaration"),
                        ));
                    }
                }

                Result::Ok(())
            })?;
        }

        Result::Ok(())
    })?;

    Result::Ok(domain)
}

#[test]
fn test_lexer_empty() {
    let ts = Vec::from_iter(lexer(""));
    assert!(ts.is_empty());
}

#[test]
fn test_lexer_parens() {
    let ts = Vec::from_iter(lexer("()())").map(|lexeme| lexeme.token));

    use lexer::Token::*;
    assert_eq!(ts, vec![LParen, RParen, LParen, RParen, RParen]);
}

#[test]
fn test_lexer_atoms() {
    let ts = Vec::from_iter(lexer("foo bar baz? :bonk").map(|lexeme| lexeme.token));

    use lexer::Token::*;
    assert_eq!(ts, vec![Atom, Atom, Atom, Atom]);
}

#[test]
fn test_source_extraction() {
    let text = "foo bar (baz?) :bonk";
    let ts = Vec::from_iter(lexer(text));

    assert_eq!("foo", ts[0].loc.text(text));
    assert_eq!("bar", ts[1].loc.text(text));
    assert_eq!("baz?", ts[3].loc.text(text));
    assert_eq!(":bonk", ts[5].loc.text(text));
}

#[test]
fn test_source_extraction_comments() {
    let text = "foo ;; foo bar ()\n  bar (baz?) :bonk";
    let ts = Vec::from_iter(lexer(text));

    assert_eq!("foo", ts[0].loc.text(text));
    assert_eq!("bar", ts[1].loc.text(text));
    assert_eq!("(", ts[2].loc.text(text));
    assert_eq!("baz?", ts[3].loc.text(text));
    assert_eq!(")", ts[4].loc.text(text));
    assert_eq!(":bonk", ts[5].loc.text(text));
}

#[test]
fn test_empty_domain() {
    let text = "(define (domain foo))";
    let result = parse_domain(text).expect("Failed to parse domain");
    assert_eq!("foo", result.name);
}

#[test]
fn test_simple_types() {
    let text = "(define (domain foo) (:types a b - object))";
    let domain = parse_domain(text).expect("Failed to parse domain");
    assert_eq!("foo", domain.name);

    let super_type = Id::new(2);
    assert_eq!(3, domain.types.len());
    assert_eq!(super_type, domain.types[Id::new(0)].super_type);
    assert_eq!(super_type, domain.types[Id::new(1)].super_type);
    assert!(!domain.types[Id::new(2)].super_type.exists());
}
