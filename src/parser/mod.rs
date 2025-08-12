mod lexer;
mod parser;
pub use lexer::Loc;

use crate::ir::{Arena, Constant, Id, NamedArena, Param, Property, Type};
use lexer::Token;
use parser::{Error, Parser, Result};

pub fn lexer<'a>(bytes: &'a str) -> impl Iterator<Item = lexer::Lexeme> + 'a {
    lexer::Lexer::new(bytes)
}

pub fn parse_types(p: &mut Parser<'_>, types: &mut NamedArena<Type>) -> Result<()> {
    // As this is called within the context of a `list`, we terminate when we find a RParen.
    let mut buffer = Vec::new();
    println!("types");
    while p.peek()?.token == Token::Atom {
        let next = p.consume()?;
        match p.text(next.loc) {
            "-" => {
                let next = p.expect(Token::Atom)?;
                let super_type = types.add(Type {
                    loc: next.loc,
                    name: p.text(next.loc).to_owned(),
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

fn parse_constants(
    p: &mut Parser<'_>,
    types: &NamedArena<Type>,
    constants: &mut NamedArena<Constant>,
) -> parser::Result<()> {
    let mut buffer = Vec::new();
    while p.peek()?.token == Token::Atom {
        let next = p.consume()?;
        match p.text(next.loc) {
            "-" => {
                let next = p.expect(Token::Atom)?;
                let name = p.text(next.loc);
                let to_update = std::mem::take(&mut buffer);

                // TODO: error in the else case
                if let Some(ty) = types.get(name) {
                    for id in to_update {
                        constants[id].ty = ty;
                    }
                }
            }

            text => buffer.push(constants.add(Constant {
                loc: next.loc,
                name: text.to_owned(),
                ty: Id::none(),
            })),
        }
    }

    Result::Ok(())
}

fn parse_properties(
    p: &mut Parser<'_>,
    types: &NamedArena<Type>,
    properties: &mut NamedArena<Property>,
) -> parser::Result<()> {
    while p.peek()?.token == Token::LParen {
        p.list(|p| {
            let next = p.expect(Token::Atom)?;
            let mut prop = Property {
                loc: next.loc,
                name: p.text(next.loc).to_owned(),
                params: Vec::new(),
            };

            let mut start = 0;
            while p.peek()?.token == Token::Atom {
                let next = p.consume()?;
                match p.text(next.loc) {
                    "-" => {
                        let next = p.expect(Token::Atom)?;
                        let name = p.text(next.loc);
                        // TODO: error for missing type
                        if let Some(ty) = types.get(name) {
                            for param in &mut prop.params[start..] {
                                param.ty = ty;
                            }
                        }
                        start = prop.params.len();
                    }

                    text => {
                        prop.params.push(Param {
                            loc: next.loc,
                            name: text.to_owned(),
                            ty: Id::none(),
                        });
                    }
                }
            }

            properties.add(prop);

            Result::Ok(())
        })?;
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
                    ":constants" => parse_constants(p, &domain.types, &mut domain.constants)?,
                    ":properties" => parse_properties(p, &domain.types, &mut domain.properties)?,

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
    let text = "(define (domain foo) \
                (:types a b - object) \
                (:constants foo bar - a baz - b))";
    let domain = parse_domain(text).expect("Failed to parse domain");
    assert_eq!("foo", domain.name);

    let a = Id::new(0);
    let b = Id::new(1);
    let object = Id::new(2);
    assert_eq!(3, domain.types.len());
    assert_eq!(object, domain.types[a].super_type);
    assert_eq!(object, domain.types[b].super_type);
    assert!(!domain.types[object].super_type.exists());

    let foo = Id::new(0);
    let bar = Id::new(1);
    let baz = Id::new(2);
    assert_eq!(3, domain.constants.len());
    assert_eq!(a, domain.constants[foo].ty);
    assert_eq!(a, domain.constants[bar].ty);
    assert_eq!(b, domain.constants[baz].ty);
}

#[test]
fn test_properties() {
    let text = "(define (domain foo) \
                (:types location character) \
                (:properties (scary ?who - character) (connected ?a ?b - location)))";
    let domain = parse_domain(text).expect("Failed to parse domain");
    assert_eq!("foo", domain.name);

    let location = Id::new(0);
    let character = Id::new(1);
    assert_eq!(2, domain.types.len());
    assert!(!domain.types[location].super_type.exists());
    assert!(!domain.types[character].super_type.exists());

    let scary = Id::new(0);
    let connected = Id::new(1);
    assert_eq!(2, domain.properties.len());
    assert_eq!(1, domain.properties[scary].params.len());
    assert_eq!(character, domain.properties[scary].params[0].ty);
    assert_eq!(2, domain.properties[connected].params.len());
    for param in &domain.properties[connected].params {
        assert_eq!(location, param.ty);
    }
}
