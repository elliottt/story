mod lexer;
mod parser;
pub use lexer::Loc;

use crate::ir::{Action, Constant, Domain, Expr, Id, Ident, NamedArena, Param, Predicate, Type};
use lexer::Token;
use parser::{Error, Parser, Result};

pub fn lexer<'a>(bytes: &'a str) -> impl Iterator<Item = lexer::Lexeme> + 'a {
    lexer::Lexer::new(bytes)
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
                    ":properties" => {
                        parse_predicates(p, &domain.types, &mut domain.predicates, true)?
                    }
                    ":predicates" => {
                        parse_predicates(p, &domain.types, &mut domain.predicates, false)?
                    }

                    ":action" => parse_action(p, &mut domain)?,

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

pub fn parse_types(p: &mut Parser<'_>, types: &mut NamedArena<Type>) -> Result<()> {
    // As this is called within the context of a `list`, we terminate when we find a RParen.
    let mut buffer = Vec::new();
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

fn parse_parameters(
    p: &mut Parser<'_>,
    types: &NamedArena<Type>,
    params: &mut Vec<Param>,
) -> parser::Result<()> {
    let mut start = 0;
    while p.next_is(Token::Atom)? {
        let next = p.consume()?;
        match p.text(next.loc) {
            "-" => {
                let next = p.expect(Token::Atom)?;
                let name = p.text(next.loc);
                // TODO: error for missing type
                if let Some(ty) = types.get(name) {
                    for param in &mut params[start..] {
                        param.ty = ty;
                    }
                }
                start = params.len();
            }

            text => {
                params.push(Param {
                    loc: next.loc,
                    name: text.to_owned(),
                    ty: Id::none(),
                });
            }
        }
    }

    Result::Ok(())
}

fn parse_predicates(
    p: &mut Parser<'_>,
    types: &NamedArena<Type>,
    predicates: &mut NamedArena<Predicate>,
    is_const: bool,
) -> parser::Result<()> {
    while p.peek()?.token == Token::LParen {
        p.list(|p| {
            let next = p.expect(Token::Atom)?;
            let mut prop = Predicate {
                loc: next.loc,
                name: p.text(next.loc).to_owned(),
                params: Vec::new(),
                is_const,
            };

            parse_parameters(p, types, &mut prop.params)?;

            predicates.add(prop);

            Result::Ok(())
        })?;
    }

    Result::Ok(())
}

fn parse_ident(p: &mut Parser<'_>) -> parser::Result<Ident> {
    let lex = p.expect(Token::Atom)?;
    Result::Ok(Ident {
        loc: lex.loc,
        name: p.text(lex.loc).to_owned(),
    })
}

fn parse_expr(p: &mut Parser<'_>, domain: &mut Domain) -> parser::Result<Id<Expr>> {
    p.list(|p| {
        let next = p.expect(Token::Atom)?;

        match p.text(next.loc) {
            "not" => {
                let arg = parse_expr(p, domain)?;
                Result::Ok(domain.exprs.add(Expr::Not { arg }))
            }

            "=" => {
                let left = parse_ident(p)?;
                let right = parse_ident(p)?;
                Result::Ok(domain.exprs.add(Expr::Eq { left, right }))
            }

            "and" => {
                let mut exprs = Vec::new();
                while p.next_is(Token::LParen)? {
                    exprs.push(parse_expr(p, domain)?);
                }
                Result::Ok(domain.exprs.add(Expr::And { exprs }))
            }

            "or" => {
                let mut exprs = Vec::new();
                while p.next_is(Token::LParen)? {
                    exprs.push(parse_expr(p, domain)?);
                }
                Result::Ok(domain.exprs.add(Expr::Or { exprs }))
            }

            "when" => {
                let pred = parse_expr(p, domain)?;
                let cons = parse_expr(p, domain)?;
                Result::Ok(domain.exprs.add(Expr::When { pred, cons }))
            }

            text => {
                let pred = if let Some(pred) = domain.predicates.get(text) {
                    pred
                } else {
                    return Result::Err(Error::new(
                        next.loc,
                        format!("Unknown predicate: {}", text),
                    ));
                };

                let mut args = Vec::new();
                while p.next_is(Token::Atom)? {
                    args.push(parse_ident(p)?);
                }

                Result::Ok(domain.exprs.add(Expr::Inst { pred, args }))
            }
        }
    })
}

fn parse_action(p: &mut Parser<'_>, domain: &mut Domain) -> parser::Result<()> {
    let name = p.expect(Token::Atom)?;
    let mut action = Action {
        loc: name.loc,
        name: p.text(name.loc).to_owned(),
        params: Vec::new(),
        precond: Id::none(),
        effect: Id::none(),
    };
    while p.next_is(Token::Atom)? {
        let next = p.consume()?;
        match p.text(next.loc) {
            ":parameters" => p.list(|p| parse_parameters(p, &domain.types, &mut action.params))?,

            ":precondition" => {
                action.precond = parse_expr(p, domain)?;
            }

            ":effect" => {
                action.effect = parse_expr(p, domain)?;
            }

            _ => {
                return Result::Err(Error::new(
                    next.loc,
                    format!("Expected :parameters, :precondition, or :effect"),
                ));
            }
        }
    }

    domain.actions.add(action);

    Result::Ok(())
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
    assert_eq!(2, domain.predicates.len());
    assert_eq!(1, domain.predicates[scary].params.len());
    assert_eq!(character, domain.predicates[scary].params[0].ty);
    assert_eq!(2, domain.predicates[connected].params.len());
    for param in &domain.predicates[connected].params {
        assert_eq!(location, param.ty);
    }

    for prop in domain.predicates.iter() {
        assert!(prop.is_const);
    }
}

#[test]
fn test_predicates() {
    let text = "(define (domain foo) \
                (:types location character) \
                (:predicates (scary ?who - character) (connected ?a ?b - location)))";
    let domain = parse_domain(text).expect("Failed to parse domain");
    assert_eq!("foo", domain.name);

    let location = Id::new(0);
    let character = Id::new(1);
    assert_eq!(2, domain.types.len());
    assert!(!domain.types[location].super_type.exists());
    assert!(!domain.types[character].super_type.exists());

    let scary = Id::new(0);
    let connected = Id::new(1);
    assert_eq!(2, domain.predicates.len());
    assert_eq!(1, domain.predicates[scary].params.len());
    assert_eq!(character, domain.predicates[scary].params[0].ty);
    assert_eq!(2, domain.predicates[connected].params.len());
    for param in &domain.predicates[connected].params {
        assert_eq!(location, param.ty);
    }

    for prop in domain.predicates.iter() {
        assert!(!prop.is_const);
    }
}

#[test]
fn test_expressions() {
    let mut domain = parse_domain(
        "(define (domain :testing) \
                 (:types a b - object) \
                 (:properties (prop ?a - a ?b - b)) \
                 (:predicates (pred ?a ?b - object)))",
    )
    .expect("failed to parse testing domain");

    let prop = domain.predicates.get("prop").expect("missing prop");
    let pred = domain.predicates.get("pred").expect("missing pred");

    let id =
        parse_expr(&mut Parser::new("(prop ?a ?b)"), &mut domain).expect("Failed to parse inst");

    if let Expr::Inst { pred: p, args } = &domain.exprs[id] {
        assert_eq!(prop, *p);
        assert_eq!(2, args.len());
    } else {
        panic!("bad parse");
    }

    let id =
        parse_expr(&mut Parser::new("(pred ?a ?b)"), &mut domain).expect("Failed to parse inst");

    if let Expr::Inst { pred: p, args } = &domain.exprs[id] {
        assert_eq!(pred, *p);
        assert_eq!(2, args.len());
    } else {
        panic!("bad parse");
    }
}

#[test]
fn test_actions() {
    let mut domain = parse_domain(
        "(define (domain :testing) \
                 (:types actor location) \
                 (:predicates \
                    (at ?who - actor ?where - location)) \
                 (:action travel \
                    :parameters (?who - actor ?from ?to - location) \
                    :precondition (at ?who ?from) \
                    :effect (and (at ?who ?to) (not (at ?who ?from)))))",
    )
    .expect("failed to parse testing domain");

    let actor = domain.types.get("actor").expect("missing type");
    let location = domain.types.get("location").expect("missing type");
    assert_eq!(1, domain.predicates.len());
    assert_eq!(1, domain.actions.len());

    let travel = domain.actions.get("travel").expect("missing action");
    assert_eq!("travel", domain.actions[travel].name);
    assert_eq!(3, domain.actions[travel].params.len());
    assert_eq!(actor, domain.actions[travel].params[0].ty);
    assert_eq!(location, domain.actions[travel].params[1].ty);
    assert_eq!(location, domain.actions[travel].params[2].ty);
}
