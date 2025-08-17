use ariadne::Fmt;
use std::collections::HashMap;

mod lexer;
mod parser;
pub use lexer::Loc;

use crate::ir::{
    Action, Constant, Domain, Expr, Ident, NamedArena, Param, Predicate, Problem, Type,
};
use crate::{Context, File, arena::Id};
use lexer::Token;
use parser::{Parser, Result};

pub fn lexer<'a>(bytes: &'a str) -> impl Iterator<Item = lexer::Lexeme> + 'a {
    lexer::Lexer::new(Id::none(), bytes)
}

/// Parse a domain specification out of the bytes given.
pub fn parse_domain<'a>(
    context: &'a Context,
    file: Id<File>,
) -> std::result::Result<Domain, Vec<parser::Report<'a>>> {
    let mut parser = Parser::new(file, context.files[file].source.text());

    let mut domain = crate::ir::Domain::default();

    let res = parser.list(|p| {
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
                        return p.parse_error(case.loc, "Expected a declaration".to_owned());
                    }
                }

                Result::Ok(())
            })?;
        }

        Result::Ok(())
    });

    let errs = parser.take_errors();
    match res {
        std::result::Result::Ok(_) => {
            if errs.is_empty() {
                return std::result::Result::Ok(domain);
            }
        }
        std::result::Result::Err(_) => {}
    }

    std::result::Result::Err(errs)
}

/// Parse a problem description.
pub fn parse_problem<'a>(
    context: &'a Context,
    file: Id<File>,
    domains: &mut HashMap<String, Domain>,
) -> std::result::Result<Problem, Vec<parser::Report<'a>>> {
    let mut parser = Parser::new(file, context.files[file].source.text());
    let mut problem = crate::ir::Problem::default();

    let mut empty_domain = Domain::default();

    let res = parser.list(|p| {
        p.keyword("define")?;

        p.list(|p| {
            p.keyword("problem")?;
            problem.name = p.atom()?.to_owned();
            Result::Ok(())
        })?;

        while p.peek()?.token != Token::RParen {
            p.list(|p| {
                let case = p.expect(Token::Atom)?;
                match p.text(case.loc) {
                    ":domain" => {
                        let name = p.expect(Token::Atom)?;
                        problem.domain = p.text(name.loc).to_owned();
                    }

                    ":objects" => {
                        let domain = domains
                            .get_mut(&problem.domain)
                            .unwrap_or(&mut empty_domain);
                        parse_constants(p, &domain.types, &mut domain.constants)?;
                    }

                    ":init" => {
                        let domain = domains
                            .get_mut(&problem.domain)
                            .unwrap_or(&mut empty_domain);
                        problem.init = parse_expr_list(p, &[], domain)?;
                    }

                    ":goal" => {
                        let domain = domains
                            .get_mut(&problem.domain)
                            .unwrap_or(&mut empty_domain);
                        problem.goal = parse_expr(p, &[], domain)?;
                    }

                    _ => {
                        return p.parse_error(case.loc, "Expected a declaration");
                    }
                }
                Result::Ok(())
            })?;
        }

        // If we didn't find a domain, any expressions created won't be anchored to a domain's
        // expression store, so we don't produce anything..
        if !domains.contains_key(&problem.domain) {
            return Result::Err(());
        }

        Result::Ok(())
    });

    let errs = parser.take_errors();
    match res {
        Result::Ok(_) => {
            if errs.is_empty() {
                return std::result::Result::Ok(problem);
            }
        }
        Result::Err(_) => {}
    }

    std::result::Result::Err(errs)
}

pub fn parse_types(p: &mut Parser<'_>, types: &mut NamedArena<Type>) -> Result<()> {
    // As this is called within the context of a `list`, we terminate when we find a RParen.
    let mut buffer = Vec::new();
    while p.peek()?.token == Token::Atom {
        let next = p.consume()?;
        match p.text(next.loc) {
            "-" => {
                let next = p.expect(Token::Atom)?;
                let name = p.text(next.loc);
                let super_type = if let Some(ty) = types.get(name) {
                    ty
                } else {
                    types.add(Type {
                        loc: next.loc,
                        name: p.text(next.loc).to_owned(),
                        super_type: Id::none(),
                    })
                };
                for ty in buffer.drain(..) {
                    // Should be impossible, as we don't enter types multiple times
                    debug_assert!(!types[ty].super_type.exists());
                    types[ty].super_type = super_type;
                }
            }

            text => {
                if let Some(prev) = types.get(text) {
                    let mut e = p.error(
                        next.loc,
                        format!("Type `{}` has already been defined", text),
                    );
                    e.label(types[prev].loc, "Previously defined here");
                    e.label(next.loc, "Conflicting definition");
                } else {
                    buffer.push(types.add(Type {
                        loc: next.loc,
                        name: text.to_owned(),
                        super_type: Id::none(),
                    }))
                }
            }
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
                let ty = parse_type_ref(p, types)?;
                for id in std::mem::take(&mut buffer) {
                    constants[id].ty = ty;
                }
            }

            text => {
                let name = text.to_owned();
                if let Some(prev) = constants.iter().find(|c| c.name == text) {
                    let mut e = p.error(next.loc, "Constant redefined");
                    let a = e.label(prev.loc, "Previous definition");
                    e.label(next.loc, "Redefinition here");
                    e.note(format!(
                        "The constant named `{}` has already been defined",
                        name.fg(a)
                    ));
                } else {
                    buffer.push(constants.add(Constant {
                        loc: next.loc,
                        name,
                        ty: Id::none(),
                    }))
                }
            }
        }
    }

    Result::Ok(())
}

fn parse_type_ref(p: &mut Parser<'_>, types: &NamedArena<Type>) -> Result<Id<Type>> {
    let next = p.expect(Token::Atom)?;
    let name = p.text(next.loc);
    let id = if let Some(ty) = types.get(name) {
        ty
    } else {
        p.error(next.loc, format!("Unknown type, `{}`", name))
            .label(next.loc, "Referenced here");
        Id::none()
    };

    Result::Ok(id)
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
                let ty = parse_type_ref(p, types)?;
                for param in &mut params[start..] {
                    param.ty = ty;
                }
                start = params.len();
            }

            text => {
                if let Some(prev) = params.iter().find(|p| p.name == text) {
                    let mut e = p.error(
                        next.loc,
                        format!("Parameter `{}` has already been defined", text),
                    );
                    e.label(prev.loc, format!("Previously defined here"));
                    e.label(next.loc, format!("Conflicting declaration"));
                } else {
                    params.push(Param {
                        loc: next.loc,
                        name: text.to_owned(),
                        ty: Id::none(),
                    })
                };
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

fn parse_expr_list(
    p: &mut Parser<'_>,
    params: &[Param],
    domain: &mut Domain,
) -> parser::Result<Vec<Id<Expr>>> {
    let mut result = Vec::new();
    while p.next_is(Token::LParen)? {
        result.push(parse_expr(p, params, domain)?);
    }
    parser::Result::Ok(result)
}

fn parse_expr(
    p: &mut Parser<'_>,
    params: &[Param],
    domain: &mut Domain,
) -> parser::Result<Id<Expr>> {
    p.list(|p| {
        let next = p.expect(Token::Atom)?;

        match p.text(next.loc) {
            "not" => {
                let arg = parse_expr(p, params, domain)?;
                Result::Ok(domain.exprs.add(Expr::Not { arg }))
            }

            "=" => {
                let left = parse_ident(p)?;
                let right = parse_ident(p)?;
                Result::Ok(domain.exprs.add(Expr::Eq { left, right }))
            }

            "and" => {
                let exprs = parse_expr_list(p, params, domain)?;
                Result::Ok(domain.exprs.add(Expr::And { exprs }))
            }

            "or" => {
                let exprs = parse_expr_list(p, params, domain)?;
                Result::Ok(domain.exprs.add(Expr::Or { exprs }))
            }

            "when" => {
                let pred = parse_expr(p, params, domain)?;
                let cons = parse_expr(p, params, domain)?;
                Result::Ok(domain.exprs.add(Expr::When { pred, cons }))
            }

            text => {
                let pred = if let Some(pred) = domain.predicates.get(text) {
                    pred
                } else {
                    let name = text.to_owned();
                    let mut e = p.error(next.loc, "Unknown predicate");
                    let a = e.label(next.loc, "Referenced here");
                    e.note(format!(
                        "The predicate `{}` has not been defined",
                        name.fg(a)
                    ));
                    Id::none()
                };

                let mut end = next.loc;
                let mut args = Vec::new();
                while p.next_is(Token::Atom)? {
                    let ident = parse_ident(p)?;
                    end = ident.loc;
                    args.push(ident);
                }

                if !pred.exists() {
                    return Result::Ok(Id::none());
                }

                {
                    let pred = &domain.predicates[pred];
                    if args.len() != pred.params.len() {
                        let mut e = p.error(next.loc, "Arity mismatch");
                        let a = e.label(pred.loc, "Definition");
                        let b = e.label(next.loc.join(end), "Instantiation");
                        e.note(format!(
                            "Predicate `{}` expects {} arguments, but got {}",
                            pred.name.clone().fg(a),
                            pred.params.len().fg(a),
                            args.len().fg(b)
                        ));
                    }

                    for (arg, param) in args.iter().zip(pred.params.iter()) {
                        let arg_ty = if arg.name.starts_with('?') {
                            let Some(def) = params.iter().find(|p| p.name == arg.name) else {
                                p.error(arg.loc, "Unknown param")
                                    .label(arg.loc, "Used here");
                                continue;
                            };

                            def.ty
                        } else {
                            let Some(def) = domain.constants.iter().find(|c| c.name == arg.name)
                            else {
                                p.error(arg.loc, "Unknown constant")
                                    .label(arg.loc, "Used here");
                                continue;
                            };

                            def.ty
                        };

                        if arg_ty != param.ty {
                            let mut e = p.error(arg.loc, "Type mismatch");
                            e.label(arg.loc, format!("Has type `{}`", domain.types[arg_ty].name));
                            e.note(format!("Expected type `{}`", domain.types[param.ty].name));
                        }
                    }
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

    if let Some(prev) = domain.actions.iter().find(|a| a.name == action.name) {
        let mut e = p.error(
            action.loc,
            format!("Action `{}` has already been defined", action.name),
        );
        e.label(prev.loc, "Previously defined here");
        e.label(action.loc, "Conflicting definition");
    }

    while p.next_is(Token::Atom)? {
        let next = p.consume()?;
        match p.text(next.loc) {
            ":parameters" => p.list(|p| parse_parameters(p, &domain.types, &mut action.params))?,

            ":precondition" => {
                action.precond = parse_expr(p, &action.params, domain)?;
            }

            ":effect" => {
                action.effect = parse_expr(p, &action.params, domain)?;
            }

            _ => {
                return p.parse_error(
                    next.loc,
                    format!("Expected :parameters, :precondition, or :effect"),
                );
            }
        }
    }

    domain.actions.add(action);

    Result::Ok(())
}
