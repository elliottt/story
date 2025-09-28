use ariadne::Fmt;

mod lexer;
mod parser;
pub use lexer::Loc;

use crate::{
    File, Files,
    arena::Id,
    ir::{
        Action, Atom, Constant, Context, Effect, Expr, Ident, NamedArena, Param, Predicate, Type,
        Var, VarKind,
    },
};
use lexer::Token;
use parser::{Parser, Result};

pub fn lexer<'a>(bytes: &'a str) -> impl Iterator<Item = lexer::Lexeme> + 'a {
    lexer::Lexer::new(Id::none(), bytes)
}

/// Parse a domain specification out of the bytes given.
pub fn parse_domain<'a>(
    files: &'a Files,
    file: Id<File>,
    context: &mut Context,
) -> std::result::Result<(), Vec<parser::Report<'a>>> {
    let mut parser = Parser::new(file, files[file].source.text());

    let res = parser.list(|p| {
        p.keyword("define")?;

        p.list(|p| {
            p.keyword("domain")?;
            context.domain_name = parse_ident(p)?;
            Result::Ok(())
        })?;

        while p.peek()?.token != lexer::Token::RParen {
            p.list(|p| {
                let case = p.token(lexer::Token::Atom)?;
                match p.text(case.loc) {
                    ":types" => parse_types(p, &mut context.types)?,
                    ":constants" => parse_constants(p, context)?,
                    ":predicates" => parse_predicates(p, &context.types, &mut context.predicates)?,

                    ":action" => parse_action(p, context)?,

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
                return std::result::Result::Ok(());
            }
        }
        std::result::Result::Err(_) => {}
    }

    std::result::Result::Err(errs)
}

/// Parse a problem description.
pub fn parse_problem<'a>(
    files: &'a Files,
    file: Id<File>,
    context: &mut Context,
) -> std::result::Result<(), Vec<parser::Report<'a>>> {
    let mut parser = Parser::new(file, files[file].source.text());

    let res = parser.list(|p| {
        p.keyword("define")?;

        p.list(|p| {
            p.keyword("problem")?;
            context.problem_name = parse_ident(p)?;
            Result::Ok(())
        })?;

        while p.peek()?.token != Token::RParen {
            p.list(|p| {
                let case = p.expect(Token::Atom)?;
                match p.text(case.loc) {
                    ":domain" => {
                        let name = p.expect(Token::Atom)?;
                        if p.text(name.loc) != context.domain_name.name {
                            let text = p.text(name.loc).to_owned();
                            let mut e = p.error(name.loc, "Unknown domain");
                            if context.domain_name.loc.exists() {
                                let b = e.label(name.loc, "Referenced here");
                                let a = e.label(context.domain_name.loc, "Defined here");
                                e.note(format!(
                                    "Unknown domain `{}`, expected `{}`",
                                    text.fg(b),
                                    context.domain_name.name.clone().fg(a),
                                ));
                            } else {
                                let a = e.label(context.domain_name.loc, "Defined here");
                                e.note(format!("Unknown domain named `{}`", text.fg(a),));
                            }
                        }
                    }

                    ":objects" => {
                        parse_constants(p, context)?;
                    }

                    ":init" => {
                        context.init = parse_expr_list(p, context, &[])?;
                    }

                    ":goal" => {
                        context.goal = parse_expr(p, context, &[])?;
                    }

                    _ => {
                        return p.parse_error(case.loc, "Expected a declaration");
                    }
                }
                Result::Ok(())
            })?;
        }

        Result::Ok(())
    });

    let errs = parser.take_errors();
    match res {
        Result::Ok(_) => {
            if errs.is_empty() {
                return std::result::Result::Ok(());
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

fn parse_constants(p: &mut Parser<'_>, context: &mut Context) -> parser::Result<()> {
    let mut buffer = Vec::new();
    while p.peek()?.token == Token::Atom {
        let next = p.consume()?;
        match p.text(next.loc) {
            "-" => {
                let ty = parse_type_ref(p, &context.types)?;
                for id in std::mem::take(&mut buffer) {
                    context.constants[id].ty = ty;
                }
            }

            text => {
                let name = text.to_owned();
                if let Some(prev) = context.constants.iter().find(|c| c.name == text) {
                    let mut e = p.error(next.loc, "Constant redefined");
                    let a = e.label(prev.loc, "Previous definition");
                    e.label(next.loc, "Redefinition here");
                    e.note(format!(
                        "The constant named `{}` has already been defined",
                        name.fg(a)
                    ));
                } else {
                    buffer.push(context.constants.add(Constant {
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
) -> parser::Result<()> {
    while p.peek()?.token == Token::LParen {
        p.list(|p| {
            let next = p.expect(Token::Atom)?;
            let mut prop = Predicate {
                loc: next.loc,
                name: p.text(next.loc).to_owned(),
                params: Vec::new(),
                is_const: false,
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
    context: &mut Context,
    params: &[Param],
) -> parser::Result<Vec<Id<Expr>>> {
    let mut result = Vec::new();
    while p.next_is(Token::LParen)? {
        result.push(parse_expr(p, context, params)?);
    }
    parser::Result::Ok(result)
}

// Parse and validate an atomic formula.
fn parse_atom(
    p: &mut Parser<'_>,
    context: &mut Context,
    params: &[Param],
    next: lexer::Lexeme,
) -> parser::Result<Option<Atom>> {
    let text = p.text(next.loc);
    let pred = if let Some(pred) = context.predicates.get(text) {
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
        let ident = parse_var(p, context, params)?;
        end = ident.loc;
        args.push(ident);
    }

    if !pred.exists() {
        return Result::Ok(None);
    }

    {
        let pred = &context.predicates[pred];
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
            let arg_ty = match arg.kind {
                VarKind::Param { ix } => {
                    if ix == VarKind::INVALID_PARAM {
                        continue;
                    }
                    params[usize::from(ix)].ty
                }
                VarKind::Const { id } => {
                    if !id.exists() {
                        continue;
                    }
                    context.constants[id].ty
                }
            };

            if arg_ty.exists() && param.ty.exists() && arg_ty != param.ty {
                let mut e = p.error(arg.loc, "Type mismatch");
                let a = e.next_color();
                let b = e.next_color();
                let expected_ty = context.types[param.ty].name.clone().fg(a);
                let actual_ty = context.types[arg_ty].name.clone().fg(b);
                e.label_with_color(param.loc, a, format!("Has type `{}`", expected_ty));
                e.label_with_color(arg.loc, b, format!("Has type `{}`", actual_ty));
                e.note(format!(
                    "Expected type `{}`, but found type `{}`",
                    expected_ty, actual_ty,
                ));
            }
        }
    }

    Result::Ok(Some(Atom { pred, args }))
}

fn parse_var(p: &mut Parser<'_>, context: &mut Context, params: &[Param]) -> parser::Result<Var> {
    let lex = p.expect(Token::Atom)?;
    let name = p.text(lex.loc);
    let kind = if name.starts_with('?') {
        let ix = if let Some(ix) = params.iter().rposition(|p| p.name == name) {
            ix.try_into().unwrap()
        } else {
            p.error(lex.loc, "Unknown param")
                .label(lex.loc, "Used here");
            VarKind::INVALID_PARAM
        };
        VarKind::Param { ix }
    } else {
        let id = if let Some(ix) = context.constants.iter().position(|c| c.name == name) {
            Id::new(ix)
        } else {
            p.error(lex.loc, "Unknown constant")
                .label(lex.loc, "Used here");
            Id::none()
        };
        VarKind::Const { id }
    };

    Result::Ok(Var { loc: lex.loc, kind })
}

fn parse_expr(
    p: &mut Parser<'_>,
    context: &mut Context,
    params: &[Param],
) -> parser::Result<Id<Expr>> {
    p.list(|p| {
        let next = p.expect(Token::Atom)?;

        match p.text(next.loc) {
            "not" => {
                let arg = parse_expr(p, context, params)?;
                Result::Ok(context.exprs.add(Expr::Not { arg }))
            }

            "=" => {
                let left = parse_var(p, context, params)?;
                let right = parse_var(p, context, params)?;
                Result::Ok(context.exprs.add(Expr::Eq { left, right }))
            }

            "and" => {
                let exprs = parse_expr_list(p, context, params)?;
                Result::Ok(context.exprs.add(Expr::And { exprs }))
            }

            "or" => {
                let exprs = parse_expr_list(p, context, params)?;
                Result::Ok(context.exprs.add(Expr::Or { exprs }))
            }

            // Desugar `(imply p q)` as `(or (not p) q)`
            "imply" => {
                let pred = parse_expr(p, context, params)?;
                let cons = parse_expr(p, context, params)?;
                let exprs = vec![context.exprs.add(Expr::Not { arg: pred }), cons];
                Result::Ok(context.exprs.add(Expr::Or { exprs }))
            }

            _ => {
                if let Some(atom) = parse_atom(p, context, params, next)? {
                    Result::Ok(context.exprs.add(Expr::Atom { atom }))
                } else {
                    Result::Ok(Id::none())
                }
            }
        }
    })
}

fn parse_effect(
    p: &mut Parser<'_>,
    context: &mut Context,
    params: &[Param],
) -> parser::Result<Id<Effect>> {
    p.list(|p| {
        let next = p.expect(Token::Atom)?;
        match p.text(next.loc) {
            "when" => {
                let cond = parse_expr(p, context, params)?;
                let effect = parse_effect(p, context, params)?;
                Result::Ok(context.effects.add(Effect::When { cond, effect }))
            }
            "not" => p.list(|p| {
                let next = p.expect(Token::Atom)?;
                if let Some(atom) = parse_atom(p, context, params, next)? {
                    Result::Ok(context.effects.add(Effect::Atom { neg: true, atom }))
                } else {
                    Result::Ok(Id::none())
                }
            }),
            "and" => {
                let mut effects = Vec::new();
                while p.next_is(Token::LParen)? {
                    effects.push(parse_effect(p, context, params)?);
                }
                Result::Ok(context.effects.add(Effect::And { effects }))
            }
            _ => {
                if let Some(atom) = parse_atom(p, context, params, next)? {
                    Result::Ok(context.effects.add(Effect::Atom { neg: false, atom }))
                } else {
                    Result::Ok(Id::none())
                }
            }
        }
    })
}

fn parse_action(p: &mut Parser<'_>, context: &mut Context) -> parser::Result<()> {
    let name = p.expect(Token::Atom)?;
    let mut params = Vec::new();
    let mut precond = Id::none();
    let mut effect = Id::none();
    let mut action = Action {
        loc: name.loc,
        name: p.text(name.loc).to_owned(),
        effect: Id::none(),
    };

    if let Some(prev) = context.actions.iter().find(|a| a.name == action.name) {
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
            ":parameters" => {
                if params.is_empty() {
                    p.list(|p| parse_parameters(p, &context.types, &mut params))?
                }
            }

            ":precondition" => {
                if !precond.exists() {
                    precond = parse_expr(p, context, &params)?;
                }
            }

            ":effect" => {
                if !effect.exists() {
                    effect = parse_effect(p, context, &params)?;
                }
            }

            _ => {
                return p.parse_error(
                    next.loc,
                    format!("Expected :parameters, :precondition, or :effect"),
                );
            }
        }
    }

    let when = context.effects.add(Effect::When {
        cond: precond,
        effect,
    });
    action.effect = context.effects.add(Effect::Forall { params, body: when });

    context.actions.add(action);

    Result::Ok(())
}
