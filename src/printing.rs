use pretty::BoxDoc;

use crate::ir::{
    Action, Constant, Context, Effect, Expr, Id, Ident, Param, Predicate, Var, VarKind,
};

pub fn print_context(c: &Context) -> String {
    let mut doc = BoxDoc::nil();
    let mut ps = Vec::with_capacity(2);

    for p in c.predicates.iter() {
        doc = doc.append(BoxDoc::concat([
            p.to_doc(c, &mut ps),
            BoxDoc::hardline(),
            BoxDoc::hardline(),
        ]));
    }

    for action in c.actions.iter() {
        doc = BoxDoc::concat([doc, action.to_doc(c, &mut ps), BoxDoc::hardline()]);
        ps.pop();
    }

    let mut w = Vec::new();
    doc.render(80, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

fn list<'a>(ts: impl IntoIterator<Item = BoxDoc<'a>>) -> BoxDoc<'a> {
    let args = BoxDoc::intersperse(ts, BoxDoc::line()).append(BoxDoc::text(")"));
    BoxDoc::text("(").append(BoxDoc::group(args).nest(2))
}

fn apply<'a>(fun: &str, ts: impl IntoIterator<Item = BoxDoc<'a>>) -> BoxDoc<'a> {
    let mut args = BoxDoc::nil();
    for p in ts.into_iter() {
        args = args.append(BoxDoc::line()).append(p);
    }
    args = args.append(BoxDoc::text(")"));

    BoxDoc::concat([
        BoxDoc::text("("),
        BoxDoc::text(fun.to_owned()),
        BoxDoc::group(args).nest(2),
    ])
}

pub type Env<'a> = Vec<Vec<BoxDoc<'a>>>;

pub trait Pretty {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a>;
}

impl Pretty for Predicate {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        BoxDoc::concat([
            BoxDoc::text("; "),
            if self.is_const {
                BoxDoc::text("property")
            } else {
                BoxDoc::text("predicate")
            },
            BoxDoc::hardline(),
            apply(&self.name, self.params.iter().map(|p| p.to_doc(c, ps))),
        ])
    }
}

impl Pretty for Ident {
    fn to_doc<'a>(&self, _c: &Context, _ps: &mut Env<'a>) -> BoxDoc<'a> {
        BoxDoc::text(self.name.clone())
    }
}

impl Pretty for Param {
    fn to_doc<'a>(&self, c: &Context, _ps: &mut Env<'a>) -> BoxDoc<'a> {
        let name = BoxDoc::text(self.name.clone());
        if self.ty.exists() {
            BoxDoc::concat([
                name,
                BoxDoc::space(),
                BoxDoc::text("-"),
                BoxDoc::space(),
                BoxDoc::text(c.types[self.ty].name.clone()),
            ])
            .group()
        } else {
            name
        }
    }
}

impl Pretty for Var {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        match self.kind {
            VarKind::Param { ix } => {
                let mut ix: usize = ix.into();
                for scope in ps.iter().rev() {
                    if ix > scope.len() {
                        ix -= scope.len();
                        continue;
                    }

                    return scope[usize::from(ix)].clone();
                }
                BoxDoc::text(format!("??{}", ix))
            }
            VarKind::Const { id } => BoxDoc::text(c.constants[id].name.clone()),
        }
    }
}

fn pp_inst<'a, T: Pretty>(
    c: &Context,
    ps: &mut Env<'a>,
    args: &[Id<Constant>],
    body: &T,
) -> BoxDoc<'a> {
    let arg_names = args
        .iter()
        .map(|k| BoxDoc::text(c.constants[*k].name.clone()))
        .collect();

    ps.push(arg_names);
    let doc = body.to_doc(c, ps);
    ps.pop();
    doc
}

fn pp_quantifier<'a, T: Pretty>(
    c: &Context,
    ps: &mut Env<'a>,
    name: &str,
    params: &[Param],
    body: &T,
) -> BoxDoc<'a> {
    let mut param_names = Vec::with_capacity(params.len());

    let params_doc = list(params.iter().map(|p| {
        let name = BoxDoc::text(p.name.clone());
        param_names.push(name.clone());
        p.to_doc(c, ps)
    }));

    ps.push(param_names);
    let doc = apply(name, [params_doc, body.to_doc(c, ps)]);
    ps.pop();
    doc
}

impl Pretty for Expr {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        match self {
            Expr::Atom { pred, args } => apply(
                &c.predicates[*pred].name,
                args.iter().map(|a| a.to_doc(c, ps)),
            ),

            Expr::Inst { args, body } => pp_inst(c, ps, args, &c.exprs[*body]),

            Expr::Forall { params, body } => {
                pp_quantifier(c, ps, "forall", params, &c.exprs[*body])
            }

            Expr::Exists { params, body } => {
                pp_quantifier(c, ps, "exists", params, &c.exprs[*body])
            }

            Expr::Not { arg } => apply("not", [c.exprs[*arg].to_doc(c, ps)]),
            Expr::Eq { left, right } => apply("=", [left.to_doc(c, ps), right.to_doc(c, ps)]),
            Expr::And { exprs } => apply("and", exprs.iter().map(|e| c.exprs[*e].to_doc(c, ps))),
            Expr::Or { exprs } => apply("or", exprs.iter().map(|e| c.exprs[*e].to_doc(c, ps))),
            Expr::True => BoxDoc::text("#t"),
            Expr::False => BoxDoc::text("#f"),
        }
    }
}

impl Pretty for Effect {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        match self {
            Effect::Inst { args, body } => pp_inst(c, ps, args, &c.effects[*body]),

            Effect::Forall { params, body } => {
                pp_quantifier(c, ps, "forall", params, &c.effects[*body])
            }

            Effect::And { effects } => {
                apply("and", effects.iter().map(|e| c.effects[*e].to_doc(c, ps)))
            }
            Effect::Atom { neg, pred, args } if *neg => {
                let pred = apply(
                    &c.predicates[*pred].name,
                    args.iter().map(|a| a.to_doc(c, ps)),
                );
                apply("not", [pred])
            }
            Effect::Atom { pred, args, .. } => apply(
                &c.predicates[*pred].name,
                args.iter().map(|a| a.to_doc(c, ps)),
            ),
            Effect::When { cond, effect } => apply(
                "when",
                [
                    c.exprs[*cond].to_doc(c, ps),
                    c.effects[*effect].to_doc(c, ps),
                ],
            ),
            Effect::True => BoxDoc::text("#t"),
        }
    }
}

impl Pretty for Action {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        BoxDoc::concat([
            BoxDoc::hardline(),
            BoxDoc::text("; Action"),
            BoxDoc::hardline(),
            apply(
                ":action",
                [
                    BoxDoc::text(self.name.clone()),
                    BoxDoc::concat([
                        BoxDoc::text(":effect"),
                        BoxDoc::line(),
                        c.effects[self.effect].to_doc(c, ps),
                    ])
                    .nest(2),
                ],
            ),
        ])
    }
}
