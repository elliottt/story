use pretty::BoxDoc;

use crate::ir::{Action, Context, Effect, Expr, Ident, Param, Predicate};

pub fn print_context(context: &Context) -> String {
    let mut doc = BoxDoc::nil();

    for p in context.predicates.iter() {
        doc = doc.append(BoxDoc::concat([
            p.to_doc(context),
            BoxDoc::hardline(),
            BoxDoc::hardline(),
        ]));
    }

    doc = BoxDoc::concat([doc, BoxDoc::text("; Expressions"), BoxDoc::hardline()]);
    for e in context.exprs.iter() {
        doc = BoxDoc::concat([doc, e.to_doc(context), BoxDoc::hardline()])
    }

    doc = BoxDoc::concat([
        doc,
        BoxDoc::hardline(),
        BoxDoc::text("; Effects"),
        BoxDoc::hardline(),
    ]);
    for e in context.effects.iter() {
        doc = BoxDoc::concat([doc, e.to_doc(context), BoxDoc::hardline()])
    }

    for action in context.actions.iter() {
        doc = BoxDoc::concat([doc, BoxDoc::hardline(), action.to_doc(context)]);
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

pub trait Pretty {
    fn to_doc<'a>(&self, context: &Context) -> BoxDoc<'a>;
}

impl Pretty for Predicate {
    fn to_doc<'a>(&self, context: &Context) -> BoxDoc<'a> {
        BoxDoc::concat([
            BoxDoc::text("; "),
            if self.is_const {
                BoxDoc::text("property")
            } else {
                BoxDoc::text("predicate")
            },
            BoxDoc::hardline(),
            apply(&self.name, self.params.iter().map(|p| p.to_doc(context))),
        ])
    }
}

impl Pretty for Ident {
    fn to_doc<'a>(&self, _context: &Context) -> BoxDoc<'a> {
        BoxDoc::text(self.name.clone())
    }
}

impl Pretty for Param {
    fn to_doc<'a>(&self, context: &Context) -> BoxDoc<'a> {
        BoxDoc::group(BoxDoc::concat([
            BoxDoc::text(self.name.clone()),
            BoxDoc::space(),
            BoxDoc::text("-"),
            BoxDoc::space(),
            BoxDoc::text(context.types[self.ty].name.clone()),
        ]))
    }
}

impl Pretty for Expr {
    fn to_doc<'a>(&self, context: &Context) -> BoxDoc<'a> {
        match self {
            Expr::Atom { pred, args } => apply(
                &context.predicates[*pred].name,
                args.iter().map(|a| a.to_doc(context)),
            ),

            Expr::Not { arg } => apply("not", [context.exprs[*arg].to_doc(context)]),
            Expr::Eq { left, right } => apply("=", [left.to_doc(context), right.to_doc(context)]),
            Expr::And { exprs } => apply(
                "and",
                exprs.iter().map(|e| context.exprs[*e].to_doc(context)),
            ),
            Expr::Or { exprs } => apply(
                "or",
                exprs.iter().map(|e| context.exprs[*e].to_doc(context)),
            ),
        }
    }
}

impl Pretty for Effect {
    fn to_doc<'a>(&self, context: &Context) -> BoxDoc<'a> {
        match self {
            Effect::And { effects } => apply(
                "and",
                effects.iter().map(|e| context.effects[*e].to_doc(context)),
            ),
            Effect::Atom { neg, pred, args } if *neg => {
                let pred = apply(
                    &context.predicates[*pred].name,
                    args.iter().map(|a| a.to_doc(context)),
                );
                apply("not", [pred])
            }
            Effect::Atom { pred, args, .. } => apply(
                &context.predicates[*pred].name,
                args.iter().map(|a| a.to_doc(context)),
            ),
            Effect::When { cond, effect } => apply(
                "when",
                [
                    context.exprs[*cond].to_doc(context),
                    context.effects[*effect].to_doc(context),
                ],
            ),
            Effect::True => apply("true", []),
        }
    }
}

impl Pretty for Action {
    fn to_doc<'a>(&self, c: &Context) -> BoxDoc<'a> {
        BoxDoc::concat([
            BoxDoc::hardline(),
            BoxDoc::text("; Action"),
            BoxDoc::hardline(),
            apply(
                ":action",
                [
                    BoxDoc::text(self.name.clone()),
                    BoxDoc::concat([
                        BoxDoc::text(":parameters"),
                        BoxDoc::line(),
                        list(self.params.iter().map(|p| p.to_doc(c))),
                    ])
                    .nest(2),
                    BoxDoc::concat([
                        BoxDoc::text(":precondition"),
                        BoxDoc::line(),
                        c.exprs[self.precond].to_doc(c),
                    ]).nest(2),
                    BoxDoc::concat([
                        BoxDoc::text(":effect"),
                        BoxDoc::line(),
                        c.effects[self.effect].to_doc(c),
                    ]).nest(2),
                ],
            ),
        ])
    }
}
