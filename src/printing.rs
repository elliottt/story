use pretty::BoxDoc;

use crate::ir::{Context, Expr, Ident, Param, Predicate};

pub fn print_context(context: &Context) -> String {
    let mut doc = BoxDoc::nil();

    for p in context.predicates.iter() {
        doc = doc.append(BoxDoc::concat([
            p.to_doc(context),
            BoxDoc::hardline(),
            BoxDoc::hardline(),
        ]));
    }

    for e in context.exprs.iter() {
        doc = doc.append(BoxDoc::concat([e.to_doc(context), BoxDoc::hardline()]));
    }

    let mut w = Vec::new();
    doc.render(80, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

fn apply<'a, 't, T: Pretty + 'static>(
    context: &Context,
    fun: &str,
    ts: impl IntoIterator<Item = &'t T>,
) -> BoxDoc<'a> {
    let mut args = BoxDoc::nil();
    for p in ts.into_iter() {
        args = args.append(BoxDoc::line()).append(p.to_doc(context));
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
            apply(context, &self.name, &self.params),
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
            Expr::Inst { pred, args } => apply(context, &context.predicates[*pred].name, args),

            Expr::Not { arg } => apply(context, "not", [&context.exprs[*arg]]),
            Expr::Eq { left, right } => apply(context, "=", [left, right]),
            Expr::And { exprs } => apply(
                context,
                "and",
                exprs.iter().copied().map(|e| &context.exprs[e]),
            ),
            Expr::Or { exprs } => apply(
                context,
                "or",
                exprs.iter().copied().map(|e| &context.exprs[e]),
            ),
        }
    }
}
