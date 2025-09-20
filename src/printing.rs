use pretty::BoxDoc;

use crate::ir::{Action, Context, Effect, Expr, Ident, Param, Predicate, Var, VarKind};

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

    doc = BoxDoc::concat([doc, BoxDoc::text("; Expressions"), BoxDoc::hardline()]);
    for e in c.exprs.iter() {
        doc = BoxDoc::concat([doc, e.to_doc(c, &mut ps), BoxDoc::hardline()])
    }

    doc = BoxDoc::concat([
        doc,
        BoxDoc::hardline(),
        BoxDoc::text("; Effects"),
        BoxDoc::hardline(),
    ]);
    for e in c.effects.iter() {
        doc = BoxDoc::concat([doc, e.to_doc(c, &mut ps), BoxDoc::hardline()])
    }

    for action in c.actions.iter() {
        ps.push(&action.params);
        doc = BoxDoc::concat([doc, BoxDoc::hardline(), action.to_doc(c, &mut ps)]);
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

pub trait Pretty {
    fn to_doc<'a, 'c>(&self, c: &'c Context, ps: &mut Vec<&'c [Param]>) -> BoxDoc<'a>;
}

impl Pretty for Predicate {
    fn to_doc<'a, 'c>(&self, c: &'c Context, ps: &mut Vec<&'c [Param]>) -> BoxDoc<'a> {
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
    fn to_doc<'a, 'c>(&self, _c: &Context, _ps: &mut Vec<&'c [Param]>) -> BoxDoc<'a> {
        BoxDoc::text(self.name.clone())
    }
}

impl Pretty for Param {
    fn to_doc<'a, 'c>(&self, c: &Context, _ps: &mut Vec<&'c [Param]>) -> BoxDoc<'a> {
        BoxDoc::group(BoxDoc::concat([
            BoxDoc::text(self.name.clone()),
            BoxDoc::space(),
            BoxDoc::text("-"),
            BoxDoc::space(),
            BoxDoc::text(c.types[self.ty].name.clone()),
        ]))
    }
}

impl Pretty for Var {
    fn to_doc<'a, 'c>(&self, c: &'c Context, ps: &mut Vec<&'c [Param]>) -> BoxDoc<'a> {
        match self.kind {
            VarKind::Param { ix } => {
                let mut ix: usize = ix.into();
                for scope in ps.iter().rev().copied() {
                    if ix > scope.len() {
                        ix -= scope.len();
                        continue;
                    }

                    let rel = scope.len() - 1 - ix;
                    let p = &scope[rel];
                    return BoxDoc::text(p.name.clone());
                }
                BoxDoc::text(format!("??{}", ix))
            }
            VarKind::Const { id } => BoxDoc::text(c.constants[id].name.clone()),
        }
    }
}

impl Pretty for Expr {
    fn to_doc<'a, 'c>(&self, c: &'c Context, ps: &mut Vec<&'c [Param]>) -> BoxDoc<'a> {
        match self {
            Expr::Atom { pred, args } => apply(
                &c.predicates[*pred].name,
                args.iter().map(|a| a.to_doc(c, ps)),
            ),

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
    fn to_doc<'a, 'c>(&self, c: &'c Context, ps: &mut Vec<&'c [Param]>) -> BoxDoc<'a> {
        match self {
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
    fn to_doc<'a, 'c>(&self, c: &'c Context, ps: &mut Vec<&'c [Param]>) -> BoxDoc<'a> {
        BoxDoc::concat([
            BoxDoc::hardline(),
            BoxDoc::text("; Action"),
            BoxDoc::hardline(),
            apply(
                ":action",
                [
                    BoxDoc::text(self.name.clone()),
                    if self.params.len() != self.args.len() {
                        BoxDoc::concat([
                            BoxDoc::text(":parameters"),
                            BoxDoc::line(),
                            list(self.params.iter().map(|p| p.to_doc(c, ps))),
                        ])
                    } else {
                        BoxDoc::concat([
                            BoxDoc::text(":arguments"),
                            BoxDoc::line(),
                            list(
                                self.args
                                    .iter()
                                    .map(|k| BoxDoc::text(c.constants[*k].name.clone())),
                            ),
                        ])
                    }
                    .nest(2),
                    BoxDoc::concat([
                        BoxDoc::text(":precondition"),
                        BoxDoc::line(),
                        c.exprs[self.precond].to_doc(c, ps),
                    ])
                    .nest(2),
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
