use pretty::BoxDoc;

use crate::ir::{
    Action, Atom, Constant, Context, Effect, Expr, Ident, Param, Predicate, Var, VarKind,
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

    doc = doc.append(BoxDoc::concat([
        BoxDoc::hardline(),
        BoxDoc::text("; Init"),
        BoxDoc::hardline(),
        c.effects[c.init].to_doc(c, &mut ps),
        BoxDoc::hardline(),
        BoxDoc::hardline(),
        BoxDoc::text("; Goal"),
        BoxDoc::hardline(),
        c.exprs[c.goal].to_doc(c, &mut ps),
    ]));

    let mut w = Vec::new();
    doc.render(80, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

pub fn show(c: &Context, e: &impl Pretty) -> String {
    let mut ps = Vec::with_capacity(2);
    let doc = e.to_doc(c, &mut ps);
    let mut w = Vec::new();
    doc.render(80, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

fn list<'a>(ts: impl IntoIterator<Item = BoxDoc<'a>>) -> BoxDoc<'a> {
    let args = BoxDoc::intersperse(ts, BoxDoc::line()).append(BoxDoc::text(")"));
    BoxDoc::text("(").append(BoxDoc::group(args).nest(2))
}

fn apply_with_name<'a>(fun: BoxDoc<'a>, ts: impl IntoIterator<Item = BoxDoc<'a>>) -> BoxDoc<'a> {
    let mut args = BoxDoc::nil();
    for p in ts.into_iter() {
        args = args.append(BoxDoc::line()).append(p);
    }
    args = args.append(BoxDoc::text(")"));

    BoxDoc::concat([BoxDoc::text("("), fun, BoxDoc::group(args).nest(2)])
}

fn apply<'a>(fun: &str, ts: impl IntoIterator<Item = BoxDoc<'a>>) -> BoxDoc<'a> {
    apply_with_name(BoxDoc::text(fun.to_owned()), ts)
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
            if self.is_negated {
                BoxDoc::text(", negated")
            } else {
                BoxDoc::nil()
            },
            BoxDoc::hardline(),
            apply(&self.name, self.params.iter().map(|p| p.to_doc(c, ps))),
        ])
    }
}

impl Pretty for Constant {
    fn to_doc<'a>(&self, _c: &Context, _ps: &mut Env<'a>) -> BoxDoc<'a> {
        BoxDoc::text(self.name.clone())
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

impl Pretty for Atom {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        let pred = &c.predicates[self.pred];
        let fun = if pred.is_negated {
            BoxDoc::text(format!("[negated]{}", pred.name))
        } else {
            BoxDoc::text(pred.name.clone())
        };
        apply_with_name(fun, self.args.iter().map(|a| a.to_doc(c, ps)))
    }
}

impl Pretty for Expr {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        match self {
            Expr::Atom { neg, atom } if *neg => apply("not", [c.atoms[*atom].to_doc(c, ps)]),
            Expr::Atom { atom, .. } => c.atoms[*atom].to_doc(c, ps),
            Expr::Eq { neg, left, right } if *neg => apply(
                "not",
                [apply("=", [left.to_doc(c, ps), right.to_doc(c, ps)])],
            ),
            Expr::Eq { left, right, .. } => apply("=", [left.to_doc(c, ps), right.to_doc(c, ps)]),
            Expr::And { exprs } => apply("and", exprs.iter().map(|e| c.exprs[*e].to_doc(c, ps))),
            Expr::True => BoxDoc::text("#t"),
            Expr::False => BoxDoc::text("#f"),
        }
    }
}

impl Pretty for Effect {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        match self {
            Effect::And { effects } => {
                apply("and", effects.iter().map(|e| c.effects[*e].to_doc(c, ps)))
            }
            Effect::Intends { actor, neg, atom } if *neg => apply(
                "intends",
                [
                    actor.to_doc(c, ps),
                    apply("not", [c.atoms[*atom].to_doc(c, ps)]),
                ],
            ),
            Effect::Intends { actor, atom, .. } => apply(
                "intends",
                [actor.to_doc(c, ps), c.atoms[*atom].to_doc(c, ps)],
            ),
            Effect::Atom { neg, atom } if *neg => apply("not", [c.atoms[*atom].to_doc(c, ps)]),
            Effect::Atom { atom, .. } => c.atoms[*atom].to_doc(c, ps),
            Effect::True => BoxDoc::text("#t"),
        }
    }
}

impl Pretty for Action {
    fn to_doc<'a>(&self, c: &Context, ps: &mut Env<'a>) -> BoxDoc<'a> {
        let mut params = Vec::new();

        let params_label = if self.inst.is_empty() {
            for p in &self.params {
                params.push(BoxDoc::intersperse(
                    [
                        BoxDoc::text(p.name.clone()),
                        BoxDoc::text("-"),
                        BoxDoc::text(c.types[p.ty].name.clone()),
                    ],
                    BoxDoc::space(),
                ));
            }

            BoxDoc::text(":parameters")
        } else {
            for (p, v) in self.params.iter().zip(self.inst.iter()) {
                params.push(BoxDoc::intersperse(
                    [
                        BoxDoc::text(p.name.clone()),
                        BoxDoc::text("="),
                        BoxDoc::text(c.constants[*v].name.clone()),
                    ],
                    BoxDoc::space(),
                ));
            }

            BoxDoc::text(":instantiation")
        };

        BoxDoc::concat([
            BoxDoc::hardline(),
            BoxDoc::text("; Action"),
            BoxDoc::hardline(),
            apply(
                ":action",
                [
                    BoxDoc::text(self.name.clone()),
                    BoxDoc::concat([params_label, BoxDoc::line(), list(params)]),
                    BoxDoc::concat([
                        BoxDoc::text(":precondition"),
                        BoxDoc::line(),
                        c.exprs[self.pre].to_doc(c, ps),
                    ]),
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
