use crate::ir::{And, Atom, Constant, Context, Effect, Expr, Id, Param, Predicate, Var, VarKind};
use std::collections::HashMap;

type Env = Vec<Vec<Id<Constant>>>;

pub fn simplify(c: &mut Context, effect: Id<Effect>) -> Id<Effect> {
    Simplify::new(c).effect(c, effect)
}

struct Simplify {
    t: Id<Expr>,
    f: Id<Expr>,
    env: Env,
    atoms: HashMap<Id<Predicate>, HashMap<Vec<Id<Constant>>, Id<Atom>>>,
}

impl Simplify {
    fn new(c: &mut Context) -> Self {
        Self {
            t: c.exprs.add(Expr::True),
            f: c.exprs.add(Expr::False),
            env: Vec::new(),
            atoms: HashMap::new(),
        }
    }

    fn with_args<T>(&mut self, args: &[Id<Constant>], body: impl FnOnce(&mut Self) -> T) -> T {
        self.env.push(Vec::from(args));
        let res = body(self);
        self.env.pop();
        res
    }

    fn with_params<T>(&mut self, params: &[Param], body: impl FnOnce(&mut Self) -> T) -> T {
        self.env
            .push(std::iter::repeat_n(Id::none(), params.len()).collect());
        let res = body(self);
        self.env.pop();
        res
    }

    fn param(&self, ix: u16) -> Id<Constant> {
        let mut ix = usize::from(ix);
        for scope in self.env.iter() {
            if scope.len() < ix {
                ix -= scope.len();
                continue;
            }

            return scope[ix];
        }
        Id::none()
    }

    fn lookup(&self, var: &Var) -> Id<Constant> {
        match var.kind {
            VarKind::Param { ix } => self.param(ix),
            VarKind::Const { id } => id,
        }
    }

    fn cache_atom(&mut self, c: &mut Context, pred: Id<Predicate>, args: Vec<Var>) -> Id<Atom> {
        let preds = self.atoms.entry(pred).or_default();
        let key = Vec::from_iter(args.iter().map(|var| {
            let VarKind::Const { id } = var.kind else {
                panic!("All atoms should be instantiated at this point")
            };
            id
        }));

        if let Some(id) = preds.get(&key) {
            *id
        } else {
            let id = c.atoms.add(Atom { pred, args });
            preds.insert(key, id);
            id
        }
    }

    /// Fully instantiate an atom, if possible.
    fn atom(&mut self, c: &mut Context, id: Id<Atom>) -> Id<Atom> {
        let Atom { pred, args } = &c.atoms[id];
        let mut changed = false;
        let args = Vec::from_iter(args.into_iter().map(|var| match var.kind {
            VarKind::Param { ix } => {
                let id = self.param(ix);
                if !id.exists() {
                    var.clone()
                } else {
                    changed = true;
                    Var {
                        loc: var.loc,
                        kind: VarKind::Const { id },
                    }
                }
            }
            VarKind::Const { .. } => var.clone(),
        }));

        self.cache_atom(c, *pred, args)
    }

    fn effect(&mut self, c: &mut Context, id: Id<Effect>) -> Id<Effect> {
        let eff = std::mem::replace(&mut c.effects[id], Effect::True);
        let new = match &eff {
            Effect::Inst { args, body } => {
                let sbody = self.with_args(args, |s| s.effect(c, *body));
                match c.effects[sbody] {
                    Effect::True => sbody,
                    _ => {
                        if sbody == *body {
                            id
                        } else {
                            c.effects.add(Effect::Inst {
                                args: args.clone(),
                                body: sbody,
                            })
                        }
                    }
                }
            }

            Effect::Forall { params, body } => {
                let sbody = self.with_params(params, |s| s.effect(c, *body));
                match c.effects[sbody] {
                    Effect::True => sbody,
                    _ => {
                        if sbody == *body {
                            id
                        } else {
                            c.effects.add(Effect::Forall {
                                params: params.clone(),
                                body: sbody,
                            })
                        }
                    }
                }
            }

            Effect::Exists { params, body } => {
                let sbody = self.with_params(params, |s| s.effect(c, *body));
                match c.effects[sbody] {
                    Effect::True => sbody,
                    _ => {
                        if sbody == *body {
                            id
                        } else {
                            c.effects.add(Effect::Forall {
                                params: params.clone(),
                                body: sbody,
                            })
                        }
                    }
                }
            }

            Effect::Atom { neg, atom } => {
                let satom = self.atom(c, *atom);
                if satom == *atom {
                    id
                } else {
                    c.effects.add(Effect::Atom {
                        neg: *neg,
                        atom: satom,
                    })
                }
            }

            Effect::When { cond, effect } => {
                let scond = self.expr(c, *cond);
                let seffect = self.effect(c, *effect);
                match c.exprs[scond] {
                    Expr::True => seffect,
                    Expr::False => c.effects.add(Effect::True),
                    _ => {
                        if scond == *cond && seffect == *effect {
                            id
                        } else {
                            c.effects.add(Effect::When {
                                cond: scond,
                                effect: seffect,
                            })
                        }
                    }
                }
            }

            Effect::And { effects } => {
                let mut changed = false;
                let seffects = Vec::from_iter(effects.iter().filter_map(|e| {
                    let new = self.effect(c, *e);
                    if matches!(c.effects[new], Effect::True) {
                        changed = true;
                        None
                    } else {
                        changed = changed || new != *e;
                        Some(new)
                    }
                }));
                if !changed {
                    id
                } else {
                    Effect::and(c, seffects)
                }
            }

            Effect::True => id,
        };
        c.effects[id] = eff;
        new
    }

    fn expr(&mut self, c: &mut Context, id: Id<Expr>) -> Id<Expr> {
        let expr = std::mem::replace(&mut c.exprs[id], Expr::True);

        let new = match &expr {
            Expr::Inst { args, body } => {
                let sbody = self.with_args(args, |s| s.expr(c, *body));
                if sbody == *body {
                    id
                } else {
                    c.exprs.add(Expr::Inst {
                        args: args.clone(),
                        body: sbody,
                    })
                }
            }

            Expr::Forall { params, body } => {
                let sbody = self.with_params(params, |s| s.expr(c, *body));
                if sbody == *body {
                    id
                } else {
                    c.exprs.add(Expr::Forall {
                        params: params.clone(),
                        body: sbody,
                    })
                }
            }

            Expr::Exists { params, body } => {
                let sbody = self.with_params(params, |s| s.expr(c, *body));
                if sbody == *body {
                    id
                } else {
                    c.exprs.add(Expr::Exists {
                        params: params.clone(),
                        body: sbody,
                    })
                }
            }

            Expr::Not { arg } => {
                let sarg = self.expr(c, *arg);
                match c.exprs[sarg] {
                    Expr::True => self.f,
                    Expr::False => self.t,
                    _ => {
                        if sarg == *arg {
                            id
                        } else {
                            c.exprs.add(Expr::Not { arg: sarg })
                        }
                    }
                }
            }

            Expr::Eq { left, right } => {
                let l = self.lookup(left);
                let r = self.lookup(right);
                if l.exists() && r.exists() {
                    if l == r { self.t } else { self.f }
                } else {
                    id
                }
            }

            Expr::And { exprs } => {
                let mut changed = false;
                let mut collapsed = false;
                let sexprs = Vec::from_iter(exprs.iter().filter_map(|e| {
                    let new = self.expr(c, *e);
                    match &c.exprs[new] {
                        Expr::True => {
                            changed = true;
                            None
                        }
                        Expr::False => {
                            collapsed = true;
                            None
                        }
                        _ => {
                            changed = changed || new != *e;
                            Some(new)
                        }
                    }
                }));
                if collapsed {
                    self.f
                } else if !changed {
                    id
                } else {
                    if sexprs.is_empty() {
                        self.t
                    } else {
                        Expr::and(c, sexprs)
                    }
                }
            }

            Expr::Or { exprs } => {
                let mut changed = false;
                let mut collapsed = false;
                let sexprs = Vec::from_iter(exprs.iter().filter_map(|e| {
                    let new = self.expr(c, *e);
                    match &c.exprs[new] {
                        Expr::True => {
                            collapsed = true;
                            None
                        }
                        Expr::False => {
                            changed = true;
                            None
                        }
                        _ => {
                            changed = changed || new != *e;
                            Some(new)
                        }
                    }
                }));
                if collapsed {
                    self.t
                } else if !changed {
                    id
                } else {
                    if sexprs.is_empty() {
                        self.f
                    } else {
                        Expr::or(c, sexprs)
                    }
                }
            }

            Expr::Atom { atom } => {
                let satom = self.atom(c, *atom);
                if satom == *atom {
                    id
                } else {
                    c.exprs.add(Expr::Atom { atom: satom })
                }
            }

            Expr::True | Expr::False => id,
        };

        c.exprs[id] = expr;
        new
    }
}
