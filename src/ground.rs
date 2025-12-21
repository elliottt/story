use std::collections::{HashMap, HashSet};

use crate::{
    arena::Id,
    ir::{
        And, Arena, Atom, Constant, Context, Effect, Expr, NamedArena, Param, Predicate, Type, Var,
        VarKind,
    },
};

// TODO: grounding needs to be able to report errors.
pub fn ground(context: &mut Context) {
    // Determine constant predicates by determining which ones don't show up in action effects.
    let knowledge = determine_const_predicates(context);

    // Instantiate all actions so that we only deal with concrete atoms from here.
    Instantiate::run(knowledge, context);

    // Introduce copies of predicates used as negative preconditions
    remove_negative_preconditions(context)
}

#[derive(Debug)]
struct StaticKnowledge {
    preds: HashMap<Id<Predicate>, HashSet<Vec<Id<Constant>>>>,
}

impl StaticKnowledge {
    /// Lookup the instantiation of this predicate, and return if it's known to be true. It's
    /// assumed that if we're looking up a predicate in the static knowledge struct, that we
    /// already know that it's constant.
    fn is_known(&self, p: Id<Predicate>, args: &[Id<Constant>]) -> bool {
        self.preds
            .get(&p)
            .map_or(false, |insts| insts.contains(args))
    }
}

fn determine_const_predicates(context: &mut Context) -> StaticKnowledge {
    let mut knowledge = StaticKnowledge {
        preds: HashMap::new(),
    };

    // Mark everything as constant, so that we can mark it as non-const when traversing effects.
    for pred in context.predicates.iter_mut() {
        pred.is_const = true;
    }

    for action in context.actions.iter() {
        used_effect_preds(
            &mut context.predicates,
            &context.atoms,
            &context.exprs,
            &context.effects,
            action.effect,
        );
    }

    // Any predicates that don't show up in action effects, but do show up in the init of the
    // problem indicate static information that we can use when pruning down the space of
    // instantiated actions.
    context.init = collect_static_knowledge(context, &mut knowledge, context.init);

    knowledge
}

fn collect_static_knowledge(
    c: &mut Context,
    k: &mut StaticKnowledge,
    id: Id<Effect>,
) -> Id<Effect> {
    let eff = std::mem::replace(&mut c.effects[id], Effect::True);
    let res = match &eff {
        Effect::Atom { neg, atom } => {
            let Atom { pred, args } = &c.atoms[*atom];

            // We assume unspecified static data is false, so we don't need to process negations.
            if !*neg && c.predicates[*pred].is_const {
                let insts = k.preds.entry(*pred).or_default();

                // TODO: avoid unwrapping consts, and exit early if they're not all constants
                // instead
                let args = args.iter().map(|var| var.kind.unwrap_const()).collect();

                // TODO: check the return value here and reject inconsistent static data.
                insts.insert(args);

                Id::none()
            } else {
                id
            }
        }
        Effect::And { effects } => {
            let mut es = Vec::with_capacity(effects.len());
            for id in effects {
                let id = collect_static_knowledge(c, k, *id);
                if id.exists() {
                    es.push(id);
                }
            }
            Effect::and(c, es)
        }

        // We can't learn anything from the atoms present in an `intends`, as the intent is
        // impossible to fulfill through action.
        Effect::Intends { .. } => {
            // TODO: raise errors for impossible to satisfy intents
            id
        }

        Effect::True => id,
    };
    c.effects[id] = eff;
    res
}

fn used_effect_preds(
    predicates: &mut NamedArena<Predicate>,
    atoms: &Arena<Atom>,
    exprs: &Arena<Expr>,
    effects: &Arena<Effect>,
    effect: Id<Effect>,
) {
    match &effects[effect] {
        Effect::Atom { atom, .. } => {
            predicates[atoms[*atom].pred].is_const = false;
        }
        Effect::And { effects: es } => {
            for eff in es.iter().copied() {
                used_effect_preds(predicates, atoms, exprs, effects, eff);
            }
        }

        // Intends doesn't contribute towards the referenced predicate being non-static--the
        // predicate must occur in a non-intends effect context for that to be true. (A character
        // could intend something impossible, but there wouldn't be any point in trying to plan
        // action based on that.)
        Effect::Intends { .. } => {
            // TODO: raise errors for intents that can't be fulfilled.
        }

        Effect::True => {}
    }
}

type Values = HashMap<Id<Type>, Vec<Id<Constant>>>;

struct Instantiate {
    k: StaticKnowledge,
    values: Values,
    inst: Vec<Vec<Id<Constant>>>,
    atoms: HashMap<Id<Predicate>, HashMap<Vec<Id<Constant>>, Id<Atom>>>,
    t: Id<Expr>,
    f: Id<Expr>,
}

enum CacheResult {
    Atom(Id<Atom>),
    Known(bool),
}

impl CacheResult {
    fn unwrap_atom(self) -> Id<Atom> {
        match self {
            CacheResult::Atom(id) => id,
            CacheResult::Known(_) => {
                panic!("Called `unwrap_atom` on a non-atom result")
            }
        }
    }
}

impl Instantiate {
    fn run(k: StaticKnowledge, ctx: &mut Context) {
        let mut values = Values::new();

        let all_values = Vec::from_iter(ctx.constants.iter_with_id().map(|(i, _)| i));
        values.insert(Id::none(), all_values);

        let mut work = Vec::from_iter(ctx.constants.iter_with_id().map(|(id, c)| (id, c.ty)));
        while let Some((c, ty)) = work.pop() {
            values.entry(ty).or_default().push(c);
            let st = ctx.types[ty].super_type;
            if st.exists() {
                work.push((c, st))
            }
        }

        let mut rq = Self {
            k,
            values,
            inst: Vec::new(),
            atoms: HashMap::new(),
            t: ctx.exprs.add(Expr::True),
            f: ctx.exprs.add(Expr::False),
        };

        let mut actions = std::mem::take(&mut ctx.actions);
        for action in actions.iter_mut() {
            for inst in rq.all_insts(&action.params) {
                let mut a = action.clone();
                a.inst = inst.clone();
                rq.with_inst(inst, |rq| {
                    a.pre = rq.from_expr(ctx, a.pre);
                    a.effect = rq.from_eff(ctx, a.effect);
                });

                // Filter out actions whose preconditions have collapsed to `false`. I'm not sure
                // what to do about cases that collapse to `true`, as that means they can always be
                // applied.
                if a.pre == rq.f {
                    continue;
                }

                ctx.actions.add(a);
            }
        }
    }

    fn all_insts(&self, ps: &[Param]) -> Vec<Vec<Id<Constant>>> {
        // If this action has any parameters whose type is uninhabited, we can skip specializing it
        // at all.
        if ps
            .iter()
            .any(|p| p.ty.exists() && self.values[&p.ty].is_empty())
        {
            return Vec::new();
        }

        let mut insts = vec![Vec::new()];
        let mut next = Vec::new();
        for p in ps {
            for inst in &mut insts {
                let (last, front) = self.values[&p.ty].split_last().unwrap();
                for val in front {
                    let mut inst = inst.clone();
                    inst.push(*val);
                    next.push(inst);
                }
                inst.push(*last);
            }
            insts.extend(next.drain(..));
        }
        insts
    }

    fn with_inst<T>(&mut self, inst: Vec<Id<Constant>>, mut f: impl FnMut(&mut Self) -> T) -> T {
        self.inst.push(inst);
        let ret = f(self);
        self.inst.pop();
        ret
    }

    fn param(&self, ix: u16) -> Id<Constant> {
        let mut ix = usize::from(ix);
        for scope in self.inst.iter() {
            if scope.len() < ix {
                ix -= scope.len();
                continue;
            }

            return scope[ix];
        }
        Id::none()
    }

    fn from_var(&mut self, var: &Var) -> Option<Var> {
        match var.kind {
            VarKind::Param { ix } => {
                let id = self.param(ix);
                if !id.exists() {
                    panic!("Unknown variable: {}\n: {:?}", ix, self.inst);
                }
                Some(Var {
                    loc: var.loc,
                    kind: VarKind::Const { id },
                })
            }
            VarKind::Const { .. } => None,
        }
    }

    fn from_atom(&mut self, ctx: &mut Context, id: Id<Atom>) -> CacheResult {
        let &Atom { pred, ref args } = &ctx.atoms[id];
        let args = Vec::from_iter(
            args.into_iter()
                .map(|var| self.from_var(var).unwrap_or_else(|| var.clone())),
        );

        let key = Vec::from_iter(args.iter().map(|var| var.kind.unwrap_const()));

        if ctx.predicates[pred].is_const {
            return CacheResult::Known(self.k.is_known(pred, key.as_slice()));
        }

        let preds = self.atoms.entry(pred).or_default();
        if let Some(id) = preds.get(&key) {
            CacheResult::Atom(*id)
        } else {
            let id = ctx.atoms.add(Atom { pred, args: args });
            preds.insert(key, id);
            CacheResult::Atom(id)
        }
    }

    fn from_eff(&mut self, ctx: &mut Context, id: Id<Effect>) -> Id<Effect> {
        let eff = std::mem::replace(&mut ctx.effects[id], Effect::True);
        let res = match &eff {
            Effect::And { effects } => {
                let mut changed = false;
                let effects = Vec::from_iter(effects.into_iter().map(|id| {
                    let sid = self.from_eff(ctx, *id);
                    changed = changed || sid != *id;
                    sid
                }));
                if !changed {
                    id
                } else {
                    Effect::and(ctx, effects)
                }
            }

            Effect::Atom { neg, atom } => {
                let satom = self.from_atom(ctx, *atom).unwrap_atom();
                if satom == *atom {
                    id
                } else {
                    ctx.effects.add(Effect::Atom {
                        neg: *neg,
                        atom: satom,
                    })
                }
            }

            Effect::Intends { actor, neg, atom } => {
                let sactor = self.from_var(actor);
                let satom = self.from_atom(ctx, *atom).unwrap_atom();
                if sactor.is_none() && satom == *atom {
                    id
                } else {
                    ctx.effects.add(Effect::Intends {
                        actor: sactor.unwrap_or_else(|| actor.clone()),
                        neg: *neg,
                        atom: satom,
                    })
                }
            }

            Effect::True => id,
        };
        ctx.effects[id] = eff;
        res
    }

    fn from_expr(&mut self, ctx: &mut Context, id: Id<Expr>) -> Id<Expr> {
        let expr = std::mem::replace(&mut ctx.exprs[id], Expr::True);
        let res = match &expr {
            Expr::And { exprs } => {
                let mut changed = false;
                let effects = Vec::from_iter(exprs.into_iter().map(|id| {
                    let sid = self.from_expr(ctx, *id);
                    changed = changed || sid != *id;
                    sid
                }));
                if !changed {
                    id
                } else {
                    let res = Expr::and(ctx, effects);
                    res
                }
            }

            // TODO: evaluation of static knowledge
            Expr::Atom { neg, atom } => match self.from_atom(ctx, *atom) {
                CacheResult::Atom(satom) => {
                    if satom == *atom {
                        id
                    } else {
                        ctx.exprs.add(Expr::Atom {
                            neg: *neg,
                            atom: satom,
                        })
                    }
                }
                CacheResult::Known(valid) => {
                    if valid != *neg {
                        self.t
                    } else {
                        self.f
                    }
                }
            },

            Expr::Eq { neg, left, right } => {
                let sleft = self.from_var(left).expect("Unbound parameter");
                let sright = self.from_var(right).expect("Unbound parameter");
                let equal = sleft.kind == sright.kind;
                if *neg != equal { self.t } else { self.f }
            }

            Expr::True | Expr::False => id,
        };
        ctx.exprs[id] = expr;
        res
    }
}

fn remove_negative_preconditions(c: &mut Context) {
    let mut ps = NegativePreconds::new();
    for action in c.actions.iter() {
        ps.from_expr(c, action.pre);
        ps.from_effect(c, action.effect);
    }
    ps.from_effect(c, c.init);
    ps.from_expr(c, c.goal);

    let mut negatives = NegatedPreds::new();
    for id in ps.into_preds() {
        let mut copy = c.predicates[id].clone();
        copy.is_negated = true;
        negatives.insert(id, c.predicates.add(copy));
    }

    // If there weren't any negative preconditions, we can exit early.
    if negatives.is_empty() {
        return;
    }

    // Otherwise, we rewrite for mutual exclusion in the effects, and remove negations in favor of
    // using the negated veresions in the preconditions.
    let mut actions = std::mem::take(&mut c.actions);
    for action in actions.iter_mut() {
        action.pre = translate_negative_exprs(&negatives, c, action.pre);
        action.effect = translate_negative_effects(&negatives, c, action.effect);
    }
    c.actions = actions;

    c.init = translate_negative_effects(&negatives, c, c.init);
    c.goal = translate_negative_exprs(&negatives, c, c.goal);
}

type NegatedPreds = HashMap<Id<Predicate>, Id<Predicate>>;

struct NegativePreconds {
    /// Predicates used as negative preconditions.
    preconds: HashSet<Id<Predicate>>,
}

impl NegativePreconds {
    fn new() -> Self {
        NegativePreconds {
            preconds: HashSet::new(),
        }
    }

    fn into_preds(self) -> Vec<Id<Predicate>> {
        Vec::from_iter(self.preconds.into_iter())
    }

    fn from_effect(&mut self, c: &Context, id: Id<Effect>) {
        match &c.effects[id] {
            Effect::Intends { neg, atom, .. } if *neg => {
                let &Atom { pred, .. } = &c.atoms[*atom];

                if !c.predicates[pred].is_const {
                    self.preconds.insert(pred);
                }
            }

            Effect::And { effects } => {
                for id in effects {
                    self.from_effect(c, *id);
                }
            }

            Effect::Atom { .. } | Effect::Intends { .. } | Effect::True => {}
        }
    }

    fn from_expr(&mut self, c: &Context, id: Id<Expr>) {
        match &c.exprs[id] {
            Expr::Atom { neg, atom } if *neg => {
                let &Atom { pred, .. } = &c.atoms[*atom];

                // We only care about negative preconditions for predicates that can change over
                // the course of planning.
                if !c.predicates[pred].is_const {
                    self.preconds.insert(pred);
                }
            }

            Expr::And { exprs } => {
                for id in exprs {
                    self.from_expr(c, *id)
                }
            }

            Expr::Atom { .. } | Expr::Eq { .. } | Expr::True | Expr::False => {}
        }
    }
}

fn translate_negative_effects(negs: &NegatedPreds, c: &mut Context, id: Id<Effect>) -> Id<Effect> {
    let eff = std::mem::replace(&mut c.effects[id], Effect::True);
    let res = match &eff {
        Effect::Atom { neg, atom } => {
            let Atom { pred, args } = &c.atoms[*atom];
            if let Some(nid) = negs.get(pred) {
                let natom = c.atoms.add(Atom {
                    pred: *nid,
                    args: args.clone(),
                });

                let nid = c.effects.add(Effect::Atom {
                    neg: !*neg,
                    atom: natom,
                });
                Effect::and(c, [id, nid])
            } else {
                id
            }
        }

        // We only remove negation from intents by using a negated predicate.
        Effect::Intends { actor, neg, atom } if *neg => {
            let Atom { pred, args } = &c.atoms[*atom];
            if let Some(nid) = negs.get(pred) {
                let natom = c.atoms.add(Atom {
                    pred: *nid,
                    args: args.clone(),
                });

                c.effects.add(Effect::Intends {
                    actor: actor.clone(),
                    neg: false,
                    atom: natom,
                })
            } else {
                id
            }
        }

        Effect::And { effects } => {
            let mut changed = false;
            let neffects = Vec::from_iter(effects.iter().copied().map(|id| {
                let nid = translate_negative_effects(negs, c, id);
                changed = changed || id != nid;
                nid
            }));
            if changed {
                Effect::and(c, neffects)
            } else {
                id
            }
        }

        Effect::Intends { .. } | Effect::True => id,
    };
    c.effects[id] = eff;
    res
}

fn translate_negative_exprs(negs: &NegatedPreds, c: &mut Context, id: Id<Expr>) -> Id<Expr> {
    let expr = std::mem::replace(&mut c.exprs[id], Expr::True);
    let res = match &expr {
        Expr::And { exprs } => {
            let mut changed = false;
            let nexprs = Vec::from_iter(exprs.iter().copied().map(|id| {
                let nid = translate_negative_exprs(negs, c, id);
                changed = changed || id != nid;
                nid
            }));
            if changed { Expr::and(c, nexprs) } else { id }
        }

        Expr::Atom { neg, atom } if *neg => {
            let &Atom { pred, ref args } = &c.atoms[*atom];
            if let Some(npred) = negs.get(&pred) {
                let natom = c.atoms.add(Atom {
                    pred: *npred,
                    args: args.clone(),
                });
                c.exprs.add(Expr::Atom {
                    neg: false,
                    atom: natom,
                })
            } else {
                id
            }
        }

        Expr::Atom { .. } | Expr::Eq { .. } | Expr::True | Expr::False => id,
    };
    c.exprs[id] = expr;
    res
}
