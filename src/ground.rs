use std::collections::{HashMap, HashSet};

use crate::{
    arena::Id,
    eval,
    ir::{Action, And, Arena, Atom, Constant, Context, Effect, Expr, NamedArena, Predicate, Type},
};

pub fn ground(context: &mut Context) {
    // Determine constant predicates by determining which ones don't show up in action effects.
    determine_const_predicates(context);

    // Remove uses of `when` in effects, by duplicating actions.
    elim_when(context);

    // Remove parameters by instantiating all actions
    instantiate_actions(context);

    // Put the context into negation normal form
    nnf_context(context);

    // Introduce copies of predicates used as negative preconditions
    remove_negative_preconditions(context)
}

fn determine_const_predicates(context: &mut Context) {
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
}

fn used_effect_preds(
    predicates: &mut NamedArena<Predicate>,
    atoms: &Arena<Atom>,
    exprs: &Arena<Expr>,
    effects: &Arena<Effect>,
    effect: Id<Effect>,
) {
    match &effects[effect] {
        Effect::Inst { body, .. } | Effect::Forall { body, .. } => {
            used_effect_preds(predicates, atoms, exprs, effects, *body);
        }

        Effect::Atom { atom, .. } => {
            predicates[atoms[*atom].pred].is_const = false;
        }
        // NOTE: we ignore the condition in a `when` clause, as it is treated as a secondary
        // precondition of the action.
        Effect::When { effect, .. } => {
            used_effect_preds(predicates, atoms, exprs, effects, *effect);
        }
        Effect::And { effects: es } => {
            for eff in es.iter().copied() {
                used_effect_preds(predicates, atoms, exprs, effects, eff);
            }
        }
        Effect::True => {}
    }
}

fn elim_when(context: &mut Context) {
    let mut work = std::mem::take(&mut context.actions).into_inner();

    let mut whens = Vec::new();
    while let Some(action) = work.pop() {
        remove_when(context, &mut whens, action.effect);

        // Queue up versions of this action that have additional preconditions and actions for each
        // `when`.
        work.extend(whens.drain(..).map(|w| w.extend(context, &action)));

        // If all the effects were `when` nodes, can skip adding this effect back in.
        if !context.effects[action.effect].is_true() {
            context.actions.add(action);
        }
    }
}

struct When {
    cond: Id<Expr>,
    effect: Id<Effect>,
}

impl When {
    fn extend(self, context: &mut Context, action: &Action) -> Action {
        let mut copy = action.clone();
        let mut outer = context.effects[copy.effect].clone();
        match &mut outer {
            Effect::Forall { body, .. } | Effect::Inst { body, .. } => {
                let mut inner = context.effects[*body].clone();
                match &mut inner {
                    Effect::When { cond, effect } => {
                        *cond = Expr::and(context, [*cond, self.cond]);
                        *effect = Effect::and(context, [*effect, self.effect]);
                    }

                    _ => {
                        inner = Effect::When {
                            cond: self.cond,
                            effect: Effect::and(context, [copy.effect, self.effect]),
                        }
                    }
                }
                *body = context.effects.add(inner);
            }

            Effect::When { cond, effect } => {
                *cond = Expr::and(context, [*cond, self.cond]);
                *effect = Effect::and(context, [*effect, self.effect]);
            }

            _ => {
                outer = Effect::When {
                    cond: self.cond,
                    effect: Effect::and(context, [copy.effect, self.effect]),
                }
            }
        }

        copy.effect = context.effects.add(outer);

        return copy;
    }
}

/// Remove the outer-most uses of `when` in the effects of an action. Mutates the action in-place
/// so that it's left as the version that includes no uses of `when`.
fn remove_when(context: &mut Context, whens: &mut Vec<When>, id: Id<Effect>) {
    let mut eff = std::mem::replace(&mut context.effects[id], Effect::True);
    match &mut eff {
        &mut Effect::When { cond, effect } => {
            whens.push(When { cond, effect });
        }

        Effect::And { effects } => {
            effects.retain(|id| {
                remove_when(context, whens, *id);
                !context.effects[*id].is_true()
            });
            if effects.is_empty() {
                return;
            }
            context.effects[id] = eff;
        }

        // TODO: Unclear what to do here
        Effect::Forall { .. } | Effect::Inst { .. } => {
            context.effects[id] = eff;
        }

        Effect::Atom { .. } | Effect::True => {
            context.effects[id] = eff;
        }
    }
}

type Values = HashMap<Id<Type>, Vec<Id<Constant>>>;

/// Duplicate actions for every instantiation of their parameters
fn instantiate_actions(context: &mut Context) {
    let mut type_values = Values::new();

    let all_values = Vec::from_iter(context.constants.iter_with_id().map(|(i, _)| i));
    type_values.insert(Id::none(), all_values);

    let mut work = Vec::from_iter(context.constants.iter_with_id().map(|(id, c)| (id, c.ty)));
    while let Some((c, ty)) = work.pop() {
        type_values.entry(ty).or_default().push(c);
        let st = context.types[ty].super_type;
        if st.exists() {
            work.push((c, st))
        }
    }

    for action in std::mem::take(&mut context.actions).drain() {
        let param_tys = match &context.effects[action.effect] {
            Effect::Forall { params, .. } => Vec::from_iter(params.iter().map(|p| p.ty)),
            _ => continue,
        };

        // If this action has any parameters whose type is uninhabited, we can skip specializing it
        // at all.
        if param_tys
            .iter()
            .any(|ty| ty.exists() && type_values[ty].is_empty())
        {
            continue;
        }

        let mut insts = vec![Vec::new()];
        let mut next = Vec::new();
        for ty in param_tys {
            for inst in &mut insts {
                let (last, front) = type_values[&ty].split_last().unwrap();
                for val in front {
                    let mut inst = inst.clone();
                    inst.push(*val);
                    next.push(inst);
                }
                inst.push(*last);
            }
            insts.extend(next.drain(..));
        }

        for args in insts.drain(..) {
            let mut inst = action.instantiate(context, args);
            inst.effect = eval::simplify(context, inst.effect);

            // If the effect collapsed to #t, we can ignore this action.
            if !matches!(context.effects[inst.effect], Effect::True) {
                context.actions.add(inst);
            }
        }
    }
}

/// Put all referenced expressions in [`Context`] into negation normal form.
fn nnf_context(context: &mut Context) {
    let mut actions = std::mem::take(&mut context.actions);
    for action in actions.iter_mut() {
        nnf_action(context, action)
    }
    context.actions = actions;

    let mut init = std::mem::take(&mut context.init);
    for expr in init.iter_mut() {
        *expr = nnf_expr(context, *expr);
    }
    context.init = init;

    context.goal = nnf_expr(context, context.goal);
}

/// Put an [`Action`] into negation normal form.
fn nnf_action(context: &mut Context, action: &mut Action) {
    action.effect = nnf_effect(context, action.effect);
}

/// Effects are already in negation normal form, but the expressions held within a `when` might not
/// be.
fn nnf_effect(c: &mut Context, id: Id<Effect>) -> Id<Effect> {
    let mut effect = std::mem::replace(&mut c.effects[id], Effect::True);
    match &mut effect {
        Effect::Inst { body, .. } | Effect::Forall { body, .. } => {
            *body = nnf_effect(c, *body);
        }

        Effect::When { cond, effect } => {
            *cond = nnf_expr(c, *cond);
            *effect = nnf_effect(c, *effect);
        }

        Effect::And { effects } => {
            for effect in effects.iter_mut() {
                *effect = nnf_effect(c, *effect);
            }
        }

        Effect::Atom { .. } | Effect::True => {}
    }
    c.effects[id] = effect;
    id
}

fn nnf_expr(context: &mut Context, id: Id<Expr>) -> Id<Expr> {
    let mut expr = std::mem::replace(&mut context.exprs[id], Expr::True);
    let new = match &mut expr {
        Expr::Inst { body, .. } => {
            *body = nnf_expr(context, *body);
            id
        }

        Expr::Forall { body, .. } => {
            *body = nnf_expr(context, *body);
            id
        }

        Expr::Exists { body, .. } => {
            *body = nnf_expr(context, *body);
            id
        }

        Expr::Not { arg } => negate_expr(context, *arg),

        // There's nothing to be done for an atom, equality, true, or false.
        Expr::Atom { .. } | Expr::Eq { .. } | Expr::True | Expr::False => id,

        Expr::And { exprs } => {
            for arg in exprs.iter_mut() {
                *arg = nnf_expr(context, *arg);
            }
            id
        }
        Expr::Or { exprs } => {
            for arg in exprs.iter_mut() {
                *arg = nnf_expr(context, *arg);
            }
            id
        }
    };
    context.exprs[id] = expr;
    new
}

/// Negate an expression.
fn negate_expr(context: &mut Context, id: Id<Expr>) -> Id<Expr> {
    match &context.exprs[id] {
        Expr::Inst { args, body } => {
            let args = args.clone();
            let body = negate_expr(context, *body);
            context.exprs.add(Expr::Inst { args, body })
        }

        Expr::Forall { params, body } => {
            let params = params.clone();
            let body = negate_expr(context, *body);
            context.exprs.add(Expr::Exists { params, body })
        }

        Expr::Exists { params, body } => {
            let params = params.clone();
            let body = negate_expr(context, *body);
            context.exprs.add(Expr::Forall { params, body })
        }

        // We can't push negation down any further here.
        Expr::Atom { .. } | Expr::Eq { .. } => context.exprs.add(Expr::Not { arg: id }),

        // Double-negation elimination
        &Expr::Not { arg } => negate_expr(context, arg),

        // De Morgan's laws
        Expr::And { exprs } => {
            let mut args = exprs.clone();
            for arg in args.iter_mut() {
                *arg = negate_expr(context, *arg);
            }
            context.exprs.add(Expr::Or { exprs: args })
        }

        Expr::Or { exprs } => {
            let mut args = exprs.clone();
            for arg in args.iter_mut() {
                *arg = negate_expr(context, *arg);
            }
            Expr::and(context, args)
        }

        Expr::True => context.exprs.add(Expr::False),

        Expr::False => context.exprs.add(Expr::True),
    }
}

fn remove_negative_preconditions(c: &mut Context) {
    let mut ps = NegativePreconds::new();
    for action in c.actions.iter() {
        ps.from_effect(c, action.effect);
    }

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
        action.effect = translate_negative_effects(&negatives, c, action.effect);
    }
    c.actions = actions;
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
            Effect::Inst { body, .. } => self.from_effect(c, *body),

            Effect::Forall { .. } => {
                panic!("Quantifiers must be removed prior to negative precondition removal");
            }

            Effect::When { cond, effect } => {
                self.from_expr(c, *cond);
                self.from_effect(c, *effect);
            }

            Effect::And { effects } => {
                for id in effects {
                    self.from_effect(c, *id);
                }
            }

            Effect::Atom { .. } | Effect::True => {}
        }
    }

    fn from_expr(&mut self, c: &Context, id: Id<Expr>) {
        match &c.exprs[id] {
            Expr::Not { arg } => {
                let &Expr::Atom { atom } = &c.exprs[*arg] else {
                    panic!("Negation applied to a non-atom expression");
                };

                let &Atom { pred, .. } = &c.atoms[atom];

                // We only care about negative preconditions for predicates that can change over
                // the course of planning.
                if !c.predicates[pred].is_const {
                    self.preconds.insert(pred);
                }
            }

            Expr::Inst { body, .. } => self.from_expr(c, *body),

            Expr::And { exprs } | Expr::Or { exprs } => {
                for id in exprs {
                    self.from_expr(c, *id)
                }
            }

            Expr::Forall { .. } | Expr::Exists { .. } => {
                panic!("Quantifiers must be removed prior to negative precondition removal");
            }

            Expr::Atom { .. } | Expr::Eq { .. } | Expr::True | Expr::False => {}
        }
    }
}

fn translate_negative_effects(negs: &NegatedPreds, c: &mut Context, id: Id<Effect>) -> Id<Effect> {
    let eff = std::mem::replace(&mut c.effects[id], Effect::True);
    let res = match &eff {
        Effect::Inst { args, body } => {
            let nbody = translate_negative_effects(negs, c, *body);
            if nbody != *body {
                c.effects.add(Effect::Inst {
                    args: args.clone(),
                    body: nbody,
                })
            } else {
                id
            }
        }
        Effect::Forall { .. } => {
            panic!("Quantifiers must be removed prior to negative precondition removal");
        }
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

        Effect::When { cond, effect } => {
            let ncond = translate_negative_exprs(negs, c, *cond);
            let neffect = translate_negative_effects(negs, c, *effect);
            if ncond != *cond || neffect != *effect {
                c.effects.add(Effect::When {
                    cond: ncond,
                    effect: neffect,
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
        Effect::True => id,
    };
    c.effects[id] = eff;
    res
}

fn translate_negative_exprs(negs: &NegatedPreds, c: &mut Context, id: Id<Expr>) -> Id<Expr> {
    let expr = std::mem::replace(&mut c.exprs[id], Expr::True);
    let res = match &expr {
        Expr::Inst { args, body } => {
            let nbody = translate_negative_exprs(negs, c, *body);
            if nbody != *body {
                c.exprs.add(Expr::Inst {
                    args: args.clone(),
                    body: nbody,
                })
            } else {
                id
            }
        }

        Expr::Forall { .. } | Expr::Exists { .. } => {
            panic!("Quantifiers must be removed prior to negative precondition removal");
        }

        Expr::And { exprs } => {
            let mut changed = false;
            let nexprs = Vec::from_iter(exprs.iter().copied().map(|id| {
                let nid = translate_negative_exprs(negs, c, id);
                changed = changed || id != nid;
                nid
            }));
            if changed { Expr::and(c, nexprs) } else { id }
        }

        Expr::Or { exprs } => {
            let mut changed = false;
            let nexprs = Vec::from_iter(exprs.iter().copied().map(|id| {
                let nid = translate_negative_exprs(negs, c, id);
                changed = changed || id != nid;
                nid
            }));
            if changed { Expr::or(c, nexprs) } else { id }
        }

        Expr::Not { arg } => {
            let &Expr::Atom { atom } = &c.exprs[*arg] else {
                panic!("Negation applied to a non-atom expression");
            };

            let &Atom { pred, ref args } = &c.atoms[atom];
            if let Some(npred) = negs.get(&pred) {
                let natom = c.atoms.add(Atom {
                    pred: *npred,
                    args: args.clone(),
                });
                c.exprs.add(Expr::Atom { atom: natom })
            } else {
                id
            }
        }

        Expr::Atom { .. } | Expr::Eq { .. } | Expr::True | Expr::False => id,
    };
    c.exprs[id] = expr;
    res
}
