use std::collections::HashMap;

use crate::{
    arena::Id,
    eval,
    ir::{Action, And, Arena, Constant, Context, Effect, Expr, NamedArena, Predicate, Type},
};

pub fn ground(context: &mut Context) {
    // Determine constant predicates by determining which ones don't show up in action effects.
    determine_const_predicates(context);

    // Remove uses of `when` in effects, by duplicating actions.
    elim_when(context);

    // Remove parameters by instantiating all actions
    instantiate_actions(context);

    nnf_context(context);
}

fn determine_const_predicates(context: &mut Context) {
    // Mark everything as constant, so that we can mark it as non-const when traversing effects.
    for pred in context.predicates.iter_mut() {
        pred.is_const = true;
    }

    for action in context.actions.iter() {
        used_effect_preds(
            &mut context.predicates,
            &context.exprs,
            &context.effects,
            action.effect,
        );
    }
}

fn used_effect_preds(
    predicates: &mut NamedArena<Predicate>,
    exprs: &Arena<Expr>,
    effects: &Arena<Effect>,
    effect: Id<Effect>,
) {
    match &effects[effect] {
        Effect::Inst { body, .. } | Effect::Forall { body, .. } => {
            used_effect_preds(predicates, exprs, effects, *body);
        }

        Effect::Atom { pred, .. } => {
            predicates[*pred].is_const = false;
        }
        // NOTE: we ignore the condition in a `when` clause, as it is treated as a secondary
        // precondition of the action.
        Effect::When { effect, .. } => {
            used_effect_preds(predicates, exprs, effects, *effect);
        }
        Effect::And { effects: es } => {
            for eff in es.iter().copied() {
                used_effect_preds(predicates, exprs, effects, eff);
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
            context.exprs.add(Expr::And { exprs: args })
        }

        Expr::True => context.exprs.add(Expr::False),

        Expr::False => context.exprs.add(Expr::True),
    }
}
