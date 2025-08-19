use crate::{
    arena::Id,
    ir::{Action, Context, Expr},
};

pub fn ground(context: &mut Context) {
    nnf_context(context);
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
    action.precond = nnf_expr(context, action.precond);
    action.effect = nnf_expr(context, action.effect);
}

fn nnf_expr(context: &mut Context, id: Id<Expr>) -> Id<Expr> {
    match &mut context.exprs[id] {
        &mut Expr::Not { arg } => negate_expr(context, arg),

        // There's nothing to be done for an instantiation, or equality.
        Expr::Inst { .. } | Expr::Eq { .. } => id,

        Expr::And { exprs } => {
            let mut exprs = std::mem::take(exprs);
            for arg in exprs.iter_mut() {
                *arg = nnf_expr(context, *arg);
            }
            context.exprs[id] = Expr::And { exprs };
            id
        }
        Expr::Or { exprs } => {
            let mut exprs = std::mem::take(exprs);
            for arg in exprs.iter_mut() {
                *arg = nnf_expr(context, *arg);
            }
            context.exprs[id] = Expr::Or { exprs };
            id
        }
    }
}

/// Negate an expression.
fn negate_expr(context: &mut Context, id: Id<Expr>) -> Id<Expr> {
    match &context.exprs[id] {
        // We can't push negation down any further here.
        Expr::Inst { .. } | Expr::Eq { .. } => context.exprs.add(Expr::Not { arg: id }),

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
    }
}
