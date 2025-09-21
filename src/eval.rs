use crate::ir::{Constant, Context, Effect, Expr, Id, Var, VarKind};

type Env = Vec<Vec<Id<Constant>>>;

fn lookup(env: &Env, var: &Var) -> Id<Constant> {
    match var.kind {
        VarKind::Param { ix } => {
            let mut ix = usize::from(ix);
            for scope in env.iter() {
                if scope.len() < ix {
                    ix -= scope.len();
                    continue;
                }

                return scope[ix];
            }
            Id::none()
        }
        VarKind::Const { id } => id,
    }
}

pub fn valid(c: &Context, e: Id<Effect>) -> bool {
    let mut env = Env::new();
    e.valid(c, &mut env) != Valid::False
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum Valid {
    False,
    Unknown,
    True,
}

impl Valid {
    fn negate(self) -> Self {
        match self {
            Valid::False => Valid::True,
            Valid::Unknown => Valid::Unknown,
            Valid::True => Valid::False,
        }
    }

    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Valid::False, _) => Valid::False,
            (_, Valid::False) => Valid::False,
            (Valid::Unknown, _) => Valid::Unknown,
            (_, Valid::Unknown) => Valid::Unknown,
            _ => Valid::True,
        }
    }

    fn or(self, other: Self) -> Self {
        match (self, other) {
            (Valid::True, _) => Valid::True,
            (_, Valid::True) => Valid::True,
            (Valid::Unknown, _) => Valid::Unknown,
            (_, Valid::Unknown) => Valid::Unknown,
            _ => Valid::False,
        }
    }
}

impl From<bool> for Valid {
    fn from(value: bool) -> Self {
        if value { Valid::True } else { Valid::False }
    }
}

trait IsValid {
    fn valid(&self, c: &Context, env: &mut Env) -> Valid;
}

impl IsValid for Id<Effect> {
    fn valid(&self, c: &Context, env: &mut Env) -> Valid {
        match &c.effects[*self] {
            Effect::Inst { args, body } => {
                env.push(Vec::from(args.as_slice()));
                let res = body.valid(c, env);
                env.pop();
                res
            }
            Effect::Forall { params, body } => {
                env.push(Vec::from_iter(std::iter::repeat_n(
                    Id::none(),
                    params.len(),
                )));
                let res = body.valid(c, env);
                env.pop();
                res
            }
            Effect::Atom { .. } => Valid::Unknown,
            Effect::When { cond, .. } => cond.valid(c, env),
            Effect::And { effects } => effects
                .iter()
                .fold(Valid::True, |acc, e| acc.and(e.valid(c, env))),
            Effect::True => Valid::True,
        }
    }
}

impl IsValid for Id<Expr> {
    fn valid(&self, c: &Context, env: &mut Env) -> Valid {
        let res = match &c.exprs[*self] {
            Expr::Inst { args, body } => {
                env.push(Vec::from(args.as_slice()));
                let res = body.valid(c, env);
                env.pop();
                res
            }
            Expr::Forall { params, body } => {
                env.push(Vec::from_iter(std::iter::repeat_n(
                    Id::none(),
                    params.len(),
                )));
                let res = body.valid(c, env);
                env.pop();
                res
            }
            Expr::Exists { params, body } => {
                env.push(Vec::from_iter(std::iter::repeat_n(
                    Id::none(),
                    params.len(),
                )));
                let res = body.valid(c, env);
                env.pop();
                res
            }
            Expr::Atom { .. } => Valid::Unknown,
            Expr::Not { arg } => arg.valid(c, env).negate(),
            Expr::Eq { left, right } => {
                let l = lookup(env, left);
                let r = lookup(env, right);
                if l.exists() && r.exists() {
                    Valid::from(l == r)
                } else {
                    Valid::Unknown
                }
            }
            Expr::And { exprs } => {
                let mut acc = Valid::True;
                for e in exprs.iter() {
                    acc = acc.and(e.valid(c, env));
                    if acc == Valid::False {
                        break;
                    }
                }
                acc
            }
            Expr::Or { exprs } => {
                let mut acc = Valid::False;
                for e in exprs.iter() {
                    acc = acc.or(e.valid(c, env));
                    if acc == Valid::True {
                        break;
                    }
                }
                acc
            }
            Expr::True => Valid::True,
            Expr::False => Valid::False,
        };
        res
    }
}
