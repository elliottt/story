pub use crate::arena::{Arena, Id, Named, NamedArena};

#[derive(Clone, Debug, Default)]
pub struct Context {
    pub domain_name: Ident,
    pub problem_name: Ident,
    pub constants: Arena<Constant>,
    pub exprs: Arena<Expr>,
    pub effects: Arena<Effect>,
    pub types: NamedArena<Type>,
    pub predicates: NamedArena<Predicate>,
    pub actions: NamedArena<Action>,
    pub init: Vec<Id<Expr>>,
    pub goal: Id<Expr>,
}

pub trait And: Sized {
    fn and(c: &mut Context, es: impl IntoIterator<Item = Id<Self>>) -> Id<Self>;
}

impl And for Expr {
    fn and(c: &mut Context, es: impl IntoIterator<Item = Id<Self>>) -> Id<Self> {
        let mut conjuncts = Vec::new();
        for e in es.into_iter() {
            if let Expr::And { exprs } = &c.exprs[e] {
                conjuncts.extend(exprs.iter().copied());
            } else {
                conjuncts.push(e);
            }
        }
        c.exprs.add(Expr::And { exprs: conjuncts })
    }
}

impl And for Effect {
    fn and(c: &mut Context, es: impl IntoIterator<Item = Id<Self>>) -> Id<Self> {
        let mut conjuncts = Vec::new();
        for e in es.into_iter() {
            if let Effect::And { effects } = &c.effects[e] {
                conjuncts.extend(effects.iter().copied());
            } else {
                conjuncts.push(e);
            }
        }
        c.effects.add(Effect::And { effects: conjuncts })
    }
}

#[derive(Clone, Debug)]
pub struct Type {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub super_type: Id<Type>,
}

impl Named for Type {
    fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Clone, Debug)]
pub struct Constant {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub ty: Id<Type>,
}

impl Named for Constant {
    fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Clone, Debug)]
pub struct Param {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub ty: Id<Type>,
}

/// Predicates are assertions about the world state.
#[derive(Clone, Debug)]
pub struct Predicate {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub params: Vec<Param>,
    pub is_const: bool,
}

impl Named for Predicate {
    fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Clone, Debug, Default)]
pub struct Ident {
    pub loc: crate::parser::Loc,
    pub name: String,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Atom {
        pred: Id<Predicate>,
        args: Vec<Ident>,
    },

    Not {
        arg: Id<Expr>,
    },

    Eq {
        left: Ident,
        right: Ident,
    },

    And {
        exprs: Vec<Id<Expr>>,
    },

    Or {
        exprs: Vec<Id<Expr>>,
    },
}

#[derive(Clone, Debug)]
pub enum Effect {
    Atom {
        neg: bool,
        pred: Id<Predicate>,
        args: Vec<Ident>,
    },

    When {
        cond: Id<Expr>,
        effect: Id<Effect>,
    },

    And {
        effects: Vec<Id<Effect>>,
    },

    // NOTE: This would probably be better to reserve in the effect arena and have a canonical
    // value instead of making it show up all over the place, but it's also a really convenient
    // default.
    True,
}

impl Effect {
    pub fn is_true(&self) -> bool {
        matches!(self, Effect::True)
    }
}

impl Default for Effect {
    fn default() -> Self {
        Effect::True
    }
}

#[derive(Clone, Debug)]
pub struct Action {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub params: Vec<Param>,
    pub precond: Id<Expr>,
    pub effect: Id<Effect>,
}

impl Named for Action {
    fn name(&self) -> &str {
        &self.name
    }
}
