pub use crate::arena::{Arena, Id, Named, NamedArena};

#[derive(Clone, Debug, Default)]
pub struct Context {
    pub domain_name: Ident,
    pub problem_name: Ident,
    pub constants: Arena<Constant>,
    pub atoms: Arena<Atom>,
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

        match conjuncts.len() {
            0 => c.exprs.add(Expr::True),
            1 => conjuncts[0],
            _ => c.exprs.add(Expr::And { exprs: conjuncts }),
        }
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
        match conjuncts.len() {
            0 => c.effects.add(Effect::True),
            1 => conjuncts[0],
            _ => c.effects.add(Effect::And { effects: conjuncts }),
        }
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

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum VarKind {
    Param { ix: u16 },
    Const { id: Id<Constant> },
}

impl VarKind {
    pub const INVALID_PARAM: u16 = u16::MAX;
}

#[derive(Clone, Debug)]
pub struct Var {
    pub loc: crate::parser::Loc,
    pub kind: VarKind,
}

/// An atomic formula.
#[derive(Clone, Debug)]
pub struct Atom {
    pub pred: Id<Predicate>,
    pub args: Vec<Var>,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Inst {
        args: Vec<Id<Constant>>,
        body: Id<Expr>,
    },

    Forall {
        params: Vec<Param>,
        body: Id<Expr>,
    },

    Exists {
        params: Vec<Param>,
        body: Id<Expr>,
    },

    Atom {
        atom: Id<Atom>,
    },

    Not {
        arg: Id<Expr>,
    },

    Eq {
        left: Var,
        right: Var,
    },

    And {
        exprs: Vec<Id<Expr>>,
    },

    Or {
        exprs: Vec<Id<Expr>>,
    },

    True,
    False,
}

#[derive(Clone, Debug)]
pub enum Effect {
    /// Instantiation of a forall. The forall will be replaced when the instantiation occurrs.
    Inst {
        args: Vec<Id<Constant>>,
        body: Id<Effect>,
    },

    Forall {
        params: Vec<Param>,
        body: Id<Effect>,
    },

    Atom {
        neg: bool,
        atom: Id<Atom>,
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

impl Id<Effect> {
    pub fn instantiate(self, c: &mut Context, args: Vec<Id<Constant>>) -> Self {
        let body = match &c.effects[self] {
            Effect::Forall { body, .. } => *body,
            _ => self,
        };

        c.effects.add(Effect::Inst { args, body })
    }
}

#[derive(Clone, Debug)]
pub struct Action {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub effect: Id<Effect>,
}

impl Named for Action {
    fn name(&self) -> &str {
        &self.name
    }
}

impl Action {
    pub fn instantiate(&self, c: &mut Context, args: Vec<Id<Constant>>) -> Self {
        let mut instantiated = self.clone();

        for arg in &args {
            instantiated.name += "-";
            instantiated.name += &c.constants[*arg].name;
        }

        instantiated.effect = self.effect.instantiate(c, args);

        instantiated
    }
}
