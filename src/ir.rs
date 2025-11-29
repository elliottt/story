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
    pub init: Id<Effect>,
    pub goal: Id<Expr>,
}

pub trait And: Sized {
    fn and(c: &mut Context, es: impl IntoIterator<Item = Id<Self>>) -> Id<Self>;
}

impl And for Expr {
    fn and(c: &mut Context, es: impl IntoIterator<Item = Id<Self>>) -> Id<Self> {
        let mut exprs = Vec::new();
        for e in es.into_iter() {
            if let Expr::And { exprs: es } = &c.exprs[e] {
                exprs.extend(es.iter().copied());
            } else {
                exprs.push(e);
            }
        }

        match exprs.len() {
            0 => c.exprs.add(Expr::True),
            1 => exprs[0],
            _ => c.exprs.add(Expr::And { exprs }),
        }
    }
}

impl And for Effect {
    fn and(c: &mut Context, es: impl IntoIterator<Item = Id<Self>>) -> Id<Self> {
        let mut effects = Vec::new();
        for e in es.into_iter() {
            if let Effect::And { effects: es } = &c.effects[e] {
                effects.extend(es.iter().copied());
            } else {
                effects.push(e);
            }
        }
        match effects.len() {
            0 => c.effects.add(Effect::True),
            1 => effects[0],
            _ => c.effects.add(Effect::And { effects }),
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
    /// True for copies introduced for negative preconditions.
    pub is_negated: bool,
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

    pub fn unwrap_const(&self) -> Id<Constant> {
        match self {
            VarKind::Param { .. } => panic!("Unexpected param"),
            VarKind::Const { id } => *id,
        }
    }
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
    Atom { neg: bool, atom: Id<Atom> },

    Eq { neg: bool, left: Var, right: Var },

    And { exprs: Vec<Id<Expr>> },

    True,
    False,
}

#[derive(Clone, Debug)]
pub enum Effect {
    Atom { neg: bool, atom: Id<Atom> },

    And { effects: Vec<Id<Effect>> },

    Intends { actor: Var, neg: bool, atom: Id<Atom> },

    // NOTE: These would probably be better to reserve in the effect arena and have a canonical
    // value instead of making it show up all over the place, but it's also a really convenient
    // default.
    True,
}

impl Effect {
    pub fn is_true(&self) -> bool {
        matches!(self, Effect::True)
    }
}

#[derive(Clone, Debug)]
pub struct Action {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub params: Vec<Param>,
    pub inst: Vec<Id<Constant>>,
    pub pre: Id<Expr>,
    pub effect: Id<Effect>,
}

impl Named for Action {
    fn name(&self) -> &str {
        &self.name
    }
}
