pub use crate::arena::{Arena, Id, Named, NamedArena};

#[derive(Clone, Debug, Default)]
pub struct Context {
    pub domain_name: Ident,
    pub problem_name: Ident,
    pub constants: Arena<Constant>,
    pub exprs: Arena<Expr>,
    pub types: NamedArena<Type>,
    pub predicates: NamedArena<Predicate>,
    pub actions: NamedArena<Action>,
    pub init: Vec<Id<Expr>>,
    pub goal: Id<Expr>,
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

/// Predicates are assertions about the world state. They can be marked `const`, in which case they
/// can never change, and can instead be used to prune the space of available actions during
/// grounding.
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
    Inst {
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
pub struct Action {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub params: Vec<Param>,
    pub precond: Id<Expr>,
    pub effect: Id<Expr>,
}

impl Named for Action {
    fn name(&self) -> &str {
        &self.name
    }
}
