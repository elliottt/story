mod arena;
pub use arena::{Arena, Id, Named, NamedArena};

#[derive(Default)]
pub struct Domain {
    pub name: String,
    pub types: NamedArena<Type>,
    pub constants: NamedArena<Constant>,
    pub properties: NamedArena<Predicate>,
    pub predicates: NamedArena<Predicate>,
}

pub struct Problem {}

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

pub struct Param {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub ty: Id<Type>,
}

/// Predicates are assertions about the world state. They can be marked `const`, in which case they
/// can never change, and can instead be used to prune the space of available actions during
/// grounding.
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
