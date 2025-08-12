mod arena;
pub use arena::{Arena, Id, Named, NamedArena};

#[derive(Default)]
pub struct Domain {
    pub name: String,
    pub types: NamedArena<Type>,
    pub constants: NamedArena<Constant>,
    pub properties: NamedArena<Property>,
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

/// Properties are like predicates that can never change. They are useful for expressing immutable
/// facts of the domain, so that during grounding we can control action explosion a bit.
pub struct Property {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub params: Vec<Param>,
}

impl Named for Property {
    fn name(&self) -> &str {
        &self.name
    }
}
