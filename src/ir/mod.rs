mod arena;
pub use arena::{Arena, Id, Named, NamedArena};

#[derive(Default)]
pub struct Domain {
    pub name: String,
    pub types: NamedArena<Type>,
    pub constants: NamedArena<Constant>,
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
