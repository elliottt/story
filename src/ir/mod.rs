
mod arena;

pub use arena::{Arena, Id};

#[derive(Default)]
pub struct Domain {
    pub name: String,
    pub types: Arena<Type>,
}

pub struct Problem {}

pub struct Type {
    pub loc: crate::parser::Loc,
    pub name: String,
    pub super_type: Id<Type>,
}
