use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct Typed<T> {
    pub value: T,
    pub ty: Option<Arc<String>>,
}

impl<T> Typed<T> {
    pub fn new(value: T) -> Self {
        Typed { value, ty: None }
    }
}

#[derive(Debug, Clone)]
pub struct Problem {
    pub name: String,
    pub domain: String,
    pub objects: Vec<Typed<String>>,
}

#[derive(Debug, Clone)]
pub struct Domain {}
