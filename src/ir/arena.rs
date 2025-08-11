pub struct Arena<T> {
    elems: Vec<T>,
}

pub struct Id<T> {
    index: u32,
    _elem: std::marker::PhantomData<T>,
}

impl<T> std::fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Id").field("index", &self.index).field("_elem", &self._elem).finish()
    }
}

impl<T> PartialEq for Id<T> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<T> Eq for Id<T> {}

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        Self {
            index: self.index.clone(),
            _elem: self._elem.clone(),
        }
    }
}

impl<T> Copy for Id<T> {}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self { elems: Vec::new() }
    }

    pub fn add(&mut self, elem: T) -> Id<T> {
        let index = self.elems.len();
        self.elems.push(elem);
        Id::new(index)
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.elems.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.elems.iter_mut()
    }

    pub fn len(&self) -> usize {
        self.elems.len()
    }
}

impl<T> std::ops::Index<Id<T>> for Arena<T> {
    type Output = T;

    fn index(&self, index: Id<T>) -> &Self::Output {
        &self.elems[index.index as usize]
    }
}

impl<T> std::ops::IndexMut<Id<T>> for Arena<T> {
    fn index_mut(&mut self, index: Id<T>) -> &mut Self::Output {
        &mut self.elems[index.index as usize]
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self { elems: Vec::new() }
    }
}

impl<T> Id<T> {
    pub(crate) fn new(index: usize) -> Self {
        Id {
            index: index as u32,
            _elem: Default::default(),
        }
    }

    pub fn none() -> Self {
        Id {
            index: u32::MAX,
            _elem: Default::default(),
        }
    }

    pub fn exists(self) -> bool {
        self.index != u32::MAX
    }
}
