use std::collections::HashMap;

pub struct Id<T> {
    index: u32,
    _elem: std::marker::PhantomData<T>,
}

impl<T> std::hash::Hash for Id<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self._elem.hash(state);
    }
}

impl<T> Default for Id<T> {
    fn default() -> Self {
        Self::none()
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

impl<T: 'static> std::fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Id<{}>", std::any::type_name::<T>())?;
        if self.exists() {
            write!(f, "({})", self.index)
        } else {
            write!(f, "::none")
        }
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

#[derive(Clone, Debug)]
pub struct IdSet<T> {
    ids: fixedbitset::FixedBitSet,
    _elem: std::marker::PhantomData<T>,
}

impl<T: 'static> IdSet<T> {
    /// Construct a new id set.
    pub fn new() -> Self {
        IdSet {
            ids: fixedbitset::FixedBitSet::new(),
            _elem: Default::default(),
        }
    }

    pub fn with_capacity(size: usize) -> Self {
        IdSet {
            ids: fixedbitset::FixedBitSet::with_capacity(size),
            _elem: Default::default(),
        }
    }

    pub fn insert(&mut self, id: Id<T>) {
        if id.exists() {
            self.ids.set(id.index.try_into().unwrap(), true);
        }
    }

    pub fn union(&mut self, other: &Self) {
        self.ids.union_with(&other.ids);
    }

    pub fn difference(&mut self, other: &Self) {
        self.ids.difference_with(&other.ids);
    }

    pub fn iter(&self) -> impl Iterator<Item = Id<T>> {
        self.ids.ones().map(Id::new)
    }

    pub fn len(&self) -> usize {
        self.ids.count_ones(..)
    }
}

#[derive(Debug, Clone)]
pub struct Arena<T> {
    elems: Vec<T>,
}

impl<T: 'static> Arena<T> {
    pub fn new() -> Self {
        Self { elems: Vec::new() }
    }

    pub fn reserve(&mut self, size: usize) {
        self.elems.reserve(size);
    }

    pub fn add(&mut self, elem: T) -> Id<T> {
        let index = self.elems.len();
        self.elems.push(elem);
        Id::new(index)
    }

    pub fn drain(&mut self) -> impl Iterator<Item = T> {
        self.elems.drain(..)
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.elems.iter()
    }

    pub fn iter_with_id(&self) -> impl Iterator<Item = (Id<T>, &T)> + '_ {
        self.elems
            .iter()
            .enumerate()
            .map(|(ix, e)| (Id::new(ix), e))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.elems.iter_mut()
    }

    pub fn iter_mut_with_id(&mut self) -> impl Iterator<Item = (Id<T>, &mut T)> + '_ {
        self.elems
            .iter_mut()
            .enumerate()
            .map(|(ix, e)| (Id::new(ix), e))
    }

    pub fn len(&self) -> usize {
        self.elems.len()
    }

    pub fn into_inner(self) -> Vec<T> {
        self.elems
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

impl<T> IntoIterator for Arena<T> {
    type Item = T;

    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.elems.into_iter()
    }
}

#[derive(Debug, Clone)]
pub struct NamedArena<T: 'static> {
    elems: Arena<T>,
    names: HashMap<String, Id<T>>,
}

pub trait Named {
    fn name(&self) -> &str;
}

impl<T: Named> NamedArena<T> {
    pub fn new() -> Self {
        Self {
            elems: Arena::new(),
            names: HashMap::new(),
        }
    }

    pub fn reserve(&mut self, size: usize) {
        self.elems.reserve(size);
    }

    pub fn len(&self) -> usize {
        self.elems.len()
    }

    pub fn add(&mut self, elem: T) -> Id<T> {
        let entry = self.names.entry(elem.name().to_owned());
        let id = self.elems.add(elem);
        entry.insert_entry(id);
        id
    }

    pub fn get(&self, name: &str) -> Option<Id<T>> {
        self.names.get(name).copied()
    }

    pub fn into_inner(self) -> Vec<T> {
        self.elems.into_inner()
    }

    pub fn drain(&mut self) -> impl Iterator<Item = T> {
        self.names.clear();
        self.elems.drain()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.elems.iter()
    }

    pub fn iter_with_id(&self) -> impl Iterator<Item = (Id<T>, &T)> {
        self.elems.iter_with_id()
    }

    pub fn iter_mut_with_id(&mut self) -> impl Iterator<Item = (Id<T>, &mut T)> + '_ {
        self.elems.iter_mut_with_id()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.elems.iter_mut()
    }

    pub fn ids(&self) -> impl Iterator<Item = Id<T>> {
        self.names.values().copied()
    }
}

impl<T> std::ops::Index<Id<T>> for NamedArena<T> {
    type Output = T;

    fn index(&self, index: Id<T>) -> &Self::Output {
        self.elems.index(index)
    }
}

impl<T> std::ops::IndexMut<Id<T>> for NamedArena<T> {
    fn index_mut(&mut self, index: Id<T>) -> &mut Self::Output {
        self.elems.index_mut(index)
    }
}

impl<T> Default for NamedArena<T> {
    fn default() -> Self {
        Self {
            elems: Arena::default(),
            names: HashMap::default(),
        }
    }
}

impl<T> IntoIterator for NamedArena<T> {
    type Item = T;

    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.elems.into_iter()
    }
}
