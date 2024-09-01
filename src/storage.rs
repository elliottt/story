
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct Index<T> {
    index: u32,
    _marker: std::marker::PhantomData<T>,
}

#[derive(Default, Debug, Clone)]
pub(crate) struct Storage<T> {
    elems: Vec<T>,
}

impl<T> Storage<T> {
    pub(crate) fn push(&mut self, val: T) -> Index<T> {
        let index = self.elems.len();
        self.elems.push(val);
        Index {
            index: index as u32,
            _marker: Default::default(),
        }
    }
}

impl<T> std::ops::Index<Index<T>> for Storage<T> {
    type Output = T;

    fn index(&self, index: Index<T>) -> &Self::Output {
        &self.elems[index.index as usize]
    }
}

impl<T> std::ops::IndexMut<Index<T>> for Storage<T> {
    fn index_mut(&mut self, index: Index<T>) -> &mut Self::Output {
        &mut self.elems[index.index as usize]
    }
}
