use interval::Interval;
use diet_node::DietNode;
use binary_tree::iter::{Iter as GenIter, IntoIter as GenIntoIter};

pub struct Iter<'a, T: 'a> {
    inner: GenIter<'a, DietNode<T>>,
}

impl<'a, T> Iter<'a, T> {
    pub(crate) fn new(root: Option<&'a DietNode<T>>) -> Self {
        Iter { inner: GenIter::new(root) }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a Interval<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

pub struct IntoIter<T> {
    inner: GenIntoIter<DietNode<T>>,
}

impl<T> IntoIter<T> {
    pub(crate) fn new(root: Option<Box<DietNode<T>>>) -> Self {
        IntoIter { inner: GenIntoIter::new(root) }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = Interval<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}