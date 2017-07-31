use std::ops::Range;
use std::borrow::Borrow;
use std::mem;

/// A wrapper for `Range<T>` which exposes some useful methods.
#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct Interval<T>(Range<T>);

impl<T> From<Range<T>> for Interval<T> {
    fn from(value: Range<T>) -> Self {
        Interval(value)
    }
}

impl<T> Into<Range<T>> for Interval<T> {
    fn into(self) -> Range<T> {
        self.0
    }
}

impl<T> Interval<T> {
    pub fn borrow<Q>(&self) -> Interval<&Q>
    where
        T: Borrow<Q>,
        Q: ?Sized,
    {
        Interval(self.0.start.borrow()..self.0.end.borrow())
    }

    pub fn take_inclusive_start(self) -> T {
        self.0.start
    }

    pub fn inclusive_start(&self) -> &T {
        &self.0.start
    }

    pub fn inclusive_start_mut(&mut self) -> &mut T {
        &mut self.0.start
    }

    pub fn set_inclusive_start(&mut self, value: T) -> T {
        mem::replace(&mut self.0.start, value)
    }

    pub fn take_exclusive_end(self) -> T {
        self.0.end
    }

    pub fn exclusive_end(&self) -> &T {
        &self.0.end
    }

    pub fn exclusive_end_mut(&mut self) -> &mut T {
        &mut self.0.end
    }

    pub fn set_exclusive_end(&mut self, value: T) -> T {
        mem::replace(&mut self.0.end, value)
    }

    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        value >= self.inclusive_start().borrow() && value < self.exclusive_end().borrow()
    }
}
