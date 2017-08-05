#![cfg_attr(feature = "nightly", feature(i128_type))]
#![cfg_attr(feature = "nightly", feature(u128_type))]

#[macro_use]
extern crate matches;
extern crate binary_tree;

#[macro_use]
extern crate log;

#[cfg(feature = "chrono")]
extern crate chrono;

#[cfg(feature = "extprim")]
extern crate extprim;

mod node_mut_ext;
mod interval;
pub use interval::Interval;

mod adjacent_bound;
pub use adjacent_bound::AdjacentBound;

mod walk_direction;
pub(crate) use walk_direction::WalkDirection;

mod split_result;
pub(crate) use split_result::SplitResult;

mod diet_node;
pub use diet_node::{DietNode, DietNodePtr};

mod iterators;
pub use iterators::{IntoIter, Iter};

use std::iter::FromIterator;
use std::borrow::{Borrow, Cow};
use std::hash::{Hash, Hasher};
use binary_tree::{BinaryTree, Node, NodeMut, WalkAction};
use binary_tree::iter::IntoIter as GenIntoIter;

/// An AVL balanced Discrete Interval Encoding Tree where each node represents
/// a discrete (non-touching) interval.
#[derive(Debug, Clone, Eq)]
pub struct Diet<T> {
    root: Option<Box<DietNode<T>>>,
}

impl<T> Drop for Diet<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<T> Diet<T> {
    /// Creates a new `Diet<T>`.
    ///
    /// ```
    /// use lz_diet::Diet;
    ///
    /// let diet : Diet<u32> = Diet::new();
    /// ```
    pub fn new() -> Self {
        Self { root: None }
    }

    /// Iterate over a borrow of the `Interval<T>` values.
    ///
    /// ```
    /// use lz_diet::Diet;
    ///
    /// let mut diet = Diet::new();
    /// diet.insert(5u32);
    ///
    /// let intervals : Vec<_> = diet.iter().collect();
    /// assert_eq!(intervals, vec![&(5..6).into()]);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        self.into_iter()
    }

    /// Clears the `Diet<T>`.
    ///
    /// ```
    /// use lz_diet::Diet;
    ///
    /// let mut diet = Diet::new();
    /// diet.insert(7u32);
    /// assert_eq!(diet.len(), 1);
    /// assert_eq!(diet.is_empty(), false);
    ///
    /// diet.clear();
    /// assert_eq!(diet.len(), 0);
    /// assert_eq!(diet.is_empty(), true);
    /// ```
    pub fn clear(&mut self) {
        debug!("clearing Diet");

        {
            // The iterator ensures we don't get a stackoverflow for a large tree
            // as its drop implementation iterates and drops each node individually
            let _: GenIntoIter<DietNode<_>> = GenIntoIter::new(self.root.take());
        }

        debug!("cleared Diet");
    }

    /// Gets the number of `Interval<T>` values in the tree.
    ///
    /// ```
    /// use lz_diet::Diet;
    ///
    /// let mut diet = Diet::new();
    ///
    /// assert_eq!(diet.len(), 0);
    ///
    /// diet.insert(8u32);
    /// assert_eq!(diet.len(), 1);
    ///
    /// diet.insert(10);
    /// assert_eq!(diet.len(), 2, "a new interval should have started");
    ///
    /// diet.insert(9);
    /// assert_eq!(diet.len(), 1, "the previous intervals should have merged");
    /// ```
    pub fn len(&self) -> usize {
        self.root().map_or(0, |node| node.len())
    }

    /// Gets whether the `Diet<T>` is empty or contains `Interval<T>` values.
    ///
    /// ```
    /// use lz_diet::Diet;
    ///
    /// let mut diet = Diet::new();
    /// assert!(diet.is_empty(), "a new tree should always be empty");
    ///
    /// diet.insert(7u32);
    /// assert_eq!(diet.is_empty(), false);
    ///
    /// diet.clear();
    /// assert_eq!(diet.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root().is_none()
    }

    /// Gets whether the `Diet<T>` contains the specified value.
    ///
    /// ```
    /// use lz_diet::Diet;
    ///
    /// let mut diet = Diet::new();
    /// assert_eq!(diet.contains(&5), false);
    ///
    /// diet.insert(5u32);
    /// assert!(diet.contains(&5));
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        if let Some(ref root) = self.root {
            let mut contains = false;
            root.walk(|node| {
                let walk_action = node.calculate_walk_direction(value)
                    .ok()
                    .map(|direction| direction.into())
                    .unwrap_or(WalkAction::Stop);

                if matches!(walk_action, WalkAction::Stop) {
                    contains = true;
                }
                walk_action
            });

            contains
        } else {
            false
        }
    }
}

impl<A: AdjacentBound> FromIterator<A> for Diet<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        let mut diet = Diet::new();

        for value in iter {
            diet.insert(value);
        }

        diet
    }
}

impl<T> BinaryTree for Diet<T> {
    type Node = DietNode<T>;

    fn root(&self) -> Option<&Self::Node> {
        self.root.as_ref().map(|n| &**n)
    }
}

impl<T: PartialEq> PartialEq for Diet<T> {
    fn eq(&self, other: &Self) -> bool {
        let self_intervals = self.into_iter();
        let other_intervals = other.into_iter();

        self_intervals.eq(other_intervals)
    }
}
impl<T: Hash> Hash for Diet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let intervals: Vec<_> = self.into_iter().collect();

        intervals.hash(state);
    }
}

impl<'a, T> IntoIterator for &'a Diet<T> {
    type Item = &'a Interval<T>;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self.root())
    }
}

impl<T> IntoIterator for Diet<T> {
    type Item = Interval<T>;
    type IntoIter = IntoIter<T>;

    fn into_iter(mut self) -> Self::IntoIter {
        IntoIter::new(self.root.take())
    }
}

impl<T: AdjacentBound> Diet<T> {
    /// Inserts a new value into the `Diet<T>`.
    ///
    /// # Returns
    /// true - if the value was inserted.
    /// false - if the value already existed contained.
    ///
    /// ```
    /// use lz_diet::Diet;
    ///
    /// let mut diet = Diet::new();
    /// assert!(diet.insert(5u32));
    /// assert_eq!(diet.insert(5), false);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        if let Some(ref mut root) = self.root {
            root.insert(value)
        } else {
            let exclusive_end = value.increment();

            let new_node = Box::new(DietNode::new(value..exclusive_end));

            self.root = Some(new_node);
            true
        }
    }

    /// Removes a value from the `Diet<T>`.
    ///
    /// This takes a `Cow<T>` as an owned value is only required if the value
    /// is in the middle of an `Interval<T>`.
    ///
    /// # Returns
    /// true - if the value was found and removed.
    /// false - if the value was not found.
    ///
    /// ```
    /// use lz_diet::Diet;
    /// use std::borrow::Cow;
    ///
    /// let mut diet = Diet::new();
    ///
    /// let to_remove = 5u32;
    /// // for a u32 we would probably just use Owned but this demonstrates how
    /// // borrowed values may also be used.
    /// assert_eq!(diet.remove(Cow::Borrowed(&to_remove)), false);
    ///
    /// diet.insert(5u32);
    /// assert!(diet.remove(Cow::Borrowed(&to_remove)));
    /// ```
    pub fn remove<Q>(&mut self, value: Cow<Q>) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord + ToOwned<Owned = T> + AdjacentBound,
    {
        let remove_result = self.root
            .as_mut()
            .map(|root| root.remove(value))
            .unwrap_or(Err(()));

        match remove_result {
            Ok(true) => {
                if self.root
                    .as_mut()
                    .expect("there must be a root node to be removed")
                    .try_remove(|node, _| node.rebalance())
                    .is_none()
                {
                    self.root = None;
                }

                true
            }
            Ok(false) => true,
            Err(()) => false,
        }
    }

    /// Splits a `Diet<T>` on a value.
    /// 
    /// # Returns
    /// Two `Diet<T>` values where the first contains children less than the
    /// value and the second is all children greater than the value.
    ///
    /// ```
    /// use lz_diet::Diet;
    /// use std::borrow::Cow;
    /// 
    /// let mut diet = Diet::new();
    /// diet.extend_from_slice(&[6u32, 7, 10, 11, 15, 16, 17]);
    /// 
    /// let (left, right) = diet.split(Cow::Owned(16));
    /// assert_eq!(left.into_iter().collect::<Vec<_>>(), vec![(6..8).into(), (10..12).into(), (15..16).into()]);
    /// assert_eq!(right.into_iter().collect::<Vec<_>>(), vec![(17..18).into()]);
    /// ```
    pub fn split<Q>(mut self, value: Cow<Q>) -> (Diet<T>, Diet<T>)
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord + ToOwned<Owned = T> + AdjacentBound,
    {
        let split_result = self.root
            .take()
            .map(|node| node.split(value))
            .unwrap_or(SplitResult::None);

        match split_result {
            SplitResult::Split(left, right) => (
                Diet {
                    root: Some(Box::new(left)),
                },
                Diet {
                    root: Some(Box::new(right)),
                },
            ),
            SplitResult::Single(node) => (
                Diet {
                    root: Some(Box::new(node)),
                },
                Diet::new(),
            ),
            SplitResult::None => (Diet::new(), Diet::new()),
        }
    }
}

impl<T: AdjacentBound + Clone> Diet<T> {
    pub fn extend_from_slice(&mut self, other: &[T]) {
        for val in other.into_iter().cloned() {
            self.insert(val);
        }
    }
}

impl<T> Default for Diet<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Cow;

    #[test]
    fn contains_returns_false_for_default() {
        let diet = Diet::<u32>::default();

        assert!(!diet.contains(&5));
    }

    #[test]
    fn contains_returns_true_for_existing_value() {
        let diet = Diet::from_iter([3, 1, 5].iter().cloned());

        assert!(diet.contains(&5));
    }

    #[test]
    fn len_returns_zero_for_default() {
        let diet = Diet::<u32>::default();

        assert_eq!(diet.len(), 0);
    }

    #[test]
    fn insert_returns_true_for_new_value() {
        let mut diet = Diet::default();

        assert!(diet.insert(1));
    }

    #[test]
    fn insert_returns_false_for_existing_value() {
        let mut diet = Diet::default();

        diet.insert(1);
        assert!(!diet.insert(1));
    }

    #[test]
    fn insert_extends_existing_ranges() {
        let mut diet = Diet::from_iter([1, 5].iter().cloned());

        diet.insert(2);
        diet.insert(4);

        assert_eq!(diet.len(), 2);
    }

    #[test]
    fn insert_combines_range() {
        let mut diet = Diet::from_iter([1, 3].iter().cloned());

        diet.insert(2);

        assert_eq!(diet.len(), 1);
    }

    #[test]
    fn insert_combines_ranges() {
        let mut diet = Diet::from_iter([3, 1, 5, 8].iter().cloned());

        diet.insert(2);
        diet.insert(4);
        diet.insert(6);
        diet.insert(7);

        assert_eq!(diet.len(), 1);
    }

    #[test]
    fn remove_returns_false_for_default() {
        let mut diet = Diet::<u32>::default();

        assert!(!diet.remove(Cow::Owned(5)));
    }

    #[test]
    fn remove_returns_false_for_non_existant_value() {
        let mut diet = Diet::from_iter([1, 2, 3, 6].iter().cloned());

        assert!(!diet.remove(Cow::Owned(10)));
    }

    #[test]
    fn remove_of_adjacent_returns_false() {
        let mut diet = Diet::from_iter([4, 5, 6].iter().cloned());

        assert!(!diet.remove(Cow::Owned(3)));
    }

    #[test]
    fn remove_of_lower_bounds() {
        let mut diet = Diet::from_iter([50, 51, 52, 1, 2, 20, 21].iter().cloned());

        assert!(diet.remove(Cow::Owned(50)));
        assert!(!diet.contains(&50));

        assert!(diet.remove(Cow::Owned(51)));
        assert!(!diet.contains(&51));

        assert!(diet.remove(Cow::Owned(1)));
        assert!(!diet.contains(&1));

        assert!(diet.remove(Cow::Owned(20)));
        assert!(!diet.contains(&20));

        assert_eq!(diet.len(), 3);
    }

    #[test]
    fn remove_of_upper_bounds() {
        let mut diet = Diet::from_iter([50, 51, 52, 1, 2, 20, 21].iter().cloned());

        assert!(diet.remove(Cow::Owned(52)));
        assert!(!diet.contains(&52));

        assert!(diet.remove(Cow::Owned(51)));
        assert!(!diet.contains(&51));

        assert!(diet.remove(Cow::Owned(2)));
        assert!(!diet.contains(&2));

        assert!(diet.remove(Cow::Owned(21)));
        assert!(!diet.contains(&21));

        assert_eq!(diet.len(), 3);
    }

    #[test]
    fn remove_root_node() {
        let mut diet = Diet::from_iter([50, 51, 1, 2, 10, 20, 21].iter().cloned());

        assert!(diet.remove(Cow::Owned(50)));
        assert!(!diet.contains(&50));
        assert!(diet.remove(Cow::Owned(51)));
        assert!(!diet.contains(&51));

        assert_eq!(diet.len(), 3);

        assert!(diet.contains(&1));
        assert!(diet.contains(&2));
        assert!(diet.contains(&10));
        assert!(diet.contains(&20));
        assert!(diet.contains(&21));
    }

    #[test]
    fn remove_within_interval() {
        let mut diet = Diet::from_iter([1, 2, 3, 5].iter().cloned());

        assert!(diet.remove(Cow::Owned(2)));

        assert!(!diet.contains(&2));

        assert!(diet.contains(&1));
        assert!(diet.contains(&3));
        assert!(diet.contains(&5));

        assert_eq!(diet.len(), 3);
    }

    #[test]
    fn remove_entire_node() {
        let mut diet = Diet::from_iter([1, 3, 5].iter().cloned());

        assert!(diet.remove(Cow::Owned(3)));
        assert_eq!(diet.len(), 2);
        assert!(diet.contains(&1));
        assert!(diet.contains(&5));
    }

    #[test]
    fn extend_from_slice_inserts_values() {
        let mut diet = Diet::default();

        diet.extend_from_slice(&[1, 5, 3]);

        assert!(diet.contains(&1));
        assert!(diet.contains(&5));
        assert!(diet.contains(&3));
    }

    #[test]
    fn equals_with_different_insertion_order() {
        let first = Diet::from_iter([1, 2, 5].iter().cloned());
        let second = Diet::from_iter([5, 1, 2].iter().cloned());

        assert_eq!(first, second);
    }

    #[test]
    fn clone() {
        let diet = Diet::from_iter([1, 2, 5].iter().cloned());
        let cloned = diet.clone();

        assert_eq!(diet, cloned);
    }
}
