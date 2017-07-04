use node_mut_ext::NodeMutExt;
use interval::Interval;
use adjacent_bound::AdjacentBound;
use binary_tree::{Node, NodeMut};
use std::mem;
use std::borrow::Borrow;
use walk_direction::WalkDirection;
use std::cmp;
use std::borrow::Cow;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct DietNode<T> {
    interval: Interval<T>,
    left: Option<DietNodePtr<T>>,
    right: Option<DietNodePtr<T>>,

    /// The number of nodes in this sub-tree.
    count: usize,

    /// The height of this node, i.e. how many child levels there are.
    height: usize,
}

pub type DietNodePtr<T> = Box<DietNode<T>>;

impl<T> Node for DietNode<T> {
    type Value = Interval<T>;

    fn left(&self) -> Option<&Self> {
        self.left.as_ref().map(|n| &**n)
    }

    fn right(&self) -> Option<&Self> {
        self.right.as_ref().map(|n| &**n)
    }

    fn value(&self) -> &Self::Value {
        &self.interval
    }
}

impl<T> NodeMut for DietNode<T> {
    type NodePtr = DietNodePtr<T>;

    fn detach_left(&mut self) -> Option<Self::NodePtr> {
        let detached = self.left.take();
        self.update_stats();

        detached
    }

    fn detach_right(&mut self) -> Option<Self::NodePtr> {
        let detached = self.right.take();
        self.update_stats();

        detached
    }

    fn insert_left(&mut self, tree: Option<Self::NodePtr>) -> Option<Self::NodePtr> {
        let old_left = mem::replace(&mut self.left, tree);
        self.update_stats();

        old_left
    }

    fn insert_right(&mut self, tree: Option<Self::NodePtr>) -> Option<Self::NodePtr> {
        let old_right = mem::replace(&mut self.right, tree);
        self.update_stats();

        old_right
    }

    fn value_mut(&mut self) -> &mut Self::Value {
        &mut self.interval
    }

    fn into_parts(self) -> (Self::Value, Option<Self::NodePtr>, Option<Self::NodePtr>) {
        (self.interval, self.left, self.right)
    }

    fn left_mut(&mut self) -> Option<&mut Self> {
        self.left.as_mut().map(|l| &mut **l)
    }

    fn right_mut(&mut self) -> Option<&mut Self> {
        self.right.as_mut().map(|r| &mut **r)
    }
}

impl<T> DietNode<T> {
    pub fn new<I>(value: I) -> Self
        where I: Into<Interval<T>>
    {
        Self {
            interval: value.into(),
            left: None,
            right: None,
            count: 1,
            height: 0,
        }
    }

    pub(crate) fn calculate_walk_direction<Q: ?Sized>(&self, value: &Q) -> Result<WalkDirection, ()> where T: Borrow<Q>, Q: Ord {
        let interval = self.value();

        if value < interval.inclusive_start().borrow() {
            Ok(WalkDirection::Left)
        } else if value >= interval.exclusive_end().borrow() {
            Ok(WalkDirection::Right)
        } else {
            debug_assert!(interval.contains(value));
            Err(())
        }
    }

    pub fn len(&self) -> usize {
        self.count
    }

    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    pub(crate) fn balance_factor(&self) -> i8 {
        let balance_factor = self.left().map_or(0, |node| (node.height + 1) as isize) -
                             self.right().map_or(0, |node| (node.height + 1) as isize);

        balance_factor as i8
    }

    fn update_stats(&mut self) {
        self.count = 1;
        self.height = 0;

        let children = [self.left.as_ref(), self.right.as_ref()];

        for child in children.iter().flat_map(|x| x) {
            self.count += child.count;
            self.height = cmp::max(self.height, child.height + 1);
        }
    }

    pub(crate) fn is_balanced(&self) -> bool{
        let balance_factor = self.balance_factor();

        balance_factor <= 1 && balance_factor >= -1
    }

    pub(crate) fn rebalance(&mut self) {
        let balance_factor = self.balance_factor();

        if balance_factor > 1 {
            self.left_mut().map(|node| {
                if node.balance_factor() < 0 {
                    node.rotate_left()
                        .expect("if the node is left-heavy there must be a left child");
                }
            });

            self.rotate_right()
                .expect("if the node is overly right-heavy there must be a right child");
        } else if balance_factor < -1 {
            self.right_mut().map(|node| {
                if node.balance_factor() > 0 {
                    node.rotate_right()
                        .expect("if the node is right-heavy there must be a right child");
                }
            });

            self.rotate_left()
                .expect("if the node is overly left-heavy there must be a left child");
        }

        debug_assert!(self.is_balanced());
    }
}

impl<T: AdjacentBound> DietNode<T> {
    fn split_on_value(&mut self, value: T) {
        if self.balance_factor() > 0 {
            self.split_left_on_value(value);
        } else {
            self.split_right_on_value(value);
        }
    }

    fn split_left_on_value(&mut self, value: T) {
        let old_inclusive_start = self.value_mut().set_inclusive_start(value.increment());

        if old_inclusive_start != value {
            let new_left_interval = Interval::from(old_inclusive_start..value);

            let old_left = self.detach_left();

            let mut new_left = Box::new(DietNode::new(new_left_interval));
            new_left.insert_left(old_left);

            self.insert_left(Some(new_left));
        }
    }

    fn split_right_on_value(&mut self, value: T) {
        let new_inclusive_start = value.increment();

        let old_exclusive_end = self.value_mut().set_exclusive_end(value);

        if old_exclusive_end != new_inclusive_start {
            let new_right_interval = Interval::from(new_inclusive_start..old_exclusive_end);

            let old_right = self.detach_right();

            let mut new_right = Box::new(DietNode::new(new_right_interval));
            new_right.insert_right(old_right);

            self.insert_right(Some(new_right));
        }
    }

    pub (crate) fn insert_or_walk(&mut self, mut value: T) -> Result<bool, (T, WalkDirection)> {
        if &value < self.value().inclusive_start() {
            if value.comes_before(self.value().inclusive_start()) {
                self.value_mut().set_inclusive_start(value);
                self.join_left();

                Ok(true)
            } else {
                Err((value, WalkDirection::Left))
            }
        } else if &value > self.value().exclusive_end() {
            Err((value, WalkDirection::Right))
        } else if &value == self.value().exclusive_end() {
            value.increment_ref();
            self.value_mut().set_exclusive_end(value);
            self.join_right();

            Ok(true)
        } else {
            debug_assert!(self.value().contains(&value),
                          "the value should already be contained within the interval");
            Ok(false)
        }
    }

    pub(crate) fn remove_or_walk<'a, Q: ?Sized>(&mut self, value: Cow<'a, Q>) -> Result<bool, (WalkDirection, Cow<'a, Q>)>
    where T: Borrow<Q>,
          Q: Ord + ToOwned<Owned=T> {

        if let Ok(direction) = self.calculate_walk_direction(&value) {
            Err((direction, value))
        } else {
            debug_assert!(self.value().contains(&value));

            let value = value.into_owned();
            let comes_before_end = value.comes_before(self.value().exclusive_end());
            let requires_node_removal = if &value == self.value().inclusive_start() {
                if comes_before_end {
                    true
                } else {
                    self.value_mut().inclusive_start_mut().increment_ref();
                    false
                }
            } else if comes_before_end {
                self.value_mut().exclusive_end_mut().decrement_ref();
                false
            } else {
                self.split_on_value(value);
                false
            };

            Ok(requires_node_removal)
        }
    }
}

impl<T: PartialEq> DietNode<T> {
    fn join_left(&mut self) -> bool {
        if let Some(mut left) = self.detach_left() {

            let max;
            if left.value().exclusive_end() == self.value().inclusive_start() {
                self.insert_left(left.detach_left());
                max = Some(left);
            } else {
                max = left.detach_max(|max| {
                                          max.value().exclusive_end() ==
                                          self.value().inclusive_start()
                                      },
                                      |node, _| node.rebalance());
                self.insert_left(Some(left));
            }

            if let Some(max) = max {
                debug_assert!(max.right().is_none());

                self.value_mut().set_inclusive_start(max.into_parts().0.take_inclusive_start());

                true
            } else {
                false
            }
        } else {
            false
        }
    }

    fn join_right(&mut self) -> bool {
        if let Some(mut right) = self.detach_right() {

            let min;
            if right.value().inclusive_start() == self.value().exclusive_end() {
                self.insert_right(right.detach_right());
                min = Some(right);
            } else {
                min = right.detach_min(|min| {
                                           min.value().inclusive_start() ==
                                           self.value().exclusive_end()
                                       },
                                       |node, _| node.rebalance());
                self.insert_right(Some(right));
            }

            if let Some(min) = min {
                debug_assert!(min.left().is_none());

                self.value_mut().set_exclusive_end(min.into_parts().0.take_exclusive_end());

                true
            } else {
                false
            }
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detach_max_returns_none_for_no_right() {
        let mut node = DietNode::new(0..5);

        assert_matches!(node.detach_max(|_| true, |_, _| {}), None);
    }

    #[test]
    fn detach_max_takes_max() {
        let max = Box::new(DietNode::new(0..5));

        let mut parent = Box::new(DietNode::new(0..5));
        parent.insert_right(Some(max.clone()));

        let mut root = DietNode::new(0..5);
        root.insert_right(Some(parent));

        assert_eq!(root.detach_max(|_| true, |_, _| {}), Some(max));
    }

    #[test]
    fn try_detach_min_returns_none_for_no_left() {
        let mut node = DietNode::new(0..5);

        assert_matches!(node.detach_min(|_| true, |_, _| {}), None);
    }

    #[test]
    fn try_detach_min_multiple_levels_takes_min() {
        let min = Box::new(DietNode::new(0..5));

        let mut parent = Box::new(DietNode::new(0..5));
        parent.insert_left(Some(min.clone()));

        let mut root = DietNode::new(0..5);
        root.insert_left(Some(parent));

        assert_eq!(root.detach_min(|_| true, |_, _| {}), Some(min));
    }
}