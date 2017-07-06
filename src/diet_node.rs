use node_mut_ext::NodeMutExt;
use interval::Interval;
use adjacent_bound::AdjacentBound;
use binary_tree::{Node, NodeMut, WalkAction};
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

    // Detaches max from `self` or `self` if there are no right children.
    // Returns the remaining self (if any) and the max.
    fn detach_max_or_self(mut self) -> (Option<Self>, Self) {
        if let Some(n) = self.detach_max(|_| true, |node, _| node.rebalance()) {
            (Some(self), *n)
        } else {
            (None, self)
        }
    }

    // Detaches min from `self` or `self` if there are no left children.
    // Returns the remaining self (if any) and the min.
    fn detach_min_or_self(mut self) -> (Option<Self>, Self) {
        if let Some(n) = self.detach_min(|_| true, |node, _| node.rebalance()) {
            (Some(self), *n)
        } else {
            (None, self)
        }
    }

    fn navigate_right_and_insert_at_height(&mut self, height: usize, new_node: DietNode<T>) {
        
        // Wrap it in an option so it may be taken
        let mut new_node = Some(new_node);

        self.walk_reshape(|l| {
                    if l.height == height {
                        let new_node = new_node.take()
                            .expect("only one node should have the same height");

                        // 4. replace that node with a new node with value n, and subtrees l and right. O(1) 
                        // By construction, the new node is AVL-balanced, and its subtree 1 taller than right.
                        let new_left = mem::replace(l, new_node);

                        l.insert_left(Some(Box::new(new_left)));

                        WalkAction::Stop
                    } else {
                        WalkAction::Right
                    }
                },
                                   |_| {},
                                   |node, _| node.rebalance());
    }

    fn navigate_left_and_insert_at_height(&mut self, height: usize, new_node: DietNode<T>) {
        
        let mut new_node = Some(new_node);

        self.walk_reshape(|r| {
                    if r.height == height {
                        let new_node = new_node.take()
                            .expect("only one node should have the same height");

                        // 4. replace that node with a new node with value n, and subtrees left and r. O(1) 
                        // By construction, the new node is AVL-balanced, and its subtree 1 taller than r.
                        let new_right = mem::replace(r, new_node);

                        r.insert_right(Some(Box::new(new_right)));

                        WalkAction::Stop
                    } else {
                        WalkAction::Left
                    }
                },
                                   |_| {},
                                   |node, _| node.rebalance());
    }

    pub(crate) fn join(mut left: DietNode<T>, mut right: DietNode<T>) -> Self
    {
        // Logic from https://stackoverflow.com/a/2037338/921321

        // 1. Determine the height of both trees.
        let mut joined = if left.height < right.height {

            // 2. remove the rightmost element from the left tree. Let 'n' be that element. (Adjust its computed height if necessary).
            let (left, n) = left.detach_max_or_self();

            let mut new_node = DietNode::new(n.into_parts().0);

            if let Some(left_height) = left.as_ref().map(|node| node.height) {
                new_node.insert_left(left.map(Box::new));

                right.navigate_left_and_insert_at_height(left_height, new_node);
                
                right
            } else {
                // When there is no left node

                // 3. In the right tree, navigate left until you reach the node whose subtree has the same height as the left tree. Let r be that node.

                // 4. replace that node with a new node with value n, and subtrees left and r.
                // By construction, the new node is AVL-balanced, and its subtree 1 taller than r.
                new_node.insert_right(Some(Box::new(right)));

                new_node
            }
        } else {

            // 2. remove the leftmost element from the right tree. Let 'n' be that element. (Adjust its computed height if necessary).
            let (right, n) = right.detach_min_or_self();

            let mut new_node = DietNode::new(n.into_parts().0);

            if let Some(right_height) = right.as_ref().map(|node| node.height) {
                new_node.insert_right(right.map(Box::new));

                left.navigate_right_and_insert_at_height(right_height, new_node);
                
                left
            } else {
                // When there is no right node

                // 3. In the left tree, navigate right until you reach the node whose subtree has the same height as the right tree. Let l be that node.

                // 4. replace that node with a new node with value n, and subtrees l and right.
                // By construction, the new node is AVL-balanced, and its subtree 1 taller than l.
                new_node.insert_left(Some(Box::new(left)));

                new_node
            }
        };

        joined.rebalance();
        
        joined
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
    pub(crate) fn insert(&mut self, value: T) -> bool {
        let (inserted, _) =
            self.walk_reshape_state((false, Some(value)),
                                    |node, &mut (ref mut inserted, ref mut value_option)| {
                let value = value_option.take().unwrap();
                match node.insert_or_walk(value) {
                    Ok(did_insert) => {
                        *inserted = did_insert;
                        WalkAction::Stop
                    }
                    Err((value, direction)) => {
                        *value_option = Some(value);
                        direction.into()
                    }
                }
            },
                                    |node, &mut (ref mut inserted, ref mut value_option)| {
                if let Some(value) = value_option.take() {
                    match node.insert_or_walk(value) {
                        Ok(did_insert) => {
                            *inserted = did_insert;

                            debug_assert!(node.is_balanced());
                        }
                        Err((value, WalkDirection::Left)) => {
                            let exclusive_end = value.increment();
                            node.insert_left(Some(Box::new(DietNode::new(value..exclusive_end))));

                            node.rebalance();
                        }
                        Err((value, WalkDirection::Right)) => {
                            let exclusive_end = value.increment();
                            node.insert_right(Some(Box::new(DietNode::new(value..exclusive_end))));

                            node.rebalance();
                        }
                    }
                }

            },
                                    |node, _, _| node.rebalance());

        self.rebalance();

        inserted
    }

    
    pub(crate) fn remove<Q>(&mut self, value: Cow<Q>) -> (bool, bool) 
        where T: Borrow<Q>, 
              Q: ?Sized + Ord + ToOwned<Owned=T>
        {
            let result = self.walk_reshape_state((false, false, Some(value)),
            |node, &mut (ref mut removed, ref mut remove_node, ref mut to_remove)| {
                
                let value = to_remove.take().expect("should only be traversing if there is a value to remove");
                match node.remove_or_walk(value) {
                    Ok(true) => {
                        *remove_node = true;
                        WalkAction::Stop
                    }
                    Ok(false) => {
                        *removed = true;
                        WalkAction::Stop
                    },
                    Err((value, direction)) => {
                        *to_remove = Some(value);
                        direction.into()
                    }
                }
            },
            |node, _| node.rebalance(),
            |node, action, &mut (ref mut removed, ref mut remove_node, _) | {
                if mem::replace(remove_node, false) {
                    debug_assert_eq!(*removed, false);
                    
                    match action {
                        WalkAction::Left => {
                            let mut left = node.detach_left().unwrap();    
                            if left.try_remove(|node, _| node.rebalance()).is_some() {
                                node.insert_left(Some(left));
                            }
                        }
                        WalkAction::Right => {
                            let mut right = node.detach_right().unwrap();    
                            if right.try_remove(|node, _| node.rebalance()).is_some() {
                                node.insert_right(Some(right));
                            }
                        }
                        WalkAction::Stop => unreachable!()
                    }

                    *removed = true;
                }

                node.rebalance();
            });

        self.rebalance();

        (result.0, result.1)
    }

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
            new_left.rebalance();

            self.insert_left(Some(new_left));
            self.rebalance();
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
            new_right.rebalance();

            self.insert_right(Some(new_right));
            self.rebalance();
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

    pub(crate) fn remove_or_walk<'a, Q: ?Sized>(&mut self, value: Cow<'a, Q>) -> Result<bool, (Cow<'a, Q>, WalkDirection)>
    where T: Borrow<Q>,
          Q: Ord + ToOwned<Owned=T> {

        if let Ok(direction) = self.calculate_walk_direction(&value) {
            Err((value, direction))
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

    #[test]
    fn join_root_with_taller_right() {
        let left = DietNode::new(0..3);

        let mut right = DietNode::new(7..9);
        right.insert_right(Some(Box::new(DietNode::new(13..14))));

        let joined = DietNode::join(left, right);

        assert_eq!(joined.value(), &(7..9).into());

        assert_eq!(joined.left.unwrap().value(), &(0..3).into());
        assert_eq!(joined.right.unwrap().value(), &(13..14).into());
    }

    #[test]
    fn join_root_with_taller_left() {
        let mut left = DietNode::new(0..3);
        left.insert_right(Some(Box::new(DietNode::new(5..6))));

        let right = DietNode::new(7..9);

        let joined = DietNode::join(left, right);

        assert_eq!(joined.value(), &(5..6).into());

        assert_eq!(joined.left.unwrap().value(), &(0..3).into());
        assert_eq!(joined.right.unwrap().value(), &(7..9).into());
    }
}