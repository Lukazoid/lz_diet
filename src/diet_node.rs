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
        trace!("detaching left node");

        if let Some(detached) = self.left.take() {

            // Only update stats if the node actually changed
            self.update_stats();

            debug!("detached left node");

            Some(detached)
        } else {
            trace!("there was no left node to detach");

            None
        }
    }

    fn detach_right(&mut self) -> Option<Self::NodePtr> {
        trace!("detaching right node");

        if let Some(detached) = self.right.take() {

            // Only update stats if the node actually changed
            self.update_stats();

            debug!("detached right node");

            Some(detached)
        } else {
            trace!("there was no right node to detach");

            None
        }
    }

    fn insert_left(&mut self, tree: Option<Self::NodePtr>) -> Option<Self::NodePtr> {
        trace!("inserting left node");

        if self.left.is_some() || tree.is_some() {

            let old_left = mem::replace(&mut self.left, tree);
            self.update_stats();

            debug!("replaced left node");

            old_left
        } else {
            trace!("left node not changed as old and new were both None");

            None
        }

    }

    fn insert_right(&mut self, tree: Option<Self::NodePtr>) -> Option<Self::NodePtr> {
        trace!("inserting right node");

        if self.right.is_some() || tree.is_some() {

            let old_right = mem::replace(&mut self.right, tree);
            self.update_stats();

            debug!("replaced right node");

            old_right
        } else {
            trace!("right node not changed as old and new were both None");

            None
        }
    }

    fn value_mut(&mut self) -> &mut Self::Value {
        &mut self.interval
    }

    fn into_parts(self) -> (Self::Value, Option<Self::NodePtr>, Option<Self::NodePtr>) {
        trace!("deconstructing DietNode into parts");

        let parts = (self.interval, self.left, self.right);

        debug!("deconstructed DietNode into parts");

        parts
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
    where
        I: Into<Interval<T>>,
    {
        let interval = value.into();

        trace!("creating new DietNode");

        let diet_node = Self {
            interval: interval,
            left: None,
            right: None,
            count: 1,
            height: 0,
        };

        debug!("created new DietNode");

        diet_node
    }

    // Detaches max from `self` or `self` if there are no right children.
    // Returns the remaining self (if any) and the max.
    fn detach_max_or_self(mut self) -> (Option<Self>, Self) {
        trace!("detaching maximum or self");

        if let Some(n) = self.detach_max(|_| true, |node, _| node.rebalance()) {
            (Some(self), *n)
        } else {
            debug!("returning self as maximum as there were no right children");

            (None, self)
        }
    }

    // Detaches min from `self` or `self` if there are no left children.
    // Returns the remaining self (if any) and the min.
    fn detach_min_or_self(mut self) -> (Option<Self>, Self) {
        trace!("detaching minimum or self");

        if let Some(n) = self.detach_min(|_| true, |node, _| node.rebalance()) {
            (Some(self), *n)
        } else {
            debug!("returning self as minimum as there were no left children");

            (None, self)
        }
    }

    fn navigate_right_and_insert_at_height(&mut self, height: usize, new_node: DietNode<T>) {

        trace!("navigating right and inserting node at height {}", height);

        // Wrap it in an option so it may be taken
        let mut new_node = Some(new_node);

        self.walk_reshape(
            |l| {
                if l.height <= height + 1 {
                    trace!("found node with height {}", l.height);

                    let new_node = new_node.take().unwrap();

                    // 4. replace that node with a new node with value n, and subtrees
                    // l and right. O(1)
                    // By construction, the new node is AVL-balanced, and its subtree 1
                    // taller than right.
                    let new_left = mem::replace(l, new_node);

                    l.insert_left(Some(Box::new(new_left)));

                    debug!("navigated right and inserted node");

                    WalkAction::Stop
                } else {
                    WalkAction::Right
                }
            },
            |_| {},
            |node, _| node.rebalance(),
        );
    }

    fn navigate_left_and_insert_at_height(&mut self, height: usize, new_node: DietNode<T>) {

        trace!("navigating left and inserting node at height {}", height);

        let mut new_node = Some(new_node);

        self.walk_reshape(
            |r| {
                if r.height <= height + 1 {
                    trace!("found node with height {}", r.height);

                    let new_node = new_node.take().unwrap();

                    // 4. replace that node with a new node with value n, and subtrees
                    // left and r. O(1)
                    // By construction, the new node is AVL-balanced, and its subtree
                    // 1 taller than r.
                    let new_right = mem::replace(r, new_node);

                    r.insert_right(Some(Box::new(new_right)));

                    debug!("navigated left and inserted node");

                    WalkAction::Stop
                } else {
                    WalkAction::Left
                }
            },
            |_| {},
            |node, _| node.rebalance(),
        );
    }

    fn join_optional(left: Option<DietNode<T>>, right: Option<DietNode<T>>) -> Option<DietNode<T>> {
        trace!("joining optional nodes");

        let result = if let Some(left) = left {
            let joined = if let Some(right) = right {
                Self::join(left, right)
            } else {
                left
            };

            Some(joined)

        } else {
            right
        };

        debug!("joined optional nodes");

        result
    }

    pub(crate) fn join(mut left: DietNode<T>, mut right: DietNode<T>) -> Self {
        trace!("joining two nodes");

        // Logic from https://stackoverflow.com/a/2037338/921321

        // 1. Determine the height of both trees.
        let mut joined = if left.height < right.height {
            trace!("inserting left node as a child of the right node");

            // 2. remove the rightmost element from the left tree.
            // Let 'n' be that element. (Adjust its computed height if necessary).
            let (left, n) = left.detach_max_or_self();

            let mut new_node = DietNode::new(n.into_parts().0);

            let left_height = left.as_ref().map(|l| l.height).unwrap_or(0);

            new_node.insert_left(left.map(Box::new));

            // 3. In the right tree, navigate left until you reach the node
            // whose subtree has the same height as the left tree. Let r be that node.
            right.navigate_left_and_insert_at_height(left_height, new_node);

            right
        } else {
            trace!("inserting right node as a child of the left node");

            // 2. remove the leftmost element from the right tree.
            // Let 'n' be that element. (Adjust its computed height if necessary).
            let (right, n) = right.detach_min_or_self();

            let mut new_node = DietNode::new(n.into_parts().0);

            let right_height = right.as_ref().map(|r| r.height).unwrap_or(0);

            new_node.insert_right(right.map(Box::new));

            // 3. In the left tree, navigate right until you reach the node
            // whose subtree has the same height as the right tree. Let l be that node.
            left.navigate_right_and_insert_at_height(right_height, new_node);

            left
        };

        joined.rebalance();

        debug!("joined two nodes");

        joined
    }

    pub(crate) fn calculate_walk_direction<Q>(&self, value: &Q) -> Result<WalkDirection, ()>
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        trace!("calculating walk direction for value");

        let interval = self.value();

        if value < interval.inclusive_start().borrow() {
            debug!("walking left as value is less than start");

            Ok(WalkDirection::Left)
        } else if value >= interval.exclusive_end().borrow() {
            debug!("walking left as value is greater than or equal to end");
            Ok(WalkDirection::Right)
        } else {
            debug_assert!(interval.contains(value));

            debug!("no walking as value is contained in interval");
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
        trace!("calculating balance factor");

        let left_height = self.left().map_or(0, |node| node.height + 1);
        trace!("left height: {}", left_height);

        let right_height = self.right().map_or(0, |node| node.height + 1);
        trace!("right height: {}", right_height);

        let balance_factor = right_height as isize - left_height as isize;

        debug!("calculated balance factor: {}", balance_factor);

        balance_factor as i8
    }

    fn update_stats(&mut self) {
        trace!("updating node stats");

        self.count = 1;
        self.height = 0;

        let children = [self.left.as_ref(), self.right.as_ref()];

        for child in children.iter().flat_map(|x| x) {
            self.count += child.count;
            self.height = cmp::max(self.height, child.height + 1);
        }

        debug!(
            "updated node stats, count: {}, height: {}",
            self.count,
            self.height
        );
    }

    pub(crate) fn is_balanced(&self) -> bool {
        trace!("determining if node is balanced");

        let balance_factor = self.balance_factor();

        let is_balanced = balance_factor <= 1 && balance_factor >= -1;

        debug!(
            "node is {}",
            if is_balanced {
                "balanced"
            } else {
                "not balanced"
            }
        );

        is_balanced
    }

    pub(crate) fn rebalance(&mut self) {
        trace!("rebalancing");

        let balance_factor = self.balance_factor();

        if balance_factor > 1 {
            trace!("node is right heavy");

            self.right_mut().map(|node| if node.balance_factor() < 0 {
                trace!("rotating right node right");

                node.rotate_right()
                    .expect("if the node is right-heavy there must be a right child");

                debug!("rotated right node right");
            });

            trace!("rotating node left");
            self.rotate_left().expect(
                "if the node is overly left-heavy there must be a left child",
            );

            debug!("rotated node left");
        } else if balance_factor < -1 {
            trace!("node is left heavy");

            self.left_mut().map(|node| if node.balance_factor() > 0 {
                trace!("rotating left node left");

                node.rotate_left()
                    .expect("if the node is left-heavy there must be a left child");

                debug!("rotated left node left");
            });

            trace!("rotating node right");
            self.rotate_right().expect(
                "if the node is overly right-heavy there must be a right child",
            );

            debug!("rotated node right");
        }

        debug_assert!(self.is_balanced());
        debug!("completed rebalancing");
    }
}

impl<T: AdjacentBound> DietNode<T> {
    pub(crate) fn insert(&mut self, value: T) -> bool {
        trace!("inserting value");

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

        if inserted {
            debug!("inserted value");
        } else {
            debug!("value was already contained within a node's interval");
        }

        inserted
    }

    pub(crate) fn split<Q>(mut self, value: Cow<Q>) -> Result<(Self, Self), Self>
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord + ToOwned<Owned = T>,
    {
        let (merged_left, merged_right, _) = self.walk_reshape_state((None, None, Some(value)),
            |node, &mut (ref mut merged_left, ref mut merged_right, ref mut to_split_on)|{
                let value = to_split_on.take().unwrap();

                match node.calculate_walk_direction(&value) {
                    Ok(WalkDirection::Left) => {
                        *to_split_on = Some(value);

                        let right = node.detach_right().map(|b| *b);
                        *merged_right = Self::join_optional(merged_right.take(), right);

                        WalkAction::Left
                    },
                    Ok(WalkDirection::Right) => {
                        *to_split_on = Some(value);

                        WalkAction::Right
                    },
                    Err(_) => WalkAction::Stop,
                }
            },
            |node, _|{},
            |node, action, _|node.rebalance());

        match (merged_left, merged_right) {
            (Some(left), Some(right)) => Ok((left, right)),
            (Some(only), _) | (_, Some(only)) => Err(only),
            _ => Err(self),
        }
    }

    /// Attempts to remove `value`.
    ///
    /// Returns
    /// Ok(remove_node) - When the value was removed and whether the node should be removed
    /// Err - The value could not be found
    pub(crate) fn remove<Q>(&mut self, value: Cow<Q>) -> Result<bool, ()>
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord + ToOwned<Owned = T> + AdjacentBound,
    {
        trace!("removing value");

        let (result, _) = self.walk_reshape_state((Err(()), Some(value)),
            |node, &mut (ref mut result, ref mut to_remove)| {

                let value = to_remove.take()
                    .expect("should only be traversing if there is a value to remove");

                match node.remove_or_walk(value) {
                    Ok(remove_node) => {
                        *result = Ok(remove_node);
                        WalkAction::Stop
                    },
                    Err((value, direction)) => {
                        *to_remove = Some(value);
                        direction.into()
                    }
                }
            },
            |node, _| node.rebalance(),
            |node, action, &mut (ref mut result, _) | {
                if result.unwrap_or(false) {
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

                    *result = Ok(false);
                }

                node.rebalance();
            });

        self.rebalance();

        result
    }

    fn split_on_value(&mut self, value: T) {
        trace!("splitting the node on a value");

        if self.balance_factor() > 0 {
            self.split_left_on_value(value);
        } else {
            self.split_right_on_value(value);
        }

        debug!("split the node on a value");
    }

    fn split_left_on_value(&mut self, value: T) {
        trace!("splitting left on a value");

        let old_inclusive_start = self.value_mut().set_inclusive_start(value.increment());

        if old_inclusive_start != value {

            let new_left_interval = Interval::from(old_inclusive_start..value);

            let old_left = self.detach_left();

            let mut new_left = Box::new(DietNode::new(new_left_interval));
            new_left.insert_left(old_left);
            new_left.rebalance();

            self.insert_left(Some(new_left));
            self.rebalance();
        } else {
            trace!("no interval to insert as a left child");
        }

        debug!("split left on a value");
    }

    fn split_right_on_value(&mut self, value: T) {
        trace!("splitting right on a value");

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
        } else {
            trace!("no interval to insert as a right child");
        }

        debug!("split right on a value");
    }

    pub(crate) fn insert_or_walk(&mut self, mut value: T) -> Result<bool, (T, WalkDirection)> {
        trace!("inserting value or walking tree to where the value can be inserted");

        if &value < self.value().inclusive_start() {
            if value.is_immediately_before(self.value().inclusive_start()) {
                trace!(
                    "value comes immediately before this node's interval, \
                     extending to include value"
                );

                self.value_mut().set_inclusive_start(value);
                self.join_left();

                debug!("extended lower bound of interval to insert the value");

                Ok(true)
            } else {
                debug!("walking left as value comes before this node's interval");

                Err((value, WalkDirection::Left))
            }
        } else if &value > self.value().exclusive_end() {
            debug!("walking right as value comes after this node's interval");

            Err((value, WalkDirection::Right))
        } else if &value == self.value().exclusive_end() {
            trace!(
                "value comes immediately after this node's interval, \
                 extending to include value"
            );

            value.increment_ref();
            self.value_mut().set_exclusive_end(value);
            self.join_right();

            debug!("extended upper bound of interval to insert the value");

            Ok(true)
        } else {
            debug_assert!(
                self.value().contains(&value),
                "the value should already be contained within the interval"
            );

            debug!("value was already contained in the node's interval");

            Ok(false)
        }
    }

    pub(crate) fn remove_or_walk<'a, Q>(
        &mut self,
        value: Cow<'a, Q>,
    ) -> Result<bool, (Cow<'a, Q>, WalkDirection)>
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord + ToOwned<Owned = T> + AdjacentBound,
    {
        trace!("removing value or walking tree to where the value can be removed from");

        if let Ok(direction) = self.calculate_walk_direction(&value) {
            debug!(
                "walking {:?} to where the value can be removed from",
                direction
            );

            Err((value, direction))
        } else {
            debug_assert!(self.value().contains(&value));

            trace!("this node contains the value");
            let is_last_value;
            let is_first_value;
            {
                let value_borrow: &Q = value.borrow();

                is_last_value =
                    value_borrow.is_immediately_before(self.value().exclusive_end().borrow());

                is_first_value = value_borrow == self.value().inclusive_start().borrow();
            };

            let requires_node_removal = if is_first_value {
                trace!("value is the first value in the nodes interval");
                if is_last_value {
                    trace!("value is the last value in the node's interval");
                    debug!("removing the value requires removal of the entire node");

                    true
                } else {
                    self.value_mut().inclusive_start_mut().increment_ref();

                    debug!("incremented the start of the node's interval to remove the value");

                    false
                }
            } else if is_last_value {
                trace!("value is the last value in the node's interval");

                self.value_mut().exclusive_end_mut().decrement_ref();

                debug!("decremented the end of the node's interval to remove the value");
                false
            } else {
                trace!("the value is in the middle of the node's interval so must be split");

                let value = value.into_owned();
                self.split_on_value(value);

                debug!("split the node to remove the value");
                false
            };

            Ok(requires_node_removal)
        }
    }
}

impl<T: PartialEq> DietNode<T> {
    fn join_left(&mut self) -> bool {
        trace!("attempting to join this node with a left child");

        if let Some(mut left) = self.detach_left() {

            let max;
            if left.value().exclusive_end() == self.value().inclusive_start() {
                trace!(
                    "the left child interval ends at our interval start so we can join to the left"
                );

                self.insert_left(left.detach_left());
                max = Some(left);
            } else {
                trace!(
                    "attempting to detach the maximum child from the left tree which can be joined"
                );

                max = left.detach_max(|max| {
                                          max.value().exclusive_end() ==
                                          self.value().inclusive_start()
                                      },
                                      |node, _| node.rebalance());
                self.insert_left(Some(left));
            }

            if let Some(max) = max {
                debug_assert!(max.right().is_none());

                self.value_mut()
                    .set_inclusive_start(max.into_parts().0.take_inclusive_start());

                debug!("successfully joined with a left child");

                true
            } else {
                debug!("unable to join with a left child as no children were touching this node");
                false
            }
        } else {
            debug!("unable to join with the left child as there was no left child");
            false
        }
    }

    fn join_right(&mut self) -> bool {
        trace!("attempting to join this node with a right child");

        if let Some(mut right) = self.detach_right() {

            let min;
            if right.value().inclusive_start() == self.value().exclusive_end() {
                trace!(
                    "the right child interval starts at our interval end \
                     so we can join to the right"
                );

                self.insert_right(right.detach_right());
                min = Some(right);
            } else {
                trace!(
                    "attempting to detach the minimum child from the right tree which can be joined"
                );

                min = right.detach_min(|min| {
                                           min.value().inclusive_start() ==
                                           self.value().exclusive_end()
                                       },
                                       |node, _| node.rebalance());
                self.insert_right(Some(right));
            }

            if let Some(min) = min {
                debug_assert!(min.left().is_none());

                self.value_mut()
                    .set_exclusive_end(min.into_parts().0.take_exclusive_end());

                debug!("successfully joined with a right child");

                true
            } else {
                debug!("unable to join with a right child as no children were touching this node");
                false
            }
        } else {
            debug!("unable to join with the right child as there was no right child");
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
