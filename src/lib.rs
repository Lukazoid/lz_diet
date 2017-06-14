mod interval;
mod adjacent_bound;

pub use adjacent_bound::AdjacentBound;

use interval::Interval;
use std::borrow::Borrow;
use std::ops::Range;
use std::collections::VecDeque;
use std::iter::FromIterator;

#[derive(Debug)]
struct DietNode<T> {
    interval: Interval<T>,
    left: Option<Box<DietNode<T>>>,
    right: Option<Box<DietNode<T>>>,
}

#[derive(Debug)]
pub struct Diet<T> {
    root: Option<Box<DietNode<T>>>,
}

#[derive(Debug)]
struct DietNodeIterator<T> {
    pending: VecDeque<T>
}

trait DietNodeRelationshipOps {
    type Bound : AdjacentBound;

    fn max_parent_mut(&mut self) -> &mut Self;

    fn min_parent_mut(&mut self) -> &mut Self;

    fn traverse_to_node_containing(&self, value: &Self::Bound) -> &Self;

    fn traverse_to_node_containing_mut(&mut self, value: &Self::Bound) -> &mut Self;

    fn insert(&mut self, value: Self::Bound) -> bool;

    fn remove(&mut self, value: &Self::Bound) -> bool;
}

impl<T : AdjacentBound> DietNodeRelationshipOps for Option<Box<DietNode<T>>> {
    type Bound = T;

    fn max_parent_mut(&mut self) -> &mut Self {
        let mut parent = self;

        loop {
            let move_next = parent.as_ref().map_or(false, |c|c.right.is_some());
            if move_next {
                parent = &mut {parent}.as_mut().unwrap().right
            } else {
                return parent;
            }
        }
    }

    fn min_parent_mut(&mut self) ->  &mut Self {
        let mut parent = self;

        loop {
            let move_next = parent.as_ref().map_or(false, |c|c.left.is_some());
            if move_next {
                parent = &mut {parent}.as_mut().unwrap().left
            } else {
                return parent;
            }
        }
    }

    fn traverse_to_node_containing(&self, value: &Self::Bound) -> &Self {
        let mut current = self;

        while let Some(ref node) = *current {
            if node.interval.contains(value) {
                break;
            }

            if value < node.interval.inclusive_start() {
                current = &node.left
            } else {
                debug_assert!(value >= node.interval.exclusive_end());
                current = &node.right
            }
        }

        current
    }

    fn traverse_to_node_containing_mut(&mut self, value: &Self::Bound) -> &mut Self {
        let mut current = self;

        loop {
            let local_current = current;
            if let Some(node) = local_current.take() {
                if node.interval.contains(value) {
                    *local_current = Some(node);
                    return local_current;
                }

                if node.is_adjacent(value) {
                    *local_current = Some(node);
                    return local_current;
                }

                if value < node.interval.inclusive_start() {
                    *local_current = Some(node);
                    current = &mut local_current.as_mut().unwrap().left
                } else {
                    debug_assert!(value >= node.interval.exclusive_end());
                    *local_current = Some(node);
                    current = &mut local_current.as_mut().unwrap().right
                }
            } else {
                return local_current;
            }
        }
    }

    fn insert(&mut self, value: Self::Bound) -> bool {
        let mut current = self;
        loop {
            let local_current = current;
            if let Some(ref mut node) = *local_current {
                if value.comes_before(node.interval.inclusive_start()) {

                    node.interval.set_inclusive_start(value);
                    node.join_left();

                    return true;

                } else if &value == node.interval.exclusive_end() {

                    node.interval.set_exclusive_end(value.increment());
                    node.join_right();

                    return true;

                } if &value < node.interval.inclusive_start() {
                    current = &mut node.left;
                } else if &value > node.interval.exclusive_end() {
                    current = &mut node.right;
                }  else {
                    debug_assert!(node.interval.contains(&value), "the value should already be contained within the interval");
                    return false;
                }
            } else {
                let new_exclusive_end = value.increment();
                
                *local_current = Some(Box::new(DietNode {
                    interval: Interval::from(value..new_exclusive_end),
                    left: None, 
                    right: None
                }));

                return true;
            }     
        }   
    }
    
    fn remove(&mut self, value: &Self::Bound) -> bool {
        let containing_node = self.traverse_to_node_containing_mut(value);

        let mut delete_node = false;

        let removed = if let Some(ref mut node) = *containing_node {
            if value == node.interval.inclusive_start() {
                if value.comes_before(node.interval.exclusive_end()) {
                    // The entire node needs to be removed but any children should be moved up
                    match (node.left.take(), node.right.take()) {
                        (None, None) => {
                            delete_node = true
                        }
                        (Some(child), None) | (None, Some(child)) => {
                            *node = child;
                        }
                        (mut left @ Some(_), right @ Some(_)) => {
                            let max = *(left.max_parent_mut().take().unwrap());

                            node.interval = max.interval;
                            node.left = left;
                            node.right = right;
                        }
                    }
                } else {
                    node.interval.inclusive_start_mut().increment_ref();
                }
            } else if value.comes_before(node.interval.exclusive_end()) {
                node.interval.exclusive_end_mut().decrement_ref();
            } else {
                node.split_on_value(value);
            };
            true
        } else {
            false
        };

        if delete_node {
            *containing_node = None;
        }

        removed
    }
}

impl<'a, T> Iterator for DietNodeIterator<&'a DietNode<T>> {
    type Item = &'a DietNode<T>;
    
    fn next(&mut self) -> Option<&'a DietNode<T>> {
        self.pending.pop_front()
            .map(|current| {
                let children = [&current.left, &current.right];
                for child in children.into_iter().flat_map(|x| x.as_ref()) {
                    self.pending.push_back(child);

                }
                current
            })
    }
}

impl<T> DietNode<T> {
    fn min_inclusive_start(&self) -> &T {
        let mut current = self;

        loop {
            if let Some(child) = current.left.as_ref() {
                current = child;
            } else {
                return current.interval.inclusive_start();   
            }
        }
    }

    fn max_exclusive_end(&self) -> &T {
        let mut current = self;

        loop {
            if let Some(child) = current.right.as_ref() {
                current = child;
            } else {
                return current.interval.exclusive_end();   
            }
        }
    }

    pub fn nodes(&self) -> DietNodeIterator<&DietNode<T>> {
        let mut pending = VecDeque::new();
        pending.push_back(self);

        DietNodeIterator {
            pending: pending
        }
    }

    pub fn len(&self) -> usize {
        self.nodes().count()
    }

    pub fn is_adjacent<Q: ?Sized>(&self, value: &Q) -> bool where T : Borrow<Q>, Q : AdjacentBound {
        value.comes_before(self.interval.inclusive_start().borrow()) || 
                    value == self.interval.exclusive_end().borrow()
    }
}

impl<T: AdjacentBound> DietNode<T> {

    pub fn split_on_value(&mut self, value: &T) {
        debug_assert!(self.interval.contains(value), "the value should be contained within the interval");

        let old_exclusive_end = self.interval.set_exclusive_end(value.decrement());

        let new_right_interval = Interval::from(value.increment()..old_exclusive_end);

        let right = self.right.take();
        self.right = Some(Box::new(DietNode {
            interval: new_right_interval,
            left: None,
            right: right
        }));
    }

    fn join_left(&mut self) {
        let max_parent_mut = self.left.max_parent_mut();

        if let Some(max) = max_parent_mut.take() {

            debug_assert!(max.right.is_none(), "the maximum node should have no right children");

            if max.interval.exclusive_end() == self.interval.inclusive_start() {
                // Deref the box so we can take the field values
                let max = *max;

                // If the maximum should be joined with self then the thing which used to point at max should now point at max's left node
                *max_parent_mut = max.left;
                self.interval.set_inclusive_start(max.interval.take_inclusive_start());
            } else {
                *max_parent_mut = Some(max);
            }
        }
        
    }

    fn join_right(&mut self) {
        let min_parent_mut = self.right.min_parent_mut();

        if let Some(min) = min_parent_mut.take() {

            debug_assert!(min.left.is_none(), "the minimum node should have no left children");

            if min.interval.inclusive_start() == self.interval.exclusive_end() {
                // Deref the box so we can take the field values
                let min = *min;

                // If the minimum should be joined with self then the thing which used to point at max should now point at min's right node
                *min_parent_mut = min.right;
                self.interval.set_exclusive_end(min.interval.take_exclusive_end());
            } else {
                *min_parent_mut = Some(min);
            }
        }
    }
}

impl<T> Diet<T> {
    pub fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |n| n.len())
    }
}

impl<T: AdjacentBound> Diet<T> {
    
    pub fn insert(&mut self, value: T) -> bool {
        self.root.insert(value)
    }

    pub fn remove(&mut self, value: &T) -> bool {
        self.root.remove(value)
    }

    pub fn contains(&self, value: &T) -> bool {
        self.root.traverse_to_node_containing(value).is_some()
    }
}

// TODO LH Implement iterators which traverse the intervals in the tree

impl<T> Default for Diet<T>{
    fn default() -> Self {
        Self {
            root: None
        }
    }
}

impl<A : AdjacentBound> FromIterator<A> for Diet<A> {
    fn from_iter<T>(iter: T) -> Self where T: IntoIterator<Item = A> {
        let mut diet = Diet::default();

        for value in iter {
            diet.insert(value);
        }

        diet
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contains_returns_false_for_default(){
        let diet = Diet::<u32>::default();

        assert!(!diet.contains(&5));
    }

    #[test]
    fn contains_returns_true_for_existing_value(){
        let mut diet = Diet::from_iter([3, 1, 5].iter().cloned());

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
    fn insert_combines_ranges() {
        let mut diet = Diet::from_iter([3, 1, 5, 8].iter().cloned());

        diet.insert(2);
        diet.insert(4);
        diet.insert(6);
        diet.insert(7);

        assert_eq!(diet.len(), 1);
    }

    #[test]
    fn remove_returns_false_for_default(){
        let mut diet = Diet::<u32>::default();

        assert!(!diet.remove(&5));
    }

    #[test]
    fn remove_returns_false_for_non_existant_value(){
        let mut diet = Diet::from_iter([1, 2, 3, 6].iter().cloned());

        assert!(!diet.remove(&10));
    }

    #[test]
    fn remove_removes_values(){
        let mut diet = Diet::from_iter([5, 6, 1, 2, 8, 9].iter().cloned());

        assert!(diet.remove(&5));
        assert!(diet.remove(&6));

        assert_eq!(diet.len(), 2);
    }

     #[test]
    fn test_delete_split_left() {
        let mut d = Diet::default();
        d.insert(8);
        d.insert(9);
        d.insert(10);

        d.insert(2);
        d.insert(4);
        d.insert(6);
        d.insert(14);
        d.insert(12);
        d.insert(16);

        d.remove(&8);
        d.remove(&9);
        d.remove(&10);

        assert!(d.contains(&2));
        assert!(d.contains(&4));
        assert!(d.contains(&6));
        assert!(d.contains(&14));
        assert!(d.contains(&12));
        assert!(d.contains(&16));
    }

    
    #[test]
    fn test_delete_simple() {
        let mut d = Diet::default();
        d.remove(&5);
        d.insert(5);
        assert!(d.contains(&5));
        d.remove(&5);
        assert!(!d.contains(&5));
    }

    #[test]
    fn test_delete_branch() {
        let mut d = Diet::default();
        d.insert(5);
        d.insert(3);
        d.insert(7);

        d.remove(&3);
        assert!(!d.contains(&3));
        assert!(d.contains(&5));
        assert!(d.contains(&7));

        d.remove(&7);
        assert!(d.contains(&5));
    }

    #[test]
    fn test_delete_replace_merge() {
        let mut d = Diet::default();
        d.insert(5);
        d.insert(3);

        d.remove(&5);
        assert!(!d.contains(&5));
        assert!(d.contains(&3));

        d.insert(7);
        d.remove(&3);
        assert!(!d.contains(&3));
        assert!(d.contains(&7));
    }

    #[test]
    fn test_delete_lower_upper() {
        let mut d = Diet::default();
        d.insert(5);
        d.insert(6);
        d.insert(7);

        d.remove(&5);
        assert!(d.contains(&6));
        assert!(d.contains(&7));

        d.remove(&7);
        assert!(d.contains(&6));
    }

}
