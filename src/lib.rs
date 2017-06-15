mod interval;
mod adjacent_bound;

pub use adjacent_bound::AdjacentBound;

use interval::Interval;
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
struct DietNodeBreadthIterator<T> {
    pending: VecDeque<T>
}

#[derive(Debug)]
struct DietNodeOrderedIterator<T> {
    current: Option<T>,
    stack: Vec<T>,
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

            match current.as_ref().map(|n| n.interval.contains(value)) {
                None | Some(true) => {
                    // If there is no current or current contains the value then return it
                    return current; 
                }
                _ => { }
            }

            let node = {current}.as_mut().unwrap();
            if value < node.interval.inclusive_start() {
                current = &mut node.left;
            } else {
                debug_assert!(value >= node.interval.exclusive_end());

                current = &mut node.right;
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

impl<'a, T> Iterator for DietNodeBreadthIterator<&'a DietNode<T>> {
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

impl<'a, T> Iterator for DietNodeOrderedIterator<&'a DietNode<T>> {
    type Item = &'a DietNode<T>;

    fn next(&mut self) -> Option<&'a DietNode<T>> {
        
        let mut current = self.current.take();

        // Move to the left-most node
        while let Some(node) = current {
            // As we pass each node push it to the stack to be returned and right-traversed later
            self.stack.push(node);

            current = node.left.as_ref().map(Box::as_ref);
        }

        let result = self.stack.pop();

        // Attempt to move the iterator to the right node
        self.current = result.and_then(|n| n.right.as_ref()).map(Box::as_ref);

        result
    }
}

impl<T> DietNode<T> {
    pub fn nodes(&self) -> DietNodeBreadthIterator<&DietNode<T>> {
        let mut pending = VecDeque::new();
        pending.push_back(self);

        DietNodeBreadthIterator {
            pending: pending
        }
    }

    pub fn ordered_nodes(&self) -> DietNodeOrderedIterator<&DietNode<T>> {
        DietNodeOrderedIterator {
            current: Some(self),
            stack: Default::default()
        }
    }

    pub fn len(&self) -> usize {
        self.nodes().count()
    }
}

impl<T: AdjacentBound> DietNode<T> {

    pub fn split_on_value(&mut self, value: &T) {
        debug_assert!(self.interval.contains(value), "the value should be contained within the interval");

        let old_exclusive_end = self.interval.set_exclusive_end(value.to_owned());

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

        let interval = &mut self.interval;       

        let should_merge = max_parent_mut.as_ref().map_or(false, |c| c.interval.exclusive_end() == interval.inclusive_start());

        if should_merge {
            let max = *max_parent_mut.take().unwrap();
            *max_parent_mut = max.left;
            interval.set_inclusive_start(max.interval.take_inclusive_start());
        }        
    }

    fn join_right(&mut self) {
        let min_parent_mut = self.right.min_parent_mut();

        let interval = &mut self.interval;

        let should_merge = min_parent_mut.as_ref().map_or(false, |c| c.interval.inclusive_start() == interval.exclusive_end());

        if should_merge {
            let min = *min_parent_mut.take().unwrap();
            *min_parent_mut = min.right;
            interval.set_exclusive_end(min.interval.take_exclusive_end());
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
    fn remove_of_adjacent_returns_false() {
        let mut diet = Diet::from_iter([4, 5, 6].iter().cloned());

        assert!(!diet.remove(&3));
    }

    #[test]
    fn remove_of_lower_bounds() {
        let mut diet = Diet::from_iter([50, 51, 52, 1, 2, 20, 21].iter().cloned());

        assert!(diet.remove(&50));
        assert!(!diet.contains(&50));

        assert!(diet.remove(&51));
        assert!(!diet.contains(&51));

        assert!(diet.remove(&1));
        assert!(!diet.contains(&1));

        assert!(diet.remove(&20));
        assert!(!diet.contains(&20));

        assert_eq!(diet.len(), 3);
    }

    #[test]
    fn remove_of_upper_bounds() {
        let mut diet = Diet::from_iter([50, 51, 52, 1, 2, 20, 21].iter().cloned());

        assert!(diet.remove(&52));
        assert!(!diet.contains(&52));

        assert!(diet.remove(&51));
        assert!(!diet.contains(&51));

        assert!(diet.remove(&2));
        assert!(!diet.contains(&2));

        assert!(diet.remove(&21));
        assert!(!diet.contains(&21));

        assert_eq!(diet.len(), 3);
    }

    #[test]
    fn remove_root_node() {
        let mut diet = Diet::from_iter([50, 51, 1, 2, 10, 20, 21].iter().cloned());

        assert!(diet.remove(&50));
        assert!(!diet.contains(&50));
        assert!(diet.remove(&51));
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
        let mut diet = Diet::from_iter([1, 2, 3].iter().cloned());

        assert!(diet.remove(&2));
        assert!(!diet.contains(&2));

        assert!(diet.contains(&1));
        assert!(diet.contains(&3));

        assert_eq!(diet.len(), 2);
    } 

    

}
