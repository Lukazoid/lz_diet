use binary_tree::{NodeMut, WalkAction};
use std::cell::RefCell;

/// Some additional methods for `NodeMut`.
pub(crate) trait NodeMutExt: NodeMut {
    /// Insert `new_node` in-order after `self`. `step_out` will be invoked for
    /// all nodes in path from (excluding) the point of insertion, to
    /// (including) `self`, unless `self` is the point of insertion.
    fn insert_after<F>(&mut self, new_node: <Self as NodeMut>::NodePtr, mut step_out: F)
    where
        F: FnMut(&mut Self, WalkAction),
    {
        // this logic is the inverse of the logic taken from insert_before

        if let Some(mut right) = self.detach_right() {
            right.walk_reshape(
                |_| WalkAction::Left,
                move |node| { node.insert_left(Some(new_node)); },
                &mut step_out,
            );
            self.insert_right(Some(right));
            step_out(self, WalkAction::Right);
        } else {
            self.insert_right(Some(new_node));
        }
    }

    fn insert_max<F>(&mut self, new_node: <Self as NodeMut>::NodePtr, mut step_out: F)
    where
        F: FnMut(&mut Self, WalkAction),
    {
        trace!("inserting maximum child node");

        self.walk_reshape(
            |_| WalkAction::Right,
            move |node| {
                debug_assert!(node.right().is_none());

                node.insert_right(Some(new_node));
            },
            &mut step_out,
        );

        debug!("inserted maximum child node");
    }

    fn insert_min<F>(&mut self, new_node: <Self as NodeMut>::NodePtr, mut step_out: F)
    where
        F: FnMut(&mut Self, WalkAction),
    {
        trace!("inserting minimum child node");

        self.walk_reshape(
            |_| WalkAction::Left,
            move |node| {
                debug_assert!(node.left().is_none());

                node.insert_left(Some(new_node));
            },
            &mut step_out,
        );

        debug!("inserted minimum child node");
    }

    fn walk_reshape_state<S, FI, FS, FO>(
        &mut self,
        initial_state: S,
        mut step_in: FI,
        stop: FS,
        mut step_out: FO,
    ) -> S
    where
        FI: FnMut(&mut Self, &mut S) -> WalkAction,
        FS: FnOnce(&mut Self, &mut S),
        FO: FnMut(&mut Self, WalkAction, &mut S),
    {
        let state = RefCell::new(initial_state);

        self.walk_reshape(|node| step_in(node, &mut *state.borrow_mut()),
            |node| stop(node, &mut *state.borrow_mut()),
            |node, action| step_out(node, action, &mut *state.borrow_mut()));

        state.into_inner()
    }

    fn detach_max<P, F>(
        &mut self,
        predicate: P,
        mut step_out: F,
    ) -> Option<<Self as NodeMut>::NodePtr>
    where
        P: FnOnce(&Self) -> bool,
        F: FnMut(&mut Self, WalkAction),
    {
        trace!("conditionally detaching max");

        let (_, extracted_max) = self.walk_reshape_state((None, None),
            |_, _| WalkAction::Right,
            |node, &mut (ref mut new_max, _)| {
                debug_assert!(node.right().is_none());

                if predicate(node) {

                    trace!("detach max predicate passed");
                    *new_max = Some(node.detach_left());
                } else {
                    trace!("detach max predicate failed");
                }
            },
            |node, action, &mut (ref mut new_max, ref mut extracted_max) | {
                if let Some(new_max) = new_max.take() {
                    debug_assert!(extracted_max.is_none());

                    *extracted_max = node.insert_right(new_max);
                }

                step_out(node, action);
            });

        if extracted_max.is_some() {
            debug!("successfully extracted max");
        } else {
            debug!("failed to extract max");
        }

        extracted_max
    }

    fn detach_min<P, F>(
        &mut self,
        predicate: P,
        mut step_out: F,
    ) -> Option<<Self as NodeMut>::NodePtr>
    where
        P: FnOnce(&Self) -> bool,
        F: FnMut(&mut Self, WalkAction),
    {
        trace!("conditionally detaching min");

        let (_, extracted_min) = self.walk_reshape_state((None, None),
            |_, _| WalkAction::Left,
            |node, &mut (ref mut new_min, _)| {
                debug_assert!(node.left().is_none());

                if predicate(node) {
                    trace!("detach min predicate passed");
                    *new_min = Some(node.detach_right());
                } else {
                    trace!("detach min predicate failed");
                }
            },
            |node, action, &mut (ref mut new_min, ref mut extracted_min)| {
                if let Some(new_min) = new_min.take() {
                    debug_assert!(extracted_min.is_none());

                    trace!("detach max predicate passed");
                    *extracted_min = node.insert_left(new_min);
                }

                step_out(node, action);
            });


        if extracted_min.is_some() {
            debug!("successfully extracted min");
        } else {
            debug!("failed to extract min");
        }

        extracted_min
    }
}

// Extend any NodeMut implementors with the additional methods
impl<N> NodeMutExt for N
where
    N: NodeMut,
{
}
