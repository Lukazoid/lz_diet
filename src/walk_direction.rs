use binary_tree::WalkAction;

/// The directions which a walk can be performed in.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub(crate) enum WalkDirection {
    /// Walk to the left.
    Left,

    /// Walk to the right.
    Right,
}

impl Into<WalkAction> for WalkDirection {
    fn into(self) -> WalkAction {
        match self {
            WalkDirection::Left => WalkAction::Left,
            WalkDirection::Right => WalkAction::Right,
        }
    }
}
