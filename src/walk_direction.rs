use binary_tree::WalkAction;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub(crate) enum WalkDirection {
    Left, 
    Right
}

impl Into<WalkAction> for WalkDirection {
    fn into(self) -> WalkAction{
        match self {
            WalkDirection::Left => WalkAction::Left,
            WalkDirection::Right => WalkAction::Right
        }
    }
}