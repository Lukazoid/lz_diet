#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SplitResult<T> {
    Split(T, T),
    Single(T),
    None,
}
