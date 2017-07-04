pub trait AdjacentBound: Ord {
    fn is_adjacent(&self, other: &Self) -> bool {
        self.comes_before(other) || self.comes_after(other)
    }

    fn comes_before(&self, other: &Self) -> bool;

    fn comes_after(&self, other: &Self) -> bool;

    fn increment(&self) -> Self;

    fn decrement(&self) -> Self;

    fn increment_ref(&mut self);

    fn decrement_ref(&mut self);
}

macro_rules! adjacent_bound_impl {
    ($type:ty, $one:expr) => {
        impl AdjacentBound for $type {
            fn comes_before(&self, other: &Self) -> bool {
                self == &(other - $one)
            }

            fn comes_after(&self, other: &Self) -> bool {
                self == &(other + $one)
            }

            fn increment(&self) -> Self {
                *self + $one
            }

            fn decrement(&self) -> Self {
                *self - $one
            }

            fn increment_ref(&mut self) {
                *self += $one;
            }

            fn decrement_ref(&mut self) {
                *self -= $one;
            }
        }
    }
}

adjacent_bound_impl!(u8, 1u8);
adjacent_bound_impl!(i8, 1i8);

adjacent_bound_impl!(u16, 1u16);
adjacent_bound_impl!(i16, 1i16);

adjacent_bound_impl!(u32, 1u32);
adjacent_bound_impl!(i32, 1i32);

adjacent_bound_impl!(u64, 1u64);
adjacent_bound_impl!(i64, 1i64);

adjacent_bound_impl!(usize, 1usize);
adjacent_bound_impl!(isize, 1isize);