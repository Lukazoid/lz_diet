/// For types which have adjacent values.
pub trait AdjacentBound: Ord {
    /// Determines whether `self` and `other` are adjacent.
    fn is_adjacent(&self, other: &Self) -> bool {
        self.is_immediately_before(other) || self.is_immediately_after(other)
    }

    /// Determines whether `self` is immediately before `other`.
    fn is_immediately_before(&self, other: &Self) -> bool;

    /// Determines whether `self` is immediately after `other`.
    fn is_immediately_after(&self, other: &Self) -> bool;

    /// Returns a new value which is `self` incremented.
    fn increment(&self) -> Self;

    /// Returns a new value which is `self` decremented.
    fn decrement(&self) -> Self;

    /// Increments `self` in place.
    fn increment_ref(&mut self);

    /// Decrements `self` in place.
    fn decrement_ref(&mut self);
}

macro_rules! adjacent_bound_impl {
    ($type:ty, $one:expr) => {
        impl AdjacentBound for $type {
            fn is_immediately_before(&self, other: &Self) -> bool {
                *self == (*other - $one)
            }

            fn is_immediately_after(&self, other: &Self) -> bool {
                *self == (*other + $one)
            }

            fn increment(&self) -> Self {
                *self + $one
            }

            fn decrement(&self) -> Self {
                *self - $one
            }

            fn increment_ref(&mut self) {
                *self = *self + $one;
            }

            fn decrement_ref(&mut self) {
                *self = *self - $one;
            }
        }
    }
}

macro_rules! adjacent_bound_impl_and_wrapping {
    ($type:ty, $one:expr) => {
        adjacent_bound_impl!($type, $one);
        adjacent_bound_impl!(::std::num::Wrapping<$type>, ::std::num::Wrapping($one));
    }
}

adjacent_bound_impl_and_wrapping!(u8, 1u8);
adjacent_bound_impl_and_wrapping!(i8, 1i8);

adjacent_bound_impl_and_wrapping!(u16, 1u16);
adjacent_bound_impl_and_wrapping!(i16, 1i16);

adjacent_bound_impl_and_wrapping!(u32, 1u32);
adjacent_bound_impl_and_wrapping!(i32, 1i32);

adjacent_bound_impl_and_wrapping!(u64, 1u64);
adjacent_bound_impl_and_wrapping!(i64, 1i64);

adjacent_bound_impl_and_wrapping!(usize, 1usize);
adjacent_bound_impl_and_wrapping!(isize, 1isize);

#[cfg(test)]
mod tests {
    use std::num::Wrapping;
    use AdjacentBound;

    #[test]
    fn overflow_wrapping_tests() {
        assert!(Wrapping(u32::max_value()).is_immediately_before(&Wrapping(0)));
        assert!(Wrapping(0).is_immediately_after(&Wrapping(u32::max_value())));
    }
}

#[cfg(feature = "chrono")]
mod chrono_impl {
    use chrono::{Date, DateTime, Duration, FixedOffset, Local, NaiveDate, NaiveDateTime,
                 NaiveTime, Utc};
    use AdjacentBound;

    adjacent_bound_impl!(NaiveDate, Duration::days(1));
    adjacent_bound_impl!(NaiveDateTime, Duration::min_value());
    adjacent_bound_impl!(NaiveTime, Duration::min_value());

    adjacent_bound_impl!(Date<Utc>, Duration::days(1));
    adjacent_bound_impl!(Date<FixedOffset>, Duration::days(1));
    adjacent_bound_impl!(Date<Local>, Duration::days(1));


    adjacent_bound_impl!(DateTime<Utc>, Duration::min_value());
    adjacent_bound_impl!(DateTime<FixedOffset>, Duration::min_value());
    adjacent_bound_impl!(DateTime<Local>, Duration::min_value());

}

#[cfg(feature = "chrono")]
pub use self::chrono_impl::*;
