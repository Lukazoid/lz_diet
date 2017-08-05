/// For types which have adjacent values.
pub trait AdjacentBound: Ord {
    /// Determines whether `self` and `other` are adjacent.
    fn is_adjacent(&self, other: &Self) -> bool {
        self.is_immediately_before(other) || self.is_immediately_after(other)
    }

    /// Determines whether `self` is immediately before `other`.
    ///
    /// ```
    /// use lz_diet::AdjacentBound;
    ///
    /// assert!(5u32.is_immediately_before(&6));
    /// assert_eq!(5u32.is_immediately_before(&7), false);
    /// ```
    fn is_immediately_before(&self, other: &Self) -> bool;

    /// Determines whether `self` is immediately after `other`.
    ///
    /// ```
    /// use lz_diet::AdjacentBound;
    ///
    /// assert!(6u32.is_immediately_after(&5));
    /// assert_eq!(7u32.is_immediately_after(&5), false);
    /// ```
    fn is_immediately_after(&self, other: &Self) -> bool;

    /// Returns a new value which is `self` incremented.
    ///
    /// ```
    /// use lz_diet::AdjacentBound;
    ///
    /// assert_eq!(6u32.increment(), 7);
    /// ```
    fn increment(&self) -> Self;

    /// Returns a new value which is `self` decremented.
    ///
    /// ```
    /// use lz_diet::AdjacentBound;
    ///
    /// assert_eq!(6u32.decrement(), 5);
    /// ```
    fn decrement(&self) -> Self;

    /// Increments `self` in place.
    ///
    /// ```
    /// use lz_diet::AdjacentBound;
    ///
    /// let mut value = 6u32;
    /// value.increment_ref();
    /// assert_eq!(value, 7);
    /// ```
    fn increment_ref(&mut self);

    /// Decrements `self` in place.
    ///
    /// ```
    /// use lz_diet::AdjacentBound;
    ///
    /// let mut value = 6u32;
    /// value.decrement_ref();
    /// assert_eq!(value, 5);
    /// ```
    fn decrement_ref(&mut self);
}

/// Implements `AdjacentBound` for a type using the specified value to
/// represent an increment of "one".
///
/// For numeric types $one should be 1, however for other types this
/// will be up the implementor, for dates $one may be a single day.
#[macro_export]
macro_rules! adjacent_bound_impl {
    ($type:ty, $one:expr) => {
        impl ::AdjacentBound for $type {
            fn is_immediately_before(&self, other: &Self) -> bool {
                *self == other.decrement()
            }

            fn is_immediately_after(&self, other: &Self) -> bool {
                *self == other.increment()
            }

            fn increment(&self) -> Self {
                self.to_owned() + $one
            }

            fn decrement(&self) -> Self {
                self.to_owned() - $one
            }

            fn increment_ref(&mut self) {
                *self = self.increment();
            }

            fn decrement_ref(&mut self) {
                *self = self.decrement();
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


#[cfg(feature = "extprim")]
mod extprim_impl {
    use extprim::i128::i128;
    use extprim::u128::u128;

    adjacent_bound_impl!(i128, i128::one());
    adjacent_bound_impl!(u128, u128::one());
}

#[cfg(feature = "extprim")]
pub use self::extprim_impl::*;

#[cfg(feature = "nightly")]
mod nightly_impl {
    adjacent_bound_impl_and_wrapping!(u128, 1u128);
    adjacent_bound_impl_and_wrapping!(i128, 1i128);
}

#[cfg(feature = "nightly")]
pub use self::nightly_impl::*;


#[cfg(feature = "bigint")]
mod num_bigint_impl {
    use num_bigint::{BigInt, BigUint};
    use num_traits::identities::One;

    adjacent_bound_impl!(BigInt, BigInt::one());
    adjacent_bound_impl!(BigUint, BigUint::one());
}

#[cfg(feature = "bigint")]
pub use self::num_bigint_impl::*;
