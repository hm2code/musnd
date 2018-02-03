//! A set of utilities for dealing with values at given points in time.

use std::error::Error;
use std::f32;
use std::fmt;

/// An immutable time/value pair that represents a value at a point in time.
///
/// # Examples
/// ```rust
/// use musnd::time_val::Pair;
///
/// let p = Pair::new(1.0, 2.0);
/// assert_eq!(p.time(), 1.0);
/// assert_eq!(p.value(), 2.0);
/// ```
#[derive(Debug, PartialEq)]
pub struct Pair {
    time: f32,
    value: f32,
}

impl Pair {
    /// Creates a new `Pair` from the given `time` and `value`.
    ///
    /// # Panics
    ///
    /// If `time` is negative.
    pub fn new(time: f32, value: f32) -> Pair {
        assert!(time >= 0.0, "time can't be negative: {}", time);
        Pair { time, value }
    }

    /// Returns time stored within `self`.
    pub fn time(&self) -> f32 {
        self.time
    }

    /// Returns value stored within `self`.
    pub fn value(&self) -> f32 {
        self.value
    }
}

impl fmt::Display for Pair {
    /// Formats `self` into `"(time, value)"` string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.time, self.value)
    }
}

/// An immutable sequence of `Pair` elements in time increasing order.
///
/// The following is true for any `Seq`:
///
/// * The length is two or greater.
/// * The first `Pair` has time equal to zero.
/// * Time of the last `Pair` represents duration of the whole sequence.
/// * Time of any `Pair` starting from the second position is greater than
/// the time of the previous `Pair` within the sequence.
///
/// `Seq` does not have public constructors so the only way to create a new
/// `Seq` is to use a `SeqBuilder`.
///
/// # Examples
/// ```rust
/// use musnd::time_val::*;
///
/// # fn try_main() -> Result<(), SeqBuilder> {
/// let mut sb = SeqBuilder::new();
/// sb.push(Pair::new(0.0, 1.0));
/// sb.push(Pair::new(1.0, 3.0));
/// sb.push(Pair::new(1.1, 2.0));
/// let s = sb.build()?;
///
/// assert_eq!(s.duration(), 1.1);
/// assert_eq!(s.min(), 1.0);
/// assert_eq!(s.max(), 3.0);
/// # Ok(())
/// # }
/// # fn main() {
/// #     try_main().unwrap();
/// # }
/// ```
#[derive(Debug)]
pub struct Seq {
    pairs: Vec<Pair>,
    duration: f32,
    min: f32,
    max: f32,
}

impl Seq {
    fn new(pairs: Vec<Pair>) -> Seq {
        // Assuming that the input does not break the rules.
        debug_assert!(pairs.len() > 1);
        let mut duration = 0.0;
        let mut min = f32::MAX;
        let mut max = f32::MIN;
        for pair in &pairs {
            duration = pair.time;
            let value = pair.value();
            if value < min {
                min = value;
            }
            if value > max {
                max = value;
            }
        }
        Seq { pairs, duration, min, max }
    }

    /// Extracts a slice containing the entire sequence.
    pub fn as_slice(&self) -> &[Pair] {
        self.pairs.as_slice()
    }

    /// Returns time duration of `self`. The complexity is `O(1)`.
    pub fn duration(&self) -> f32 {
        self.duration
    }

    /// Returns minimal value within `self`. The complexity is `O(1)`.
    pub fn min(&self) -> f32 {
        self.min
    }

    /// Returns maximal value within `self`. The complexity is `O(1)`.
    pub fn max(&self) -> f32 {
        self.max
    }
}

/// A builder for creating a new `Seq` object.
///
/// # Examples
/// ```rust
/// use musnd::time_val::*;
///
/// # fn try_main() -> Result<(), SeqBuilder> {
/// let mut sb = SeqBuilder::new();
/// sb.push(Pair::new(0.0, 1.0));
/// sb.push(Pair::new(2.0, 3.0));
/// let s = sb.build()?;
///
/// assert_eq!(s.as_slice().len(), 2);
/// assert_eq!(s.duration(), 2.0);
/// # Ok(())
/// # }
/// # fn main() {
/// #     try_main().unwrap();
/// # }
/// ```
#[derive(Debug)]
pub struct SeqBuilder {
    pairs: Vec<Pair>,
}

impl SeqBuilder {
    /// Creates a new empty `SeqBuilder`. If the number of `Pair`s is known
    /// in advance, then it would be more efficient to use `with_capacity`
    /// function instead of `new` in order to avoid unnecessary memory
    /// allocations.
    pub fn new() -> SeqBuilder {
        SeqBuilder { pairs: Vec::new() }
    }

    /// Creates a new empty `SeqBuilder` with the given capacity.
    pub fn with_capacity(c: usize) -> SeqBuilder {
        SeqBuilder { pairs: Vec::with_capacity(c) }
    }

    /// Adds `pair` to the sequence. Prefer using `try_push` method for better
    /// error handling and the ability to recover the `pair` in case of an
    /// error.
    ///
    /// # Panics
    ///
    /// * If `self` is empty and `pair.time()` is not 0.0.
    /// * If `pair.time()` is not greater than time of the last `Pair` within
    /// the sequence.
    pub fn push(&mut self, pair: Pair) {
        match self.pairs.last() {
            Some(last) if last.time() >= pair.time() =>
                panic!(TIME_NOT_INCREASING_ERR_MSG),
            None if pair.time() != 0.0 =>
                panic!(NON_ZERO_TIME_ERR_MSG),
            _ => (),
        }
        self.pairs.push(pair);
    }

    /// Adds `pair` to the sequence.
    ///
    /// # Error
    ///
    /// * `SeqError::NonZeroTime` if `self` is empty and `pair.time()` is not
    /// 0.0.
    /// * `SeqError::TimeNotIncreasing` if `pair.time()` is not greater than
    /// time of the last `Pair` within the sequence.
    ///
    /// In case of an error, the `pair` is not added to the sequence and it
    /// can be recovered from the returned enum value.
    pub fn try_push(&mut self, pair: Pair) -> Result<(), SeqError> {
        match self.pairs.last() {
            Some(last) if last.time() >= pair.time() =>
                return Err(SeqError::TimeNotIncreasing(pair)),
            None if pair.time() != 0.0 =>
                return Err(SeqError::NonZeroTime(pair)),
            _ => (),
        }
        self.pairs.push(pair);
        Ok(())
    }

    /// Builds a `Seq` from `self`. Please note that `self` is consumed and
    /// can no longer be used if this method was successful.
    ///
    /// # Error
    ///
    /// A `Seq` cannot be created if `self` contains less than two `Pair`
    /// elements. In this case `self` can be recovered from `Err`.
    pub fn build(mut self) -> Result<Seq, SeqBuilder> {
        if self.pairs.len() < 2 {
            Err(self)
        } else {
            self.pairs.shrink_to_fit();
            Ok(Seq::new(self.pairs))
        }
    }
}

const NON_ZERO_TIME_ERR_MSG: &str =
    "time/value sequence must start with 0.0 time";
const TIME_NOT_INCREASING_ERR_MSG: &str =
    "time is not increasing";

/// Error returned from `SeqBuilder::try_push` method.
///
/// Each variant contains a `Pair` that caused the error.
#[derive(Debug, PartialEq)]
pub enum SeqError {
    /// Indicates that the `Pair` was going to be the first within the sequence
    /// but its time is not 0.0.
    NonZeroTime(Pair),

    /// Indicates that the `Pair` contains time that is less than or equal to
    /// time of the last successfuly added `Pair`.
    TimeNotIncreasing(Pair),
}

impl Error for SeqError {
    fn description(&self) -> &str {
        match self {
            &SeqError::NonZeroTime(_) => NON_ZERO_TIME_ERR_MSG,
            &SeqError::TimeNotIncreasing(_) => TIME_NOT_INCREASING_ERR_MSG,
        }
    }
}

impl fmt::Display for SeqError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &SeqError::NonZeroTime(ref pair) =>
                write!(f, "NonZeroTime{}", pair),
            &SeqError::TimeNotIncreasing(ref pair) =>
                write!(f, "TimeNotIncreasing{}", pair),
        }
    }
}

#[cfg(test)]
mod pair_tests {
    use super::*;

    #[test]
    fn new() {
        let pair = Pair::new(0.0, 1.0);
        assert_eq!(pair.time(), 0.0);
        assert_eq!(pair.value(), 1.0);
    }

    #[test]
    #[should_panic(expected = "time can't be negative")]
    fn new_panics_on_negative_time() {
        Pair::new(-1.0, 1.0);
    }

    #[test]
    fn display() {
        assert_eq!(Pair::new(0.1, 2.3).to_string(), "(0.1, 2.3)");
    }
}

#[cfg(test)]
mod seq_tests {
    use super::*;

    fn new_test_seq() -> Seq {
        let pairs = vec![Pair::new(0.0, 1.0), Pair::new(2.0, 3.0)];
        Seq::new(pairs)
    }

    #[test]
    fn new() {
        let seq = new_test_seq();
        assert_eq!(seq.pairs.len(), 2);
        assert_eq!(seq.pairs[0], Pair::new(0.0, 1.0));
        assert_eq!(seq.pairs[1], Pair::new(2.0, 3.0));
    }

    #[test]
    fn as_slice() {
        let seq = new_test_seq();
        let slice = seq.as_slice();
        assert_eq!(slice.len(), 2);
        assert_eq!(slice[0], Pair::new(0.0, 1.0));
        assert_eq!(slice[1], Pair::new(2.0, 3.0));
    }

    #[test]
    fn duration() {
        assert_eq!(new_test_seq().duration(), 2.0);
    }

    #[test]
    fn min() {
        assert_eq!(new_test_seq().min(), 1.0);
    }

    #[test]
    fn max() {
        assert_eq!(new_test_seq().max(), 3.0);
    }
}

#[cfg(test)]
mod seq_builder_tests {
    use super::*;

    #[test]
    fn new() {
        let builder = SeqBuilder::new();
        assert!(builder.pairs.is_empty());
    }

    #[test]
    fn with_capacity() {
        let builder = SeqBuilder::with_capacity(7);
        assert!(builder.pairs.is_empty());
        assert_eq!(builder.pairs.capacity(), 7);
    }

    #[test]
    fn push() {
        let mut builder = SeqBuilder::new();
        builder.push(Pair::new(0.0, 0.0));
        builder.push(Pair::new(0.1, 1.0));
        builder.push(Pair::new(0.3, 1.0));
        builder.push(Pair::new(1.0, 0.0));
        assert_eq!(builder.pairs.len(), 4);
        assert_eq!(builder.pairs[0], Pair::new(0.0, 0.0));
        assert_eq!(builder.pairs[1], Pair::new(0.1, 1.0));
        assert_eq!(builder.pairs[2], Pair::new(0.3, 1.0));
        assert_eq!(builder.pairs[3], Pair::new(1.0, 0.0));
    }

    #[test]
    #[should_panic(expected = "must start with 0.0 time")]
    fn push_panics_on_nonzero_first() {
        SeqBuilder::new().push(Pair::new(1.0, 2.0));
    }

    #[test]
    #[should_panic(expected = "not increasing")]
    fn push_panics_on_not_increasing() {
        let mut builder = SeqBuilder::new();
        builder.push(Pair::new(0.0, 0.0));
        builder.push(Pair::new(0.0, 1.0));
    }

    #[test]
    fn try_push() {
        let mut builder = SeqBuilder::new();
        assert!(builder.try_push(Pair::new(0.0, 0.0)).is_ok());
        assert!(builder.try_push(Pair::new(0.1, 1.0)).is_ok());
        assert!(builder.try_push(Pair::new(0.4, 0.9)).is_ok());
        assert!(builder.try_push(Pair::new(1.0, 0.1)).is_ok());
        assert_eq!(builder.pairs.len(), 4);
        assert_eq!(builder.pairs[0], Pair::new(0.0, 0.0));
        assert_eq!(builder.pairs[1], Pair::new(0.1, 1.0));
        assert_eq!(builder.pairs[2], Pair::new(0.4, 0.9));
        assert_eq!(builder.pairs[3], Pair::new(1.0, 0.1));
    }

    #[test]
    fn try_push_fails_on_nonzero_first() {
        let result = SeqBuilder::new().try_push(Pair::new(1.0, 2.0));
        assert_eq!(result.unwrap_err().to_string(), "NonZeroTime(1, 2)");
    }

    #[test]
    fn try_push_fails_on_not_increasing() {
        let mut builder = SeqBuilder::new();
        builder.push(Pair::new(0.0, 0.0));
        let result = builder.try_push(Pair::new(0.0, 1.0));
        assert_eq!(result.unwrap_err().to_string(), "TimeNotIncreasing(0, 1)");
        assert_eq!(builder.pairs.len(), 1);
        assert_eq!(builder.pairs[0], Pair::new(0.0, 0.0));
    }

    #[test]
    fn build() {
        let mut builder = SeqBuilder::new();
        builder.push(Pair::new(0.0, 1.0));
        builder.push(Pair::new(2.0, 3.0));
        let seq = builder.build().unwrap();
        let data = seq.as_slice();
        assert_eq!(data.len(), 2);
        assert_eq!(data[0], Pair::new(0.0, 1.0));
        assert_eq!(data[1], Pair::new(2.0, 3.0));
    }

    #[test]
    fn build_fails_if_len_lt_2() {
        let mut builder = SeqBuilder::new();
        builder.push(Pair::new(0.0, 1.0));
        builder = builder.build().unwrap_err();
        assert_eq!(builder.pairs.len(), 1);
        assert_eq!(builder.pairs[0], Pair::new(0.0, 1.0));
        builder.push(Pair::new(0.1, 1.1));
        assert!(builder.build().is_ok());
    }
}

#[cfg(test)]
mod seq_error_tests {
    use super::*;

    #[test]
    fn description() {
        assert_eq!(SeqError::NonZeroTime(Pair::new(0.0, 0.0)).description(),
                   NON_ZERO_TIME_ERR_MSG);
        assert_eq!(SeqError::TimeNotIncreasing(Pair::new(0.0, 0.0))
                       .description(),
                   TIME_NOT_INCREASING_ERR_MSG);
    }

    #[test]
    fn display() {
        assert_eq!(SeqError::NonZeroTime(Pair::new(0.0, 0.0)).to_string(),
                   "NonZeroTime(0, 0)");
        assert_eq!(SeqError::TimeNotIncreasing(Pair::new(0.0, 0.0)).to_string(),
                   "TimeNotIncreasing(0, 0)");
    }
}
