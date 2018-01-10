//! A set of utilities for dealing with values at given points in time.

use std::error::Error;
use std::fmt;

/// An immutable time/value pair that represents a value at a point in time.
#[derive(Debug, PartialEq)]
pub struct Pair {
    time: f32,
    value: f32,
}

impl Pair {
    /// Creates a new `Pair` from the given `time` and `value`.
    ///
    /// # Panics
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

/// An immutable sequence of `Pair` elements in time increasing order.
/// The following is true for any `Seq`:
///
/// * The length is two or greater.
/// * The first `Pair` has time equal to zero.
/// * Time of the last `Pair` represents duration of the whole sequence.
/// * Time of any `Pair` starting from the second position is greater than
/// the time of the previous `Pair` within the sequence.
pub struct Seq {
    pairs: Vec<Pair>,
}

impl Seq {
    // Assumes that the input does not break the rules.
    fn new(pairs: Vec<Pair>) -> Seq {
        Seq { pairs }
    }
}

/// A builder for creating new `Seq` objects.
pub struct SeqBuilder {
    pairs: Vec<Pair>,
}

impl SeqBuilder {
    /// Creates a new empty `SeqBuilder`. If the number of `Pair`s is known
    /// in advance, then it would be more efficient to create a new
    /// `SeqBuilder` using `with_capacity` instead of `new` in order to avoid
    /// unnecessary memory allocations.
    pub fn new() -> SeqBuilder {
        SeqBuilder { pairs: Vec::new() }
    }

    /// Creates a new empty `SeqBuilder` with the given capacity.
    pub fn with_capacity(c: usize) -> SeqBuilder {
        SeqBuilder { pairs: Vec::with_capacity(c) }
    }

    /// Adds the `pair` to the sequence.
    ///
    /// # Panics
    ///
    /// * If `self` is empty and `pair.time()` is not 0.0.
    /// * If `pair.time()` is not greater than the last `Pair` in the sequence.
    pub fn push(&mut self, pair: Pair) {
        match self.pairs.last() {
            Some(p) if p.time() >= pair.time() =>
                panic!(SeqError::TimeNotIncreasing.description()),
            None if pair.time() != 0.0 =>
                panic!(SeqError::NonZeroTime.description()),
            _ => (),
        }
        self.pairs.push(pair);
    }

    // TODO: try_push() -> Result
    // TODO: build() -> Seq
}

#[derive(Debug, PartialEq)]
pub enum SeqError {
    NonZeroTime,
    TimeNotIncreasing,
}

impl Error for SeqError {
    fn description(&self) -> &str {
        match self {
            &SeqError::NonZeroTime =>
                "Time/value sequence must start with 0.0 time.",
            &SeqError::TimeNotIncreasing =>
                "Time must be greater than previous."
        }
    }
}

impl fmt::Display for SeqError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &SeqError::NonZeroTime => write!(f, "NonZeroTime"),
            &SeqError::TimeNotIncreasing => write!(f, "TimeNotIncreasing"),
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
    fn new_time_negative() {
        Pair::new(-1.0, 1.0);
    }
}

#[cfg(test)]
mod seq_tests {
    use super::*;

    #[test]
    fn new() {
        let pairs = vec![Pair::new(0.0, 1.0), Pair::new(2.0, 3.0)];
        let seq = Seq::new(pairs);
        assert_eq!(seq.pairs.len(), 2);
        assert_eq!(seq.pairs[0], Pair::new(0.0, 1.0));
        assert_eq!(seq.pairs[1], Pair::new(2.0, 3.0));
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
    #[should_panic(expected = "must be greater than previous")]
    fn push_panics_on_not_increasing() {
        let mut builder = SeqBuilder::new();
        builder.push(Pair::new(0.0, 0.0));
        builder.push(Pair::new(0.0, 1.0));
    }
}

#[cfg(test)]
mod seq_error_tests {
    use super::*;

    #[test]
    fn description() {
        assert_eq!(SeqError::NonZeroTime.description(),
                   "Time/value sequence must start with 0.0 time.");
    }

    #[test]
    fn display() {
        assert_eq!(SeqError::NonZeroTime.to_string(), "NonZeroTime");
    }
}
