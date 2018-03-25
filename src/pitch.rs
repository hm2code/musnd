//! A collection of utilities relates to pitch of musical notes.

use bits::U7;

use std::fmt;
use std::mem;
use std::ops::{Add, Sub};
use std::result;
use std::str::FromStr;

/// Specialized `Result` type for pitch operations.
pub type Result<T> = result::Result<T, Error>;

/// Contains errors reported by this module.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Indicates a pitch parse error.
    ///
    /// Enclosed is the string that cannot be parsed.
    Parse(String),

    /// Indicates a pitch out of range error.
    ///
    /// Enclosed is the number that cannot be converted into a pitch.
    OutOfRange(i32),

    /// Indicates a frequency out of range error.
    ///
    /// Enclosing is the frequency that cannot be converted into a pitch.
    FreqOutOfRange(f32),
}

/// Represents a pitch of a musical note.
///
/// The supported note range is `[C-1, G9]` (from `C` in -1st octave to `G` in
/// 9th octave inclusive). This is the same range as defined by MIDI
/// specification and it can be represented as a number in `[0, 127]` range
/// (7-bit).
///
/// # Examples
/// ```rust
/// use musnd::bits::U7;
/// use musnd::pitch::{Pitch, PitchClass};
///
/// # fn try_main() -> musnd::pitch::Result<()> {
/// let p: Pitch = "A4".parse()?;
/// assert_eq!(PitchClass::from(p), PitchClass::A);
/// assert_eq!(p.octave(), 4);
/// assert_eq!(p.freq(), 440.0);
/// assert_eq!(p.to_string(), "A4");
/// assert_eq!(u8::from(p), 69);
///
/// let p = Pitch::from(U7::from(49));
/// assert_eq!(p.to_string(), "C#3");
/// assert_eq!(u8::from(p), 49);
///
/// let p = Pitch::from_freq(900.0)?;
/// assert_eq!(p.to_string(), "A5");
/// assert_eq!(p.freq(), 880.0);
/// # Ok(())
/// # }
/// # fn main() {
/// #     try_main().unwrap();
/// # }
/// ```
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Pitch(u8);

impl Pitch {
    /// The lowest supported `Pitch`: `C-1`.
    pub const MIN: Pitch = Pitch(0);

    /// The highest supported `Pitch`: `G9`.
    pub const MAX: Pitch = Pitch(U7::MAX);

    /// Minimal frequency in Hertz that can be converted into `Pitch` using
    /// `from_freq` constructor.
    ///
    /// The closest pitch to this frequency is `C-1`.
    pub const MIN_FREQ: f32 = 8.0;

    /// Maximal frequency in Hertz that can be converted into `Pitch` using
    /// `from_freq` constructor.
    ///
    /// The closest pitch to this frequency is `G9`.
    pub const MAX_FREQ: f32 = 12900.0;

    /// Returns a `Pitch` with a frequency that is closest to the given `freq`
    /// in Herz.
    ///
    /// Returns `Error::FreqOutOfRange` if `freq` is less than
    /// `Pitch::MIN_FREQ` or greater than `Pitch::MAX_FREQ`.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::pitch::Pitch;
    ///
    /// # fn try_main() -> musnd::pitch::Result<()> {
    /// assert_eq!(Pitch::from_freq(440.0)?.to_string(), "A4");
    /// assert_eq!(Pitch::from_freq(430.0)?.to_string(), "A4");
    /// assert_eq!(Pitch::from_freq(420.0)?.to_string(), "G#4");
    /// # Ok(())
    /// # }
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    pub fn from_freq(freq: f32) -> Result<Pitch> {
        if freq < Pitch::MIN_FREQ || freq > Pitch::MAX_FREQ {
            return Err(Error::FreqOutOfRange(freq));
        }
        // freq = 440 * pow(2, (pitch - 69) / 12) ->
        // pow(2, (pitch - 69) / 12) = freq / 440 ->
        // (pitch - 69) / 12 = log2(freq / 440) ->
        // pitch - 69 = log2(freq / 440) * 12 ->
        // pitch = log2(freq / 440) * 12 + 69
        let pitch = ((freq / 440.0).log2() * 12.0 + 69.0).round() as u8;
        Ok(Pitch(pitch))
    }

    /// Returns the octave number of `self`.
    ///
    /// The returned number is in `[-1, 9]` range.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::pitch::Pitch;
    ///
    /// assert_eq!(Pitch::MIN.octave(), -1);
    /// assert_eq!(Pitch::MAX.octave(), 9);
    /// ```
    pub fn octave(&self) -> i32 {
        self.0 as i32 / 12 - 1
    }

    /// Returns the frequency of `self` in Hertz.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::pitch::Pitch;
    ///
    /// # use musnd::pitch::Result;
    /// # fn try_main() -> Result<()> {
    /// let p: Pitch = "A4".parse()?;
    /// assert_eq!(p.freq(), 440.0);
    /// # Ok(())
    /// # }
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    pub fn freq(&self) -> f32 {
        440.0 * 2_f32.powf((self.0 as f32 - 69.0) / 12.0)
    }
}

impl From<U7> for Pitch {
    fn from(value: U7) -> Self {
        Pitch(u8::from(value))
    }
}

impl From<Pitch> for U7 {
    fn from(pitch: Pitch) -> Self {
        U7::from(pitch.0)
    }
}

impl From<Pitch> for u8 {
    fn from(pitch: Pitch) -> Self {
        pitch.0
    }
}

impl fmt::Display for Pitch {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", PitchClass::from(*self), self.octave())
    }
}

impl From<Pitch> for String {
    fn from(pitch: Pitch) -> Self {
        pitch.to_string()
    }
}

impl FromStr for Pitch {
    type Err = Error;

    /// Creates a new `Pitch` by parsing `s` string.
    ///
    /// The string must follow Scientific Pitch Notation that has the following
    /// format:
    ///
    /// `P[A][O]`
    ///
    /// where:
    ///
    /// - `P` is the pitch character; can be one of the following characters:
    ///   `C`, `D`, `E`, `F`, `G`, `A`, `B`.
    /// - `A` is the optional pitch adjustment character; can be either `#`
    ///   for sharp note or `b` for flat note.
    /// - `O` is the optional octave number; if omitted, then the 4th octave
    ///   is assumed.
    ///
    /// # Errors
    ///
    /// * `Error::Parse` if `s` is not properly formatted.
    /// * `Error::OutOfRange` if resulting pitch is out of range.
    ///
    /// # Examples
    /// ```
    /// use musnd::pitch::Pitch;
    /// use std::str::FromStr;
    ///
    /// assert!(Pitch::from_str("C").is_ok());
    /// assert!(Pitch::from_str("c").is_err());
    ///
    /// assert!("Bb8".parse::<Pitch>().is_ok());
    /// assert!("Bb9".parse::<Pitch>().is_err());
    /// ```
    fn from_str(s: &str) -> Result<Pitch> {
        if s.is_empty() {
            return Err(Error::Parse("<empty string>".to_string()));
        }

        let bytes = s.as_bytes();
        let mut pitch_class = match bytes[0] {
            b'C' => 0,
            b'D' => 2,
            b'E' => 4,
            b'F' => 5,
            b'G' => 7,
            b'A' => 9,
            b'B' => 11,
            _ => return Err(Error::Parse(s.to_string())),
        };

        let mut octave = 4;
        let len = bytes.len();
        if len > 1 {
            let num_start = match bytes[1] {
                b'#' => {
                    pitch_class += 1;
                    2
                }
                b'b' => {
                    pitch_class -= 1;
                    2
                }
                _ => 1,
            };

            if num_start < len {
                match s[num_start..].parse::<i32>() {
                    Ok(num) => {
                        octave = num;
                    }
                    Err(_) => {
                        return Err(Error::Parse(s.to_string()));
                    }
                }
            }
        }

        let pitch = (octave + 1) * 12 + pitch_class;
        if pitch & !(U7::MAX as i32) != 0 {
            Err(Error::OutOfRange(pitch))
        } else {
            Ok(Pitch(pitch as u8))
        }
    }
}

#[cfg(test)]
mod pitch_tests {
    use super::*;

    #[test]
    fn created_from_u7() {
        assert_eq!(Pitch::from(U7::from(123)).0, 123);
    }

    #[test]
    fn converted_to_u7() {
        assert_eq!(U7::from(Pitch(18)), U7::from(18));
    }

    #[test]
    fn converted_to_u8() {
        assert_eq!(u8::from(Pitch(18)), 18);
    }

    #[test]
    fn created_from_freq() {
        assert_eq!(Pitch::from_freq(430.0).unwrap().0, 69);
        assert_eq!(Pitch::from_freq(440.0).unwrap().0, 69);
        assert_eq!(Pitch::from_freq(450.0).unwrap().0, 69);

        assert_eq!(Pitch::from_freq(8.176).unwrap().0, 0);
        assert_eq!(Pitch::from_freq(12543.9).unwrap().0, U7::MAX);

        assert_eq!(Pitch::from_freq(Pitch::MIN_FREQ).unwrap().0, 0);
        assert_eq!(Pitch::from_freq(Pitch::MAX_FREQ).unwrap().0, U7::MAX);
    }

    #[test]
    fn from_freq_can_fail() {
        assert_eq!(
            Pitch::from_freq(7.9).unwrap_err(),
            Error::FreqOutOfRange(7.9)
        );
        assert_eq!(
            Pitch::from_freq(12900.1).unwrap_err(),
            Error::FreqOutOfRange(12900.1)
        );
    }

    #[test]
    fn parsed_from_str_char() {
        assert_eq!("C".parse::<Pitch>().unwrap(), Pitch(60));
        assert_eq!("D".parse::<Pitch>().unwrap(), Pitch(62));
        assert_eq!("E".parse::<Pitch>().unwrap(), Pitch(64));
        assert_eq!("F".parse::<Pitch>().unwrap(), Pitch(65));
        assert_eq!("G".parse::<Pitch>().unwrap(), Pitch(67));
        assert_eq!("A".parse::<Pitch>().unwrap(), Pitch(69));
        assert_eq!("B".parse::<Pitch>().unwrap(), Pitch(71));
    }

    #[test]
    fn parsed_from_str_sharp() {
        assert_eq!("C#".parse::<Pitch>().unwrap(), Pitch(61));
        assert_eq!("G#".parse::<Pitch>().unwrap(), Pitch(68));
        assert_eq!("E#".parse::<Pitch>().unwrap(), Pitch(65));
    }

    #[test]
    fn parsed_from_str_flat() {
        assert_eq!("Eb".parse::<Pitch>().unwrap(), Pitch(63));
        assert_eq!("Bb".parse::<Pitch>().unwrap(), Pitch(70));
        assert_eq!("Cb".parse::<Pitch>().unwrap(), Pitch(59));
    }

    #[test]
    fn parsed_from_str() {
        assert_eq!("C-1".parse::<Pitch>().unwrap(), Pitch::MIN);
        assert_eq!("C#0".parse::<Pitch>().unwrap(), Pitch(13));
        assert_eq!("Bb1".parse::<Pitch>().unwrap(), Pitch(34));
        assert_eq!("G9".parse::<Pitch>().unwrap(), Pitch::MAX);
    }

    #[test]
    fn parse_can_fail() {
        assert_eq!(
            "".parse::<Pitch>().unwrap_err(),
            Error::Parse("<empty string>".to_string())
        );
        assert_eq!(
            "&".parse::<Pitch>().unwrap_err(),
            Error::Parse("&".to_string())
        );
        assert_eq!(
            "x".parse::<Pitch>().unwrap_err(),
            Error::Parse("x".to_string())
        );
        assert_eq!(
            "Foo Fighters".parse::<Pitch>().unwrap_err(),
            Error::Parse("Foo Fighters".to_string())
        );
        assert_eq!(
            "Abba".parse::<Pitch>().unwrap_err(),
            Error::Parse("Abba".to_string())
        );
        assert_eq!(
            "C# Language".parse::<Pitch>().unwrap_err(),
            Error::Parse("C# Language".to_string())
        );
        assert_eq!("C-2".parse::<Pitch>().unwrap_err(), Error::OutOfRange(-12));
        assert_eq!("A9".parse::<Pitch>().unwrap_err(), Error::OutOfRange(129));
    }

    #[test]
    fn formatted() {
        assert_eq!(format!("{}", Pitch::MIN), "C-1");
        assert_eq!(format!("{}", Pitch(1)), "C#-1");

        assert_eq!(Pitch(U7::MAX - 1).to_string(), "F#9");
        assert_eq!(Pitch::MAX.to_string(), "G9");
    }

    #[test]
    fn converted_to_string() {
        assert_eq!(String::from(Pitch(69)), "A4");
        assert_eq!(String::from(Pitch(70)), "A#4");
    }

    #[test]
    fn octave() {
        assert_eq!(Pitch::MIN.octave(), -1);
        assert_eq!(Pitch(60).octave(), 4);
        assert_eq!(Pitch::MAX.octave(), 9);
    }

    #[test]
    fn freq() {
        assert_eq!(Pitch(69).freq(), 440.0);
        assert_eq!(Pitch(57).freq(), 220.0);
        assert_eq!(Pitch(81).freq(), 880.0);

        assert_eq!(Pitch::MIN.freq(), 8.175798);
        assert_eq!(Pitch::MAX.freq(), 12543.855);

        assert!(Pitch::MIN.freq() > Pitch::MIN_FREQ);
        assert!(Pitch::MAX.freq() < Pitch::MAX_FREQ);
    }
}

/// Represents a pitch class.
///
/// A pitch class is a set of all pitches (notes) that are a whole number of
/// octaves apart, e.g., the pitch class `C` consists of the `C`s in all
/// octaves.
///
/// A `PitchClass` can be transformed into another `PitchClass` using `+` and
/// `-` operators and a number of semitones.
///
/// A number of semitones in both up and down directions between two
/// `PitchClass`es can be obtained using `-` operator.
///
/// # Examples
/// ```rust
/// use musnd::pitch::{Pitch, PitchClass};
///
/// # fn try_main() -> musnd::pitch::Result<()> {
/// let pc_a = PitchClass::from("A3".parse::<Pitch>()?);
/// let pc_c: PitchClass = "C5".parse()?;
///
/// assert_eq!(pc_a, PitchClass::A);
/// assert_eq!(pc_c, PitchClass::C);
///
/// assert_eq!(pc_a + 7, PitchClass::E);
/// assert_eq!(pc_c - 2, PitchClass::ASharp);
///
/// let (up, down) = pc_a - pc_c;
/// assert_eq!(up, 3);   // 3 semitones from A to C
/// assert_eq!(down, 9); // 9 semitones from C to A
///
/// assert_eq!(PitchClass::GSharp.as_str(), "G#");
/// assert_eq!(PitchClass::GSharp.as_str_flat(), "Ab");
/// # Ok(())
/// # }
/// # fn main() {
/// #     try_main().unwrap();
/// # }
/// ```
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum PitchClass {
    /// All `C` pitches.
    C,

    /// All `C#` (`Db`) pitches.
    CSharp,

    /// All `D` pitches.
    D,

    /// All `D#` (`Eb`) pitches.
    DSharp,

    /// All `E` pitches.
    E,

    /// All `F` pitches.
    F,

    /// All `F#` (`Gb`) pitches.
    FSharp,

    /// All `G` pitches.
    G,

    /// All `G#` (`Ab`) pitches.
    GSharp,

    /// All `A` pitches.
    A,

    /// All `A#` (`Bb`) pitches.
    ASharp,

    /// All `B` pitches.
    B,
}

impl PitchClass {
    /// Returns textual representation of `self`.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::pitch::PitchClass;
    ///
    /// assert_eq!(PitchClass::C.as_str(), "C");
    /// assert_eq!(PitchClass::CSharp.as_str(), "C#");
    /// ```
    pub fn as_str(&self) -> &str {
        [
            "C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"
        ][*self as usize]
    }

    /// Returns textual representation of `self` using flats instead of sharps.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::pitch::PitchClass;
    ///
    /// assert_eq!(PitchClass::C.as_str_flat(), "C");
    /// assert_eq!(PitchClass::CSharp.as_str_flat(), "Db");
    /// ```
    pub fn as_str_flat(&self) -> &str {
        [
            "C", "Db", "D", "Eb", "E", "F", "Gb", "G", "Ab", "A", "Bb", "B"
        ][*self as usize]
    }

    /// Returns a `Vec` that contains all supported pitches of the pitch class
    /// `self`.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::pitch::PitchClass;
    ///
    /// let pitches = PitchClass::C.pitches();
    /// assert_eq!(pitches.len(), 11);
    /// assert_eq!(pitches[0].octave(), -1);
    /// assert_eq!(PitchClass::from(pitches[0]), PitchClass::C);
    /// assert_eq!(pitches[10].octave(), 9);
    /// assert_eq!(PitchClass::from(pitches[10]), PitchClass::C);
    ///
    /// let pitches = PitchClass::A.pitches();
    /// assert_eq!(pitches.len(), 10);
    /// assert_eq!(pitches[0].octave(), -1);
    /// assert_eq!(PitchClass::from(pitches[0]), PitchClass::A);
    /// assert_eq!(pitches[9].octave(), 8);
    /// assert_eq!(PitchClass::from(pitches[9]), PitchClass::A);
    /// ```
    pub fn pitches(&self) -> Vec<Pitch> {
        let mut pitch = *self as u8;
        // The last allocated element is unused for pitches greater than 7 (G).
        let mut vec = Vec::with_capacity(11);
        while pitch & !U7::MAX == 0 {
            vec.push(Pitch(pitch));
            pitch += 12;
        }
        vec
    }
}

impl From<Pitch> for PitchClass {
    /// Extracts `PitchClass` from `pitch`.
    ///
    /// # Examples:
    /// ```rust
    /// use musnd::pitch::{Pitch, PitchClass};
    ///
    /// # fn try_main() -> musnd::pitch::Result<()> {
    /// let p: Pitch = "A4".parse()?;
    ///
    /// let pc = PitchClass::from(p);
    /// assert_eq!(pc, PitchClass::A);
    ///
    /// let pc: PitchClass = p.into();
    /// assert_eq!(pc, PitchClass::A);
    /// # Ok(())
    /// # }
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    fn from(pitch: Pitch) -> Self {
        unsafe { mem::transmute::<u8, PitchClass>(pitch.0 % 12) }
    }
}

impl fmt::Display for PitchClass {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl FromStr for PitchClass {
    type Err = Error;

    /// Parses `s` into a `PitchClass`.
    ///
    /// The result is the same as if `s` was parsed into `Pitch` and then
    /// `PitchClass` was extracted from it.
    ///
    /// # Errors
    ///
    /// * `Error::Parse` if `s` is not properly formatted.
    /// * `Error::OutOfRange` if resulting pitch is out of range.
    ///
    /// # Examples
    /// ```
    /// use musnd::pitch::{Pitch, PitchClass};
    ///
    /// # fn try_main() -> musnd::pitch::Result<()> {
    /// let pc: PitchClass = "C#6".parse()?;
    /// assert_eq!(pc, PitchClass::CSharp);
    /// # Ok(())
    /// # }
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    fn from_str(s: &str) -> Result<PitchClass> {
        match Pitch::from_str(s) {
            Ok(pitch) => Ok(PitchClass::from(pitch)),
            Err(err) => Err(err),
        }
    }
}

impl Add<i32> for PitchClass {
    type Output = PitchClass;

    /// Performs the `+` operation and returns a `PitchClass` that is `rhs`
    /// semitones up from `self`.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::pitch::PitchClass;
    ///
    /// assert_eq!(PitchClass::C + 5, PitchClass::F);
    /// assert_eq!(PitchClass::C + 15, PitchClass::DSharp);
    /// ```
    fn add(self, rhs: i32) -> PitchClass {
        let pclass = (((self as i32 + rhs) % 12) + 12) % 12;
        unsafe { mem::transmute(pclass as u8) }
    }
}

impl Sub<i32> for PitchClass {
    type Output = PitchClass;

    /// Performs the `-` operation and returns a `PitchClass` that is `rhs`
    /// semitones down from `self`.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::pitch::PitchClass;
    ///
    /// assert_eq!(PitchClass::C - 5, PitchClass::G);
    /// assert_eq!(PitchClass::C - 15, PitchClass::A);
    /// ```
    fn sub(self, rhs: i32) -> PitchClass {
        self + (-rhs)
    }
}

impl Sub<PitchClass> for PitchClass {
    /// The resulting type after applying the `-` operator.
    ///
    /// The first element is the number of semitones up and the second is
    /// the number of semitones down. Both values are in [0, 11] range and
    /// represented as `i32` for convenience.
    type Output = (i32, i32);

    /// Performs the `-` operation and returns the number of semitones between
    /// the operands in both up and down directions.
    ///
    /// # Example
    /// ```rust
    /// use musnd::pitch::PitchClass;
    ///
    /// let (up, down) = PitchClass::C - PitchClass::E;
    /// assert_eq!(up, 4);   // 4 semitones up from C to E
    /// assert_eq!(down, 8); // 8 semitones down from C to E
    ///
    /// let (up, down) = PitchClass::E - PitchClass::C;
    /// assert_eq!(up, 8);   // 8 semitones up from E to C
    /// assert_eq!(down, 4); // 4 semitones down from E to C
    /// ```
    fn sub(self, rhs: PitchClass) -> (i32, i32) {
        let lhs = self as i32;
        let rhs = rhs as i32;
        ((rhs - lhs + 12) % 12, (lhs - rhs + 12) % 12)
    }
}

#[cfg(test)]
mod pitch_class_tests {
    use super::*;

    #[test]
    fn created_from_pitch() {
        assert_eq!(PitchClass::from(Pitch(0)), PitchClass::C);
        assert_eq!(PitchClass::from(Pitch(13)), PitchClass::CSharp);
        assert_eq!(PitchClass::from(Pitch(26)), PitchClass::D);
        assert_eq!(PitchClass::from(Pitch(39)), PitchClass::DSharp);
        assert_eq!(PitchClass::from(Pitch(52)), PitchClass::E);
        assert_eq!(PitchClass::from(Pitch(65)), PitchClass::F);
        assert_eq!(PitchClass::from(Pitch(78)), PitchClass::FSharp);
        assert_eq!(PitchClass::from(Pitch(91)), PitchClass::G);
        assert_eq!(PitchClass::from(Pitch(104)), PitchClass::GSharp);
        assert_eq!(PitchClass::from(Pitch(117)), PitchClass::A);
        assert_eq!(PitchClass::from(Pitch(118)), PitchClass::ASharp);
        assert_eq!(PitchClass::from(Pitch(119)), PitchClass::B);
    }

    #[test]
    fn parsed_from_str() {
        assert_eq!("C".parse::<PitchClass>().unwrap(), PitchClass::C);
        assert_eq!("C#".parse::<PitchClass>().unwrap(), PitchClass::CSharp);
        assert_eq!("Eb".parse::<PitchClass>().unwrap(), PitchClass::DSharp);
        assert_eq!("A4".parse::<PitchClass>().unwrap(), PitchClass::A);
        assert_eq!("F#-1".parse::<PitchClass>().unwrap(), PitchClass::FSharp);
        assert_eq!("Bb8".parse::<PitchClass>().unwrap(), PitchClass::ASharp);
    }

    #[test]
    fn parse_can_fail() {
        assert_eq!(
            "BAR".parse::<PitchClass>().unwrap_err(),
            Error::Parse("BAR".to_string())
        );
    }

    #[test]
    fn as_str() {
        assert_eq!(PitchClass::C.as_str(), "C");
        assert_eq!(PitchClass::CSharp.as_str(), "C#");
        assert_eq!(PitchClass::D.as_str(), "D");
        assert_eq!(PitchClass::DSharp.as_str(), "D#");
        assert_eq!(PitchClass::E.as_str(), "E");
        assert_eq!(PitchClass::F.as_str(), "F");
        assert_eq!(PitchClass::FSharp.as_str(), "F#");
        assert_eq!(PitchClass::G.as_str(), "G");
        assert_eq!(PitchClass::GSharp.as_str(), "G#");
        assert_eq!(PitchClass::A.as_str(), "A");
        assert_eq!(PitchClass::ASharp.as_str(), "A#");
        assert_eq!(PitchClass::B.as_str(), "B");
    }

    #[test]
    fn as_str_flat() {
        assert_eq!(PitchClass::C.as_str_flat(), "C");
        assert_eq!(PitchClass::CSharp.as_str_flat(), "Db");
        assert_eq!(PitchClass::D.as_str_flat(), "D");
        assert_eq!(PitchClass::DSharp.as_str_flat(), "Eb");
        assert_eq!(PitchClass::E.as_str_flat(), "E");
        assert_eq!(PitchClass::F.as_str_flat(), "F");
        assert_eq!(PitchClass::FSharp.as_str_flat(), "Gb");
        assert_eq!(PitchClass::G.as_str_flat(), "G");
        assert_eq!(PitchClass::GSharp.as_str_flat(), "Ab");
        assert_eq!(PitchClass::A.as_str_flat(), "A");
        assert_eq!(PitchClass::ASharp.as_str_flat(), "Bb");
        assert_eq!(PitchClass::B.as_str_flat(), "B");
    }

    #[test]
    fn pitches() {
        fn check_pitches(pc: PitchClass, len: usize) {
            let pitches = pc.pitches();
            assert_eq!(
                pitches.len(),
                len,
                "Expected {} elements for {} pitches, got {}",
                len,
                pc,
                pitches.len()
            );
            for (i, &p) in pitches.iter().enumerate() {
                assert_eq!(PitchClass::from(p), pc);
                assert_eq!(p.octave(), i as i32 - 1);
            }
        }

        check_pitches(PitchClass::C, 11);
        check_pitches(PitchClass::G, 11);
        check_pitches(PitchClass::GSharp, 10);
        check_pitches(PitchClass::B, 10);
    }

    #[test]
    fn formatted() {
        assert_eq!(format!("{}", PitchClass::C), PitchClass::C.as_str());
        assert_eq!(PitchClass::CSharp.to_string(), PitchClass::CSharp.as_str());
    }

    #[test]
    fn add_i32() {
        assert_eq!(PitchClass::C + 2, PitchClass::D);
        assert_eq!(PitchClass::A + 15, PitchClass::C);
        assert_eq!(PitchClass::C + (-2), PitchClass::ASharp);
        assert_eq!(PitchClass::A + (-28), PitchClass::F);
    }

    #[test]
    fn sub_i32() {
        assert_eq!(PitchClass::C - 2, PitchClass::ASharp);
        assert_eq!(PitchClass::A - 15, PitchClass::FSharp);
        assert_eq!(PitchClass::C - (-2), PitchClass::D);
        assert_eq!(PitchClass::A - (-28), PitchClass::CSharp);
    }

    #[test]
    fn sub_pitch_class() {
        assert_eq!(PitchClass::C - PitchClass::A, (9, 3));
        assert_eq!(PitchClass::A - PitchClass::C, (3, 9));
        assert_eq!(PitchClass::E - PitchClass::E, (0, 0));
        assert_eq!(PitchClass::E - PitchClass::ASharp, (6, 6));
    }
}
