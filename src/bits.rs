//! Unsigned integers of non-standard size.

/// An immutable 3-bit unsigned integer.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct U3(u8);

impl U3 {
    /// Maximal `u8` value that can fit into `U3`.
    pub const MAX: u8 = 0x07;

    /// Tries to convert `v` into `U3`.
    ///
    /// The conversion is possible only if `v` is less than or equal to
    /// `MAX` value. Use `from` for conversion by ignoring upper 5 bits.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U3;
    ///
    /// assert_eq!(U3::try_from(0x07), Some(U3::from(0x07)));
    /// assert_eq!(U3::try_from(0xFF), None);
    /// ```
    pub fn try_from(v: u8) -> Option<U3> {
        if v & !U3::MAX == 0 {
            Some(U3(v))
        } else {
            None
        }
    }
}

impl From<u8> for U3 {
    /// Convets lower 3 bits of `v` into `U3`.
    ///
    /// The upper 5 bits are ignored.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U3;
    ///
    /// let v = U3::from(0x07);
    /// assert_eq!(u8::from(v), 0x07);
    ///
    /// let v = U3::from(0xFF);
    /// assert_eq!(u8::from(v), 0x07);
    /// ```
    fn from(v: u8) -> U3 {
        U3(v & U3::MAX)
    }
}

impl From<U3> for u8 {
    fn from(v: U3) -> u8 {
        v.0
    }
}

#[cfg(test)]
mod u3_tests {
    use super::U3;

    #[test]
    fn from() {
        assert_eq!(U3::from(0x00).0, 0x00);
        assert_eq!(U3::from(0x05).0, 0x05);
        assert_eq!(U3::from(0x0F).0, 0x07);
        assert_eq!(U3::from(0x12).0, 0x02);
    }

    #[test]
    fn try_from() {
        assert_eq!(U3::try_from(0x07), Some(U3::from(0x07)));
        assert_eq!(U3::try_from(0x08), None);
    }
}

/// An immutable 4-bit unsigned integer.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct U4(u8);

impl U4 {
    /// Maximal `u8` value that can fit into `U4`.
    pub const MAX: u8 = 0x0F;

    /// Tries to convert `v` into `U4`.
    ///
    /// The conversion is possible only if `v` is less than or equal to
    /// `MAX` value. Use `from` for conversion by ignoring upper 4 bits.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U4;
    ///
    /// assert_eq!(U4::try_from(0x0F), Some(U4::from(0x0F)));
    /// assert_eq!(U4::try_from(0xFF), None);
    /// ```
    pub fn try_from(v: u8) -> Option<U4> {
        if v & !U4::MAX == 0 {
            Some(U4(v))
        } else {
            None
        }
    }
}

impl From<u8> for U4 {
    /// Convets lower 4 bits of `v` into `U4`.
    ///
    /// The upper 4 bits are ignored.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U4;
    ///
    /// let v = U4::from(0x0F);
    /// assert_eq!(u8::from(v), 0x0F);
    ///
    /// let v = U4::from(0xAB);
    /// assert_eq!(u8::from(v), 0x0B);
    /// ```
    fn from(v: u8) -> U4 {
        U4(v & U4::MAX)
    }
}

impl From<U4> for u8 {
    fn from(v: U4) -> u8 {
        v.0
    }
}

#[cfg(test)]
mod u4_tests {
    use super::U4;

    #[test]
    fn from() {
        assert_eq!(U4::from(0x00).0, 0x00);
        assert_eq!(U4::from(0x0F).0, 0x0F);
        assert_eq!(U4::from(0x12).0, 0x02);
    }

    #[test]
    fn try_from() {
        assert_eq!(U4::try_from(0x0F), Some(U4::from(0x0F)));
        assert_eq!(U4::try_from(0xFF), None);
    }
}

/// An immutable 7-bit unsigned integer.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct U7(u8);

impl U7 {
    /// Maximal `u8` value that can fit into `U7`.
    pub const MAX: u8 = 0x7F;

    /// Tries to convert `v` into `U7`.
    ///
    /// The conversion is possible only if `v` is less than or equal to
    /// `MAX` value. Use `from` for conversion by ignoring the most significant
    /// bit.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U7;
    ///
    /// assert_eq!(U7::try_from(0x7F), Some(U7::from(0x7F)));
    /// assert_eq!(U7::try_from(0x80), None);
    /// ```
    pub fn try_from(v: u8) -> Option<U7> {
        if v & !U7::MAX == 0 {
            Some(U7(v))
        } else {
            None
        }
    }
}

impl From<u8> for U7 {
    /// Convets lower 7 bits of `v` into `U7`.
    ///
    /// The most significant bit is ignored.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U7;
    ///
    /// let v = U7::from(0x7F);
    /// assert_eq!(u8::from(v), 0x7F);
    ///
    /// let v = U7::from(0xFF);
    /// assert_eq!(u8::from(v), 0x7F);
    /// ```
    fn from(v: u8) -> U7 {
        U7(v & U7::MAX)
    }
}

impl From<U7> for u8 {
    fn from(v: U7) -> u8 {
        v.0
    }
}

#[cfg(test)]
mod u7_tests {
    use super::U7;

    #[test]
    fn from() {
        assert_eq!(U7::from(0x00).0, 0x00);
        assert_eq!(U7::from(0x7F).0, 0x7F);
        assert_eq!(U7::from(0x82).0, 0x02);
    }

    #[test]
    fn try_from() {
        assert_eq!(U7::try_from(0x7F), Some(U7::from(0x7F)));
        assert_eq!(U7::try_from(0x80), None);
    }
}

/// An immutable 14-bit unsigned integer.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct U14(u16);

impl U14 {
    /// Maximal `u16` value that can fit into `U14`.
    pub const MAX: u16 = 0x3FFF;

    /// Creates new `U14` by combining two `U7` values.
    ///
    /// The less significant bits are passed as `lsb` parameter and the most
    /// significant bits as `msb`. The bits are combined as `(msb << 7) | lsb`.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::{U14, U7};
    ///
    /// let lsb = U7::from(0b0010_1010);
    /// let msb = U7::from(0b0101_0101);
    /// assert_eq!(U14::new(lsb, msb), U14::from(0b0010_1010_1010_1010));
    /// ```
    pub fn new(lsb: U7, msb: U7) -> U14 {
        let lsb = u8::from(lsb) as u16;
        let msb = u8::from(msb) as u16;
        U14((msb << 7) | lsb)
    }

    /// Tries to convert `v` into `U14`.
    ///
    /// The conversion is possible only if `v` is less than or equal to
    /// `MAX` value. Use `from` for conversion by ignoring the most significant
    /// bit.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U14;
    ///
    /// assert_eq!(U14::try_from(0x3FFF), Some(U14::from(0x3FFF)));
    /// assert_eq!(U14::try_from(0x4000), None);
    /// ```
    pub fn try_from(v: u16) -> Option<U14> {
        if v & !U14::MAX == 0 {
            Some(U14(v))
        } else {
            None
        }
    }
}

impl From<u16> for U14 {
    /// Convets lower 14 bits of `v` into `U14`.
    ///
    /// The most significant bit is ignored.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U14;
    ///
    /// let v = U14::from(0x3FFF);
    /// assert_eq!(u16::from(v), 0x3FFF);
    ///
    /// let v = U14::from(0xFFFF);
    /// assert_eq!(u16::from(v), 0x3FFF);
    /// ```
    fn from(v: u16) -> U14 {
        U14(v & U14::MAX)
    }
}

impl From<U14> for u16 {
    fn from(v: U14) -> u16 {
        v.0
    }
}

#[cfg(test)]
mod u14_tests {
    use super::U14;

    #[test]
    fn new() {
        use super::U7;

        let u7max = U7::from(U7::MAX);
        assert_eq!(U14::new(u7max, u7max), U14::from(U14::MAX));

        assert_eq!(U14::new(U7::from(0x12), U7::from(0x34)), U14::from(0x1A12));
    }

    #[test]
    fn from() {
        assert_eq!(U14::from(0x0000).0, 0x0000);
        assert_eq!(U14::from(0x1234).0, 0x1234);
        assert_eq!(U14::from(0x4321).0, 0x0321);
    }

    #[test]
    fn try_from() {
        assert_eq!(U14::try_from(0x3456), Some(U14::from(0x3456)));
        assert_eq!(U14::try_from(0x4567), None);
    }
}

/// An immutable 15-bit unsigned integer.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct U15(u16);

impl U15 {
    /// Maximal `u16` value that can fit into `U15`.
    pub const MAX: u16 = 0x7FFF;

    /// Tries to convert `v` into `U15`.
    ///
    /// The conversion is possible only if `v` is less than or equal to
    /// `MAX` value. Use `from` for conversion by ignoring the most significant
    /// bit.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U15;
    ///
    /// assert_eq!(U15::try_from(0x7FFF), Some(U15::from(0x7FFF)));
    /// assert_eq!(U15::try_from(0x8000), None);
    /// ```
    pub fn try_from(v: u16) -> Option<U15> {
        if v & !U15::MAX == 0 {
            Some(U15(v))
        } else {
            None
        }
    }
}

impl From<u16> for U15 {
    /// Convets lower 15 bits of `v` into `U15`.
    ///
    /// The most significant bit is ignored.
    ///
    /// # Examples
    /// ```rust
    /// use musnd::bits::U15;
    ///
    /// let v = U15::from(0x7FFF);
    /// assert_eq!(u16::from(v), 0x7FFF);
    ///
    /// let v = U15::from(0xFFFF);
    /// assert_eq!(u16::from(v), 0x7FFF);
    /// ```
    fn from(v: u16) -> U15 {
        U15(v & U15::MAX)
    }
}

impl From<U15> for u16 {
    fn from(v: U15) -> u16 {
        v.0
    }
}

#[cfg(test)]
mod u15_tests {
    use super::U15;

    #[test]
    fn from() {
        assert_eq!(U15::from(0x0000).0, 0x0000);
        assert_eq!(U15::from(0x1234).0, 0x1234);
        assert_eq!(U15::from(0x8765).0, 0x0765);
    }

    #[test]
    fn try_from() {
        assert_eq!(U15::try_from(0x3456), Some(U15::from(0x3456)));
        assert_eq!(U15::try_from(0x8765), None);
    }
}
