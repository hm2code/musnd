//! Small (less than byte) integers.

/// An immutable 4-bit unsigned integer.
#[derive(Debug, PartialEq)]
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
    /// ```
    /// use musnd::bits::U4;
    ///
    /// assert_eq!(U4::try_from(0x0F), Some(U4::from(0x0F)));
    /// assert_eq!(U4::try_from(0xFF), None);
    /// ```
    pub fn try_from(v: u8) -> Option<U4> {
        if v & 0xF0 == 0 {
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
    /// ```
    /// use musnd::bits::U4;
    ///
    /// let v = U4::from(0x0F);
    /// assert_eq!(u8::from(v), 0x0F);
    ///
    /// let v = U4::from(0xAB);
    /// assert_eq!(u8::from(v), 0x0B);
    /// ```
    fn from(v: u8) -> U4 {
        U4(v & 0x0F)
    }
}

impl From<U4> for u8 {
    fn from(v: U4) -> u8 {
        v.0
    }
}

/// An immutable 7-bit unsigned integer.
#[derive(Debug, PartialEq)]
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
    /// ```
    /// use musnd::bits::U7;
    ///
    /// assert_eq!(U7::try_from(0x7F), Some(U7::from(0x7F)));
    /// assert_eq!(U7::try_from(0x80), None);
    /// ```
    pub fn try_from(v: u8) -> Option<U7> {
        if v & 0x80 == 0 {
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
    /// ```
    /// use musnd::bits::U7;
    ///
    /// let v = U7::from(0x7F);
    /// assert_eq!(u8::from(v), 0x7F);
    ///
    /// let v = U7::from(0xFF);
    /// assert_eq!(u8::from(v), 0x7F);
    /// ```
    fn from(v: u8) -> U7 {
        U7(v & 0x7F)
    }
}

impl From<U7> for u8 {
    fn from(v: U7) -> u8 {
        v.0
    }
}

#[cfg(test)]
mod u4_tests {
    use super::*;

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

#[cfg(test)]
mod u7_tests {
    use super::*;

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
