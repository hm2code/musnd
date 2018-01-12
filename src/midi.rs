//! MIDI support.

use std::convert::From;
use std::io::{self, Read};
use std::result;

/// A specialized `Result` type for MIDI operations.
pub type Result<T> = result::Result<T, Error>;

/// The error type for MIDI operations.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// If I/O error of the given `io::ErrorKind` occured.
    IO(io::ErrorKind),

    /// If Variable-Length Quantity sequence is malformed (i.e. too long).
    VLQ,
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IO(err.kind())
    }
}

#[allow(dead_code)]
fn read_vlq<R: Read>(bytes: &mut io::Bytes<R>) -> Result<i32> {
    let mut value = 0;
    let mut last_byte = -1;

    for (i, byte) in bytes.enumerate() {
        if i > 3 {
            break;
        }

        last_byte = byte? as i32;
        value <<= 7;
        if last_byte & 0x80 == 0 {
            return Ok(value | last_byte);
        } else {
            value |= last_byte & 0x7F;
        }
    }

    if last_byte < 0 {
        Ok(-1)
    } else {
        Err(Error::VLQ)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_vlq_one_byte() {
        let data: Vec<u8> = vec![0x00, 0x40, 0x7F];
        let mut bytes = data.bytes();

        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x00000000);
        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x00000040);
        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x0000007F);
        assert_eq!(read_vlq(&mut bytes).unwrap(), -1);
    }

    #[test]
    fn read_vlq_two_bytes() {
        let data: Vec<u8> = vec![
            0x81, 0x00,
            0xC0, 0x00,
            0xFF, 0x7F,
        ];
        let mut bytes = data.bytes();

        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x00000080);
        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x00002000);
        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x00003FFF);
        assert_eq!(read_vlq(&mut bytes).unwrap(), -1);
    }

    #[test]
    fn read_vlq_three_bytes() {
        let data: Vec<u8> = vec![
            0x81, 0x80, 0x00,
            0xC0, 0x80, 0x00,
            0xFF, 0xFF, 0x7F,
        ];
        let mut bytes = data.bytes();

        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x00004000);
        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x00100000);
        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x001FFFFF);
        assert_eq!(read_vlq(&mut bytes).unwrap(), -1);
    }

    #[test]
    fn read_vlq_four_bytes() {
        let data: Vec<u8> = vec![
            0x81, 0x80, 0x80, 0x00,
            0xC0, 0x80, 0x80, 0x00,
            0xFF, 0xFF, 0xFF, 0x7F,
        ];
        let mut bytes = data.bytes();

        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x00200000);
        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x08000000);
        assert_eq!(read_vlq(&mut bytes).unwrap(), 0x0FFFFFFF);
        assert_eq!(read_vlq(&mut bytes).unwrap(), -1);
    }

    #[test]
    fn read_vlq_fails_on_malformed() {
        let data: Vec<u8> = vec![
            0x81, 0x80, 
        ];
        let mut bytes = data.bytes();
        let result = read_vlq(&mut bytes);

        assert_eq!(result.unwrap_err(), Error::VLQ);
    }

    #[test]
    fn read_vlq_fails_on_too_long() {
        let data: Vec<u8> = vec![
            0x81, 0x80, 0x80, 0x80, 0x00,
        ];
        let mut bytes = data.bytes();
        let result = read_vlq(&mut bytes);

        assert_eq!(result.unwrap_err(), Error::VLQ);
    }
}

#[cfg(test)]
mod error_tests {
    use super::*;

    #[test]
    fn from_io_error() {
        let io_err = io::Error::new(io::ErrorKind::Other, "ouch!");
        let err = Error::from(io_err);

        assert_eq!(err, Error::IO(io::ErrorKind::Other));
    }
}
