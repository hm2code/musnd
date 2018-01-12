//! MIDI support.

use std::convert::From;
use std::io::{self, Read};
use std::result;

/// A specialized `Result` type for MIDI operations.
pub type Result<T> = result::Result<T, Error>;

/// The error type for MIDI operations.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// If I/O error of the given `std::io::ErrorKind` occured.
    Io(io::ErrorKind),

    /// If there are no more data in a reader but the data was expected.
    NoData,

    /// If Variable-Length Quantity sequence is malformed (i.e. too long).
    /// Contains the malformed VLQ.
    BadVlq(i32),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::Io(err.kind())
    }
}

/// Low-level MIDI file reader that uses an `std::io::Read` trait
/// implementation as the data source.
///
/// All `read` methods follow the same contract:
///
/// * Return `Error::Io` if the the data source reported an `std::io::Error`.
/// The reported `std::io::ErrorKind` can be found in the returned error value.
/// * Return `Error::NoData` if there is no more data in the data source to
/// fully read the requested data object.
/// * Returns a data object specific error if the resulting data object is
/// malformed (each `read` method documented such cases if there are any).
/// * Return the data object on success.
///
/// There is no guarantee that the data in the data source will remain intact
/// if a `read` method returned an error.
pub struct Reader<R: Read> {
    r: R,
}

impl<R: Read> Reader<R> {
    /// Creates a new `Reader` that will be reading from 'r'.
    pub fn new(r: R) -> Reader<R> {
        Reader { r }
    }

    /// Reads a single byte from the data source.
    pub fn read_u8(&mut self) -> Result<u8> {
        let mut buf = [0; 1];
        if self.r.read(&mut buf)? == 1 {
            Ok(buf[0])
        } else {
            Err(Error::NoData)
        }
    }

    /// Reads a Variable-Length Quantity from the data source. Returns
    /// `Error::BadVlq` if the data is malformed. The malformed VLQ can be
    /// recovered from the error.
    pub fn read_vlq(&mut self) -> Result<i32> {
        let mut value = 0;
        for _ in 0..4 {
            match self.read_u8() {
                Ok(byte) => {
                    let data = byte & 0b0111_1111;
                    value = (value << 7) | data as i32;
                    if byte == data {
                        return Ok(value)
                    }
                },
                Err(Error::NoData) => {
                    if value == 0 {
                        return Err(Error::NoData);
                    } else {
                        return Err(Error::BadVlq(value));
                    }
                },
                Err(err) => return Err(err)
            }
        }
        Err(Error::BadVlq(value))
    }
}

#[cfg(test)]
mod reader_tests {
    use super::*;

    #[test]
    fn new() {
        let data: Vec<u8> = vec![1, 2, 3];
        let bytes = &data[..];

        assert_eq!(Reader::new(bytes).r.len(), 3);
    }

    #[test]
    fn read_u8() {
        let data: Vec<u8> = vec![0x12, 0x34];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_u8().unwrap(), 0x12);
        assert_eq!(reader.read_u8().unwrap(), 0x34);
        assert_eq!(reader.read_u8().unwrap_err(), Error::NoData);
    }

    #[test]
    fn read_vlq_one_byte() {
        let data: Vec<u8> = vec![0x00, 0x40, 0x7F];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap(), 0x00000000);
        assert_eq!(reader.read_vlq().unwrap(), 0x00000040);
        assert_eq!(reader.read_vlq().unwrap(), 0x0000007F);
        assert_eq!(reader.read_vlq().unwrap_err(), Error::NoData);
    }

    #[test]
    fn read_vlq_two_bytes() {
        let data: Vec<u8> = vec![
            0x81, 0x00,
            0xC0, 0x00,
            0xFF, 0x7F,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap(), 0x00000080);
        assert_eq!(reader.read_vlq().unwrap(), 0x00002000);
        assert_eq!(reader.read_vlq().unwrap(), 0x00003FFF);
        assert_eq!(reader.read_vlq().unwrap_err(), Error::NoData);
    }

    #[test]
    fn read_vlq_three_bytes() {
        let data: Vec<u8> = vec![
            0x81, 0x80, 0x00,
            0xC0, 0x80, 0x00,
            0xFF, 0xFF, 0x7F,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap(), 0x00004000);
        assert_eq!(reader.read_vlq().unwrap(), 0x00100000);
        assert_eq!(reader.read_vlq().unwrap(), 0x001FFFFF);
        assert_eq!(reader.read_vlq().unwrap_err(), Error::NoData);
    }

    #[test]
    fn read_vlq_four_bytes() {
        let data: Vec<u8> = vec![
            0x81, 0x80, 0x80, 0x00,
            0xC0, 0x80, 0x80, 0x00,
            0xFF, 0xFF, 0xFF, 0x7F,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap(), 0x00200000);
        assert_eq!(reader.read_vlq().unwrap(), 0x08000000);
        assert_eq!(reader.read_vlq().unwrap(), 0x0FFFFFFF);
        assert_eq!(reader.read_vlq().unwrap_err(), Error::NoData);
    }

    #[test]
    fn read_vlq_fails_on_malformed() {
        let data: Vec<u8> = vec![0x81, 0x80];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap_err(), Error::BadVlq(0x00000080));
    }

    #[test]
    fn read_vlq_fails_on_too_long() {
        let data: Vec<u8> = vec![0x81, 0x80, 0x80, 0x80, 0x00];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap_err(), Error::BadVlq(0x00200000));
    }
}

#[cfg(test)]
mod error_tests {
    use super::*;

    #[test]
    fn from_io_error() {
        let io_err = io::Error::new(io::ErrorKind::Other, "ouch!");
        let err = Error::from(io_err);

        assert_eq!(err, Error::Io(io::ErrorKind::Other));
    }
}
