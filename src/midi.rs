//! MIDI support.

use std::convert::From;
use std::io::{self, Read};
use std::result;

const MTHD_4CC: i32 = 0x4D546864; // 'MThd'
const MTRK_4CC: i32 = 0x4D54726B; // 'MTrk'
const HDR_SIZE: i32 = 6;          // size of the MIDI file header

/// A specialized `Result` type for MIDI operations.
pub type Result<T> = result::Result<T, Error>;

/// The error type for MIDI operations.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// If I/O error of the given `std::io::ErrorKind` occured.
    Io(io::ErrorKind),

    /// If Variable-Length Quantity sequence is malformed (i.e. too long).
    /// Contains the malformed VLQ.
    BadVlq(i32),

    /// If MIDI file header is malformed.
    BadFileHeader,

    /// If MIDI track header is malformed.
    BadTrackHeader,
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
/// * Returns a data object specific error if the resulting data object is
/// malformed, e.g. `Error::BadVlq`.
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
        self.r.read_exact(&mut buf)?;
        Ok(buf[0])
    }

    /// Reads 16-bit unsigned integer from the data source.
    pub fn read_u16(&mut self) -> Result<u16> {
        let mut buf = [0; 2];
        self.r.read_exact(&mut buf)?;
        Ok(
            (buf[0] as u16) <<  8 |
            (buf[1] as u16)
        )
    }

    /// Reads 32-bit signed integer from the data source.
    pub fn read_i32(&mut self) -> Result<i32> {
        let mut buf = [0; 4];
        self.r.read_exact(&mut buf)?;
        Ok(
            (buf[0] as i32) << 24 |
            (buf[1] as i32) << 16 |
            (buf[2] as i32) <<  8 |
            (buf[3] as i32)
        )
    }

    /// Reads a Variable-Length Quantity from the data source. Returns
    /// `Error::BadVlq` if the data is malformed. The malformed VLQ can be
    /// recovered from the error.
    pub fn read_vlq(&mut self) -> Result<i32> {
        let mut value = 0;
        for _ in 0..4 {
            let byte = self.read_u8()?;
            let data = byte & 0b0111_1111;
            value = (value << 7) | data as i32;
            if byte == data {
                return Ok(value)
            }
        }
        Err(Error::BadVlq(value))
    }

    /// Reads MIDI file header from the data source.
    /// Returns `Error::BadFileHeader` if the data is malformed.
    pub fn read_file_hdr(&mut self) -> Result<FileHeader> {
        if self.read_i32()? != MTHD_4CC {
            return Err(Error::BadFileHeader);
        }

        if self.read_i32()? != HDR_SIZE {
            return Err(Error::BadFileHeader);
        }

        let format = self.read_u16()?;
        if format > 2 {
            return Err(Error::BadFileHeader);
        }

        let num_of_tracks = self.read_u16()?;
        if num_of_tracks == 0 || num_of_tracks > 1 && format == 0 {
            return Err(Error::BadFileHeader);
        }

        let division = self.read_u16()?;
        if division == 0 {
            return Err(Error::BadFileHeader);
        }

        Ok(FileHeader { format, num_of_tracks, division })
    }

    /// Reads MIDI file track header and returns length of the track data.
    /// Returns `Error::BadTrackHeader` if the header data is malformed.
    pub fn read_track_hdr(&mut self) -> Result<usize> {
        if self.read_i32()? != MTRK_4CC {
            return Err(Error::BadTrackHeader);
        }

        Ok((self.read_i32()? as u32) as usize)
    }
}

/// MIDI file header.
#[derive(Debug)]
pub struct FileHeader {
    /// MIDI file format. TODO: enum
    pub format: u16,

    /// Number of tracks within the file.
    pub num_of_tracks: u16,

    /// The time division. TODO: enum
    pub division: u16,
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

#[cfg(test)]
mod reader_tests {
    use super::*;

    #[test]
    fn new() {
        let data = [1, 2, 3];
        let bytes = &data[..];

        assert_eq!(Reader::new(bytes).r.len(), 3);
    }

    #[test]
    fn read_u8() {
        let data = [0x12, 0x34];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_u8().unwrap(), 0x12);
        assert_eq!(reader.read_u8().unwrap(), 0x34);
        assert_eq!(reader.read_u8().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_u16() {
        let data = [0x12, 0x34];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_u16().unwrap(), 0x1234);
        assert_eq!(reader.read_u16().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_u16_fails_on_incomplete() {
        let data = [0x12];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_u16().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_i32() {
        let data = [
            0x12, 0x34, 0x56, 0x78,
            b'M', b'T', b'h', b'd',
            b'M', b'T', b'r', b'k',
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_i32().unwrap(), 0x12345678);
        assert_eq!(reader.read_i32().unwrap(), MTHD_4CC);
        assert_eq!(reader.read_i32().unwrap(), MTRK_4CC);
        assert_eq!(reader.read_i32().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_i32_fails_on_incomplete() {
        let data = [0x12, 0x34, 0x56];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_i32().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_vlq_one_byte() {
        let data = [0x00, 0x40, 0x7F];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap(), 0x00000000);
        assert_eq!(reader.read_vlq().unwrap(), 0x00000040);
        assert_eq!(reader.read_vlq().unwrap(), 0x0000007F);
        assert_eq!(reader.read_vlq().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_vlq_two_bytes() {
        let data = [
            0x81, 0x00,
            0xC0, 0x00,
            0xFF, 0x7F,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap(), 0x00000080);
        assert_eq!(reader.read_vlq().unwrap(), 0x00002000);
        assert_eq!(reader.read_vlq().unwrap(), 0x00003FFF);
        assert_eq!(reader.read_vlq().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_vlq_three_bytes() {
        let data = [
            0x81, 0x80, 0x00,
            0xC0, 0x80, 0x00,
            0xFF, 0xFF, 0x7F,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap(), 0x00004000);
        assert_eq!(reader.read_vlq().unwrap(), 0x00100000);
        assert_eq!(reader.read_vlq().unwrap(), 0x001FFFFF);
        assert_eq!(reader.read_vlq().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_vlq_four_bytes() {
        let data = [
            0x81, 0x80, 0x80, 0x00,
            0xC0, 0x80, 0x80, 0x00,
            0xFF, 0xFF, 0xFF, 0x7F,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap(), 0x00200000);
        assert_eq!(reader.read_vlq().unwrap(), 0x08000000);
        assert_eq!(reader.read_vlq().unwrap(), 0x0FFFFFFF);
        assert_eq!(reader.read_vlq().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_vlq_fails_on_incomplete() {
        let data = [0x81, 0x80];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_vlq_fails_on_too_long() {
        let data = [0x81, 0x80, 0x80, 0x80, 0x00];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_vlq().unwrap_err(), Error::BadVlq(0x00200000));
    }

    #[test]
    fn read_file_hdr() {
        let data = [
            0x4D, 0x54, 0x68, 0x64,
            0x00, 0x00, 0x00, 0x06,
            0x00, 0x00,
            0x00, 0x01,
            0x00, 0x60,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        let hdr = reader.read_file_hdr().unwrap();

        assert_eq!(hdr.format, 0);
        assert_eq!(hdr.num_of_tracks, 1);
        assert_eq!(hdr.division, 96);
    }

    #[test]
    fn read_file_hdr_fails_on_corrupted_4cc() {
        let data = [
            0x4D, 0xFF, 0x68, 0x64,
            0x00, 0x00, 0x00, 0x06,
            0x00, 0x00,
            0x00, 0x01,
            0x00, 0x60,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_file_hdr().unwrap_err(), Error::BadFileHeader);
    }

    #[test]
    fn read_file_hdr_fails_on_corrupted_size() {
        let data = [
            0x4D, 0x54, 0x68, 0x64,
            0x00, 0x00, 0xFF, 0x06,
            0x00, 0x00,
            0x00, 0x01,
            0x00, 0x60,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_file_hdr().unwrap_err(), Error::BadFileHeader);
    }

    #[test]
    fn read_file_hdr_fails_on_bad_format() {
        let data = [
            0x4D, 0x54, 0x68, 0x64,
            0x00, 0x00, 0x00, 0x06,
            0x00, 0x03,
            0x00, 0x01,
            0x00, 0x60,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_file_hdr().unwrap_err(), Error::BadFileHeader);
    }

    #[test]
    fn read_file_hdr_fails_on_zero_tracks() {
        let data = [
            0x4D, 0x54, 0x68, 0x64,
            0x00, 0x00, 0x00, 0x06,
            0x00, 0x00,
            0x00, 0x00,
            0x00, 0x60,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_file_hdr().unwrap_err(), Error::BadFileHeader);
    }

    #[test]
    fn read_file_hdr_fails_on_too_many_tracks() {
        let data = [
            0x4D, 0x54, 0x68, 0x64,
            0x00, 0x00, 0x00, 0x06,
            0x00, 0x00,
            0x00, 0x02,
            0x00, 0x60,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_file_hdr().unwrap_err(), Error::BadFileHeader);
    }

    #[test]
    fn read_file_hdr_fails_on_zero_division() {
        let data = [
            0x4D, 0x54, 0x68, 0x64,
            0x00, 0x00, 0x00, 0x06,
            0x00, 0x00,
            0x00, 0x01,
            0x00, 0x00,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_file_hdr().unwrap_err(), Error::BadFileHeader);
    }

    #[test]
    fn read_file_hdr_fails_on_incomplete() {
        let data = [
            0x4D, 0x54, 0x68, 0x64,
            0x00, 0x00, 0x00, 0x06,
            0x00, 0x02,
            0x00, 0x01,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_file_hdr().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }

    #[test]
    fn read_track_hdr() {
        let data = [
            0x4D, 0x54, 0x72, 0x6B,
            0x87, 0x65, 0x43, 0x21,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_track_hdr().unwrap(), 0x87654321);
    }

    #[test]
    fn read_track_hdr_fails_on_corrupted_4cc() {
        let data = [
            0xFF, 0x54, 0x72, 0x6B,
            0x87, 0x65, 0x43, 0x21,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_track_hdr().unwrap_err(), Error::BadTrackHeader);
    }

    #[test]
    fn read_track_hdr_fails_on_incomplete() {
        let data = [
            0x4D, 0x54, 0x72, 0x6B,
            0x87, 0x65, 0x43,
        ];
        let bytes = &data[..];
        let mut reader = Reader::new(bytes);

        assert_eq!(reader.read_track_hdr().unwrap_err(),
                   Error::Io(io::ErrorKind::UnexpectedEof));
    }
}
