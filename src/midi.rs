//! MIDI support.

use std::cmp;

use bits::U15;

/// A MIDI sequence.
#[derive(Debug)]
pub struct Seq {
    tracks: Vec<Track>,
    div: Div,
}

impl Seq {
    /// Creates a new MIDI sequence with the given division.
    ///
    /// # Errors
    /// Returns `None` if `div`'s resolution is 0.
    pub fn new(div: Div) -> Option<Seq> {
        if div.ticks() == 0 {
            None
        } else {
            Some(Seq {
                tracks: Vec::new(),
                div,
            })
        }
    }

    /// Returns the division.
    pub fn div(&self) -> Div {
        self.div
    }

    /// Returns the number of tracks.
    pub fn track_count(&self) -> usize {
        self.tracks.len()
    }

    /// Returns the duration in ticks.
    pub fn duration(&self) -> usize {
        0
    }

    /// Returns the tracks.
    pub fn tracks(&self) -> &[Track] {
        &self.tracks[..]
    }

    /// Adds a track to `self`.
    ///
    /// # Returns
    /// Returns an index that can be used to locate the `track` within a slice
    /// returned by `tracks()` method.
    pub fn add(&mut self, track: Track) -> usize {
        self.tracks.push(track);
        self.tracks.len() - 1
    }
}

#[cfg(test)]
mod seq_tests {
    use bits::U15;
    use super::{Div, Seq, Track};

    #[test]
    fn new_sets_div() {
        let div = Div::PPQ(U15::from(16));
        let seq = Seq::new(div).unwrap();

        assert_eq!(seq.div(), div);
    }

    #[test]
    fn new_sets_div2() {
        let div = Div::SMPTE25(40);
        let seq = Seq::new(div).unwrap();

        assert_eq!(seq.div(), div);
    }

    #[test]
    fn new_fails_on_ppq_0() {
        assert!(Seq::new(Div::PPQ(U15::from(0))).is_none());
    }

    #[test]
    fn new_fails_on_smpte24_0() {
        assert!(Seq::new(Div::SMPTE24(0)).is_none());
    }

    #[test]
    fn new_fails_on_smpte25_0() {
        assert!(Seq::new(Div::SMPTE25(0)).is_none());
    }

    #[test]
    fn new_fails_on_smpte30drop_0() {
        assert!(Seq::new(Div::SMPTE30Drop(0)).is_none());
    }

    #[test]
    fn new_fails_on_smpte30_0() {
        assert!(Seq::new(Div::SMPTE30(0)).is_none());
    }

    #[test]
    fn new_has_zero_track_count() {
        assert_eq!(Seq::new(Div::SMPTE25(10)).unwrap().track_count(), 0);
    }

    #[test]
    fn new_has_zero_duration() {
        assert_eq!(Seq::new(Div::SMPTE30(1)).unwrap().duration(), 0);
    }

    #[test]
    fn new_has_no_tracks() {
        assert!(Seq::new(Div::SMPTE24(5)).unwrap().tracks().is_empty());
    }

    #[test]
    fn add_updates_track_count() {
        let mut seq = Seq::new(Div::SMPTE25(1)).unwrap();
        seq.add(Track::new());

        assert_eq!(seq.track_count(), 1);
    }

    #[test]
    fn add_updates_tracks() {
        let mut seq = Seq::new(Div::SMPTE25(1)).unwrap();
        seq.add(Track::new());

        assert_eq!(seq.tracks().len(), 1);
    }

    #[test]
    fn add_returns_index() {
        let mut seq = Seq::new(Div::SMPTE25(1)).unwrap();

        assert_eq!(seq.add(Track::new()), 0);
        assert_eq!(seq.add(Track::new()), 1);
    }
}

/// A MIDI sequence division.
///
/// Specifies the meaning of time values with MIDI sequence.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Div {
    /// Tempo based Pulses Per Quarter note.
    ///
    /// Attached is the resolution expressed in ticks (pulses) per quarter note.
    PPQ(U15),
    /// SMPTE timecode; 24 frames per second.
    ///
    /// Attached is the resolution expressed in ticks per frame.
    SMPTE24(u8),
    /// SMPTE timecode; 25 frames per second.
    ///
    /// Attached is the resolution expressed in ticks per frame.
    SMPTE25(u8),
    /// SMPTE timecode; 30 drop (30 / 1.001) frames per second.
    ///
    /// Attached is the resolution expressed in ticks per frame.
    SMPTE30Drop(u8),
    /// SMPTE timecode; 30 frames per second.
    ///
    /// Attached is the resolution expressed in ticks per frame.
    SMPTE30(u8),
}

impl Div {
    /// Returns resolution in ticks.
    pub fn ticks(&self) -> usize {
        use self::Div::*;

        match *self {
            PPQ(ticks) => u16::from(ticks) as usize,
            SMPTE24(ticks) => ticks as usize,
            SMPTE25(ticks) => ticks as usize,
            SMPTE30Drop(ticks) => ticks as usize,
            SMPTE30(ticks) => ticks as usize,
        }
    }

    /// Returns number of frames per second for SMPTE and 0 for PPQ.
    pub fn fps(&self) -> f32 {
        use self::Div::*;

        match *self {
            PPQ(_) => 0.0,
            SMPTE24(_) => 24.0,
            SMPTE25(_) => 25.0,
            SMPTE30Drop(_) => 30.0 / 1.001,
            SMPTE30(_) => 30.0,
        }
    }
}

#[cfg(test)]
mod div_tests {
    use super::Div::*;
    use bits::U15;

    #[test]
    fn ticks_ppq() {
        assert_eq!(PPQ(U15::from(1)).ticks(), 1);
    }

    #[test]
    fn ticks_smpte24() {
        assert_eq!(SMPTE24(2).ticks(), 2);
    }

    #[test]
    fn ticks_smpte25() {
        assert_eq!(SMPTE25(3).ticks(), 3);
    }

    #[test]
    fn ticks_smpte30drop() {
        assert_eq!(SMPTE30Drop(4).ticks(), 4);
    }

    #[test]
    fn ticks_smpte30() {
        assert_eq!(SMPTE30(5).ticks(), 5);
    }

    #[test]
    fn fps_ppq() {
        assert_eq!(PPQ(U15::from(0)).fps(), 0.0);
    }

    #[test]
    fn fps_smpte24() {
        assert_eq!(SMPTE24(1).fps(), 24.0);
    }

    #[test]
    fn fps_smpte25() {
        assert_eq!(SMPTE25(2).fps(), 25.0);
    }

    #[test]
    fn fps_smpte30drop() {
        assert_eq!(SMPTE30Drop(3).fps(), 30.0 / 1.001);
    }

    #[test]
    fn fps_smpte30() {
        assert_eq!(SMPTE30(4).fps(), 30.0);
    }
}

/// A MIDI track.
#[derive(Debug)]
pub struct Track {
    data: Vec<u8>,
}

impl Track {
    /// Creates a new empty track.
    pub fn new() -> Track {
        Track { data: Vec::new() }
    }

    /// Creates a new empty track with the specified capacity in bytes.
    ///
    /// This method is useful when the length of the track raw data is known,
    /// for example, when reading from SMF file.
    pub fn with_capacity(capacity: usize) -> Track {
        Track {
            data: Vec::with_capacity(capacity),
        }
    }

    /// Returns the duration in ticks.
    pub fn duration(&self) -> usize {
        0
    }

    /// Returns the raw track data.
    pub fn raw(&self) -> &[u8] {
        &self.data[..]
    }

    /// Adds a chunk of raw data.
    ///
    /// A copy of the data is appended to the track existing data. No data
    /// validation is performed so use this method with caution and make sure
    /// that `data` contains a valid byte sequence that can be stored within a
    /// track chunk of SMF file.
    pub fn add_raw(&mut self, data: &[u8]) {
        self.data.extend_from_slice(data);
    }
}

#[cfg(test)]
mod track_tests {
    use super::Track;

    #[test]
    fn new_has_zero_duration() {
        assert_eq!(Track::new().duration(), 0);
    }

    #[test]
    fn new_has_no_data() {
        assert!(Track::new().raw().is_empty());
    }

    #[test]
    fn with_capacity_reserves_capacity() {
        assert_eq!(Track::with_capacity(128).data.capacity(), 128);
    }

    #[test]
    fn with_capacity_has_zero_duration() {
        assert_eq!(Track::with_capacity(64).duration(), 0);
    }

    #[test]
    fn with_capacity_has_no_data() {
        assert!(Track::with_capacity(64).raw().is_empty());
    }

    #[test]
    fn add_raw_appends_data() {
        let mut track = Track::new();
        track.add_raw(&[1]);

        assert_eq!(track.raw(), &[1]);

        track.add_raw(&[2]);

        assert_eq!(track.raw(), &[1, 2]);
    }

    #[ignore]
    #[test]
    fn add_raw_updates_duration() {
        let mut track = Track::new();
        track.add_raw(&[0x00, 0xC0, 0x05]); // dt: 0, ch: 1, program: 5

        assert_eq!(track.duration(), 0);

        // dt: 192, ch: 1, on: E4, vel: 32
        track.add_raw(&[0x81, 0x40, 0x90, 0x4C, 0x20]);

        assert_eq!(track.duration(), 192);
    }
}

/// Represents a raw MIDI event.
pub struct RawEvent<'a> {
    /// Raw MIDI message.
    pub raw_msg: &'a [u8],
    /// The number of ticks elapsed since the beginning of the MIDI sequence.
    pub ticks: usize,
}

impl<'a> RawEvent<'a> {
    // Parses `data` starting at `pos` index and returns `RawEvent` and its
    // number of bytes within the data.
    fn parse(
        data: &'a [u8],
        pos: usize,
        prev_ticks: usize, // ticks value of the previous event
        prev_status: u8,   // status of the previous event
    ) -> Option<(RawEvent, usize)> {
        let (delta_ticks, ticks_len) = vlq(data, pos)?;

        let msg_start = pos + ticks_len;
        if msg_start < data.len() {
            let status = data[msg_start];
            let msg_len = if is_status(status) {
                if is_ch_msg(status) {
                    ch_msg_len(status)
                } else if is_sys_msg(status) {
                    sys_msg_len(data, msg_start)?
                } else if is_meta_msg(status) {
                    meta_msg_len(data, msg_start)?
                } else {
                    // Bad data: unknown status byte
                    return None;
                }
            } else if is_ch_msg(prev_status) {
                ch_msg_len(prev_status) - 1
            } else {
                // Bad data: running status for a non-channel message
                return None;
            };

            let msg_end = msg_start + msg_len;
            if msg_end <= data.len() {
                return Some((
                    RawEvent {
                        raw_msg: &data[msg_start..msg_end],
                        ticks: prev_ticks + delta_ticks,
                    },
                    ticks_len + msg_len,
                ));
            }
        }

        None
    }
}

#[cfg(test)]
mod raw_event_tests {
    use super::RawEvent;

    const DATA: [u8; 41] = [
            0x01, 0x80, 0x01, 0x02, // note off
            0x02, 0x90, 0x03, 0x04, // note on
            0x03, 0xA0, 0x05, 0x06, // polyphonic key pressure
            0x04, 0xB0, 0x07, 0x08, // control change / ch mode
            0x05, 0xC0, 0x09,       // program change
            0x06, 0xD0, 0x0A,       // channel pressure
            0x07, 0xE0, 0x0B, 0x0C, // pitch bend change
            0x08, 0xB1, 0x0D, 0x0E, // control change on channel 2
            0x09,       0x0F, 0x10, // a running status
            0x0A, 0xF0, 0x00, 0xF7, // sysex
            0x0B, 0xFF, 0x2F, 0x00, // meta, end of track
    ];

    #[test]
    fn parse_note_off() {
        let (event, count) = RawEvent::parse(&DATA[..], 0, 0, 0).unwrap();

        assert_eq!(count, 4);
        assert_eq!(event.ticks, 1);
        assert_eq!(event.raw_msg, &[0b1000_0000, 0x01, 0x02]);
    }

    #[test]
    fn parse_note_on() {
        let (event, count) = RawEvent::parse(&DATA[..], 4, 0, 0).unwrap();

        assert_eq!(count, 4);
        assert_eq!(event.ticks, 2);
        assert_eq!(event.raw_msg, &[0b1001_0000, 0x03, 0x04]);
    }

    #[test]
    fn parse_poly_key_press() {
        let (event, count) = RawEvent::parse(&DATA[..], 8, 0, 0).unwrap();

        assert_eq!(count, 4);
        assert_eq!(event.ticks, 3);
        assert_eq!(event.raw_msg, &[0b1010_0000, 0x05, 0x06]);
    }

    #[test]
    fn parse_control() {
        let (event, count) = RawEvent::parse(&DATA[..], 12, 0, 0).unwrap();

        assert_eq!(count, 4);
        assert_eq!(event.ticks, 4);
        assert_eq!(event.raw_msg, &[0b1011_0000, 0x07, 0x08]);
    }

    #[test]
    fn parse_program() {
        let (event, count) = RawEvent::parse(&DATA[..], 16, 0, 0).unwrap();

        assert_eq!(count, 3);
        assert_eq!(event.ticks, 5);
        assert_eq!(event.raw_msg, &[0b1100_0000, 0x09]);
    }

    #[test]
    fn parse_channel_press() {
        let (event, count) = RawEvent::parse(&DATA[..], 19, 0, 0).unwrap();

        assert_eq!(count, 3);
        assert_eq!(event.ticks, 6);
        assert_eq!(event.raw_msg, &[0b1101_0000, 0x0A]);
    }

    #[test]
    fn parse_channel_pitch_bend() {
        let (event, count) = RawEvent::parse(&DATA[..], 22, 0, 0).unwrap();

        assert_eq!(count, 4);
        assert_eq!(event.ticks, 7);
        assert_eq!(event.raw_msg, &[0b1110_0000, 0x0B, 0x0C]);
    }

    #[test]
    fn parse_control_ch2() {
        let (event, count) = RawEvent::parse(&DATA[..], 26, 0, 0).unwrap();

        assert_eq!(count, 4);
        assert_eq!(event.ticks, 8);
        assert_eq!(event.raw_msg, &[0b1011_0001, 0x0D, 0x0E]);
    }

    #[test]
    fn parse_control_running_status() {
        let (event, count) = RawEvent::parse(&DATA[..], 30, 0, 0xB1).unwrap();

        assert_eq!(count, 3);
        assert_eq!(event.ticks, 9);
        assert_eq!(event.raw_msg, &[0x0F, 0x10]);
    }

    #[test]
    fn parse_system() {
        let (event, count) = RawEvent::parse(&DATA[..], 33, 0, 0).unwrap();

        assert_eq!(count, 4);
        assert_eq!(event.ticks, 10);
        assert_eq!(event.raw_msg, &[0xF0, 0x00, 0xF7]);
    }

    #[test]
    fn parse_meta() {
        let (event, count) = RawEvent::parse(&DATA[..], 37, 0, 0).unwrap();

        assert_eq!(count, 4);
        assert_eq!(event.ticks, 11);
        assert_eq!(event.raw_msg, &[0xFF, 0x2F, 0x00]);
    }

    #[test]
    fn parse_reads_ticks_vlq() {
        let data: [u8; 5] = [0x81, 0x40, 0x80, 0x40, 0x7F];

        let (event, count) = RawEvent::parse(&data[..], 0, 0, 0).unwrap();

        assert_eq!(count, 5);
        assert_eq!(event.ticks, 192);
        assert_eq!(event.raw_msg, &[0b1000_0000, 0x40, 0x7F]);
    }

    #[test]
    fn parse_fails_on_bad_vlq() {
        assert!(RawEvent::parse(&[0xFF], 0, 0, 0).is_none());
    }

    #[test]
    fn parse_fails_on_bad_data() {
        assert!(RawEvent::parse(&[], 0, 0, 0).is_none());
        assert!(RawEvent::parse(&[0x00], 0, 0, 0).is_none());
        assert!(RawEvent::parse(&[0x00, 0x80], 0, 0, 0).is_none());
        assert!(RawEvent::parse(&[0x00, 0xF9], 0, 0, 0).is_none());
    }

    #[test]
    fn parse_fails_on_bad_running_status() {
        assert!(RawEvent::parse(&DATA[..], 30, 0, 0xFF).is_none());
    }
}

// Returns true if `byte` is a MIDI status byte.
fn is_status(byte: u8) -> bool {
    byte & 0x80 != 0
}

// Returns the value of Variable-Length Quantity (VLQ) located within the
// raw data at the specified position and the size the VLQ data in bytes.
// Note: 0x0FFF_FFFF is the largest value allowed by the MIDI spec.
fn vlq(data: &[u8], pos: usize) -> Option<(usize, usize)> {
    let mut value = 0usize;
    for i in pos..cmp::min(pos + 4, data.len()) {
        let byte = data[i];
        let bits7 = byte & 0x7F;
        value = value << 7 | bits7 as usize;
        if byte == bits7 {
            return Some((value, i - pos + 1));
        }
    }
    None
}

// Returns total length of a channel message that starts with the specified
// status byte.
//
// Call this function only if `is_ch_msg(status)` returns `true`.
fn ch_msg_len(status: u8) -> usize {
    let status = status >> 4;
    if status > 0b1011 && status < 0b1110 {
        // Program Change; Channel Pressure
        2
    } else {
        3
    }
}

// Returns total length of a system message that starts within `data` at `pos`
// index.
//
// Call this function only if `is_sys_msg(data[pos])` returns `true`.
fn sys_msg_len(data: &[u8], pos: usize) -> Option<usize> {
    match data[pos] {
        0xF0 => {
            // System Exclusive
            for i in (pos + 1)..data.len() {
                if data[i] == 0xF7 {
                    return Some(i - pos + 1);
                }
            }
            None
        }
        0xF1 | 0xF3 => Some(2), // Time Code Quarter Frame and Song Select
        0xF2 => Some(3),        // Song Position Pointer
        0xF6 | 0xF7 => Some(1), // Tune Request; End Of System Exclusive
        _ => None,              // Undefined
    }
}

// Returns total length of a meta message that starts within `data` at `pos`
// index.
//
// Call this function only if `is_meta_msg(data[pos])` returns `true`.
fn meta_msg_len(data: &[u8], pos: usize) -> Option<usize> {
    let (data_len, len_len) = vlq(data, pos + 2)?;
    Some(data_len + len_len + 2)
}

// Returns true if the given status byte represents a channel message.
fn is_ch_msg(status: u8) -> bool {
    status > 0x7F && status < 0xF0
}

// Returns true if the given status byte represents a system message.
fn is_sys_msg(status: u8) -> bool {
    status > 0xEF && status < 0xF8
}

// Returns true if the given status byte represents a meta message.
fn is_meta_msg(status: u8) -> bool {
    status == 0xFF
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_status_works() {
        assert!(is_status(0x80));
        assert!(!is_status(0x7F));
    }

    #[test]
    fn vlq_reads_byte() {
        let data: [u8; 2] = [0, 1];
        let slice = &data[..];
        let (value, count) = vlq(slice, 0).unwrap();

        assert_eq!(value, 0);
        assert_eq!(count, 1);

        assert_eq!(vlq(slice, 1), Some((1, 1)));
    }

    #[test]
    fn vlq_reads_multibyte() {
        let data: [u8; 9] = [
                      0x81, 0x00,               // 0x0000_0080, 2
                      0xC0, 0x80, 0x00,         // 0x0010_0000, 3
                      0xFF, 0xFF, 0xFF, 0x7F,   // 0x0FFF_FFFF, 4
        ];
        let slice = &data[..];

        assert_eq!(vlq(slice, 0), Some((0x0000_0080, 2)));
        assert_eq!(vlq(slice, 2), Some((0x0010_0000, 3)));
        assert_eq!(vlq(slice, 5), Some((0x0FFF_FFFF, 4)));
    }

    #[test]
    fn vlq_fails_on_overflow() {
        assert!(vlq(&[0xFF, 0xFF, 0xFF, 0xFF, 0x7F], 0).is_none());
    }

    #[test]
    fn vlq_fails_on_bad_data() {
        assert!(vlq(&[0xFF], 0).is_none());
    }

    #[test]
    fn vlq_fails_on_bad_pos() {
        assert!(vlq(&[], 123).is_none());
    }

    #[test]
    fn ch_msg_len_note_off() {
        assert_eq!(ch_msg_len(0x80), 3);
    }

    #[test]
    fn ch_msg_len_note_on() {
        assert_eq!(ch_msg_len(0x91), 3);
    }

    #[test]
    fn ch_msg_len_poly_key_press() {
        assert_eq!(ch_msg_len(0xA2), 3);
    }

    #[test]
    fn ch_msg_len_control() {
        assert_eq!(ch_msg_len(0xB3), 3);
    }

    #[test]
    fn ch_msg_len_program() {
        assert_eq!(ch_msg_len(0xC4), 2);
    }

    #[test]
    fn ch_msg_len_channel_press() {
        assert_eq!(ch_msg_len(0xD5), 2);
    }

    #[test]
    fn ch_msg_len_pitch_bend() {
        assert_eq!(ch_msg_len(0xE6), 3);
    }

    #[test]
    fn sys_msg_len_sysex() {
        assert_eq!(sys_msg_len(&[0x00, 0xF0, 0xF7, 0x00], 1), Some(2));
    }

    #[test]
    fn sys_msg_len_sysex2() {
        assert_eq!(sys_msg_len(&[0xF0, 0x01, 0x02, 0x03, 0xF7], 0), Some(5));
    }

    #[test]
    fn sys_msg_len_fails_on_bad_sysex() {
        assert_eq!(sys_msg_len(&[0xF0], 0), None);
    }

    #[test]
    fn sys_msg_len_fails_on_bad_sysex2() {
        assert_eq!(sys_msg_len(&[0xF0, 0x01, 0x02, 0x03], 0), None);
    }

    #[test]
    fn sys_msg_len_tcqf() {
        assert_eq!(sys_msg_len(&[0xF1], 0), Some(2));
    }

    #[test]
    fn sys_msg_len_song_pos_ptr() {
        assert_eq!(sys_msg_len(&[0xF2], 0), Some(3));
    }

    #[test]
    fn sys_msg_len_song_select() {
        assert_eq!(sys_msg_len(&[0xF3], 0), Some(2));
    }

    #[test]
    fn sys_msg_len_undef1() {
        assert_eq!(sys_msg_len(&[0xF4], 0), None);
    }

    #[test]
    fn sys_msg_len_undef2() {
        assert_eq!(sys_msg_len(&[0xF5], 0), None);
    }

    #[test]
    fn sys_msg_len_tune_req() {
        assert_eq!(sys_msg_len(&[0xF6], 0), Some(1));
    }

    #[test]
    fn sys_msg_len_sysex_end() {
        assert_eq!(sys_msg_len(&[0xF7], 0), Some(1));
    }

    #[test]
    fn meta_msg_len_works() {
        assert_eq!(meta_msg_len(&[0xFF, 0x00, 0x81, 0x00], 0), Some(132));
    }

    #[test]
    fn meta_msg_len_works2() {
        assert_eq!(meta_msg_len(&[0x00, 0xFF, 0x01, 0x01], 1), Some(4));
    }

    #[test]
    fn meta_msg_len_fails_on_bad_data() {
        assert_eq!(meta_msg_len(&[0xFF], 0), None);
    }

    #[test]
    fn meta_msg_len_fails_on_bad_data2() {
        assert_eq!(meta_msg_len(&[0xFF, 0x00, 0xFF], 0), None);
    }

    #[test]
    fn is_ch_msg_works() {
        assert!(!is_ch_msg(0x7F));
        assert!(is_ch_msg(0x80));
        assert!(is_ch_msg(0xEF));
        assert!(!is_ch_msg(0xF0));
    }

    #[test]
    fn is_sys_msg_works() {
        assert!(!is_sys_msg(0xEF));
        assert!(is_sys_msg(0xF0));
        assert!(is_sys_msg(0xF7));
        assert!(!is_sys_msg(0xF8));
    }

    #[test]
    fn is_meta_msg_works() {
        assert!(!is_meta_msg(0xFE));
        assert!(is_meta_msg(0xFF));
    }
}
