//! MIDI support.

use std::cmp;

use bits::{U3, U4, U7, U14, U15};
use pitch::Pitch;

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
            Some(Seq { tracks: Vec::new(), div })
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
    data: Vec<u8>
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
        Track { data: Vec::with_capacity(capacity) }
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

    // Returns the value of Variable-Length Quantity (VLQ) located within the
    // raw data at the specified position and the size the VLQ data in bytes.
    // Note: 0x0FFF_FFFF is the largest value allowed by the MIDI spec.
    fn vlq_at(&self, pos: usize) -> Option<(usize, usize)> {
        let mut value = 0usize;
        for i in pos..cmp::min(pos + 4, self.data.len()) {
            let byte = self.data[i];
            let bits7 = byte & 0x7F;
            value = value << 7 | bits7 as usize;
            if byte == bits7 {
                return Some((value, i - pos + 1));
            }
        }
        None
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

    #[test]
    fn vlq_at_reads_byte() {
        let mut track = Track::new();
        track.add_raw(&[0]);

        let (value, count) = track.vlq_at(0).unwrap();

        assert_eq!(value, 0);
        assert_eq!(count, 1);

        track.add_raw(&[1]);

        assert_eq!(track.vlq_at(1), Some((1, 1)));
    }

    #[test]
    fn vlq_at_reads_multibyte() {
        let mut track = Track::new();
        track.add_raw(&[
                      0x81, 0x00,               // 0x0000_0080, 2
                      0xC0, 0x80, 0x00,         // 0x0010_0000, 3
                      0xFF, 0xFF, 0xFF, 0x7F,   // 0x0FFF_FFFF, 4
        ]);

        assert_eq!(track.vlq_at(0), Some((0x0000_0080, 2)));
        assert_eq!(track.vlq_at(2), Some((0x0010_0000, 3)));
        assert_eq!(track.vlq_at(5), Some((0x0FFF_FFFF, 4)));
    }

    #[test]
    fn vlq_at_fails_on_overflow() {
        let mut track = Track::new();
        track.add_raw(&[0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);

        assert!(track.vlq_at(0).is_none());
    }

    #[test]
    fn vlq_at_fails_on_bad_data() {
        let mut track = Track::new();
        track.add_raw(&[0xFF]);

        assert!(track.vlq_at(0).is_none());
    }

    #[test]
    fn vlq_at_fails_on_bad_pos() {
        assert!(Track::new().vlq_at(123).is_none());
    }
}

/// Channel MIDI messages.
pub enum ChannelMsg {
    NoteOff { channel: U4, pitch: Pitch, velocity: U7 },
    NoteOn { channel: U4, pitch: Pitch, velocity: U7 },
    PolyKeyPress { channel: U4, pitch: Pitch, pressure: U7 },
    Control { channel: U4, controller: U7, value: U7 },
    Program { channel: U4, program: U7 },
    Press { channel: U4, pressure: U7 },
    PitchBend { channel: U4, value: U14 },
    Mode { channel: U4, mode: ChannelMode },
}

/// Holds data for `ChannelMsg::Mode` message.
pub enum ChannelMode {
    SoundOff,
    ResetControllers,
    LocalControlOff,
    LocalControlOn,
    NotesOff,
    OmniOff,
    OmniOn,
    PolyOff(U7),
    PolyOn,
}

/// System common MIDI messages.
pub enum SysMsg {
    SysEx,
    TCQF { msg_type: U3, value: U4 },
    SongPosPtr(U14),
    SongSelect(U7),
    TuneRequest,
    SysExEnd,
}

/// System real-time (non-SMF) MIDI messages.
pub enum SysRTMsg {
    Clock,
    Start,
    Continue,
    ActiveSensing,
    Reset,
}

/// Meta (SMF-only) MIDI messages.
pub enum MetaMsg {
}
