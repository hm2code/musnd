//! MIDI support.

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
}

impl Track {
    /// Creates a new empty track.
    pub fn new() -> Track {
        Track {}
    }

    /// Returns the duration in ticks.
    pub fn duration(&self) -> usize {
        0
    }
}

#[cfg(test)]
mod track_tests {
    use super::Track;

    #[test]
    fn new_has_zero_duration() {
        assert_eq!(Track::new().duration(), 0);
    }
}
