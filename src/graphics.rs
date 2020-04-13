//! A wrapper around a 64x32 bit buffer array that abstracts the Interpreter's display state

use std::ops::Index;

pub const WIDTH: usize = 64;
pub const HEIGHT: usize = 32;
pub const ENLARGE_RATIO: usize = 10;
use serde::Serialize;

const WHITE_RGB: u32 = 0x00FF_FFFF;
const BLACK_RGB: u32 = 0x0000_0000;

/// The max size the Graphic's `changes` `Vec` can grow until we set it to be empty.
/// We need this because without periodically trimming it `changes` will grow unbounded
/// and we'll run out of memory. Ideally `changes` never grows this large because
/// a user will be calling `flush_changes` in a tight loop. This length is large
/// enough for about 5 seconds of Pong at 2ms per cycle before we need to empty it.
const MAX_CHANGES_SIZE: usize = 5_000;

/// Holds the coordinates and state of a recently changed pixel in the display.
/// With DisplayChange we can return only those pixel which changed to the user,
/// which is much more performant than returning ALL of the pixel changes through
/// [`get_pixels`](function.get_pixels.html)
#[derive(Clone, PartialEq, Debug, Default, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DisplayChange {
    x: usize,
    y: usize,
    is_alive: bool,
}

pub struct Graphics {
    // the 64x32 bitmap
    buffer: [u32; WIDTH * HEIGHT],

    // our 64x32 bitmap is very small, so let's enlarge it by mapping ever pixel of our
    // bitmap to an ENLARGE_RATIO-by-ENLARGE_RATIO bitmap of the same color
    display: Vec<u32>,

    // A collection of all the pixel display changes since we last reset the changes
    changes: Vec<DisplayChange>,
}

impl Graphics {
    pub fn new() -> Self {
        Graphics {
            buffer: [0; WIDTH * HEIGHT],
            display: vec![0; (ENLARGE_RATIO * WIDTH) * (ENLARGE_RATIO * HEIGHT)],
            changes: vec![],
        }
    }

    pub fn buffer(&self) -> &[u32] {
        &self.buffer
    }

    #[cfg(test)]
    pub fn len(&self) -> usize {
        WIDTH * HEIGHT
    }

    /// Given x (column) and y (row) coordinates for a bit in the buffer, return the corresponding
    /// index of that bit in the buffer
    #[inline]
    pub(crate) fn get_graphics_idx(x: u8, y: u8) -> usize {
        let column = x as usize % WIDTH;
        let row = (y as usize % HEIGHT) * WIDTH;

        column + row
    }

    /// Set the given pixel at `idx` to the XOR of the current pixel at `idx` and black if `enable`
    /// equals true or white if `enable` equals false. Returns true if the pixel was unset
    #[inline]
    pub fn xor_set(&mut self, x: u8, y: u8, enabled: bool) -> bool {
        let idx = Self::get_graphics_idx(x, y);

        let prev_pix = self.buffer[idx];

        if enabled {
            self.buffer[idx] ^= WHITE_RGB;
        } else {
            self.buffer[idx] ^= BLACK_RGB;
        }

        // we keep a running collection of recent changes to the display, so we must update it
        self.add_change(DisplayChange {
            x: x as usize % WIDTH,
            y: y as usize % HEIGHT,
            is_alive: enabled,
        });

        prev_pix == WHITE_RGB && self.buffer[idx] == BLACK_RGB
    }

    /// Add a new DisplayChange to `changes`, and shrink `changes` if it's too large
    fn add_change(&mut self, change: DisplayChange) {
        if self.changes.len() == MAX_CHANGES_SIZE {
            self.changes.resize(0, DisplayChange::default());
        }

        self.changes.push(change);
    }

    /// set all pixels to black
    #[inline]
    pub fn clear(&mut self) {
        for i in 0..self.buffer.len() {
            self.buffer[i] = BLACK_RGB;
        }
    }

    /// Returns the pixels for a 640 x 320 resolution display.
    ///
    /// TODO NOTE: Currently we enlarge the base 64x32 resolution by
    /// ENLARGE_RATIO (currently equals 10) because otherwise the screen
    /// is far too small to view. In the future we will make this performantly
    /// dynamically updateable so users can resize their game windows.
    pub fn get_pixels(&mut self) -> &[u32] {
        // TODO: nit: refactor looping logic so that it is more cache friendly. Right now
        // we are jumping ahead in the array too much and thrashing the cache
        for y in 0..HEIGHT {
            let y_offset = y * WIDTH * ENLARGE_RATIO * ENLARGE_RATIO;
            for x in 0..WIDTH {
                //if x == 2 { panic!("D");}
                let buffer_idx = Self::get_graphics_idx(x as u8, y as u8);
                let pixel = self.buffer()[buffer_idx];

                let x_offset = x * ENLARGE_RATIO;

                // since each call to .draw reuses the same display Vec, we can save time by
                // skipping writing a square by seeing if the same color already exists in the
                // display Vec this time as it did before. Since the pixels rarely change, this will
                // save us a lot of time.
                if pixel == self.display[y_offset + x_offset] {
                    continue;
                }

                // looks like the pixel changed, so we'll have to go through the hassle of
                // writing it all to the display
                for row_square in 0..ENLARGE_RATIO {
                    let row_offset = row_square * WIDTH * ENLARGE_RATIO;
                    for col_square in 0..ENLARGE_RATIO {
                        let display_idx = (y_offset + row_offset) + (x_offset + col_square);
                        self.display[display_idx] = pixel;
                    }
                }
            }
        }

        &self.display
    }

    /// Flushes the recent changes to the interpreter's display and returns them
    pub fn flush_changes(&mut self) -> Vec<DisplayChange> {
        let changes = self.changes.clone();
        self.changes.resize(0, DisplayChange::default());

        changes
    }
}

impl Index<usize> for Graphics {
    type Output = u32;

    #[inline]
    fn index(&self, bit: usize) -> &Self::Output {
        &self.buffer[bit]
    }
}

#[cfg(test)]
pub mod graphics_tests {
    use super::*;

    #[test]
    fn changes() {
        let mut g = Graphics::new();

        // artificially set some pixels so we can xor_set them later
        g.xor_set(0, 0, true);
        g.xor_set(0, 1, false);
        g.xor_set(1, 0, false);

        assert_eq!(
            g.changes,
            vec![
                DisplayChange {
                    x: 0,
                    y: 0,
                    is_alive: true
                },
                DisplayChange {
                    x: 0,
                    y: 1,
                    is_alive: false
                },
                DisplayChange {
                    x: 1,
                    y: 0,
                    is_alive: false
                },
            ]
        );

        g.flush_changes();

        assert_eq!(g.changes, vec![]);
    }
}
