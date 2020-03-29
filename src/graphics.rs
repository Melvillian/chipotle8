//! A wrapper around a 64x32 bit buffer array that abstracts the Interpreter's display state

use std::ops::Index;

pub const WIDTH: usize = 64;
pub const HEIGHT: usize = 32;
pub const ENLARGE_RATIO: usize = 10;

const BLACK_RGB: u32 = 0xFFFFFF;
const WHITE_RGB: u32 = 0x000000;

pub struct Graphics {
    buffer: [u32; WIDTH * HEIGHT],
    display: Vec<u32>,
}

impl Graphics {
    pub fn new() -> Self {
        Graphics {
            buffer: [0; WIDTH * HEIGHT],
            // our 64x32 bitmap is very small, so let's enlarge it by mapping ever pixel of our
            // bitmap to an ENLARGE_RATIO-by-ENLARGE_RATIO bitmap of the same color
            display: vec![0; (ENLARGE_RATIO * WIDTH) * (ENLARGE_RATIO * HEIGHT)],
        }
    }

    pub fn buffer(&self) -> &[u32] {
        &self.buffer
    }

    #[cfg(test)]
    pub fn len(&self) -> usize {
        return WIDTH * HEIGHT;
    }

    /// Given x (column) and y (row) coordinates for a bit in the buffer, return the corresponding
    /// index of that bit in the buffer
    #[inline]
    pub fn get_graphics_idx(x: u8, y: u8) -> usize {
        let column = x as usize % WIDTH;
        let row = (y as usize % HEIGHT) * WIDTH;

        column + row
    }

    /// Set the given pixel to black if enabled equals true, and to white otherwise
    #[inline]
    #[cfg(test)]
    pub fn set(&mut self, x: u8, y: u8, enabled: bool) {
        let idx = Self::get_graphics_idx(x, y);
        if enabled {
            self.buffer[idx] = BLACK_RGB;
        } else {
            self.buffer[idx] = WHITE_RGB;
        }
    }

    /// Set the given pixel at `idx` to the XOR of the current pixel at `idx` and black if `enable`
    /// equals true or white if `enable` equals false. Returns true if the pixel was unset
    #[inline]
    pub fn xor_set(&mut self, x: u8, y: u8, enabled: bool) -> bool {
        let idx = Self::get_graphics_idx(x, y);

        let prev_pix = self.buffer[idx];

        if enabled {
            self.buffer[idx] ^= BLACK_RGB;
        } else {
            self.buffer[idx] ^= WHITE_RGB;
        }

        prev_pix == BLACK_RGB && self.buffer[idx] == WHITE_RGB
    }

    /// set all pixels to white (0)
    #[inline]
    pub fn clear(&mut self) {
        for i in 0..self.buffer.len() {
            self.buffer[i] = 0;
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
}

impl Index<usize> for Graphics {
    type Output = u32;

    #[inline]
    fn index(&self, bit: usize) -> &Self::Output {
        &self.buffer[bit]
    }
}
