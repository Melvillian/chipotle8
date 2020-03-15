/// A wrapper around a 64x32 bit buffer array that abstracts keyboard input and display output

use fixedbitset::FixedBitSet;
use std::ops::Index;
use std::ops::IndexMut;

const WIDTH: usize = 64;
const HEIGHT: usize = 32;

pub struct Graphics {
    buffer: FixedBitSet,
}

impl Graphics {
    pub fn new() -> Self {
        Graphics {
            buffer: FixedBitSet::with_capacity(WIDTH * HEIGHT),
        }
    }

    pub fn len(&self) -> usize {
        return WIDTH * HEIGHT;
    }

    /// Given x and y coordinate for a bit in the buffer, return the corresponding
    /// index of that bit in the buffer
    pub fn get_graphics_idx(x: u8, y: u8) -> usize {
        let column = x as usize;
        let row = (y * 8) as usize;

        column + row
    }

    pub fn set(&mut self, bit: usize, enabled: bool) {
        self.buffer.set(bit, enabled)
    }
}

impl Index<usize> for Graphics {
    type Output = bool;

    #[inline]
    fn index(&self, bit: usize) -> &Self::Output {
        &self.buffer[bit]
    }
}
