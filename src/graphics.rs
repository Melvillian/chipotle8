/// A wrapper around a 64x32 bit buffer array that abstracts keyboard input and display output

use fixedbitset::FixedBitSet;
use std::ops::Index;

const WIDTH: usize = 64;
const HEIGHT: usize = 32;

pub struct Graphics {
    buffer: FixedBitSet,
    font_set: [[u8; 5]; 16],  // stores the 16 5-byte hex font set
    key_input: FixedBitSet,     // 16 bit hex keyboard input (0-F).
    // Each bit stores the 1 (on) or 0 (off) keypress state
}

impl Graphics {
    pub fn new() -> Self {
        Graphics {
            buffer: FixedBitSet::with_capacity(WIDTH * HEIGHT),
            font_set: [
                [0xF0, 0x90, 0x90, 0x90, 0xF0],  // 0
                [0x20, 0x60, 0x20, 0x20, 0x70],  // 1
                [0xF0, 0x10, 0xF0, 0x80, 0xF0],  // 2
                [0xF0, 0x10, 0xF0, 0x10, 0xF0],  // 3
                [0x90, 0x90, 0xF0, 0x10, 0x10],  // 4
                [0xF0, 0x80, 0xF0, 0x10, 0xF0],  // 5
                [0xF0, 0x80, 0xF0, 0x90, 0xF0],  // 6
                [0xF0, 0x10, 0x20, 0x40, 0x40],  // 7
                [0xF0, 0x90, 0xF0, 0x90, 0xF0],  // 8
                [0xF0, 0x90, 0xF0, 0x10, 0xF0],  // 9
                [0xF0, 0x90, 0xF0, 0x90, 0x90],  // 10
                [0xE0, 0x90, 0xE0, 0x90, 0xE0],  // 11
                [0xF0, 0x80, 0x80, 0x80, 0xF0],  // 12
                [0xE0, 0x90, 0x90, 0x90, 0xE0],  // 13
                [0xF0, 0x80, 0xF0, 0x80, 0xF0],  // 14
                [0xF0, 0x80, 0xF0, 0x80, 0x80],  // 15
            ],
            key_input: FixedBitSet::with_capacity(16),
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

    //pub fn key_pressed
}

impl Index<usize> for Graphics {
    type Output = bool;

    #[inline]
    fn index(&self, bit: usize) -> &Self::Output {
        &self.buffer[bit]
    }
}
