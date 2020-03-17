/// A wrapper around a 64x32 bit buffer array that abstracts keyboard input and display output
use fixedbitset::FixedBitSet;
use minifb::Key;
use std::ops::Index;
use std::collections::HashSet;
use std::iter::FromIterator;

const WIDTH: usize = 64;
const HEIGHT: usize = 32;
const NUM_KEYS: usize = 16;

pub struct Graphics {
    buffer: FixedBitSet,
    font_set: [[u8; 5]; NUM_KEYS], // stores the 16 5-byte hex font set
    key_input: FixedBitSet,  // 16 bit hex keyboard input (0-F).
                             // Each bit stores the 1 (on) or 0 (off) keypress state
}

impl Graphics {
    pub fn new() -> Self {
        Graphics {
            buffer: FixedBitSet::with_capacity(WIDTH * HEIGHT),
            font_set: [
                [0xF0, 0x90, 0x90, 0x90, 0xF0], // 0
                [0x20, 0x60, 0x20, 0x20, 0x70], // 1
                [0xF0, 0x10, 0xF0, 0x80, 0xF0], // 2
                [0xF0, 0x10, 0xF0, 0x10, 0xF0], // 3
                [0x90, 0x90, 0xF0, 0x10, 0x10], // 4
                [0xF0, 0x80, 0xF0, 0x10, 0xF0], // 5
                [0xF0, 0x80, 0xF0, 0x90, 0xF0], // 6
                [0xF0, 0x10, 0x20, 0x40, 0x40], // 7
                [0xF0, 0x90, 0xF0, 0x90, 0xF0], // 8
                [0xF0, 0x90, 0xF0, 0x10, 0xF0], // 9
                [0xF0, 0x90, 0xF0, 0x90, 0x90], // 10
                [0xE0, 0x90, 0xE0, 0x90, 0xE0], // 11
                [0xF0, 0x80, 0x80, 0x80, 0xF0], // 12
                [0xE0, 0x90, 0x90, 0x90, 0xE0], // 13
                [0xF0, 0x80, 0xF0, 0x80, 0xF0], // 14
                [0xF0, 0x80, 0xF0, 0x80, 0x80], // 15
            ],
            key_input: FixedBitSet::with_capacity(NUM_KEYS),
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

    /// We use the following mapping for the 16 bit hex keyboard
    /// Keypad                   Keyboard
    /// +-+-+-+-+                +-+-+-+-+
    /// |1|2|3|C|                |1|2|3|4|
    /// +-+-+-+-+                +-+-+-+-+
    /// |4|5|6|D|                |Q|W|E|R|
    /// +-+-+-+-+       =>       +-+-+-+-+
    /// |7|8|9|E|                |A|S|D|F|
    /// +-+-+-+-+                +-+-+-+-+
    /// |A|0|B|F|                |Z|X|C|V|
    /// +-+-+-+-+                +-+-+-+-+
    pub fn map_key(k: &Key) -> Option<usize> {
        match k {
            Key::Key1 => Some(1),
            Key::Key2 => Some(2),
            Key::Key3 => Some(3),
            Key::Key4 => Some(0xC),
            Key::Q => Some(4),
            Key::W => Some(5),
            Key::E => Some(6),
            Key::R => Some(0xD),
            Key::A => Some(7),
            Key::S => Some(8),
            Key::D => Some(9),
            Key::F => Some(0xE),
            Key::Z => Some(0xA),
            Key::X => Some(0),
            Key::C => Some(0xB),
            Key::V => Some(0xF),
            _ => None,
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    pub fn handle_key_down(&mut self, k: &Key) {
        if let Some(idx) = Graphics::map_key(k) {
            self.handle_key_down_inner(idx);
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    fn handle_key_down_inner(&mut self, idx: usize) {
        if idx >= 0 && idx <= 0xF {
            self.key_input.put(idx);
        }
    }

    /// Handle the key up event for one of the 16 possible keys
    pub fn handle_key_up(&mut self, k: &Key) {
        if let Some(idx) = Graphics::map_key(k) {
            self.handle_key_up_inner(idx);
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    fn handle_key_up_inner(&mut self, idx: usize) {
        if idx >= 0 && idx <= 0xF {
            self.key_input.set(idx, false);
        }
    }

    /// Given the indices of the keys pressed down on the system keyboard,
    /// fire the appropriate key_up and key_down handlers
    pub fn update_keyboard_with_vec(&mut self, key_idxs: &Vec<usize>) {
        let set: HashSet<usize> = HashSet::from_iter(key_idxs.iter().cloned());

        // check each of the 16 keys to see which have changed from up to down or vice versa
        for i in 0..self.key_input.len() {
            let system_key_is_down = set.contains(&i);
            let interpreter_key_is_down = self.get_key_state(i);

            if system_key_is_down && !interpreter_key_is_down {
                self.handle_key_down_inner(i);
            } else if !system_key_is_down && interpreter_key_is_down {
                self.handle_key_up_inner(i);
            }
        }
    }

    /// Return the bool value of the bit at the given index
    pub fn get_key_state(&self, idx: usize) -> bool {
        self.key_input[idx]
    }
}

impl Index<usize> for Graphics {
    type Output = bool;

    #[inline]
    fn index(&self, bit: usize) -> &Self::Output {
        &self.buffer[bit]
    }
}
