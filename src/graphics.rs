/// A wrapper around a 64x32 bit buffer array that abstracts keyboard input and display output
use fixedbitset::FixedBitSet;
use minifb::Key;
use std::ops::Index;
use std::collections::HashSet;
use std::iter::FromIterator;

pub const WIDTH: usize = 64;
pub const HEIGHT: usize = 32;

const NUM_KEYS: usize = 16;
const BLACK_RGB: u32 = 0xFFFFFF;
const WHITE_RGB: u32 = 0x000000;

pub struct Graphics {
    buffer: [u32; WIDTH * HEIGHT],
    key_input: FixedBitSet,  // 16 bit hex keyboard input (0-F).
                             // Each bit stores the 1 (on) or 0 (off) keypress state
}

impl Graphics {
    pub fn new() -> Self {
        Graphics {
            buffer: [0; WIDTH * HEIGHT],
            key_input: FixedBitSet::with_capacity(NUM_KEYS),
        }
    }

    pub fn buffer(&self) -> &[u32] {
        &self.buffer
    }

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
            self.buffer[idx]^=BLACK_RGB;
        } else {
            self.buffer[idx]^=WHITE_RGB;
        }

        prev_pix == BLACK_RGB && self.buffer[idx] == WHITE_RGB
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

    /// set all pixels to white (0)
    #[inline]
    pub fn clear(&mut self) {
        for i in 0..self.buffer.len() {
            self.buffer[i] = 0;
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    #[cfg(test)]
    pub fn handle_key_down(&mut self, k: &Key) {
        if let Some(idx) = Graphics::map_key(k) {
            self.handle_key_down_inner(idx);
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    fn handle_key_down_inner(&mut self, idx: usize) {
        if idx <= 0xF {
            self.key_input.put(idx);
        }
    }

    /// Handle the key up event for one of the 16 possible keys
    #[cfg(test)]
    pub fn handle_key_up(&mut self, k: &Key) {
        if let Some(idx) = Graphics::map_key(k) {
            self.handle_key_up_inner(idx);
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    fn handle_key_up_inner(&mut self, idx: usize) {
        if idx <= 0xF {
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
    type Output = u32;

    #[inline]
    fn index(&self, bit: usize) -> &Self::Output {
        &self.buffer[bit]
    }
}
