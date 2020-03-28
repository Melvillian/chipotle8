use minifb::Key as Mini_Key;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;

const NUM_KEYS: usize = 16;

/// Key's variants are the 16 keys from the CHIP-8's hexadecimal keyboard.
/// The recommended key mapping is:
///
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
#[derive(Eq, PartialEq, Hash)]
pub enum Key {
    Key1,
    Key2,
    Key3,
    C,
    Key4,
    Key5,
    Key6,
    D,
    Key7,
    Key8,
    Key9,
    E,
    A,
    Key0,
    B,
    F,
}

/// Contains the state (up or down) of the CHIP-8's 16 keys, as well as any
/// state related to keyboard input
pub struct Keyboard {
    key_input: HashMap<usize, bool>, // 16 bit hex keyboard input (0-F).
    // Each bit stores the 1 (on) or 0 (off) keypress state
    fx0a_metadata: FX0AMetadata, // used to store state for instruction FX0A,
}

impl Keyboard {
    pub fn new() -> Self {
        let mut key_input = HashMap::with_capacity(NUM_KEYS);
        for idx in 0..NUM_KEYS {
            key_input.insert(idx, false);
        }

        Keyboard {
            key_input,
            fx0a_metadata: FX0AMetadata {
                should_block_on_keypress: false,
                last_key_pressed: None,
                register: None,
            },
        }
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
    pub fn map_key(k: &Mini_Key) -> Option<usize> {
        match k {
            Mini_Key::Key1 => Some(1),
            Mini_Key::Key2 => Some(2),
            Mini_Key::Key3 => Some(3),
            Mini_Key::Key4 => Some(0xC),
            Mini_Key::Q => Some(4),
            Mini_Key::W => Some(5),
            Mini_Key::E => Some(6),
            Mini_Key::R => Some(0xD),
            Mini_Key::A => Some(7),
            Mini_Key::S => Some(8),
            Mini_Key::D => Some(9),
            Mini_Key::F => Some(0xE),
            Mini_Key::Z => Some(0xA),
            Mini_Key::X => Some(0),
            Mini_Key::C => Some(0xB),
            Mini_Key::V => Some(0xF),
            _ => None,
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    #[cfg(test)]
    pub fn handle_key_down(&mut self, k: &Mini_Key) {
        if let Some(idx) = Self::map_key(k) {
            self.set_key_down(idx);
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    fn set_key_down(&mut self, idx: usize) {
        if idx <= 0xF {
            self.key_input.insert(idx, true);
        }
    }

    /// Handle the key up event for one of the 16 possible keys
    #[cfg(test)]
    pub fn handle_key_up(&mut self, k: &Mini_Key) {
        if let Some(idx) = Self::map_key(k) {
            self.set_key_up(idx);
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    fn set_key_up(&mut self, idx: usize) {
        if idx <= 0xF {
            self.key_input.insert(idx, false);
        }
    }

    /// Given the indices of the keys pressed down on the system keyboard,
    /// fire the appropriate key_up and key_down handlers
    pub fn update_keyboard_with_vec(&mut self, key_idxs: &[usize]) {
        let set: HashSet<usize> = HashSet::from_iter(key_idxs.iter().cloned());

        // check each of the 16 keys to see which have changed from up to down or vice versa
        for i in 0..NUM_KEYS {
            let system_key_is_down = set.contains(&i);
            let interpreter_key_is_down = self.get_key_state(i);

            if system_key_is_down && !interpreter_key_is_down {
                self.set_key_down(i);
            } else if !system_key_is_down && interpreter_key_is_down {
                self.set_key_up(i);
            }
        }
    }

    /// Return the bool value of the bit at the given index
    pub fn get_key_state(&self, idx: usize) -> bool {
        self.key_input[&idx]
    }

    /// Called when the KeyOpGet Op is executed. The interpreter will transition out of
    /// the blocking state once a keypress gets detected
    pub fn block(&mut self, reg: u8) {
        self.fx0a_metadata.should_block_on_keypress = true;
        self.fx0a_metadata.register = Some(reg);
    }

    /// Handle and reset the Interpreter from a key press. Only gets called
    /// when the Interpreter is blocking as a result of a prior FX0A instruction. Return
    /// the index of the key stored earlier
    pub fn unblock(&mut self) -> usize {
        let reg_idx = self
            .fx0a_metadata
            .register
            .expect("invalid FXOA metadata state");
        self.fx0a_metadata = FX0AMetadata::default();
        reg_idx as usize
    }

    /// Checks if we're in a blocking state, and if a valid key has been pressed
    /// transitions out of the blocking state
    pub fn handle_fx0a_state(&mut self, key_idxs: &[usize]) -> (Option<usize>, Option<u8>) {
        // check if the FX0A instruction has us in a blocking state and if we can now unblock
        if self.fx0a_metadata.should_block_on_keypress {
            // we choose of the first key because we have to choose SOME key, so why not the first?
            key_idxs.get(0).map(|k| {
                let reg_idx = self.unblock();
                return (Some(reg_idx), Some(*k as u8));
            });
        }
        (None, None)
    }

    /// Returns true if the we're waiting on keyboard input because of a FX0A instruction,
    /// and false otherwise
    pub fn is_blocking(&self) -> bool {
        self.fx0a_metadata.should_block_on_keypress
    }
}

/// Stores data needed to handle instruction FX0A
#[derive(Default, Debug, PartialEq)]
struct FX0AMetadata {
    should_block_on_keypress: bool, // set to true if CPU is waiting on a keypress
    last_key_pressed: Option<Mini_Key>,  // once a key is pressed store it here
    register: Option<u8>,           // the register to store the pressed key in
}
