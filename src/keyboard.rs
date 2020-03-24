use fixedbitset::FixedBitSet;
use minifb::Key;
use std::collections::HashSet;
use std::iter::FromIterator;

const NUM_KEYS: usize = 16;

/// Contains the state (up or down) of the CHIP-8's 16 keys, as well as any
/// state related to keyboard input
pub struct Keyboard {
    key_input: FixedBitSet,  // 16 bit hex keyboard input (0-F).
    // Each bit stores the 1 (on) or 0 (off) keypress state
    fx0a_metadata: FX0AMetadata, // used to store state for instruction FX0A,


}

impl Keyboard {
    pub fn new() -> Self {
        Keyboard {
            key_input: FixedBitSet::with_capacity(NUM_KEYS),
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
    #[cfg(test)]
    pub fn handle_key_down(&mut self, k: &Key) {
        if let Some(idx) = Self::map_key(k) {
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
        if let Some(idx) = Self::map_key(k) {
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

    /// Called when the KeyOpGet Op is executed. The interpreter will transition out of
    /// the blocking state once a keypress gets detected
    pub fn go_to_blocking_state(&mut self, reg: u8) {
        self.fx0a_metadata.should_block_on_keypress = true;
        self.fx0a_metadata.register = Some(reg);
    }

    /// Handle and reset the Interpreter from a key press. Only gets called
    /// when the Interpreter is blocking as a result of a prior FX0A instruction. Return
    /// the index of the key stored earlier
    pub fn return_from_blocking_state(&mut self) -> usize {
        let reg_idx = self
            .fx0a_metadata
            .register
            .expect("invalid FXOA metadata state");
        self.fx0a_metadata = FX0AMetadata::default();
        reg_idx as usize
    }

    /// Checks if we're in a blocking state, and if a valid key has been pressed
    /// transitions out of the blocking state
    pub fn handle_fx0a_state(&mut self, keys: &Vec<Key>) -> (Option<usize>, Option<u8>) {
        // check if the FX0A instruction has us in a blocking state and if we can now unblock
        if self.fx0a_metadata.should_block_on_keypress {
            let key_inputs: Vec<usize> = keys.iter()
                .map(Self::map_key)
                .filter(Option::is_some)
                .map(Option::unwrap)
                .collect();

            // we choose of the first key because we have to choose SOME key, so why not the first?
            key_inputs.get(0).map(|k| {
                let reg_idx = self.return_from_blocking_state();
                (Some(reg_idx), Some(*k as u8))
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
#[derive(Default, Debug, PartialEq,)]
struct FX0AMetadata {
    should_block_on_keypress: bool, // set to true if CPU is waiting on a keypress
    last_key_pressed: Option<Key>,  // once a key is pressed store it here
    register: Option<u8>,           // the register to store the pressed key in
}