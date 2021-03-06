use slog::debug;
use slog::Logger;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::sync::Arc;

/// Key's variants are the 16 keys from the CHIP-8's hexadecimal keyboard.
/// The recommended key mapping, based on the standard CHIP-8 emulator implementation is:
///
/// ```text
/// Keyboard              Keypad
/// +-+-+-+-+             +-+-+-+-+
/// |1|2|3|4|             |1|2|3|C|
/// +-+-+-+-+             +-+-+-+-+
/// |Q|W|E|R|             |4|5|6|D|
/// +-+-+-+-+      =>     +-+-+-+-+
/// |A|S|D|F|             |7|8|9|E|
/// +-+-+-+-+             +-+-+-+-+
/// |Z|X|C|V|             |A|0|B|F|
/// +-+-+-+-+             +-+-+-+-+
/// ```
#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug)]
pub enum Key {
    Key0,
    Key1,
    Key2,
    Key3,
    Key4,
    Key5,
    Key6,
    Key7,
    Key8,
    Key9,
    A,
    B,
    C,
    D,
    E,
    F,
}

impl Key {
    /// Returns a collection of Keys which can be iterated over
    fn variants() -> Vec<Key> {
        vec![
            Self::Key0,
            Self::Key1,
            Self::Key2,
            Self::Key3,
            Self::Key4,
            Self::Key5,
            Self::Key6,
            Self::Key7,
            Self::Key8,
            Self::Key9,
            Self::A,
            Self::B,
            Self::C,
            Self::D,
            Self::E,
            Self::F,
        ]
    }
}

impl From<u8> for Key {
    fn from(reg_val: u8) -> Self {
        match reg_val {
            v if v <= 0xF => Key::variants()[v as usize],
            _ => panic!(
                "cannot convert register value {} to Key. value must be <= 0xF!",
                reg_val
            ),
        }
    }
}
/// Contains the state (up or down) of the CHIP-8's 16 keys, as well as any
/// state related to keyboard input
pub struct Keyboard {
    key_input: HashMap<Key, bool>, // 16 bit hex keyboard input (0-F). true if pressed otherwise false
    fx0a_metadata: FX0AMetadata,   // used to store state for instruction FX0A,
    logger: Arc<Logger>,
}

impl Keyboard {
    /// Creates a Keyboard with all Keys up and in the unblocking state
    pub fn new(logger: Arc<Logger>) -> Self {
        let key_input: HashMap<Key, bool> = Key::variants().iter().map(|k| (*k, false)).collect();

        Keyboard {
            key_input,
            logger,
            fx0a_metadata: FX0AMetadata {
                should_block_on_keypress: false,
                register: None,
            },
        }
    }

    /// Handle the key down event for one of the 16 possible keys
    #[cfg(test)]
    pub fn handle_key_down(&mut self, k: Key) {
        self.set_key_down(k);
    }

    /// Handle the key down event for one of the 16 possible keys
    fn set_key_down(&mut self, k: Key) {
        debug!(self.logger, "key down: {:?}", k);
        self.key_input.insert(k, true);
    }

    /// Handle the key up event for one of the 16 possible keys
    #[cfg(test)]
    pub fn handle_key_up(&mut self, k: Key) {
        self.set_key_up(k);
    }

    /// Handle the key down event for one of the 16 possible keys
    fn set_key_up(&mut self, k: Key) {
        debug!(self.logger, "key up: {:?}", k);
        self.key_input.insert(k, false);
    }

    /// Given an array of pressed down Keys on the system keyboard,
    /// fire the appropriate key up and key down functions
    pub fn update_keyboard(&mut self, keys: &[Key]) {
        let set: HashSet<Key> = HashSet::from_iter(keys.iter().cloned());

        // check each of the 16 keys to see which have changed from up to down or vice versa
        for k in Key::variants() {
            let system_key_is_down = set.contains(&k);
            let emulator_key_is_down = self.get_key_state(k);

            if system_key_is_down && !emulator_key_is_down {
                self.set_key_down(k);
            } else if !system_key_is_down && emulator_key_is_down {
                self.set_key_up(k);
            }
        }
    }

    /// Return the bool value of the bit at the given index
    pub fn get_key_state(&self, k: Key) -> bool {
        self.key_input[&k]
    }

    /// Called when the KeyOpGet Op is executed. The emulator will transition out of
    /// the blocking state once a keypress gets detected
    pub fn block(&mut self, reg: u8) {
        self.fx0a_metadata.should_block_on_keypress = true;
        self.fx0a_metadata.register = Some(reg);
    }

    /// Handle and reset the Emulator from a key press. Only gets called
    /// when the Emulator is blocking as a result of a prior FX0A instruction. Return
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
    /// transitions out of the blocking state. Returns a tuple with the register
    /// to store the key in and the Key which was pressed
    pub fn handle_fx0a_state(&mut self, keys: &[Key]) -> (Option<usize>, Option<u8>) {
        // check if the FX0A instruction has us in a blocking state and if we can now unblock
        if self.fx0a_metadata.should_block_on_keypress {
            // we choose of the first key because we have to choose SOME key, so why not the first?
            keys.get(0).map(|k: &Key| {
                let reg_idx = self.unblock();
                (Some(reg_idx), Some(*k))
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
    register: Option<u8>,           // the register to store the pressed key in
}
