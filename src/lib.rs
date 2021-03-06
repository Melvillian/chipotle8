//! A CHIP-8 emulator that can be used as a library in your Rust programs.
//!
//! `chipotle8` lets you play retro classics like Pong with the keyboard and window
//! crates of your choice. In the example below we choose to use the
//! [`minifb`](https://crates.io/crates/minifb) and [`device_query`](https://crates.io/crates/device_query)
//! crates for window and keyboard management, respectively, but you can select any you like.
//!
//! In order for `chipotle8` to understand which system keyboard keys are pressed down
//! you will need to implement the [`AsKeyboard`](trait.AsKeyboard.html) trait's
//! [`keys_down`](trait.AsKeyboard.html#tymethod.keys_down) method which should return
//! a [`Vec`](https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html)`<`[`Key`](enum.Key.html)`>`
//! representing the system keys that are currently pressed down.
//!
//! # Examples
//!
//! ```no_run
//! use chipotle8::{AsKeyboard, Emulator, Key, HEIGHT, WIDTH};
//! use device_query::{DeviceQuery, DeviceState, Keycode};
//! use minifb::{ScaleMode, Window, WindowOptions};
//! use std::io::Error;
//! use std::thread;
//! use std::time::Duration;
//!
//! struct Keyboard(pub DeviceState);
//!
//! impl AsKeyboard for Keyboard {
//!     fn keys_down(&self) -> Vec<Key> {
//!         self.0
//!             .get_keys()
//!             .iter()
//!             .filter_map(|key: &Keycode| match key {
//!                 Keycode::Key1 => Some(Key::Key1),
//!                 Keycode::Key2 => Some(Key::Key2),
//!                 Keycode::Key3 => Some(Key::Key3),
//!                 Keycode::Key4 => Some(Key::C),
//!                 Keycode::Q    => Some(Key::Key4),
//!                 Keycode::W    => Some(Key::Key5),
//!                 Keycode::E    => Some(Key::Key6),
//!                 Keycode::R    => Some(Key::D),
//!                 Keycode::A    => Some(Key::Key7),
//!                 Keycode::S    => Some(Key::Key8),
//!                 Keycode::D    => Some(Key::Key9),
//!                 Keycode::F    => Some(Key::E),
//!                 Keycode::Z    => Some(Key::A),
//!                 Keycode::X    => Some(Key::Key0),
//!                 Keycode::C    => Some(Key::B),
//!                 Keycode::V    => Some(Key::F),
//!                 _ => None,
//!             })
//!             .collect()
//!     }
//! }
//! fn main() -> Result<(), Error> {
//!     let mut window: Window = Window::new(
//!         "Chip 8 Emulator (In Rust!)",
//!         chipotle8::WIDTH,
//!         chipotle8::HEIGHT,
//!         WindowOptions {
//!             resize: true,
//!             scale_mode: ScaleMode::UpperLeft,
//!             ..WindowOptions::default()
//!         },
//!     )
//!     .expect("Unable to create window");
//!
//!     // Limit to max update rate. This only needs about 60 Hz, which is 16ms
//!     window.limit_update_rate(Some(Duration::from_millis(16)));
//!
//!     // create the emulator and load the pong game file
//!     let mut emulator = crate::Emulator::with_game_file("games/PONG")?;
//!
//!     // setup keyboard
//!     let device_state = DeviceState::new();
//!     let keyboard = Keyboard(device_state);
//!
//!     while window.is_open() {
//!         // execute the current instruction
//!         if let Some(op) = emulator.cycle() {
//!             // draw the display if it changed
//!             if op.is_display_op() {
//!                 let display = emulator.get_pixels();
//!                 window.update_with_buffer(display, WIDTH, HEIGHT).unwrap();
//!             }
//!         }
//!
//!         // check for key press changes and update the Emulator with which keys are up or down
//!         emulator.handle_key_input(&keyboard);
//!     }
//!     Ok(())
//! }
//!
//! ```

#![warn(clippy::all)]

pub use crate::graphics::DisplayChange;
use crate::graphics::Graphics;
pub use crate::keyboard::Key;
use crate::keyboard::Keyboard;
pub use op::Op;
use rand::{thread_rng, Rng};
use slog::debug;
use slog::Logger;
use sloggers::terminal::{Destination, TerminalLoggerBuilder};
use sloggers::types::Severity;
use sloggers::Build;
use std::fs::File;
use std::io::Error;
use std::io::Read;
use std::sync::Arc;
use std::time;

const MEMORY_SIZE: usize = 4096;
const DISPLAY_REFRESH_SIZE: usize = 256;
const STARTING_MEMORY_BYTE: usize = 512;
const GAME_FILE_MEMORY_SIZE: usize = MEMORY_SIZE - (DISPLAY_REFRESH_SIZE + STARTING_MEMORY_BYTE);
const FONT_DATA_START: usize = 0;
const NUM_BYTES_IN_FONT_CHAR: u8 = 5;
const CYCLES_PER_SECOND: u128 = 60; // 60 Hz
const MS_PER_SECOND: u64 = 1000;

// the number of milliseconds per cycle
pub const CYCLE_INTERVAL_MS: u64 = MS_PER_SECOND / (CYCLES_PER_SECOND as u64);
/// The width of the pixel resolution, currently 640
pub const WIDTH: usize = graphics::WIDTH * graphics::ENLARGE_RATIO;
/// the height of the pixel resolution, currently 320
pub const HEIGHT: usize = graphics::HEIGHT * graphics::ENLARGE_RATIO;

mod graphics;
mod keyboard;
mod op;

#[cfg(test)]
mod lib_test;

/// A trait for interfacing the user's chosen keyboard crate with `chipotle8`'s hexadecimal keyboard
///
/// # Examples
///
/// ```no_run
/// use chipotle8::{AsKeyboard, Key};
/// use device_query::{DeviceQuery, DeviceState, Keycode};
///
/// struct Keyboard(pub DeviceState);
///
/// impl AsKeyboard for Keyboard {
///     fn keys_down(&self) -> Vec<Key> {
///         self.0
///             .get_keys()
///             .iter()
///             .filter_map(|key: &Keycode| match key {
///                 Keycode::Key1 => Some(Key::Key1),
///                 Keycode::Key2 => Some(Key::Key2),
///                 Keycode::Key3 => Some(Key::Key3),
///                 Keycode::Key4 => Some(Key::C),
///                 Keycode::Q    => Some(Key::Key4),
///                 Keycode::W    => Some(Key::Key5),
///                 Keycode::E    => Some(Key::Key6),
///                 Keycode::R    => Some(Key::D),
///                 Keycode::A    => Some(Key::Key7),
///                 Keycode::S    => Some(Key::Key8),
///                 Keycode::D    => Some(Key::Key9),
///                 Keycode::F    => Some(Key::E),
///                 Keycode::Z    => Some(Key::A),
///                 Keycode::X    => Some(Key::Key0),
///                 Keycode::C    => Some(Key::B),
///                 Keycode::V    => Some(Key::F),
///                 _ => None,
///             })
///             .collect()
///     }
/// }
pub trait AsKeyboard {
    /// Returns A Vec of [`Key`](enum.Key.html)s which are currently down on the system keyboard. See
    /// [`Key`](enum.Key.html) for the suggested mapping for a QWERTY keyboard to CHIP-8's hexadecimal
    /// keyboard.
    fn keys_down(&self) -> Vec<Key>;
}

type Address = u16;

// Rust doesn't have a 4-bit numeric type, so we waste 4 bits by storing nibbles in a u8. Oh well!
type Nibble = u8;

/// Stores the registers, memory, timers, and any other data necessary to run the emulator.
///
/// # Examples
///
/// ```no_run
/// # use std::io::Error;
/// # use chipotle8::Emulator;
/// # fn main() -> Result<(), Error> {
/// let mut emulator = Emulator::with_game_file("games/PONG")?;
///
/// // execute the first two instructions of the `PONG` game
/// emulator.cycle();
/// emulator.cycle();
/// #    Ok(())
/// # }
#[allow(non_snake_case)]
pub struct Emulator {
    memory: [u8; 4096], // 4k of RAM

    sp: usize, // stack pointer for the 16-level
    // The stack pointer always points one beyond the top of the stack, i.e. onto
    // unallocated memory
    stack: [usize; 16],  // 16-level stack holding instructions
    I: Address,          // address instruction register
    prev_op: Option<Op>, // the instruction executed last cycle, used to know when to draw
    pc: usize, // program counter, 16 bits are needed but we use usize so we can index with it

    // 16 8-bit registers. VF is used as a flag by several of the opcodes (see @Op)
    v: [u8; 16],

    graphics: Graphics, // 64x32 pixel monochrome screen

    keyboard: Keyboard, // Stores the state of all keyboard input

    delay_timer: u8,                    // 60 Hz timer that can be set and read
    delay_timer_settime: time::Instant, // the instant we last set the delay_timer
    sound_timer: u8,                    // 60 Hz timer that beeps whenever it is nonzero
    sound_timer_settime: time::Instant, // the instant we last set the sound_timer
    logger: Arc<Logger>,
}

impl Emulator {
    /// Creates an Emulator with an optional Logger which will then need to have `initialize`
    /// called on it to load in the game file.
    ///
    /// Note: `Into` trick allows passing `Logger` directly, without the `Some` part.
    /// See http://xion.io/post/code/rust-optional-args.html.
    fn new<L: Into<Option<slog::Logger>>>(logger: L) -> Self {
        let log = logger.into().unwrap_or({
            let mut builder = TerminalLoggerBuilder::new();
            builder.level(Severity::Info);
            builder.destination(Destination::Stdout);
            let built_log = builder.build().unwrap();

            debug!(
                built_log,
                "no logger given, defaulting to slog's terminal logger"
            );
            built_log
        });
        let log = Arc::new(log);

        let mut emulator = Emulator {
            memory: [0; 4096],
            sp: 0,
            stack: [0; 16],
            I: 0,
            prev_op: None,
            pc: 0,
            v: [0; 16],
            graphics: Graphics::new(),
            keyboard: Keyboard::new(log.clone()),
            delay_timer: 0,
            delay_timer_settime: time::Instant::now(),
            sound_timer: 0,
            sound_timer_settime: time::Instant::now(),
            logger: log.clone(),
        };

        // The first 512 bytes of memory were originally used to store the emulator
        // code itself, but since we are writing an emulator and don't need to store
        // emulator code in the emulator's memory those bytes are free for us to
        // put whatever we want there. So we put the font data there.
        let font_set: [[u8; NUM_BYTES_IN_FONT_CHAR as usize]; 16] = [
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
        ];

        let mut mem_idx = FONT_DATA_START;
        for char_arr in font_set.iter() {
            for byte in char_arr.iter() {
                emulator.memory[mem_idx] = *byte;
                mem_idx += 1;
            }
        }

        emulator
    }

    /// Creates an Emulator with a path to a CHIP-8 game file.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io::Error;
    /// # use chipotle8::Emulator;
    /// # fn main() -> Result<(), Error> {
    /// let mut emulator = Emulator::with_game_file("games/PONG")?;
    ///
    /// # Ok(())
    /// # }
    pub fn with_game_file(path_to_game_file: &str) -> Result<Self, Error> {
        Self::with_game_file_and_logger(path_to_game_file, None)
    }

    /// Creates an Emulator with a path to a CHIP-8 game file and an optional logger.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io::Error;
    /// # use chipotle8::Emulator;
    /// # fn main() -> Result<(), Error> {
    /// let mut emulator = Emulator::with_game_file_and_logger("games/PONG", None)?;
    ///
    /// # Ok(())
    /// # }

    pub fn with_game_file_and_logger<L: Into<Option<slog::Logger>>>(
        path_to_game_file: &str,
        logger: L,
    ) -> Result<Self, Error> {
        // Note: `Into` trick allows passing `Logger` directly, without the `Some` part.
        // See http://xion.io/post/code/rust-optional-args.html

        let mut emulator = Emulator::new(logger);
        let res = emulator.initialize(path_to_game_file);
        if res.is_ok() {
            Ok(emulator)
        } else {
            Err(res.err().unwrap())
        }
    }

    /// Update the state of the emulator by running the operation
    fn execute(&mut self, op: Op) {
        debug!(self.logger, "executing op: {:?}", op);
        match op {
            Op::CallRca(_, _, _) => panic!("found CallRca Op {:?}", op), // assume this won't be called
            Op::DispClear => {
                self.graphics.clear();
            }
            Op::Return => {
                self.sp -= 1;
                self.pc = self.stack[self.sp];

                // zero out the stack so we don't leave any instructions hanging around.
                // This is mostly for cleanliness, so we always have exactly the data
                // we care about in our stack.
                self.stack[self.sp] = 0;
            }
            Op::Goto(msb, b, lsb) => {
                let instr = three_nibbles_to_usize(msb, b, lsb);
                self.pc = instr;
            }
            Op::GotoSubRtn(msb, b, lsb) => {
                // save the current instruction for when the subroutine returns;
                self.stack[self.sp] = self.pc + 2;
                self.sp += 1;

                // jump to the subroutine
                self.pc = three_nibbles_to_usize(msb, b, lsb);
            }
            Op::CondVxEq(x, msb, lsb) => {
                let reg = self.v[x as usize];
                let byte = two_nibbles_to_u8(msb, lsb);

                if reg == byte {
                    self.skip_instruction();
                }
            }
            Op::CondVxNe(x, msb, lsb) => {
                let reg = self.v[x as usize];
                let byte = two_nibbles_to_u8(msb, lsb);

                if reg != byte {
                    self.skip_instruction();
                }
            }
            Op::CondVxVyEq(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                if x_reg == y_reg {
                    self.skip_instruction();
                }
            }
            Op::ConstSetVx(x, msb, lsb) => {
                let byte = two_nibbles_to_u8(msb, lsb);
                self.v[x as usize] = byte;
            }
            Op::ConstAddVx(x, msb, lsb) => {
                let byte = two_nibbles_to_u8(msb, lsb);
                let (sum, _) = self.v[x as usize].overflowing_add(byte);
                self.v[x as usize] = sum;
            }
            Op::AssignVyToVx(x, y) => {
                self.v[x as usize] = self.v[y as usize];
            }
            Op::BitOpOr(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];
                self.v[x as usize] = x_reg | y_reg;
            }
            Op::BitOpAnd(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];
                self.v[x as usize] = x_reg & y_reg;
            }
            Op::BitOpXor(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];
                self.v[x as usize] = x_reg ^ y_reg;
            }
            Op::MathVxAddVy(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                // check for carry
                let (sum, did_overflow) = x_reg.overflowing_add(y_reg);
                self.v[x as usize] = sum;

                if did_overflow {
                    self.v[0xf] = 1
                } else {
                    self.v[0xf] = 0;
                }
            }
            Op::MathVxMinusVy(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                // check for borrow
                let (sum, did_borrow) = x_reg.overflowing_sub(y_reg);
                self.v[x as usize] = sum;

                if did_borrow {
                    self.v[0xf] = 0;
                } else {
                    self.v[0xf] = 1;
                }
            }
            Op::BitOpRtShift(x) => {
                let x_reg = self.v[x as usize];

                self.v[0xf] = x_reg & 1; // set VF to the value of the least significant bit
                self.v[x as usize] >>= 1;
            }
            Op::MathVyMinusVx(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                let (sum, did_borrow) = y_reg.overflowing_sub(x_reg);
                self.v[x as usize] = sum;

                if did_borrow {
                    self.v[0xf] = 0;
                } else {
                    self.v[0xf] = 1;
                }
            }
            Op::BitOpLftShift(x) => {
                let x_reg = self.v[x as usize];

                self.v[0xf] = ((x_reg & 0b1000_0000) >> 7) & 1; // set VF to the value of the most sig bit
                self.v[x as usize] <<= 1;
            }
            Op::CondVxVyNe(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                if x_reg != y_reg {
                    self.skip_instruction();
                }
            }
            Op::MemSetI(msb, b, lsb) => {
                let addr = three_nibbles_to_address(msb, b, lsb);
                self.I = addr;
            }
            Op::GotoPlusV0(msb, b, lsb) => {
                let addr = three_nibbles_to_address(msb, b, lsb);
                let v0_reg = self.v[0];

                self.pc = addr as usize + v0_reg as usize;
            }
            Op::Rand(x, msb, lsb) => {
                let random_byte: u8 = thread_rng().gen();
                let eight_bits = two_nibbles_to_u8(msb, lsb);

                self.v[x as usize] = random_byte & eight_bits;
            }
            Op::DispDraw(x, y, height) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                let mut should_set_vf = false;
                for row_delta in 0..height {
                    let byte = self.memory[self.I as usize + row_delta as usize];
                    for col_delta in 0..8 {
                        let is_black = ((byte >> (7 - col_delta)) & 1) == 1;

                        let x_coord = x_reg + col_delta;
                        let y_coord = y_reg + row_delta;

                        let is_collision = self.graphics.xor_set(x_coord, y_coord, is_black);
                        if is_collision {
                            should_set_vf = true;
                        }
                    }
                }

                if should_set_vf {
                    self.v[0xf] = 1;
                } else {
                    self.v[0xf] = 0;
                }
            }
            Op::KeyOpEqVx(x) => {
                let x_reg = self.v[x as usize];
                let is_pressed = self.keyboard.get_key_state(Key::from(x_reg));

                if is_pressed {
                    self.skip_instruction();
                }
            }
            Op::KeyOpNeVx(x) => {
                let x_reg = self.v[x as usize];
                let is_pressed = self.keyboard.get_key_state(Key::from(x_reg));

                if !is_pressed {
                    self.skip_instruction();
                }
            }
            Op::DelayGet(x) => {
                self.v[x as usize] = self.get_delay_state();
            }
            Op::KeyOpGet(x) => self.keyboard.block(x),
            Op::DelaySet(x) => {
                self.delay_timer = self.v[x as usize];
                self.delay_timer_settime = time::Instant::now();
            }
            Op::SoundSet(x) => {
                self.sound_timer = self.v[x as usize];
                self.sound_timer_settime = time::Instant::now();
            }
            Op::MemIPlusEqVx(x) => {
                let reg = self.v[x as usize];

                let (sum, did_overflow) = self.I.overflowing_add(reg as u16);
                self.I = sum;

                // don't forget to set VF if there's overflow
                if did_overflow {
                    self.v[0xF] = 1;
                } else {
                    self.v[0xF] = 0;
                }
            }
            Op::MemISetSprite(x) => {
                let reg = self.v[x as usize];

                // the spec says the register at x must store a single hex digit, but in order
                // to be safe we protect against undefined behavior if values greater than 0xF
                // exist in the register by only using the first nibble of data stored in the
                // register
                let least_nibble = reg & 0b1111;

                let font_idx = (FONT_DATA_START as u8) + (least_nibble * NUM_BYTES_IN_FONT_CHAR);

                self.I = font_idx as Address;
            }
            Op::Bcd(x) => {
                let reg = self.v[x as usize];
                let ascii_offset = 48; // we need to subtract 48 because the ascii byte for
                                       // "0" is 48, for "1" is 49, ... for "9" is 57

                let decimal_repr = format!("{:03}", reg);
                let addr_usize = self.I as usize;

                let hundreds_place = decimal_repr.get(0..1).unwrap().as_bytes()[0] - ascii_offset;
                self.memory[addr_usize + 0 as usize] = hundreds_place;

                let tens_place = decimal_repr.get(1..2).unwrap().as_bytes()[0] - ascii_offset;
                self.memory[addr_usize + 1 as usize] = tens_place;

                let ones_place = decimal_repr.get(2..3).unwrap().as_bytes()[0] - ascii_offset;
                self.memory[addr_usize + 2 as usize] = ones_place;
            }
            Op::RegDump(x) => {
                for i in 0..=x {
                    // the spec says the range in inclusive, so we do =x
                    self.memory[self.I as usize + i as usize] = self.v[i as usize];
                }
            }
            Op::RegLoad(x) => {
                for i in 0..=x {
                    // the spec says the range in inclusive, so we do =x
                    self.v[i as usize] = self.memory[self.I as usize + i as usize];
                }
            }
        }
    }

    /// Return the value of the delay timer, accounting for any timer that has passed since
    /// the timer was last set.
    fn get_delay_state(&self) -> u8 {
        // we need to do this more complicated calculation because if we did the simpler
        // implementation (just a `return self.delay_timer`) then there's an edge case
        // where we would return an incorrect value for the timer. This edge case happens
        // in the possible (though extremely unlikely since it takes our Emulator ~2ms to
        // execute its most lengthy instruction `DispDraw`) case that more than CYCLE_INTERVAL_MS
        // number of milliseconds have passed since we last called `.cycle` where we decrement
        // the `delay_timer`.
        //
        // Since the Emulator is supposed to guarantee that `delay_timer` decrements every
        // CYCLE_INTERVAL_MS ms, yet CYCLE_INTERVAL_MS ms have passed without calling `.cycle`
        // and decrementing the `delay_timer`, we'll return a higher number for `delay_timer`
        // than we should.
        //
        // To remedy this, every time `get_delay_state` gets called we need to account
        // for the real time that has passed since we last decremented the `delay_timer`
        // by calculating how many CYCLE_INTERVAL_MS number of milliseconds have passed.
        let ms_since_last_delay_set =
            (time::Instant::now() - self.delay_timer_settime).as_millis() as u64;
        let num_decrement = (ms_since_last_delay_set / CYCLE_INTERVAL_MS) as u8;

        self.delay_timer.saturating_sub(num_decrement)
    }

    /// Return the decoded Op at the current program counter. Does not increment the program counter.
    fn get_instr_at_pc(&self) -> Op {
        let msb = self.memory[self.pc];
        let lsb = self.memory[self.pc + 1];
        debug!(
            self.logger,
            "get_instr_at_pc: (msb: {:X?}, lsb: {:X?})", msb, lsb
        );
        Op::from(two_u8s_to_address(msb, lsb))
    }

    /// Update the Emulator keyboard using the state of the system keyboard.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io::Error;
    /// # use chipotle8::{Emulator, AsKeyboard, Key};
    /// use device_query::{DeviceQuery, DeviceState, Keycode};
    ///
    /// struct Keyboard(pub DeviceState);
    ///
    /// impl AsKeyboard for Keyboard {
    ///     fn keys_down(&self) -> Vec<Key> {
    ///         // TODO: if this weren't an example we'd actually implement this!
    ///         vec![Key::Key1]
    ///     }
    /// }
    ///
    /// fn main() -> Result<(), Error> {
    ///     let mut emulator = Emulator::with_game_file("games/PONG")?;
    ///
    ///     let keyboard = Keyboard(DeviceState::new());
    ///
    ///     emulator.handle_key_input(&keyboard);
    ///     Ok(())
    /// }
    pub fn handle_key_input(&mut self, keyboard: &impl AsKeyboard) {
        let keys_down = keyboard.keys_down();

        self.keyboard.update_keyboard(&keys_down);

        let (reg_idx_option, key_option) = self.keyboard.handle_fx0a_state(&keys_down);
        if let (Some(reg_idx), Some(key)) = (reg_idx_option, key_option) {
            self.v[reg_idx] = key;
        }
    }

    /// Skip executing the next instruction by incrementing the program counter 2 bytes. Used
    /// by some conditional opcodes.
    #[inline]
    fn skip_instruction(&mut self) {
        self.pc += 2;
    }

    /// Returns the display pixels with a resolution of 640x320.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::Error;
    /// # use chipotle8::Emulator;
    /// # fn main() -> Result<(), Error> {
    /// let mut emulator = Emulator::with_game_file("games/PONG")?;
    ///
    /// // this will return a slice 640x320 of all 0's,
    /// let display = emulator.get_pixels();
    /// #    Ok(())
    /// # }
    pub fn get_pixels(&mut self) -> &[u32] {
        self.graphics.get_pixels()
    }

    /// step forward one cycle in the emulator. Returns Some(op) if an opcode was executed.
    /// or None if we're in the blocking state waiting for a keyboard press.
    ///
    /// A cycle consists of:
    /// 1. read the instruction at the program counter
    /// 2. decode it
    /// 3. execute it
    /// 4. possibly advance the program counter
    /// 5. decrement the sound and delay timers
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::Error;
    /// # use chipotle8::Emulator;
    /// # fn main() -> Result<(), Error> {
    /// let mut emulator = Emulator::with_game_file("games/PONG")?;
    ///
    /// // execute the first two instructions of the `PONG` game
    /// emulator.cycle();
    /// emulator.cycle();
    /// #    Ok(())
    /// # }
    pub fn cycle(&mut self) -> Option<Op> {
        let op = self.get_instr_at_pc();
        if !self.keyboard.is_blocking() {
            debug!(
                self.logger,
                "before: (sp: {}, stack: {:?} I: {}, pc: {}, v: {:?}, delay: {}, sound: {}",
                self.sp,
                self.stack.to_vec(),
                self.I,
                self.pc,
                self.v.to_vec(),
                self.delay_timer,
                self.sound_timer
            );

            self.execute(op);

            // advance to the next instruction
            self.prev_op = Some(op);

            if Self::should_advance_pc(op) {
                self.pc += 2;
            }

            self.decrement_timers_after_cycle();

            debug!(
                self.logger,
                "after: (sp: {}, stack: {:?} I: {}, pc: {}, v: {:?}, delay: {}, sound: {}",
                self.sp,
                self.stack.to_vec(),
                self.I,
                self.pc,
                self.v.to_vec(),
                self.delay_timer,
                self.sound_timer
            );

            return Some(op);
        }
        None
    }

    /// Return true if this operation is one of the many Ops for which we should
    /// increment the program counter. All Ops except those which cause the Emulator
    /// to jump to an instruction in memory (e.g. Return, Goto, GotoSubRtn and GotoPlusV0) should
    /// advance the program counter
    fn should_advance_pc(op: Op) -> bool {
        match op {
            Op::Return | Op::Goto(_, _, _) | Op::GotoSubRtn(_, _, _) | Op::GotoPlusV0(_, _, _) => {
                false
            }
            _ => true,
        }
    }

    /// Read in a game file and initialize the necessary registers.
    ///
    /// Returns an error if we fail to open the game file
    fn initialize(&mut self, path: &str) -> Result<(), Error> {
        let game_file = File::open(path).unwrap();

        self.read_game_file(game_file)?;
        self.sp = 0;
        self.pc = STARTING_MEMORY_BYTE;

        debug!(self.logger, "initialized emulator with game file: {}", path);

        Ok(())
    }

    /// Read in a CHIP 8 game file and load it into memory starting at byte index 512
    fn read_game_file(&mut self, file: File) -> Result<(), Error> {
        let buf = read_file_to_vec(file)?;

        let err_msg = "file is too large".to_string();
        assert!(buf.len() < GAME_FILE_MEMORY_SIZE, err_msg);

        let game_file_range = STARTING_MEMORY_BYTE..(STARTING_MEMORY_BYTE + buf.len());
        self.memory[game_file_range].copy_from_slice(&buf);

        Ok(())
    }

    /// Decrement the delay and sound timers until they reach 0, at which point stop subtracting.
    /// We only decrement if sufficient time has passed. Since we want to run at 60 Hz, we'll only
    /// update if it's been at least 1000 / 60 == 16.66667 milliseconds since the last update
    fn decrement_timers_after_cycle(&mut self) {
        self.decrement_delay_timer_after_cycle();
        self.decrement_sound_timer_after_cycle();
    }

    /// Decrement the delay timer and update the delay timer's set time, but only do so if more
    /// than 16 milliseconds (the duration of a single cycle) have passed
    fn decrement_delay_timer_after_cycle(&mut self) {
        let ms_since_last_delay_set = self.delay_timer_settime.elapsed().as_millis() as u64;
        let num_decrements = (ms_since_last_delay_set / CYCLE_INTERVAL_MS) as u8;

        if num_decrements > 0 {
            self.delay_timer = self.delay_timer.saturating_sub(num_decrements);
            self.delay_timer_settime = time::Instant::now();
        }
    }

    /// Decrement the sound timer and update the sound timer's set time, but only do so if more
    /// than 16 milliseconds (the duration of a single cycle) have passed
    fn decrement_sound_timer_after_cycle(&mut self) {
        let ms_since_last_sound_set = self.sound_timer_settime.elapsed().as_millis() as u64;
        let num_decrements = (ms_since_last_sound_set / CYCLE_INTERVAL_MS) as u8;

        if num_decrements > 0 {
            self.sound_timer = self.sound_timer.saturating_sub(num_decrements);
            self.sound_timer_settime = time::Instant::now();
        }
    }

    /// Flushes the recent changes to the emulator's display and returns them
    ///
    /// # Examples
    /// ```no_run
    /// # use std::io::Error;
    /// # use chipotle8::{Emulator, DisplayChange};
    /// # fn main() -> Result<(), Error> {
    /// let mut emulator = Emulator::with_game_file("games/PONG")?;
    ///
    /// let changes: Vec<DisplayChange> = emulator.flush_changes();
    /// // update your app's own display with these recent changes to the emulator's display
    /// // ...
    /// #    Ok(())
    /// # }
    #[allow(dead_code)]
    pub fn flush_changes(&mut self) -> Vec<DisplayChange> {
        self.graphics.flush_changes()
    }
}

/// Read in a file located at path as a Vec<u8>
fn read_file_to_vec(mut file: File) -> Result<Vec<u8>, Error> {
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;

    Ok(buf)
}

fn two_nibbles_to_u8(msb: Nibble, lsb: Nibble) -> u8 {
    assert!(msb <= 0xF && lsb <= 0xF, "msb: {}, lsb: {}", msb, lsb);
    msb << 4 | lsb
}

/// Take the msb, middle byte and lsb Nibbles and merge them into a single Address. Used
/// to convert three 4-bit pieces of data in memory into a single 16-bit
/// instruction.
fn three_nibbles_to_address(msb: Nibble, b: Nibble, lsb: Nibble) -> Address {
    let mask = 0xF;
    ((msb as Address & mask) << 8) | ((b as Address & mask) << 4) | (lsb as Address & mask)
}

fn three_nibbles_to_usize(msb: Nibble, b: Nibble, lsb: Nibble) -> usize {
    three_nibbles_to_address(msb, b, lsb) as usize
}

fn two_u8s_to_address(msb: u8, lsb: u8) -> Address {
    ((msb as Address) << 8) | (lsb as Address)
}
