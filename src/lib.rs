//! An implementation of the CHIP 8 emulator in Rust with the intention to be run
//! as WebAssembly
use crate::graphics::Graphics;
use minifb::{Key, KeyRepeat, Window};
use op::Op;
use rand::{thread_rng, Rng};
use std::fs::File;
use std::io::Error;
use std::io::Read;

const MEMORY_SIZE: usize = 4096;
const DISPLAY_REFRESH_SIZE: usize = 256;
const CALL_STACK_SIZE: usize = 96;
const STARTING_MEMORY_BYTE: usize = 512;
const GAME_FILE_MEMORY_SIZE: usize =
    MEMORY_SIZE - (DISPLAY_REFRESH_SIZE + CALL_STACK_SIZE + STARTING_MEMORY_BYTE);
const STACK_START: usize = MEMORY_SIZE - DISPLAY_REFRESH_SIZE + CALL_STACK_SIZE;
const FONT_DATA_START: usize = 0;
const NUM_BYTES_IN_FONT_CHAR: u8 = 5;
mod graphics;
mod op;

// # Interpreter
// * 4096 (0x1000) bytes of memory
// * interpretor exists in the first 512 (0x200) bytes
// * uppermost 256 (0xF00-0xFFF) bytes are used for display refresh
// * 96 (0xEB0-0xEFF) for call stack, internal use and other variables
// * 16 8-bit registers: V0 - VF
// * VF if used is the carry flag in addition operations, "no borrow" flag in subtraction, in draw
// operation the VF flag is set to denote pixel collision
// * the address register I is 16 bits wide
// the stack is only used to store return addresses when subroutines are called

// # Timers
// * two timers running at 60 hertz
//  - delay timer is used for events, it can be set and read
//  - sound timer beeps when its value is nonzero

// # Input
// there is a 16 symbol hex keyboard with values 0 - F. There are 3 opcode that deal with handling input
//  - one skips an instruction if a specific key is pressed
//  - one skips an instruction if a specific key is NOT pressed
//  - waits for a key press and stores it in a register once it detects it

// # Graphics
// 64x32 pixels

/// Stores data needed to handle instruction FX0A
#[derive(Default, Debug, PartialEq,)]
struct FX0AMetadata {
    should_block_on_keypress: bool, // set to true if CPU is waiting on a keypress
    last_key_pressed: Option<Key>,  // once a key is pressed store it here
    register: Option<u8>,           // the register to store the pressed key in
}

pub struct Interpreter {
    pub memory: [u8; 4096], // 4k of RAM

    sp: usize, // stack pointer, 16 bits are needed but we use usize so we can index with it.
    // The stack pointer always points on beyond the top of the stack, i.e. onto
    // unallocated memory
    pub addr: u16, // address instruction register
    pc: usize,     // program counter, 16 bits are needed but we use usize so we can index with it

    // 16 8-bit registers. VF is used as a flag by several of the opcodes (see @Op)
    v: [u8; 16],

    graphics: Graphics, // 64x32 pixel monochrome screen

    delay_timer: u8,             // 60 Hz timer that can be set and read
    sound_timer: u8,             // 60 Hz timer that beeps whenever it is nonzero
    fx0a_metadata: FX0AMetadata, // used to store state for instruction FX0A
}

impl Interpreter {
    pub fn new() -> Self {
        let mut interpreter = Interpreter {
            memory: [0; 4096],
            sp: 0,
            addr: 0,
            pc: 0,
            v: [0; 16],
            graphics: Graphics::new(),
            delay_timer: 0,
            sound_timer: 0,
            fx0a_metadata: FX0AMetadata {
                should_block_on_keypress: false,
                last_key_pressed: None,
                register: None,
            },
        };

        // load font data into memory
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
                interpreter.memory[mem_idx] = *byte;
                mem_idx += 1;
            }
        }

        interpreter
    }

    /// Update the state of the interpreter by running the operation
    fn execute(&mut self, op: Op) {
        match op {
            Op::CallRca(_, _, _) => panic!("found CallRca Op {:?}", op), // assume this won't be called
            Op::DispClear => {
                for i in 0..self.graphics.len() {
                    self.graphics.set(i, false);
                }
            }
            Op::Return => {
                self.sp = self.sp - 1;
                let lsb = self.memory[self.sp];
                self.memory[self.sp] = 0; // zero out stack

                self.sp = self.sp - 1;
                let msb = self.memory[self.sp];
                self.memory[self.sp] = 0; // zero out stack

                let instr = two_nibbles_to_usize(msb, lsb);

                self.pc = instr;
            }
            Op::Goto(msb, b, lsb) => {
                let instr = three_nibbles_to_usize(msb, b, lsb);
                self.pc = instr;
            }
            Op::GotoSubRtn(msb, b, lsb) => {
                // save the current instruction for when the subroutine returns;
                let (pc_msb, pc_lsb) = usize_to_two_nibbles(self.pc);
                self.memory[self.sp] = pc_msb;
                self.sp = self.sp + 1;
                self.memory[self.sp] = pc_lsb;
                self.sp = self.sp + 1;

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
                self.v[x as usize] = self.v[x as usize] + byte;
            }
            Op::AssignVyToVx(x, y) => {
                let y_reg = self.v[y as usize];
                self.v[x as usize] = y_reg;
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
                let (val, did_overflow) = x_reg.overflowing_sub(y_reg);
                self.v[x as usize] = val;

                if did_overflow {
                    self.v[0xf] = 0;
                } else {
                    self.v[0xf] = 1;
                }
            }
            Op::BitOpRtShift(x) => {
                let x_reg = self.v[x as usize];

                self.v[0xf] = x_reg & 0b1; // set VF to the value of the lsb
                self.v[x as usize] = self.v[x as usize] >> 1;
            }
            Op::MathVyMinusVx(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                let (val, did_overflow) = y_reg.overflowing_sub(x_reg);
                self.v[x as usize] = val;

                if did_overflow {
                    self.v[0xf] = 0;
                } else {
                    self.v[0xf] = 1;
                }
            }
            Op::BitOpLftShift(x) => {
                let x_reg = self.v[x as usize];

                self.v[0xf] = (x_reg & 0b10000000) >> 7; // set VF to the value of the msb
                self.v[x as usize] = self.v[x as usize] << 1;
            }
            Op::CondVxVyNe(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                if x_reg != y_reg {
                    self.skip_instruction();
                }
            }
            Op::MemSetI(msb, b, lsb) => {
                let addr = three_nibbles_to_u16(msb, b, lsb);
                self.addr = addr;
            }
            Op::GotoPlusV0(msb, b, lsb) => {
                let addr = three_nibbles_to_u16(msb, b, lsb);
                let v0 = self.v[0];

                self.pc = addr as usize + v0 as usize;
            }
            Op::Rand(x, msb, lsb) => {
                let random_byte: u8 = thread_rng().gen();

                let reg_val = self.v[x as usize];
                let eight_bits = two_nibbles_to_u8(msb, lsb);

                let new_reg_val = reg_val & eight_bits;

                self.v[x as usize] = new_reg_val;
            }
            Op::DispDraw(x, y, height) => {
                let x_coord = self.v[x as usize];
                let y_coord = self.v[y as usize];

                let gfx_start_idx = Graphics::get_graphics_idx(x, y);

                let mut should_set_vf = false;
                for i in 0 as usize..height as usize {
                    let byte = self.memory[self.addr as usize + i];
                    let row = i * 8 as usize;
                    for j in 0 as usize..8 as usize {
                        let bit = ((byte >> (7 - j)) & 1) == 1;

                        let gfx_offset = row + j;

                        let is_different = should_set_vf != true
                            && self.graphics[gfx_start_idx + gfx_offset] != bit;
                        if is_different {
                            should_set_vf = true;
                        }
                        self.graphics.set(gfx_start_idx + gfx_offset, bit);
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
                let key_state = self.graphics.get_key_state(x_reg as usize);

                if key_state {
                    self.pc = self.pc + 2;
                }
            }
            Op::KeyOpNeVx(x) => {
                let x_reg = self.v[x as usize];
                let key_state = self.graphics.get_key_state(x_reg as usize);

                if !key_state {
                    self.pc = self.pc + 2;
                }
            }
            Op::DelayGet(x) => self.v[x as usize] = self.delay_timer,
            Op::KeyOpGet(x) => self.go_to_blocking_state(x),
            Op::DelaySet(x) => self.delay_timer = self.v[x as usize],
            Op::SoundSet(x) => self.sound_timer = self.v[x as usize],
            Op::MemIPlusEqVx(x) => {
                let reg = self.v[x as usize];

                let (sum, did_overflow) = self.addr.overflowing_add(reg as u16);
                self.addr = sum;

                // don't forget to set VF if there's overflow
                if did_overflow {
                    self.v[0xF] = 1;
                } else {
                    self.v[0xF] = 0;
                }
            },
            Op::MemISetSprite(x) => {
                let reg = self.v[x as usize];

                // the spec says the register at x must store a single hex digit, but in order
                // to be safe we protect against undefined behavior if values greater than 0xF
                // exist in the register by only using the first nible of data stored in the
                // register
                let least_nibble = reg & 0b1111;

                let font_idx = (FONT_DATA_START as u8) + (least_nibble * NUM_BYTES_IN_FONT_CHAR);

                self.addr = font_idx as u16;
            }

            _ => unimplemented!(),
        }
    }

    /// Called when the KeyOpGet Op is executed. The interpreter will transition out of
    /// the blocking state once a keypress gets detected
    fn go_to_blocking_state(&mut self, reg: u8) {
        self.fx0a_metadata.should_block_on_keypress = true;
        self.fx0a_metadata.register = Some(reg);
    }

    /// Handle and reset the Interpreter from a key press. Only gets called
    /// when the Interpreter is blocking as a result of a prior FX0A instruction
    fn return_from_blocking_state(&mut self, key_idx: u8) {
        let reg_idx = self
            .fx0a_metadata
            .register
            .expect("invalid FXOA metadata state");
        self.v[reg_idx as usize] = key_idx;
        self.fx0a_metadata = FX0AMetadata::default();
    }

    /// Return the decoded Op at the current program counter. Does not increment the program counter
    fn get_instr_at_pc(&self) -> Op {
        let msb = self.memory[self.pc];
        let lsb = self.memory[self.pc + 1];
        Op::from(two_u8s_to_u16(msb, lsb))
    }

    /// Given a Window with access to the system keyboard state, update the Interpreter's
    /// keyboard input state
    pub fn handle_input(&mut self, window: &Window) {
        self.handle_input_inner(window.get_keys_pressed(KeyRepeat::Yes));
    }

    /// Update the Interpreter state from possible key presses. Should only be called within
    /// handle_input, which exists so when we're testing handle_input_inner we do not need
    /// to create a Window struct, and only have to deal with Option<Vec<Key>>
    fn handle_input_inner(&mut self, keys_pressed: Option<Vec<Key>>) {
        keys_pressed.as_ref().map(|keys| {
            let key_idxs: Vec<usize> = keys.iter()
                .map(Graphics::map_key)
                .filter(Option::is_some)
                .map(Option::unwrap)
                .collect();

            self.graphics.update_keyboard_with_vec(&key_idxs);

            self.handle_fx0a_state(keys);
        });
    }

    /// Checks if we're in a blocking state, and if a valid key has been pressed
    /// transitions out of the blocking state
    fn handle_fx0a_state(&mut self, keys: &Vec<Key>) {
        // check if the FX0A instruction has us in a blocking state and if we can now unblock
        if self.fx0a_metadata.should_block_on_keypress {
            let key_inputs: Vec<usize> = keys.iter()
                .map(Graphics::map_key)
                .filter(Option::is_some)
                .map(Option::unwrap)
                .collect();

            // we choose of the first key because we have to choose SOME key, so why not the first?
            key_inputs.get(0).map(|k| {
                self.return_from_blocking_state(*k as u8);
            });
        }
    }

    /// Skip executing the next instruction by incrementing the program counter 2 bytes. Used
    /// by some conditional opcodes
    fn skip_instruction(&mut self) {
        self.pc = self.pc + 2;
    }

    /// Draw the 64x32 pixel map
    fn draw(&mut self) {}

    /// Check for any changes to keyboard input (keys pressed or unpressed)
    fn update_key_inputs(&mut self) {}

    /// step forward one cycle in the interpreter. Read the instruction
    /// at the program counter, decode it, execute it, and update any internal state
    pub fn cycle(&mut self) {
        if !self.fx0a_metadata.should_block_on_keypress {
            let op = self.get_instr_at_pc();
            self.execute(op);

            if Interpreter::is_display_op(op) {
                self.draw();
            }

            // advance to the next instruction
            self.pc = self.pc + 2;
        }
    }

    /// Return true if this op is related to the display. Later we use
    /// this to decide if we should devote cycles to redrawing the graphics buffer
    fn is_display_op(op: Op) -> bool {
        match op {
            Op::DispDraw(_, _, _) | Op::DispClear => true,
            _ => false,
        }
    }

    /// Read in a game file and initialize the necessary registers.
    ///
    /// Returns an error if we fail to open the game file
    pub fn initialize(&mut self, file: File) -> Result<(), Error> {
        self.read_game_file(file)?;
        self.sp = STACK_START;
        self.pc = STARTING_MEMORY_BYTE;

        Ok(())
    }

    /// Read in a CHIP 8 game file and load it into memory starting at byte index 512
    fn read_game_file(&mut self, file: File) -> Result<(), Error> {
        let buf = read_file_to_vec(file)?;

        let err_msg = format!("file is too large");
        assert!(buf.len() < GAME_FILE_MEMORY_SIZE, err_msg);

        let game_file_range = STARTING_MEMORY_BYTE..(STARTING_MEMORY_BYTE + buf.len());
        self.memory[game_file_range].copy_from_slice(&buf);

        Ok(())
    }
}

/// Read in a file located at path as a Vec<u8>
fn read_file_to_vec(mut file: File) -> Result<Vec<u8>, Error> {
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;

    Ok(buf)
}

/// Take the msb and lsb u8s and merge them into a single 16. Used
/// to convert two 8-bit pieces of data in memory into a single 16-bit
/// instruction.
fn two_nibbles_to_u16(msb: u8, lsb: u8) -> u16 {
    two_nibbles_to_u8(msb, lsb) as u16
}

fn two_nibbles_to_u8(msb: u8, lsb: u8) -> u8 {
    assert!(msb <= 0xF && lsb <= 0xF, "msb: {}, lsb: {}", msb, lsb);
    msb << 4 | lsb
}

fn two_nibbles_to_usize(msb: u8, lsb: u8) -> usize {
    two_nibbles_to_u8(msb, lsb) as usize
}

fn usize_to_two_nibbles(u: usize) -> (u8, u8) {
    let mask: usize = 0xF;

    let msb = ((u >> 4) & mask) as u8;
    let lsb = (u & mask) as u8;

    (msb, lsb)
}

/// Take the msb, middle byte and lsb u8s and merge them into a single 16. Used
/// to convert three 4-bit pieces of data in memory into a single 16-bit
/// instruction.
fn three_nibbles_to_u16(msb: u8, b: u8, lsb: u8) -> u16 {
    ((msb as u16) << 8) | ((b as u16) << 4) | (lsb as u16)
}

fn three_nibbles_to_usize(msb: u8, b: u8, lsb: u8) -> usize {
    three_nibbles_to_u16(msb, b, lsb) as usize
}

fn usize_to_three_nibbles(u: usize) -> (u8, u8, u8) {
    let mask: usize = 0xF;

    let msb = ((u >> 8) & mask) as u8;
    let b = ((u >> 4) & mask) as u8;
    let lsb = (u & mask) as u8;

    assert!(
        msb <= 0xF && b <= 0xF && lsb <= 0xF,
        "msb: {}, b: {}, lsb: {}",
        msb,
        b,
        lsb
    );

    (msb, b, lsb)
}

fn two_u8s_to_u16(msb: u8, lsb: u8) -> u16 {
    ((msb as u16) << 8) | (lsb as u16)
}

#[cfg(test)]
mod interpreter_tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    mod execute {
        use super::*;
        use minifb::Key;

        #[test]
        fn display_clear_op() {
            let mut interpreter = Interpreter::new();
            assert_eq!(interpreter.v[0xf], 0);

            let instr = 0x00E0;
            let op = Op::from(instr);

            // set some graphics bits to true so we can later see the set to false;
            interpreter.graphics.set(0, true);
            interpreter
                .graphics
                .set(interpreter.graphics.len() - 1, true);

            interpreter.execute(op);

            for i in 0..interpreter.graphics.len() {
                assert_eq!(interpreter.graphics[i], false);
            }
        }

        #[test]
        fn return_op() {
            let mut interpreter = Interpreter::new();

            assert_eq!(interpreter.sp, 0);
            assert_eq!(interpreter.pc, 0);

            // fake call a function so we set a return address on the stack. We use arbitrary return
            // address 0x01AA
            let arb_addr = 0x001A;
            let (msb, lsb) = usize_to_two_nibbles(arb_addr);
            interpreter.memory[interpreter.sp] = msb;
            interpreter.sp = interpreter.sp + 1;

            interpreter.memory[interpreter.sp] = lsb;
            interpreter.sp = interpreter.sp + 1;

            interpreter.pc = 0x090B; // arbitrary position for the program counter

            let instr = 0x00EE;
            let op = Op::from(instr);
            interpreter.execute(op);

            assert_eq!(interpreter.pc, arb_addr);
            assert_eq!(interpreter.sp, 0);

            assert_eq!(interpreter.memory[interpreter.sp], 0);
            assert_eq!(interpreter.memory[interpreter.sp + 1], 0);
        }

        #[test]
        fn goto_op() {
            let mut interpreter = Interpreter::new();
            assert_eq!(interpreter.pc, 0);

            let instr: usize = 0x1FAB;
            let (msb, b, lsb) = usize_to_three_nibbles(instr);
            let addr = three_nibbles_to_usize(msb, b, lsb);
            let op = Op::from(instr as u16);
            interpreter.execute(op);

            assert_eq!(interpreter.pc, addr);
        }

        #[test]
        fn call_subroutine_op() {
            let mut interpreter = Interpreter::new();
            assert_eq!(interpreter.pc, 0);
            assert_eq!(interpreter.sp, 0);

            // fake the interpreter in the middle of execution by setting pc to arbitrary address
            let arb_addr = 0xFAB;
            interpreter.pc = arb_addr;

            let instr = 0x2DEF;
            let (msb, b, lsb) = usize_to_three_nibbles(instr);
            let addr = three_nibbles_to_usize(msb, b, lsb);
            interpreter.execute(Op::from(instr as u16));

            assert_eq!(interpreter.pc, addr);
            assert_eq!(interpreter.sp, 2);
            let (msb, lsb) = usize_to_two_nibbles(arb_addr);
            assert_eq!(interpreter.memory[interpreter.sp - 1], lsb);
            assert_eq!(interpreter.memory[interpreter.sp - 2], msb);
        }

        #[test]
        fn cond_vx_eq_op_false() {
            let mut interpreter = Interpreter::new();

            // setup test

            let instr = 0x3AAB;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            interpreter.pc = STARTING_MEMORY_BYTE;

            assert_eq!(interpreter.v[x as usize], 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, STARTING_MEMORY_BYTE);
        }

        #[test]
        fn cond_vx_eq_op_true() {
            let mut interpreter = Interpreter::new();

            // setup test

            let instr = 0x3A00;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            interpreter.pc = STARTING_MEMORY_BYTE;

            assert_eq!(interpreter.v[x as usize], 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, STARTING_MEMORY_BYTE + 2);
        }

        #[test]
        fn cond_vx_ne_op_false() {
            let mut interpreter = Interpreter::new();

            // setup test

            let instr = 0x4A00;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            interpreter.pc = STARTING_MEMORY_BYTE;

            assert_eq!(interpreter.v[x as usize], 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, STARTING_MEMORY_BYTE);
        }

        #[test]
        fn cond_vx_ne_op_true() {
            let mut interpreter = Interpreter::new();

            // setup test

            let instr = 0x4AFB;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            interpreter.pc = STARTING_MEMORY_BYTE;

            assert_eq!(interpreter.v[x as usize], 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, STARTING_MEMORY_BYTE + 2);
        }

        #[test]
        fn cond_vx_vy_eq_op_false() {
            let mut interpreter = Interpreter::new();

            // setup test

            let nibbles = 0x5AF0; // arbitrary 3 nibbles
            let op = Op::from(nibbles as u16);
            let (x, y, _) = usize_to_three_nibbles(nibbles);
            let x_usize = x as usize;
            let y_usize = y as usize;
            interpreter.pc = STARTING_MEMORY_BYTE;
            let arb_byte = 0xAB;

            interpreter.v[x_usize] = arb_byte;
            interpreter.v[y_usize] = 0;

            interpreter.execute(op);

            assert_eq!(interpreter.pc, STARTING_MEMORY_BYTE);
        }

        #[test]
        fn cond_vx_vy_eq_op_true() {
            let mut interpreter = Interpreter::new();

            // setup test

            let nibbles = 0x5AF0; // arbitrary 3 nibbles
            let op = Op::from(nibbles as u16);
            let (x, y, _) = usize_to_three_nibbles(nibbles);
            interpreter.pc = STARTING_MEMORY_BYTE;
            let arb_byte = 0xAB;

            interpreter.v[x as usize] = arb_byte;
            interpreter.v[y as usize] = arb_byte;

            interpreter.execute(op);

            assert_eq!(interpreter.pc, STARTING_MEMORY_BYTE + 2);
        }

        #[test]
        fn const_vx_set_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x6AFB;
            let op = Op::from(instr as u16);
            let (x, msb, lsb) = usize_to_three_nibbles(instr);
            let x_usize = x as usize;

            assert_eq!(interpreter.v[x_usize], 0);

            interpreter.execute(op);

            let eight_bits = two_nibbles_to_u8(msb, lsb);
            assert_eq!(interpreter.v[x_usize], eight_bits);
        }

        #[test]
        fn const_vx_plus_set_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x7AFB;
            let op = Op::from(instr as u16);
            let (x, msb, lsb) = usize_to_three_nibbles(instr);
            let x_usize = x as usize;

            let offset = 1; // set vA to something other than 0 so we can make sure 0xFB gets added
            interpreter.v[x_usize] = offset;
            assert_eq!(interpreter.v[x_usize], offset);

            interpreter.execute(op);

            let eight_bits = two_nibbles_to_u8(msb, lsb);
            assert_eq!(interpreter.v[x_usize], eight_bits + offset);
        }

        #[test]
        fn assign_vx_vy_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB0;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);
            let x_usize = x as usize;
            let y_usize = y as usize;

            interpreter.v[x_usize] = 42;
            interpreter.v[y_usize] = 24;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x_usize], 24);
            assert_eq!(interpreter.v[x_usize], interpreter.v[y_usize])
        }

        #[test]
        fn bit_or_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB1;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);
            let x_usize = x as usize;
            let y_usize = y as usize;

            interpreter.v[x_usize] = 0b11001100;
            interpreter.v[y_usize] = 0b00110011;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x_usize], 0b11111111);
            assert_eq!(interpreter.v[y_usize], 0b00110011)
        }

        #[test]
        fn bit_and_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB2;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 0b11001100;
            interpreter.v[y as usize] = 0b00110011;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 0b00000000);
            assert_eq!(interpreter.v[y as usize], 0b00110011)
        }

        #[test]
        fn bit_xor_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB3;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 0b11001101;
            interpreter.v[y as usize] = 0b00110011;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 0b11111110);
            assert_eq!(interpreter.v[y as usize], 0b00110011)
        }

        #[test]
        fn math_vx_add_vy_no_carry() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB4;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 3;
            interpreter.v[y as usize] = 4;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 3 + 4);
            assert_eq!(interpreter.v[y as usize], 4);
            assert_eq!(interpreter.v[0xf], 0);
        }

        #[test]
        fn math_vx_add_vy_with_carry() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB4;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 255;
            interpreter.v[y as usize] = 3;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 2);
            assert_eq!(interpreter.v[y as usize], 3);
            assert_eq!(interpreter.v[0xf], 1);
        }

        #[test]
        fn math_vx_minus_vy_no_borrow() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB5;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 4;
            interpreter.v[y as usize] = 3;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 1);
            assert_eq!(interpreter.v[y as usize], 3);
            assert_eq!(interpreter.v[0xf], 1);
        }

        #[test]
        fn math_vx_minus_vy_with_borrow() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB5;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 1;
            interpreter.v[y as usize] = 2;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 255);
            assert_eq!(interpreter.v[y as usize], 2);
            assert_eq!(interpreter.v[0xf], 0);
        }

        #[test]
        fn bit_right_shift_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB6;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 0b10000010;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 0b01000001);
            assert_eq!(interpreter.v[0xf], 0);

            let op2 = Op::from(instr as u16);
            interpreter.execute(op2);

            assert_eq!(interpreter.v[x as usize], 0b00100000);
            assert_eq!(interpreter.v[0xf], 1);
        }

        #[test]
        fn bit_left_shift_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8ABE;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 0b10000010;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 0b00000100);
            assert_eq!(interpreter.v[0xf], 1);

            let op2 = Op::from(instr as u16);
            interpreter.execute(op2);

            assert_eq!(interpreter.v[x as usize], 0b00001000);
            assert_eq!(interpreter.v[0xf], 0);
        }

        #[test]
        fn math_vx_eq_vy_minus_vx_no_borrow() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB7;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 3;
            interpreter.v[y as usize] = 4;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 1);
            assert_eq!(interpreter.v[y as usize], 4);
            assert_eq!(interpreter.v[0xf], 1);
        }

        #[test]
        fn math_vx_eq_vy_minus_vx_borrow() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x8AB7;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 2;
            interpreter.v[y as usize] = 1;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 255);
            assert_eq!(interpreter.v[y as usize], 1);
            assert_eq!(interpreter.v[0xf], 0);
        }

        #[test]
        fn cond_vx_ne_vy_op_not_equal() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x9AB0;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 2;
            interpreter.v[y as usize] = 1;

            assert_eq!(interpreter.pc, 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, 2);
        }

        #[test]
        fn cond_vx_ne_vy_op_equal() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0x9AB0;
            let op = Op::from(instr as u16);
            let (x, y, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 2;
            interpreter.v[y as usize] = 2;

            assert_eq!(interpreter.pc, 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, 0);
        }

        #[test]
        fn mem_set_i_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xA012;
            let op = Op::from(instr as u16);
            let (msb, b, lsb) = usize_to_three_nibbles(instr);
            let addr = three_nibbles_to_u16(msb, b, lsb);

            assert_eq!(interpreter.addr, 0);

            interpreter.execute(op);

            assert_eq!(interpreter.addr, addr);
        }

        #[test]
        fn goto_plus_v0_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xB012;
            let op = Op::from(instr as u16);
            let (msb, b, lsb) = usize_to_three_nibbles(instr);
            let addr = three_nibbles_to_u16(msb, b, lsb);

            interpreter.v[0] = 42;

            assert_eq!(interpreter.pc, 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc as u16, interpreter.v[0] as u16 + addr);
        }

        #[test]
        fn random_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xC012;
            let mut op = Op::from(instr as u16);
            let (x, msb, lsb) = usize_to_three_nibbles(instr);
            let eight_bits = two_nibbles_to_u8(msb, lsb);

            let rand_byte = 0xBC;
            let mut prev_byte = rand_byte;

            // set reg to arbitrary byte so we can check that it changed later
            interpreter.v[x as usize] = rand_byte;

            // I don't want to bother setting up tests for randomness on this op, so because I'm
            // lazy I'm going to run the op 10 times and makes sure at least 1 of those times it
            // changes to reg's value to a different number. This test will produce a false negative
            // very infrequently, which I can live with.

            let mut num_different = 0;
            for _ in 0..10 {
                interpreter.execute(op);

                let reg_val = interpreter.v[x as usize];

                // check to make sure the op worked as expected
                assert_eq!(reg_val, rand_byte & eight_bits);

                // check to make sure the op is changing (i.e. it's random)
                if reg_val != rand_byte {
                    // it changed
                    num_different = num_different + 1;
                }

                prev_byte = rand_byte;
            }

            assert!(num_different > 5);
        }

        #[test]
        fn display_op_collision() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xD012;
            let mut op = Op::from(instr as u16);
            let (x, y, height) = usize_to_three_nibbles(instr);

            // add arbitrary values starting at the memory address in I (which will be 0)
            // because these will be the values that get written to the graphics array

            assert_eq!(interpreter.addr, 0);
            let starting_addr = interpreter.addr as usize;

            let mut sprite = Vec::with_capacity((height * 8) as usize);
            for i in 0 as usize..height as usize {
                // 8 bits in a byte

                let random_byte: u8 = thread_rng().gen();

                // store the bits of the sprite
                for j in 0..8 {
                    let bit = ((random_byte >> (7 - j)) & 1) == 1;
                    sprite.push(bit);
                }
                interpreter.memory[(starting_addr + i) as usize] = random_byte;
            }

            for i in 0..interpreter.graphics.len() {
                assert_eq!(interpreter.graphics[i], false);
            }

            interpreter.execute(op);

            let gfx_addr = Graphics::get_graphics_idx(x, y);
            for i in 0..height as usize * 8 as usize {
                assert_eq!(interpreter.graphics[gfx_addr + i], sprite[i]);
            }

            assert_eq!(interpreter.v[0xf], 1);
        }

        #[test]
        fn display_op_no_collision() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xD011; // height is 1, so only 8 bits
            let mut op = Op::from(instr as u16);
            let (x, y, height) = usize_to_three_nibbles(instr);

            // add arbitrary values starting at the memory address in I (which will be 0)
            // because these will be the values that get written to the graphics array

            assert_eq!(interpreter.addr, 0);
            let starting_addr = interpreter.addr as usize;

            let mut sprite = Vec::with_capacity(8);
            let arb_byte = 0b10101010;

            interpreter.memory[starting_addr] = arb_byte;

            // store the same bits we're setting in the op so we won't set reg VF to 1
            let gfx_addr = Graphics::get_graphics_idx(x, y);

            for j in 0..8 {
                let bit = ((arb_byte >> (7 - j)) & 1) == 1;
                sprite.push(bit);
                interpreter.graphics.set(gfx_addr + j as usize, bit);
            }

            interpreter.execute(op);

            for i in 0..height as usize * 8 as usize {
                assert_eq!(interpreter.graphics[gfx_addr + i], sprite[i]);
            }

            assert_eq!(interpreter.v[0xf], 0);
        }

        #[test]
        fn key_eq_vx_op_keyup() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xE09E;
            let mut op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            let x_reg = interpreter.v[x as usize] as usize;

            assert_eq!(interpreter.graphics.get_key_state(x_reg), false);
            assert_eq!(interpreter.pc, 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, 0);
        }

        #[test]
        fn key_eq_vx_op_keydown() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xE09E;
            let mut op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            interpreter.v[x as usize] = 1; // setup x register for keypress
            let x_reg = interpreter.v[x as usize] as usize;

            assert_eq!(interpreter.graphics.get_key_state(x_reg), false);
            assert_eq!(interpreter.pc, 0);

            // fake pressing down the key in reg
            interpreter.graphics.handle_key_down(&Key::Key1);
            interpreter.execute(op);

            assert_eq!(interpreter.graphics.get_key_state(x_reg), true);
            assert_eq!(interpreter.pc, 2);
        }

        #[test]
        fn key_ne_vx_op_keyup() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xE0A1;
            let mut op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            let x_reg = interpreter.v[x as usize] as usize;

            assert_eq!(interpreter.graphics.get_key_state(x_reg), false);
            assert_eq!(interpreter.pc, 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, 2);
        }

        #[test]
        fn key_ne_vx_op_keydown() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xE0A1;
            let mut op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            interpreter.v[x as usize] = 1; // setup x register for keypress
            let x_reg = interpreter.v[x as usize] as usize;

            assert_eq!(interpreter.graphics.get_key_state(x_reg), false);
            assert_eq!(interpreter.pc, 0);

            // fake pressing down the key in reg
            interpreter.graphics.handle_key_down(&Key::Key1);
            interpreter.execute(op);

            assert_eq!(interpreter.graphics.get_key_state(x_reg), true);
            assert_eq!(interpreter.pc, 0);
        }

        #[test]
        fn delay_timer_set_vx_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xF007;
            let mut op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            assert_eq!(interpreter.v[x as usize], 0);
            assert_eq!(interpreter.delay_timer, 0);

            // artificially set delay_timer reg
            interpreter.delay_timer = 42;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 42);
        }

        #[test]
        fn key_get_block_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xF00A;
            let mut op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            // set instructions near the program counter so we can run `.cycle` correctly
            interpreter.memory[interpreter.pc] = 0xF0;
            interpreter.memory[interpreter.pc + 1] = 0x0A;
            let arb_instr = 0x00E0;
            interpreter.memory[interpreter.pc + 2] = 0x00;
            interpreter.memory[interpreter.pc + 3] = 0xE0;

            assert_eq!(interpreter.v[x as usize], 0);
            assert_eq!(interpreter.pc, 0);
            assert_eq!(interpreter.fx0a_metadata, FX0AMetadata::default());

            interpreter.cycle();

            assert_eq!(interpreter.fx0a_metadata.should_block_on_keypress, true);
            assert_eq!(interpreter.fx0a_metadata.last_key_pressed, None);
            assert_eq!(interpreter.fx0a_metadata.register, Some(x));
            assert_eq!(interpreter.pc, 2);

            // assert that cycle does not advance the program counter forward like it should
            // if we're in a nonblocking state
            interpreter.cycle();

            assert_eq!(interpreter.pc, 2);

            // fake key presses so we can verify program state resumes after we press some keys
            interpreter.handle_input_inner(Some(vec!(Key::Key1)));

            interpreter.cycle();

            assert_eq!(interpreter.pc, 4);
        }

        #[test]
        fn mem_set_add_vx_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xF01E;
            let mut op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            assert_eq!(interpreter.addr, 0);

            // artificially set the register at x so the `addr` field will get set to that value
            // after the op gets run
            interpreter.v[x as usize] = 42;

            interpreter.execute(op);

            assert_eq!(interpreter.addr, 42);
            assert_eq!(interpreter.v[0xF], 0);

            // now try with overflowing
            interpreter.addr = std::u16::MAX;
            interpreter.v[x as usize] = 1;

            interpreter.execute(op);

            assert_eq!(interpreter.addr, 0);
            assert_eq!(interpreter.v[0xF], 1);
        }

        #[test]
        fn mem_set_sprite_op() {
            let mut interpreter = Interpreter::new();

            let instr: usize = 0xF129;
            let mut op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 1;
            assert_eq!(interpreter.addr, 0);
            let reg = interpreter.v[x as usize];

            interpreter.execute(op);

            assert_eq!(interpreter.addr, (reg * NUM_BYTES_IN_FONT_CHAR) as u16);

            // now try with largest byte value, we should see that we only
            // look at the least significant nibble, and so it should be char 255 % 16 === 15
            interpreter.v[x as usize] = std::u8::MAX;
            let reg = interpreter.v[x as usize];

            let mut op = Op::from(instr as u16);

            interpreter.execute(op);

            assert_eq!(interpreter.addr, (15 * NUM_BYTES_IN_FONT_CHAR) as u16);
        }
    }

    #[test]
    fn two_u8s_to_16_test() {
        let n1 = 0x0;
        let n2 = 0xF;

        let expected: u16 = 0x0F;
        assert_eq!(expected, two_nibbles_to_u16(n1, n2));
    }

    #[test]
    fn three_u8s_to_16_test() {
        let n1 = 0x0;
        let n2 = 0xF;
        let n3 = 0xA;

        let expected: u16 = 0x0FA;
        assert_eq!(expected, three_nibbles_to_u16(n1, n2, n3));
    }
}
