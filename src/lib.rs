//! An implementation of the CHIP 8 emulator in Rust with the intention to be run
//! as WebAssembly
use std::fs::remove_file;
use std::fs::File;
use std::io::Error;
use std::io::Read;
use op::Op;

const MEMORY_SIZE: usize = 4096;
const DISPLAY_REFRESH_SIZE: usize = 256;
const CALL_STACK_SIZE: usize = 96;
const STARTING_MEMORY_BYTE: usize = 512;
const GAME_FILE_MEMORY_SIZE: usize = MEMORY_SIZE - (DISPLAY_REFRESH_SIZE + CALL_STACK_SIZE + STARTING_MEMORY_BYTE);
const STACK_START: usize = MEMORY_SIZE - DISPLAY_REFRESH_SIZE + CALL_STACK_SIZE;

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

pub struct Interpreter {
    pub memory: [u8; 4096], // 4k of RAM

    sp: usize,          // stack pointer, 16 bits are needed but we use usize so we can index with it

    instr: u16,         // address instruction register
    pc: usize,          // program counter, 16 bits are needed but we use usize so we can index with it

    // 16 8-bit registers. VF is used as a flag by several of the opcodes (see @Op)
    v0: u8,
    v1: u8,
    v2: u8,
    v3: u8,
    v4: u8,
    v5: u8,
    v6: u8,
    v7: u8,
    v8: u8,
    v9: u8,
    va: u8,
    vb: u8,
    vc: u8,
    vd: u8,
    ve: u8,
    vf: u8,

    graphics: [u8; 64 * 32], // 64x32 pixel monochrome screen

    delay_timer: u8,         // 60 Hz timer that can be set and read
    sound_timer: u8,         // 60 Hz timer that beeps whenever it is nonzero

    key_input: [u8; 16],     // 16 byte hex keyboard input (0-F).
                             // Each byte stores the 1 (on) or 0 (off) keypress state
    font_set: [[u8; 5]; 2],  // stores the 16 5-byte hex font set
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            memory: [0; 4096],
            sp: 0,
            instr: 0,
            pc: 0,
            v0: 0,
            v1: 0,
            v2: 0,
            v3: 0,
            v4: 0,
            v5: 0,
            v6: 0,
            v7: 0,
            v8: 0,
            v9: 0,
            va: 0,
            vb: 0,
            vc: 0,
            vd: 0,
            ve: 0,
            vf: 0,
            graphics: [0; 64 * 32],
            delay_timer: 0,
            sound_timer: 0,
            key_input: [0; 16],
            font_set: [
                [0xF0, 0x90, 0x90, 0x90, 0xF0],  // 0
                [0x20, 0x60, 0x20, 0x20, 0x70],  // 1
            // TODO..
            ]
        }
    }

    /// Update the state of the interpreter by running the operation
    fn execute(&mut self, op: Op) {
        match op {
            Op::CallRca(_, _, _) => panic!("found CallRca Op {:?}", op), // assume this won't be called
            Op::DispClear => {
                let mut set_vf: bool = false;
                for i in 0..self.graphics.len() {
                    if 0u8 ^ self.graphics[i] == 1 {
                        set_vf = true;
                    }
                    self.graphics[i] = 0;
                }

                if set_vf {
                    self.vf = 1;
                }
            },
            Op::Return => {
                self.sp = self.sp - 1;
                let lsb = self.memory[self.sp];
                self.memory[self.sp] = 0; // zero out stack

                self.sp = self.sp - 1;
                let msb = self.memory[self.sp];
                self.memory[self.sp] = 0; // zero out stack

                let instr = two_u8s_to_usize(msb, lsb);

                self.pc = instr;
            },
            Op::Goto(msb, b, lsb) => {

            }
            _ => unimplemented!()
        }

    }

    /// Draw the 64x32 pixel map
    fn draw(&mut self) {

    }

    /// Check for any changes to keyboard input (keys pressed or unpressed)
    fn update_key_inputs(&mut self) {

    }

    /// step forward one tick in the interpreter. Read the instruction
    /// at the program counter, decode it, execute it, and update any internal state
    pub fn tick(&mut self) {
        let msb = self.memory[self.pc as usize];
        self.pc = self.pc + 1;
        let lsb = self.memory[self.pc as usize];
        self.pc = self.pc + 1;

        let instr = two_u8s_to_u16(msb, lsb);
        let op = Op::from(instr);

        self.execute(op);

        if self.vf == 1 { // a display bit changed by the previous Op?
            self.draw();
        }

        self.update_key_inputs();
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

    /// Test function which initializes the interpreter with an empty file.
    /// We use this so that we can easily run `initialize` in tests.
    fn initialize_with_dummy(&mut self) -> Result<(), Error> {
        let f = File::create("foo.txt").unwrap();
        self.initialize(f)?;
        remove_file("foo.txt");

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
    file.read_to_end(&mut buf);

    Ok(buf)
}

/// Take the msb and lsb u8s and merge them into a single 16. Used
/// to convert two 8-bit pieces of data in memory into a single 16-bit
/// instruction.
fn two_u8s_to_u16(msb: u8, lsb: u8) -> u16 {
    ((msb as u16) << 4) | (lsb as u16)
}

fn two_u8s_to_usize(msb: u8, lsb: u8) -> usize {
    two_u8s_to_u16(msb, lsb) as usize
}

/// Take the msb, middle byte and lsb u8s and merge them into a single 16. Used
/// to convert three 4-bit pieces of data in memory into a single 16-bit
/// instruction.
fn three_u8s_to_u16(msb: u8, b: u8, lsb: u8) -> u16 {
    ((msb as u16) << 8) | ((b as u16) << 4) | (lsb as u16)
}



#[test]
fn execute_display_clear() {
    let mut interpreter = Interpreter::new();
    assert_eq!(interpreter.vf, 0);

    interpreter.execute(Op::DispClear);
    for i in 0..interpreter.graphics.len() {
        assert_eq!(interpreter.graphics[i], 0);
    }
    assert_eq!(interpreter.vf, 0);

    interpreter.graphics[0] = 1;
    interpreter.execute(Op::DispClear);
    assert_eq!(interpreter.vf, 1);
}

#[test]
fn execute_return() {
    let mut interpreter = Interpreter::new();
    interpreter.initialize_with_dummy();

    assert_eq!(interpreter.sp, STACK_START);
    assert_eq!(interpreter.pc, STARTING_MEMORY_BYTE);

    // fake call a function so we set a return address on the stack. We use arbitrary return
    // address 0x01AA
    interpreter.memory[interpreter.sp] = 0x01;
    interpreter.sp = interpreter.sp + 1;

    interpreter.memory[interpreter.sp] = 0xAA;
    interpreter.sp = interpreter.sp + 1;

    interpreter.execute(Op::Return);

    assert_eq!(interpreter.pc, two_u8s_to_usize(0x01, 0xAA));
    assert_eq!(interpreter.sp, STACK_START);
}

#[test]
fn two_u8s_to_16_test() {
    let n1 = 0x0;
    let n2 = 0xF;

    let expected: u16 = 0x0F;
    assert_eq!(expected, two_u8s_to_u16(n1, n2));
}

#[test]
fn three_u8s_to_16_test() {
    let n1 = 0x0;
    let n2 = 0xF;
    let n3 = 0xA;

    let expected: u16 = 0x0FA;
    assert_eq!(expected, three_u8s_to_u16(n1, n2, n3));
}