//! An implementation of the CHIP 8 emulator in Rust with the intention to be run
//! as WebAssembly
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

    sp: usize,          // stack pointer, 16 bits are needed but we use usize so we can index with it.
                        // The stack pointer always points on beyond the top of the stack, i.e. onto
                        // unallocated memory

    instr: u16,         // address instruction register
    pc: usize,          // program counter, 16 bits are needed but we use usize so we can index with it

    // 16 8-bit registers. VF is used as a flag by several of the opcodes (see @Op)
    v: [u8; 16],

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
            v: [0; 16],
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
                    self.v[0xf] = 1;
                }
            },
            Op::Return => {
                self.sp = self.sp - 1;
                let lsb = self.memory[self.sp];
                self.memory[self.sp] = 0; // zero out stack

                self.sp = self.sp - 1;
                let msb = self.memory[self.sp];
                self.memory[self.sp] = 0; // zero out stack

                let instr = two_nibbles_to_usize(msb, lsb);

                self.pc = instr;

            },
            Op::Goto(msb, b, lsb) => {
                let instr = three_nibbles_to_usize(msb, b, lsb);
                self.pc = instr;
            },
            Op::GotoSubRtn(msb, b, lsb) => {
                // save the current instruction for when the subroutine returns;
                let (pc_msb, pc_lsb) = usize_to_two_nibbles(self.pc);
                self.memory[self.sp] = pc_msb;
                self.sp = self.sp + 1;
                self.memory[self.sp] = pc_lsb;
                self.sp = self.sp + 1;

                // jump to the subroutine
                self.pc = three_nibbles_to_usize(msb, b, lsb);
            },
            Op::CondVxEq(x, msb, lsb) => {
                let reg = self.v[x as usize];
                let byte = two_nibbles_to_u16(msb, lsb) as u8;

                if reg == byte {
                    self.skip_instruction();
                }
            },
            Op::CondVxNe(x, msb, lsb) => {
                let reg = self.v[x as usize];
                let byte = two_nibbles_to_u16(msb, lsb) as u8;

                if reg != byte {
                    self.skip_instruction();
                }
            },
            Op::CondVxVyEq(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                if x_reg == y_reg {
                    self.skip_instruction();
                }
            },
            Op::ConstSetVx(x, msb, lsb) => {
                let byte = two_nibbles_to_u16(msb, lsb) as u8;
                self.v[x as usize] = byte;
            },
            Op::ConstAddVx(x, msb, lsb) => {
                let byte = two_nibbles_to_u16(msb, lsb) as u8;
                self.v[x as usize] = self.v[x as usize] + byte;
            },
            Op::AssignVyToVx(x, y) => {
                let y_reg = self.v[y as usize];
                self.v[x as usize] = y_reg;
            },
            Op::BitOpOr(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];
                self.v[x as usize] = x_reg | y_reg;
            },
            Op::BitOpAnd(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];
                self.v[x as usize] = x_reg & y_reg;
            },
            Op::BitOpXor(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];
                self.v[x as usize] = x_reg ^ y_reg;
            },
            Op::MathVxAddVy(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                // check for carry
                let (sum, did_overflow) = x_reg.overflowing_add(y_reg);
                self.v[x as usize] = sum;

                if did_overflow  {
                    self.v[0xf] = 1
                } else {
                    self.v[0xf] = 0;
                }
            },
            Op::MathVxMinusVy(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                // check for borrow
                let (val, did_overflow) = x_reg.overflowing_sub(y_reg);
                self.v[x as usize] = val;

                if (did_overflow) {
                    self.v[0xf] = 0;
                } else {
                    self.v[0xf] = 1;
                }
            },
            Op::BitOpRtShift(x) => {
                let x_reg = self.v[x as usize];

                self.v[0xf] = x_reg & 0b1; // set VF to the value of the lsb
                self.v[x as usize] = self.v[x as usize] >> 1;
            },
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
            },
            Op::BitOpLftShift(x) => {
                let x_reg = self.v[x as usize];

                self.v[0xf] = (x_reg & 0b10000000) >> 7; // set VF to the value of the msb
                self.v[x as usize] = self.v[x as usize] << 1;
            },
            Op::CondVxVyNe(x, y) => {
                let x_reg = self.v[x as usize];
                let y_reg = self.v[y as usize];

                if x_reg != y_reg {
                    self.skip_instruction();
                }
            }

            _ => unimplemented!()
        }

    }

    /// Skip executing the next instruction by incrementing the program counter 2 bytes. Used
    /// by some conditional opcodes
    fn skip_instruction(&mut self) {
        self.pc = self.pc + 2;
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

        let instr = two_nibbles_to_u16(msb, lsb);
        let op = Op::from(instr);

        self.execute(op);

        if self.v[0xf] == 1 { // a display bit changed by the previous Op?
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
    ((msb as u16) << 4) | (lsb as u16)
}

fn two_nibbles_to_usize(msb: u8, lsb: u8) -> usize {
    two_nibbles_to_u16(msb, lsb) as usize
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

    (msb, b, lsb)
}



#[cfg(test)]
mod interpreter_tests {
    use super::*;

    mod execute {
        use super::*;

        #[test]
        fn display_clear_op() {
            let mut interpreter = Interpreter::new();
            assert_eq!(interpreter.v[0xf], 0);

            let instr = 0x00E0;
            let op = Op::from(instr);
            interpreter.execute(op);

            for i in 0..interpreter.graphics.len() {
                assert_eq!(interpreter.graphics[i], 0);
            }
            assert_eq!(interpreter.v[0xf], 0);

            interpreter.graphics[0] = 1;
            interpreter.execute(Op::DispClear);
            assert_eq!(interpreter.v[0xf], 1);
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

            let eight_bits = two_nibbles_to_u16(msb, lsb) as u8;
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

            let eight_bits = two_nibbles_to_u16(msb, lsb) as u8;
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
            assert_eq!(interpreter.v[y as usize],3);
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
            assert_eq!(interpreter.v[y as usize],4);
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

