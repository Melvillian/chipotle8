//! An implementation of the CHIP 8 emulator in Rust with the intention to be run
//! as WebAssembly
use fixedbitset::FixedBitSet;

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

struct Nibble {
    nib: FixedBitSet, // 4-bit nibble
}

impl Nibble {
    fn new(one: u8, two: u8, three: u8, four: u8) -> Self {
        let mut nib = FixedBitSet::with_capacity(4);
        nib.set(0, one as boolean);
        nib.set(1, two as boolean);
        nib.set(2, three as boolean);
        nib.set(3, four as boolean);

        Nibble {
            nib
        }
    }
}

pub struct Interpreter {
    pub memory: [u8; 4096], // 4k of RAM

    stack: [u16; 16],   // program stack. CHIP 8 can hold up to 16 return addresses
    sp: u16,            // stack pointer


    instr: u16,         // address instruction register
    pc: u16,            // program counter

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
    font_set: [[u8; 5]; 2],    // stores the 16 5-byte hex font set
}

/// 35 CHIP 8 op codes
pub enum Op {
    CALL_RCA(Nibble, Nibble, Nibble),
}

impl Interpreter {
    fn new() -> Self {
        Interpreter {
            memory: [0; 4096],
            stack: [0; 16],
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

    /// step forward one tick in the interpreter. Read the instruction
    /// at the current address instruction register, decode it, execute it,
    /// and update any internal state
    fn tick(&mut self) -> Self {

    }
}


/// # PLAN
/// * make cpu instructions enum
/// * write tick function
///     - write handlers for each instruction
/// * create cpu struct with defaults
///     - write function to zero the cpu
///     -
/// * write register getter macro

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        let mut i = Interpreter::new();
        i.memory[0] = 1;
    }
}
