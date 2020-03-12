//! An implementation of the CHIP 8 emulator in Rust with the intention to be run
//! as WebAssembly
use std::path::Path;
use std::fs::File;
use std::io::Error;
use std::io::Read;
use std::convert::From;

const MEMORY_SIZE: usize = 4096;
const DISPLAY_REFRESH_SIZE: usize = 256;
const CALL_STACK_SIZE: usize = 96;
const STARTING_MEMORY_BYTE: usize = 512;
const GAME_FILE_MEMORY_SIZE: usize = MEMORY_SIZE - (DISPLAY_REFRESH_SIZE + CALL_STACK_SIZE + STARTING_MEMORY_BYTE);
const STACK_START: usize = MEMORY_SIZE - DISPLAY_REFRESH_SIZE + CALL_STACK_SIZE;
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
    font_set: [[u8; 5]; 2],  // stores the 16 5-byte hex font set
}

/// 35 CHIP 8 op codes. The u8's are guaranteed to be between 0x0 and 0xF
#[derive(Debug, PartialOrd, PartialEq)]
enum Op {
    // 0XXX
    CallRca(u8, u8, u8),
    DispClear,
    Return,

    // 1XXX
    Goto(u8, u8, u8),

    // 2XXX
    GotoSubRtn(u8, u8, u8),

    // 3XXX
    CondVxEq(u8, u8, u8),

    // 4XXX
    CondVxNe(u8, u8, u8),

    // 5XXX
    CondVxVyEq(u8, u8),

    // 6XXX
    ConstSetVx(u8, u8, u8),

    // 7XXX
    ConstAddVx(u8, u8, u8),

    // 8XXX
    AssignVyToVx(u8, u8),
    BitOpOr(u8, u8),
    BitOpAnd(u8, u8),
    BitOpXor(u8, u8),
    MathVxAddVy(u8, u8),
    MathVxMinusVy(u8, u8),
    BitOpRtShift(u8, u8),
    MathVyMinusVx(u8, u8),
    BitOpLftShift(u8, u8),

    // 9XXX
    CondVxVyNe(u8, u8),

    // AXXX
    MemSetI(u8, u8, u8),

    // BXXX
    GotoPlusV0(u8, u8, u8),

    // CXXX
    Rand(u8, u8, u8),

    // DXXX
    DispDraw(u8, u8, u8),

    // EXXX
    KeyOpEqVx(u8),
    KeyOpNeVx(u8),

    // FXXX
    DelayGet(u8),
    KeyOpGet(u8),
    DelaySet(u8),
    SoundSet(u8),
    MemIPlusEqVx(u8),
    MemISetSprite(u8),
    Bcd(u8),
    RegDump(u8),
    RegLoad(u8),
}

impl From<u16> for Op {
    fn from(item: u16) -> Self {
        let mask = 0xF;

        // these are the 4 nibbles of item, where nibb_1 is the MSB and nibb_4 is the LSB
        let nibb_1 = ((item >> 12) & mask) as u8 ;
        let nibb_2 = ((item >> 8) & mask) as u8;
        let nibb_3 = ((item >> 4) & mask) as u8;
        let nibb_4 = (item & mask) as u8;
        let nibbles = [nibb_1, nibb_2, nibb_3, nibb_4];

        let panic_msg = format!("unknown u16 {}", item);

        match nibbles {
            [0x0, n2, n3, n4] => {
                match n4 {
                    0x0       => Op::DispClear,
                    0xE       => Op::Return,
                    _ => Op::CallRca(n2, n3, n4),
                }
            },
            [0x1, n2, n3, n4] => Op::Goto(n2, n3, n4),
            [0x2, n2, n3, n4] => Op::GotoSubRtn(n2, n3, n4),
            [0x3, n2, n3, n4] => Op::CondVxEq(n2, n3, n4),
            [0x4, n2, n3, n4] => Op::CondVxNe(n2, n3, n4),
            [0x5, n2, n3, _]  => Op::CondVxVyEq(n2, n3),
            [0x6, n2, n3, n4] => Op::ConstSetVx(n2, n3, n4),
            [0x7, n2, n3, n4] => Op::ConstAddVx(n2, n3, n4),
            [0x8, n2, n3, n4] => {
                match n4 {
                    0x0       => Op::AssignVyToVx(n2, n3),
                    0x1       => Op::BitOpOr(n2, n3),
                    0x2       => Op::BitOpAnd(n2, n3),
                    0x3       => Op::BitOpXor(n2, n3),
                    0x4       => Op::MathVxAddVy(n2, n3),
                    0x5       => Op::MathVxMinusVy(n2, n3),
                    0x6       => Op::BitOpRtShift(n2, n3),
                    0x7       => Op::MathVyMinusVx(n2, n3),
                    0xE       => Op::BitOpLftShift(n2, n3),
                    _ => panic!(panic_msg),
                }
            },
            [0x9, n2, n3, 0]  => Op::CondVxVyNe(n2, n3),
            [0xA, n2, n3, n4] => Op::MemSetI(n2, n3, n4),
            [0xB, n2, n3, n4] => Op::GotoPlusV0(n2, n3, n4),
            [0xC, n2, n3, n4] => Op::Rand(n2, n3, n4),
            [0xD, n2, n3, n4] => Op::DispDraw(n2, n3, n4),
            [0xE, n2, n3, n4] => {
                match [n3, n4] {
                    [0x9, 0xE] => Op::KeyOpEqVx(n2),
                    [0xA, 0x1] => Op::KeyOpNeVx(n2),
                    _ => panic!(panic_msg),
                }
            },
            [0xF, n2, n3, n4] => {
                match [n3, n4] {
                    [0x0, 0x7] => Op::DelayGet(n2),
                    [0x0, 0xA] => Op::KeyOpGet(n2),
                    [0x1, 0x5] => Op::DelaySet(n2),
                    [0x1, 0x8] => Op::SoundSet(n2),
                    [0x1, 0xE] => Op::MemIPlusEqVx(n2),
                    [0x2, 0x9] => Op::MemISetSprite(n2),
                    [0x3, 0x3] => Op::Bcd(n2),
                    [0x5, 0x5] => Op::RegDump(n2),
                    [0x6, 0x5] => Op::RegLoad(n2),
                    _ => panic!(panic_msg),

                }
            }
            _ => panic!(panic_msg),
        }
    }
}

impl Interpreter {
    pub fn new() -> Self {
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
    /// at the program counter, decode it, execute it, and update any internal state
    pub fn tick(&mut self) {
    }

    /// Read in a game file and initialize the necessary registers.
    ///
    /// Returns an error if we fail to open the game file
    pub fn initialize(&mut self, path: &Path) -> Result<(), Error> {
        self.read_game_file(path)?;
        self.sp = STACK_START as u16;
        self.pc = STARTING_MEMORY_BYTE as u16;

        Ok(())
    }


    /// Read in a CHIP 8 game file and load it into memory starting at byte index 512
    fn read_game_file(&mut self, path: &Path) -> Result<(), Error> {
        let buf = read_to_vec(path)?;

        let err_msg = format!("file {} is too large", path.to_str().unwrap());
        assert!(buf.len() < GAME_FILE_MEMORY_SIZE, err_msg);

        let game_file_range = STARTING_MEMORY_BYTE..(STARTING_MEMORY_BYTE + buf.len());
        self.memory[game_file_range].copy_from_slice(&buf);

        Ok(())
    }
}

/// Read in a file located at path as a Vec<u8>
fn read_to_vec(path: &Path) -> Result<Vec<u8>, Error> {
    let mut f = File::open(path)?;
    let mut buf = Vec::new();
    f.read_to_end(&mut buf);

    Ok(buf)
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
    fn convert_opcodes() {
        let mut op_num = 0x0FFF;
        assert_eq!(Op::from(op_num), Op::CallRca(0xF, 0xF, 0xF));

        op_num = 0x00E0;
        assert_eq!(Op::from(op_num), Op::DispClear);

        op_num = 0x00EE;
        assert_eq!(Op::from(op_num), Op::Return);

        op_num = 0x1000;
        assert_eq!(Op::from(op_num), Op::Goto(0x0, 0x0, 0x0));

        op_num = 0x2AAA;
        assert_eq!(Op::from(op_num), Op::GotoSubRtn(0xA, 0xA, 0xA));

        op_num = 0x3FAA;
        assert_eq!(Op::from(op_num), Op::CondVxEq(0xF, 0xA, 0xA));

        op_num = 0x4FAA;
        assert_eq!(Op::from(op_num), Op::CondVxNe(0xF, 0xA, 0xA));

        op_num = 0x5FAB;
        assert_eq!(Op::from(op_num), Op::CondVxVyEq(0xF, 0xA));

        op_num = 0x6FAB;
        assert_eq!(Op::from(op_num), Op::ConstSetVx(0xF, 0xA, 0xB));

        op_num = 0x7FAB;
        assert_eq!(Op::from(op_num), Op::ConstAddVx(0xF, 0xA, 0xB));

        op_num = 0x8FA0;
        assert_eq!(Op::from(op_num), Op::AssignVyToVx(0xF, 0xA));

        op_num = 0x8FA1;
        assert_eq!(Op::from(op_num), Op::BitOpOr(0xF, 0xA));

        op_num = 0x8FA2;
        assert_eq!(Op::from(op_num), Op::BitOpAnd(0xF, 0xA));

        op_num = 0x8FA3;
        assert_eq!(Op::from(op_num), Op::BitOpXor(0xF, 0xA));

        op_num = 0x8FA4;
        assert_eq!(Op::from(op_num), Op::MathVxAddVy(0xF, 0xA));

        op_num = 0x8FA5;
        assert_eq!(Op::from(op_num), Op::MathVxMinusVy(0xF, 0xA));

        op_num = 0x8FA6;
        assert_eq!(Op::from(op_num), Op::BitOpRtShift(0xF, 0xA));

        op_num = 0x8FA7;
        assert_eq!(Op::from(op_num), Op::MathVyMinusVx(0xF, 0xA));

        op_num = 0x8FAE;
        assert_eq!(Op::from(op_num), Op::BitOpLftShift(0xF, 0xA));

        op_num = 0x9FA0;
        assert_eq!(Op::from(op_num), Op::CondVxVyNe(0xF, 0xA));

        op_num = 0xAFAB;
        assert_eq!(Op::from(op_num), Op::MemSetI(0xF, 0xA, 0xB));

        op_num = 0xBFAB;
        assert_eq!(Op::from(op_num), Op::GotoPlusV0(0xF, 0xA, 0xB));

        op_num = 0xCFAB;
        assert_eq!(Op::from(op_num), Op::Rand(0xF, 0xA, 0xB));

        op_num = 0xDFAB;
        assert_eq!(Op::from(op_num), Op::DispDraw(0xF, 0xA, 0xB));

        op_num = 0xEF9E;
        assert_eq!(Op::from(op_num), Op::KeyOpEqVx(0xF));

        op_num = 0xEFA1;
        assert_eq!(Op::from(op_num), Op::KeyOpNeVx(0xF));

        op_num = 0xF907;
        assert_eq!(Op::from(op_num), Op::DelayGet(0x9));

        op_num = 0xF90A;
        assert_eq!(Op::from(op_num), Op::KeyOpGet(0x9));

        op_num = 0xF915;
        assert_eq!(Op::from(op_num), Op::DelaySet(0x9));

        op_num = 0xF918;
        assert_eq!(Op::from(op_num), Op::SoundSet(0x9));

        op_num = 0xF91E;
        assert_eq!(Op::from(op_num), Op::MemIPlusEqVx(0x9));

        op_num = 0xF929;
        assert_eq!(Op::from(op_num), Op::MemISetSprite(0x9));

        op_num = 0xF933;
        assert_eq!(Op::from(op_num), Op::Bcd(0x9));

        op_num = 0xF955;
        assert_eq!(Op::from(op_num), Op::RegDump(0x9));

        op_num = 0xF965;
        assert_eq!(Op::from(op_num), Op::RegLoad(0x9));
    }
}
