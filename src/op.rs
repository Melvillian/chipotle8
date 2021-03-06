// Rust doesn't have a 4-bit numeric type, so we waste 4 bits by storing nibbles in a Nibble. Oh well!
type Nibble = u8;

/// 35 CHIP 8 op codes. The Nibble's are guaranteed to be between 0x0 and 0xF.
///
/// See [the CHIP-8 Wikipedia page](https://en.wikipedia.org/wiki/CHIP-8#Opcode_table) for details
/// on each opcode.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Op {
    // 0XXX
    // 0NNN 	Call 		Calls RCA 1802 program at address NNN. Not necessary for most ROMs.
    CallRca(Nibble, Nibble, Nibble),
    // 00E0 	Display 	disp_clear() 	Clears the screen.
    DispClear,
    // 00EE 	Flow 	return; 	Returns from a subroutine.
    Return,
    // 1XXX
    // 1NNN 	Flow 	goto NNN; 	Jumps to address NNN.
    Goto(Nibble, Nibble, Nibble),

    // 2XXX
    GotoSubRtn(Nibble, Nibble, Nibble),

    // 3XXX
    CondVxEq(Nibble, Nibble, Nibble),

    // 4XXX
    CondVxNe(Nibble, Nibble, Nibble),

    // 5XXX
    CondVxVyEq(Nibble, Nibble),

    // 6XXX
    ConstSetVx(Nibble, Nibble, Nibble),

    // 7XXX
    ConstAddVx(Nibble, Nibble, Nibble),

    // 8XXX
    AssignVyToVx(Nibble, Nibble),
    BitOpOr(Nibble, Nibble),
    BitOpAnd(Nibble, Nibble),
    BitOpXor(Nibble, Nibble),
    MathVxAddVy(Nibble, Nibble),
    MathVxMinusVy(Nibble, Nibble),
    BitOpRtShift(Nibble),
    MathVyMinusVx(Nibble, Nibble),
    BitOpLftShift(Nibble),

    // 9XXX
    CondVxVyNe(Nibble, Nibble),

    // AXXX
    MemSetI(Nibble, Nibble, Nibble),

    // BXXX
    GotoPlusV0(Nibble, Nibble, Nibble),

    // CXXX
    Rand(Nibble, Nibble, Nibble),

    // DXXX
    DispDraw(Nibble, Nibble, Nibble),

    // EXXX
    KeyOpEqVx(Nibble),
    KeyOpNeVx(Nibble),

    // FXXX
    DelayGet(Nibble),
    KeyOpGet(Nibble),
    DelaySet(Nibble),
    SoundSet(Nibble),
    MemIPlusEqVx(Nibble),
    MemISetSprite(Nibble),
    Bcd(Nibble),
    RegDump(Nibble),
    RegLoad(Nibble),
}

impl Op {
    /// Return true if this op is related to the display. Later we use
    /// this to decide if we should devote cycles to redrawing the graphics buffer
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use chipotle8::Op;
    ///
    /// let op = Op::DispDraw(0x0, 0x0, 0x0);
    /// assert_eq!(op.is_display_op(), true);
    ///
    /// let op = Op::Goto(0x0, 0x0, 0x0);
    /// assert_eq!(op.is_display_op(), false);
    pub fn is_display_op(self) -> bool {
        match self {
            Op::DispDraw(_, _, _) | Op::DispClear => true,
            _ => false,
        }
    }
}

type Address = u16;

impl From<Address> for Op {
    fn from(item: Address) -> Self {
        let mask = 0xF;

        // these are the 4 nibbles of item, where nibb_1 is the MSB and nibb_4 is the LSB
        let nibb_1 = ((item >> 12) & mask) as Nibble;
        let nibb_2 = ((item >> 8) & mask) as Nibble;
        let nibb_3 = ((item >> 4) & mask) as Nibble;
        let nibb_4 = (item & mask) as Nibble;
        let nibbles = [nibb_1, nibb_2, nibb_3, nibb_4];

        let panic_msg = format!("unknown Address: {}", item);

        match nibbles {
            [0x0, n2, n3, n4] => match n4 {
                0x0 => Op::DispClear,
                0xE => Op::Return,
                _ => Op::CallRca(n2, n3, n4),
            },
            [0x1, n2, n3, n4] => Op::Goto(n2, n3, n4),
            [0x2, n2, n3, n4] => Op::GotoSubRtn(n2, n3, n4),
            [0x3, n2, n3, n4] => Op::CondVxEq(n2, n3, n4),
            [0x4, n2, n3, n4] => Op::CondVxNe(n2, n3, n4),
            [0x5, n2, n3, 0x0] => Op::CondVxVyEq(n2, n3),
            [0x6, n2, n3, n4] => Op::ConstSetVx(n2, n3, n4),
            [0x7, n2, n3, n4] => Op::ConstAddVx(n2, n3, n4),
            [0x8, n2, n3, n4] => match n4 {
                0x0 => Op::AssignVyToVx(n2, n3),
                0x1 => Op::BitOpOr(n2, n3),
                0x2 => Op::BitOpAnd(n2, n3),
                0x3 => Op::BitOpXor(n2, n3),
                0x4 => Op::MathVxAddVy(n2, n3),
                0x5 => Op::MathVxMinusVy(n2, n3),
                0x6 => Op::BitOpRtShift(n2),
                0x7 => Op::MathVyMinusVx(n2, n3),
                0xE => Op::BitOpLftShift(n2),
                _ => panic!(panic_msg),
            },
            [0x9, n2, n3, 0] => Op::CondVxVyNe(n2, n3),
            [0xA, n2, n3, n4] => Op::MemSetI(n2, n3, n4),
            [0xB, n2, n3, n4] => Op::GotoPlusV0(n2, n3, n4),
            [0xC, n2, n3, n4] => Op::Rand(n2, n3, n4),
            [0xD, n2, n3, n4] => Op::DispDraw(n2, n3, n4),
            [0xE, n2, n3, n4] => match [n3, n4] {
                [0x9, 0xE] => Op::KeyOpEqVx(n2),
                [0xA, 0x1] => Op::KeyOpNeVx(n2),
                _ => panic!(panic_msg),
            },
            [0xF, n2, n3, n4] => match [n3, n4] {
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
            },
            _ => panic!(panic_msg),
        }
    }
}

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

        op_num = 0x5FA0;
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
        assert_eq!(Op::from(op_num), Op::BitOpRtShift(0xF));

        op_num = 0x8FA7;
        assert_eq!(Op::from(op_num), Op::MathVyMinusVx(0xF, 0xA));

        op_num = 0x8FAE;
        assert_eq!(Op::from(op_num), Op::BitOpLftShift(0xF));

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

    #[test]
    #[should_panic]
    fn panic_convert_opcodes_8() {
        let op_num = 0x8DEF;
        Op::from(op_num);
    }

    #[test]
    #[should_panic]
    fn panic_convert_opcodes_9() {
        let op_num = 0x9DEF;
        Op::from(op_num);
    }

    #[test]
    #[should_panic]
    fn panic_convert_opcodes_e() {
        let op_num = 0xED9F;
        Op::from(op_num);
    }

    #[test]
    #[should_panic]
    fn panic_convert_opcodes_f() {
        let op_num = 0xFDEF;
        Op::from(op_num);
    }
}
