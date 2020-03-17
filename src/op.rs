/// 35 CHIP 8 op codes. The u8's are guaranteed to be between 0x0 and 0xF
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Op {
    // 0XXX
    // 0NNN 	Call 		Calls RCA 1802 program at address NNN. Not necessary for most ROMs.
    CallRca(u8, u8, u8),
    // 00E0 	Display 	disp_clear() 	Clears the screen.
    DispClear,
    // 00EE 	Flow 	return; 	Returns from a subroutine.
    Return,

    // 1XXX
    // 1NNN 	Flow 	goto NNN; 	Jumps to address NNN.
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
    BitOpRtShift(u8),
    MathVyMinusVx(u8, u8),
    BitOpLftShift(u8),

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
        let nibb_1 = ((item >> 12) & mask) as u8;
        let nibb_2 = ((item >> 8) & mask) as u8;
        let nibb_3 = ((item >> 4) & mask) as u8;
        let nibb_4 = (item & mask) as u8;
        let nibbles = [nibb_1, nibb_2, nibb_3, nibb_4];

        let panic_msg = format!("unknown u16 {}", item);

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
            [0x5, n2, n3, _] => Op::CondVxVyEq(n2, n3),
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
