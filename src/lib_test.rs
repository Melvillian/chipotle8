#[cfg(test)]
pub mod interpreter_tests {
    use crate::*;

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

    mod execute {
        use super::*;

        #[test]
        fn display_clear_op() {
            let mut interpreter = Interpreter::new(None);
            assert_eq!(interpreter.v[0xf], 0);

            let instr = 0x00E0;
            let op = Op::from(instr);

            // set some graphics bits to true so we can later see them set to false;
            interpreter.graphics.set(0, 0, true);
            interpreter.graphics.set(
                (graphics::WIDTH - 1) as u8,
                (graphics::HEIGHT - 1) as u8,
                true,
            );

            interpreter.execute(op);

            for i in 0..interpreter.graphics.len() {
                assert_eq!(interpreter.graphics[i], 0);
            }
        }

        #[test]
        fn return_op() {
            let mut interpreter = Interpreter::new(None);

            assert_eq!(interpreter.sp, 0);
            assert_eq!(interpreter.pc, 0);

            // fake call a function so we set a return address on the stack. We use arbitrary return
            // address 0x001A
            let arb_addr = 0x001A;
            interpreter.stack[interpreter.sp] = arb_addr;
            interpreter.sp += 1;
            interpreter.pc = 0x090B; // arbitrary position for the program counter

            let instr = 0x00EE;
            let op = Op::from(instr);
            interpreter.execute(op);

            assert_eq!(interpreter.pc, arb_addr as usize);
            assert_eq!(interpreter.sp, 0);

            assert_eq!(interpreter.stack[interpreter.sp], 0);
        }

        #[test]
        fn goto_op() {
            let mut interpreter = Interpreter::new(None);
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
            let mut interpreter = Interpreter::new(None);
            assert_eq!(interpreter.pc, 0);
            assert_eq!(interpreter.sp, 0);

            let instr = 0x2DEF;
            let (msb, b, lsb) = usize_to_three_nibbles(instr);
            let addr = three_nibbles_to_usize(msb, b, lsb);
            interpreter.execute(Op::from(instr as u16));

            assert_eq!(interpreter.pc, addr);
            assert_eq!(interpreter.sp, 1);
            assert_eq!(interpreter.stack[interpreter.sp - 1], 2);
        }

        #[test]
        fn cond_vx_eq_op_false() {
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

            let nibbles = 0x5AF0; // arbitrary 3 nibbles
            let op = Op::from(nibbles as u16);
            let (x, y, _) = usize_to_three_nibbles(nibbles);
            let x_usize = x as usize;
            let y_usize = y as usize;

            let arb_byte = 0xAB;

            interpreter.v[x_usize] = arb_byte;
            interpreter.v[y_usize] = 0;

            interpreter.execute(op);

            assert_eq!(interpreter.pc, 0);
        }

        #[test]
        fn cond_vx_vy_eq_op_true() {
            let mut interpreter = Interpreter::new(None);

            let nibbles = 0x5AF0; // arbitrary 3 nibbles
            let op = Op::from(nibbles as u16);
            let (x, y, _) = usize_to_three_nibbles(nibbles);

            let arb_byte = 0xAB;
            interpreter.v[x as usize] = arb_byte;
            interpreter.v[y as usize] = arb_byte;

            interpreter.execute(op);

            assert_eq!(interpreter.pc, 2);
        }

        #[test]
        fn const_vx_set_op() {
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0x7AFB;
            let op = Op::from(instr as u16);
            let (x, msb, lsb) = usize_to_three_nibbles(instr);
            let x_usize = x as usize;

            let offset = 1; // set VA to something other than 0 so we can make sure 0xFB gets added
            interpreter.v[x_usize] = offset;
            assert_eq!(interpreter.v[x_usize], offset);

            interpreter.execute(op);

            let eight_bits = two_nibbles_to_u8(msb, lsb);
            assert_eq!(interpreter.v[x_usize], eight_bits + offset);
        }

        #[test]
        fn assign_vx_vy_op() {
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

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
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xC0FF;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            let mut prev_byte = 0xBC;

            // set reg to arbitrary byte so we can check that it changed later
            interpreter.v[x as usize] = prev_byte;

            // I don't want to bother setting up tests for randomness on this op, so because I'm
            // lazy I'm going to run the op 10 times and makes sure at least 5 of those times it
            // changes the reg's value to a different number. This test will produce a false negative
            // very infrequently, which I can live with.

            let mut num_different = 0;
            let mut new_reg_vals = vec![]; // used for printing in case of test failure
            for _ in 0..10 {
                interpreter.execute(op);

                let reg_val = interpreter.v[x as usize];

                // check to make sure the op is changing (i.e. it's random)
                if reg_val != prev_byte {
                    // it changed
                    num_different += 1;
                }
                new_reg_vals.push((prev_byte, reg_val));

                prev_byte = reg_val;
            }

            assert!(
                num_different > 5,
                format!("number_different: {:?}", new_reg_vals)
            );
        }

        #[test]
        fn display_op_collision_and_no_collision() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xD012;
            let op = Op::from(instr as u16);
            let (x, y, height) = usize_to_three_nibbles(instr);

            // set x and y regs to arbitrary values
            interpreter.v[x as usize] = 1;
            interpreter.v[y as usize] = 2;

            let x_reg = interpreter.v[x as usize];
            let y_reg = interpreter.v[y as usize];
            // add arbitrary values starting at the memory address in I (which will be 0)
            // because these will be the values that get written to the graphics array

            assert_eq!(interpreter.addr, 0);
            let starting_addr = interpreter.addr as usize;

            let arb_byte: u8 = 0b10101010;
            for i in 0 as usize..height as usize {
                interpreter.memory[(starting_addr + i) as usize] = arb_byte;
            }

            for i in 0..interpreter.graphics.len() {
                assert_eq!(interpreter.graphics[i], 0);
            }

            interpreter.execute(op);

            for i in 0..height {
                for j in 0..8 {
                    let x_coord = x_reg + j;
                    let y_coord = y_reg + i;
                    let gfx_addr = Graphics::get_graphics_idx(x_coord, y_coord);

                    let mut pixel = 0;
                    if ((arb_byte >> (7 - j)) & 1) == 1 {
                        pixel = 0xFFFFFF;
                    }

                    assert_eq!(interpreter.graphics[gfx_addr], pixel);
                }
            }

            // VF register should not have been set, because we only set VF when a pixel goes from
            // 1 -> 0, and in this case they all started out at 0.
            assert_eq!(interpreter.v[0xf], 0);

            // now let's set them all to 0, and see that VF gets set to 1. NOTE. In the extremely
            // unlikely chance that the random bytes were all 0 and we don't end up flipping any bits
            // here, count yourself one of the luckiest humans alive

            // first set all bits for the pixels we'll use to 1 to there will be
            // a collision
            for i in 0 as usize..height as usize {
                interpreter.memory[(starting_addr + i) as usize] = 0xFF;
            }

            interpreter.execute(op);

            assert_eq!(interpreter.v[0xf], 1);

            let new_byte = 0b01010101;
            for i in 0..height {
                for j in 0..8 {
                    let x_coord = x_reg + j;
                    let y_coord = y_reg + i;
                    let gfx_addr = Graphics::get_graphics_idx(x_coord, y_coord);

                    let mut pixel = 0;
                    if ((new_byte >> (7 - j)) & 1) == 1 {
                        pixel = 0xFFFFFF;
                    }

                    assert_eq!(interpreter.graphics[gfx_addr], pixel);
                }
            }
        }

        #[test]
        fn display_op_wrap_bottom_to_top() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xD012;
            let op = Op::from(instr as u16);
            let (x, y, height) = usize_to_three_nibbles(instr);

            // set x and y regs to coordinates so when we draw a sprite it will wrap around
            // the buffer bottom to top
            interpreter.v[x as usize] = 0;
            interpreter.v[y as usize] = (graphics::HEIGHT - 1) as u8;

            let starting_addr = interpreter.addr as usize;

            let arb_byte: u8 = 0b11111111;
            for i in 0 as usize..height as usize {
                interpreter.memory[(starting_addr + i) as usize] = arb_byte;
            }

            for i in 0..interpreter.graphics.len() {
                assert_eq!(interpreter.graphics[i], 0);
            }

            interpreter.execute(op);

            // we now should have 2 rows worth sprite draw, 1 on the bottommost row and
            // 1 one the top, both starting in the 0th column
            for y_coord in &[graphics::HEIGHT as u8 - 1, 0] {
                for x_coord in 0..8 {
                    let mut pixel = 0;
                    if ((arb_byte >> (7 - x_coord)) & 1) == 1 {
                        pixel = 0xFFFFFF;
                    }
                    let gfx_addr = Graphics::get_graphics_idx(x_coord, *y_coord);

                    assert_eq!(interpreter.graphics[gfx_addr], pixel);
                }
            }
        }

        #[test]
        fn display_op_wrap_right_to_left() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xD012;
            let op = Op::from(instr as u16);
            let (x, y, height) = usize_to_three_nibbles(instr);

            // set x and y regs to coordinates so when we draw a sprite it will wrap around
            // the buffer right to left
            interpreter.v[x as usize] = (graphics::WIDTH - 1) as u8;
            interpreter.v[y as usize] = 0;

            let x_reg = interpreter.v[x as usize];
            let y_reg = interpreter.v[y as usize];

            let starting_addr = interpreter.addr as usize;

            let arb_byte: u8 = 0b11111111;
            for i in 0 as usize..height as usize {
                interpreter.memory[(starting_addr + i) as usize] = arb_byte;
            }

            for i in 0..interpreter.graphics.len() {
                assert_eq!(interpreter.graphics[i], 0);
            }

            interpreter.execute(op);

            // we now should have 2 rows worth sprite draw, 1 on the first row with one pixel
            // on the right side and 7 pixels on the left, and the same for the second row directly
            // below it
            for y_delta in 0..height {
                for x_delta in 0..8 {
                    let mut pixel = 0;
                    if ((arb_byte >> (7 - x_delta)) & 1) == 1 {
                        pixel = 0xFFFFFF;
                    }
                    let x_coord = x_reg + x_delta;
                    let y_coord = y_reg + y_delta;
                    let gfx_addr = Graphics::get_graphics_idx(x_coord, y_coord);

                    assert_eq!(interpreter.graphics[gfx_addr], pixel);
                }
            }
        }

        #[test]
        fn key_eq_vx_op_keyup() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xE09E;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            let x_reg = interpreter.v[x as usize];

            assert_eq!(interpreter.keyboard.get_key_state(x_reg.into()), false);
            assert_eq!(interpreter.pc, 0);

            // fake pressing down and up the key in reg
            interpreter.keyboard.handle_key_down(Key::Key1);
            interpreter.keyboard.handle_key_up(Key::Key1);
            interpreter.execute(op);

            assert_eq!(interpreter.pc, 0);
        }

        #[test]
        fn key_eq_vx_op_keydown() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xE09E;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            interpreter.v[x as usize] = 1; // setup x register for keypress
            let x_reg = interpreter.v[x as usize];

            assert_eq!(interpreter.keyboard.get_key_state(x_reg.into()), false);
            assert_eq!(interpreter.pc, 0);

            // fake pressing down the key in reg
            interpreter.keyboard.handle_key_down(Key::Key1);
            interpreter.execute(op);

            assert_eq!(interpreter.keyboard.get_key_state(x_reg.into()), true);
            assert_eq!(interpreter.pc, 2);
        }

        #[test]
        fn key_ne_vx_op_keyup() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xE0A1;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            let x_reg = interpreter.v[x as usize];

            assert_eq!(interpreter.keyboard.get_key_state(x_reg.into()), false);
            assert_eq!(interpreter.pc, 0);

            interpreter.execute(op);

            assert_eq!(interpreter.pc, 2);
        }

        #[test]
        fn key_ne_vx_op_keydown() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xE0A1;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);
            interpreter.v[x as usize] = 1; // setup x register for keypress
            let x_reg = interpreter.v[x as usize];

            assert_eq!(interpreter.keyboard.get_key_state(x_reg.into()), false);
            assert_eq!(interpreter.pc, 0);

            // fake pressing down the key in reg
            interpreter.keyboard.handle_key_down(Key::Key1);
            interpreter.execute(op);

            assert_eq!(interpreter.keyboard.get_key_state(x_reg.into()), true);
            assert_eq!(interpreter.pc, 0);
        }

        #[test]
        fn delay_timer_set_vx_op() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xF007;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            assert_eq!(interpreter.v[x as usize], 0);
            assert_eq!(interpreter.delay_timer, 0);

            // artificially set delay_timer reg
            interpreter.delay_timer = 42;

            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 42);

            // now wait 2 cycles worth of time (plus a little bit more so we don't have flaky tests),
            // and make sure the value we get reflects the fact that time has passed
            std::thread::sleep(std::time::Duration::from_millis(2 * TIMER_CYCLE_INTERVAL));
            std::thread::sleep(std::time::Duration::from_micros(100));
            interpreter.execute(op);

            assert_eq!(interpreter.v[x as usize], 40);
        }

        /// Used only for the test below to test AsKeyboard
        struct Keyboard(Vec<Key>);
        impl AsKeyboard for Keyboard {
            fn keys_down(&self) -> Vec<Key> {
                self.0.clone()
            }
        }

        #[test]
        fn key_get_block_op() {
            let mut interpreter = Interpreter::new(None);

            let instr = 0xF00A;
            let (x, _, _) = usize_to_three_nibbles(instr);

            // set the 0xFX0A near the program counter so we can run `.cycle` correctly
            interpreter.memory[interpreter.pc] = 0xF0;
            interpreter.memory[interpreter.pc + 1] = 0x0A;

            // set the 2nd instruction to be some arbitrary instruction, it doesn't matter what it is
            // so we we choose 0x00EO (DispClear)
            interpreter.memory[interpreter.pc + 2] = 0x00;
            interpreter.memory[interpreter.pc + 3] = 0xE0;

            assert_eq!(interpreter.v[x as usize], 0);
            assert_eq!(interpreter.pc, 0);
            assert_eq!(interpreter.keyboard.is_blocking(), false);

            interpreter.cycle();

            assert_eq!(interpreter.keyboard.is_blocking(), true);
            assert_eq!(interpreter.pc, 2);

            // assert that cycle does not advance the program counter forward like it should
            // if we're in a nonblocking state
            interpreter.cycle();

            assert_eq!(interpreter.pc, 2);

            // fake key presses so we can verify program state resumes after we press some keys
            let keys = vec![Key::Key1, Key::C];
            let keyboard = Keyboard(keys);
            interpreter.handle_key_input(&keyboard);

            interpreter.cycle();

            assert_eq!(interpreter.pc, 4);
        }

        #[test]
        fn mem_set_add_vx_op() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xF01E;
            let op = Op::from(instr as u16);
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
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xF129;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            interpreter.v[x as usize] = 1;
            let reg = interpreter.v[x as usize];
            assert_eq!(interpreter.addr, 0);

            interpreter.execute(op);

            assert_eq!(interpreter.addr, (reg * NUM_BYTES_IN_FONT_CHAR) as u16);

            // now try with largest byte value, we should see that we only
            // look at the least significant nibble, and so it should be char 255 % 16 === 15
            interpreter.v[x as usize] = std::u8::MAX;

            let op = Op::from(instr as u16);

            interpreter.execute(op);

            assert_eq!(interpreter.addr, (15 * NUM_BYTES_IN_FONT_CHAR) as u16);
        }

        #[test]
        fn bcd_op() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xF133;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            assert_eq!(interpreter.addr, 0);

            interpreter.v[x as usize] = 123;

            interpreter.execute(op);

            assert_eq!(interpreter.memory[(interpreter.addr + 0) as usize], 1);
            assert_eq!(interpreter.memory[(interpreter.addr + 1) as usize], 2);
            assert_eq!(interpreter.memory[(interpreter.addr + 2) as usize], 3);
        }

        #[test]
        fn reg_dump_op() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xFA55;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            // fake putting values in the registers so our op will put them in the x
            // bytes starting at memory location interpreter.addr
            for i in 0..x + 1 {
                interpreter.v[i as usize] = i;
            }

            interpreter.addr = STARTING_MEMORY_BYTE as u16;
            for i in 0..16 {
                assert_eq!(interpreter.memory[(interpreter.addr + i) as usize], 0);
            }

            interpreter.execute(op);

            assert_eq!(interpreter.addr, STARTING_MEMORY_BYTE as u16);
            for i in 0u8..16u8 {
                if i <= x {
                    // these should have been set from the register values
                    assert_eq!(
                        interpreter.memory[(interpreter.addr + i as u16) as usize],
                        i
                    );
                } else {
                    // these should not have changed
                    assert_eq!(
                        interpreter.memory[(interpreter.addr + i as u16) as usize],
                        0
                    );
                }
            }
        }

        #[test]
        fn reg_load_op() {
            let mut interpreter = Interpreter::new(None);

            let instr: usize = 0xFA65;
            let op = Op::from(instr as u16);
            let (x, _, _) = usize_to_three_nibbles(instr);

            // fake putting values in memory so our op will put them in the x
            // bytes starting at memory location interpreter.addr
            interpreter.addr = STARTING_MEMORY_BYTE as u16;
            for i in 0..16 {
                interpreter.memory[(interpreter.addr + i) as usize] = i as u8;
            }

            for i in 0..x + 1 {
                assert_eq!(interpreter.v[i as usize], 0);
            }

            interpreter.execute(op);

            assert_eq!(interpreter.addr, STARTING_MEMORY_BYTE as u16);
            for i in 0u8..16u8 {
                if i <= x {
                    // these should have been set from the memory values
                    assert_eq!(interpreter.v[i as usize], i);
                } else {
                    // these should not have changed
                    assert_eq!(interpreter.v[i as usize], 0);
                }
            }
        }

        #[test]
        fn timer_dec() {
            let mut interpreter = Interpreter::new(None);

            // fake setting timers to non-zero value
            interpreter.delay_timer = 2;
            interpreter.sound_timer = 4;

            std::thread::sleep(std::time::Duration::from_millis(TIMER_CYCLE_INTERVAL));
            interpreter.decrement_timers_after_cycle();

            assert_eq!(interpreter.delay_timer, 1);
            assert_eq!(interpreter.sound_timer, 3);

            // don't wait anytime, and we should see they don't decrement
            interpreter.decrement_timers_after_cycle();

            assert_eq!(interpreter.delay_timer, 1);
            assert_eq!(interpreter.sound_timer, 3);

            // now wait 2 interval's worth so they try to decrement by 2
            std::thread::sleep(std::time::Duration::from_millis(TIMER_CYCLE_INTERVAL * 2));
            interpreter.decrement_timers_after_cycle();

            assert_eq!(interpreter.delay_timer, 0);
            assert_eq!(interpreter.sound_timer, 1);

            std::thread::sleep(std::time::Duration::from_millis(TIMER_CYCLE_INTERVAL * 2));
            interpreter.decrement_timers_after_cycle();
            interpreter.decrement_timers_after_cycle();

            assert_eq!(interpreter.delay_timer, 0);
            assert_eq!(interpreter.sound_timer, 0);
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
