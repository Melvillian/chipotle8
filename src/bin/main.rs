use chipotle8::{Interpreter, AsKeyboard, keyboard::Key};
use minifb::{Key as MiniFBKey, ScaleMode, Window as MiniFBWIndow, WindowOptions};
use std::io::Error;
use std::thread;
use std::time::Duration;
use std::convert::From;

struct Keyboard(MiniFBWIndow);

impl AsKeyboard for Keyboard {

    fn keys_down(&self) -> Vec<Key> {
        self.0.get_keys()
            .unwrap()
            .iter()
            .filter_map(|mini_key: &MiniFBKey| {
                let key_integer = *mini_key as u32;

                let number_of_hex_digits = 16;
                if key_integer < number_of_hex_digits { // only the hexadecimal keys 0 - F
                    Some(Key::from(key_integer as u8))
                } else {
                    None
                }
            })
            .collect()
    }
}

fn main() -> Result<(), Error> {
    let window_keyboard: MiniFBWIndow = MiniFBWIndow::new(
        "Chip 8 Interpreter (In Rust!)",
        chipotle8::WIDTH,
        chipotle8::HEIGHT,
        WindowOptions {
            resize: true,
            scale_mode: ScaleMode::UpperLeft,
            ..WindowOptions::default()
        },
    )
    .expect("Unable to create window");

    let keyboard = Keyboard(window_keyboard);

    let mut window: MiniFBWIndow = MiniFBWIndow::new(
        "Chip 8 Interpreter (In Rust!)",
        chipotle8::WIDTH,
        chipotle8::HEIGHT,
        WindowOptions {
            resize: true,
            scale_mode: ScaleMode::UpperLeft,
            ..WindowOptions::default()
        },
    )
        .expect("Unable to create window");

    // Limit to max update rate. This only needs about 60 Hz, which is 16ms
    window.limit_update_rate(Some(Duration::from_millis(16)));

    let mut interpreter = crate::Interpreter::new(None);

    // load the game file
    interpreter.initialize("data/PONG").unwrap();

    while window.is_open() && !window.is_key_down(MiniFBKey::Escape) {
        thread::sleep(std::time::Duration::from_millis(
            chipotle8::TIMER_CYCLE_INTERVAL,
        ));

        interpreter.cycle();
        interpreter.handle_key_input(&keyboard);
        interpreter.draw(&mut window);
    }
    Ok(())
}
