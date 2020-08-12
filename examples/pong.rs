use chipotle8::{AsKeyboard, Emulator, Key, HEIGHT, WIDTH};
use device_query::{DeviceQuery, DeviceState, Keycode};
use minifb::{ScaleMode, Window, WindowOptions};
use std::io::Error;
use std::time::Duration;

struct Keyboard(pub DeviceState);

impl AsKeyboard for Keyboard {
    fn keys_down(&self) -> Vec<Key> {
        self.0
            .get_keys()
            .iter()
            .filter_map(|key: &Keycode| match key {
                Keycode::Key1 => Some(Key::Key1),
                Keycode::Key2 => Some(Key::Key2),
                Keycode::Key3 => Some(Key::Key3),
                Keycode::Key4 => Some(Key::C),
                Keycode::Q => Some(Key::Key4),
                Keycode::W => Some(Key::Key5),
                Keycode::E => Some(Key::Key6),
                Keycode::R => Some(Key::D),
                Keycode::A => Some(Key::Key7),
                Keycode::S => Some(Key::Key8),
                Keycode::D => Some(Key::Key9),
                Keycode::F => Some(Key::E),
                Keycode::Z => Some(Key::A),
                Keycode::X => Some(Key::Key0),
                Keycode::C => Some(Key::B),
                Keycode::V => Some(Key::F),
                _ => None,
            })
            .collect()
    }
}

fn main() -> Result<(), Error> {
    let mut window: Window = Window::new(
        "Chip 8 Emulator (In Rust!)",
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

    // create the emulator and load the pong game file
    let mut emulator = crate::Emulator::with_game_file("games/PONG")?;

    // setup keyboard
    let device_state = DeviceState::new();
    let keyboard = Keyboard(device_state);

    while window.is_open() {
        // execute the current instruction
        if let Some(op) = emulator.cycle() {
            // draw the display if it changed
            if op.is_display_op() {
                let display = emulator.get_pixels();
                window.update_with_buffer(display, WIDTH, HEIGHT).unwrap();
            }
        }

        // check for key press changes and update the Emulator with which keys are up or down
        emulator.handle_key_input(&keyboard);
    }
    Ok(())
}
