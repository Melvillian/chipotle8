use chipotle8::{AsKeyboard, Interpreter, Key, WIDTH, HEIGHT};
use device_query::{DeviceQuery, DeviceState, Keycode};
use minifb::{ScaleMode, Window, WindowOptions};
use std::io::Error;
use std::thread;
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

    // setup keyboard
    let device_state = DeviceState::new();
    let keyboard = Keyboard(device_state);

    while window.is_open() && !keyboard.0.get_keys().contains(&Keycode::Escape) {
        thread::sleep(std::time::Duration::from_millis(
            chipotle8::TIMER_CYCLE_INTERVAL,
        ));

        // execute the current operation and draw the display if it changed
        if let Some(op) = interpreter.cycle() {
            if op.is_display_op() {
                let display = interpreter.get_pixels();
                window
                    .update_with_buffer(display, WIDTH, HEIGHT)
                    .unwrap();
            }
        }

        // check for key press changes and update the Interpreter with which keys are up or down
        interpreter.handle_key_input(&keyboard);
    }
    Ok(())
}
