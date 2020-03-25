use std::io::Error;
use minifb::{Key, ScaleMode, Window, WindowOptions};
use chipotle8::Interpreter;
use std::thread;
use sloggers::terminal::TerminalLoggerBuilder;
use sloggers::types::Severity;
use sloggers::Build;
use sloggers::terminal::Destination;
use slog::{debug, info};
use std::time::{Duration, Instant};

const WIDTH: usize = 64;
const HEIGHT: usize = 32;
pub const ENLARGE_RATIO: usize = 10; // TODO make this part of interpreter crate


fn main() -> Result<(), Error> {
    let mut window = Window::new(
        "Chip 8 Interpreter (In Rust!)",
        WIDTH * ENLARGE_RATIO,
        HEIGHT * ENLARGE_RATIO, // TODO do not hardcode
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

    interpreter.initialize("invaders.ch8");

    let mut earlier = Instant::now();

    while window.is_open() && !window.is_key_down(Key::Escape) {
        std::thread::sleep(std::time::Duration::from_millis(chipotle8::TIMER_CYCLE_INTERVAL));

        interpreter.cycle();
        interpreter.handle_key_input(&window);
        interpreter.draw(&mut window);
    }
    Ok(())
}
