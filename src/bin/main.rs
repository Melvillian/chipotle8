use std::io::Error;
use minifb::{Key, ScaleMode, Window, WindowOptions};
use chipotle8::Interpreter;
use std::fs::File;

const WIDTH: usize = 64;
const HEIGHT: usize = 32;

fn main() -> Result<(), Error> {
    let mut window = Window::new(
        "Noise Test - Press ESC to exit",
        WIDTH,
        HEIGHT,
        WindowOptions {
            resize: true,
            scale_mode: ScaleMode::UpperLeft,
            ..WindowOptions::default()
        },
    )
        .expect("Unable to create window");

    // Limit to max ~60 fps update rate
    window.limit_update_rate(Some(std::time::Duration::from_micros(16600)));

    let mut interpreter = crate::Interpreter::new();
    let game_file = File::open("pong.ch8").unwrap();
    interpreter.initialize(game_file);

    interpreter.draw(&mut window);

    while window.is_open() && !window.is_key_down(Key::Escape) {

        interpreter.cycle();
        interpreter.handle_key_input(&window);
        interpreter.draw(&mut window);
    }
    Ok(())
}
