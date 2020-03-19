use std::io::Error;
use minifb::{Key, ScaleMode, Window, WindowOptions};
use chipotle8::Interpreter;
use std::thread;
use std::time;
use sloggers::terminal::TerminalLoggerBuilder;
use sloggers::types::Severity;
use sloggers::Build;
use sloggers::terminal::Destination;
use slog::{debug, info};

const WIDTH: usize = 64;
const HEIGHT: usize = 32;

fn main() -> Result<(), Error> {
    let mut window = Window::new(
        "Noise Test - Press ESC to exit",
        WIDTH * 32,
        HEIGHT * 32, // TODO do not hardcode
        WindowOptions {
            resize: true,
            scale_mode: ScaleMode::UpperLeft,
            ..WindowOptions::default()
        },
    )
        .expect("Unable to create window");

    // Limit to max ~60 fps update rate
    window.limit_update_rate(Some(std::time::Duration::from_micros(16600)));

    let mut interpreter = crate::Interpreter::new(None);

    interpreter.initialize("pong.ch8");

    let mut cnt = 0;
    while window.is_open() && !window.is_key_down(Key::Escape) {
        cnt+=1;
        info!(interpreter.get_logger(), "{}", cnt);
//        if (window.is_key_down(Key::Enter)) {
//            println!("HOLY FUCK");
//        }
//        window.get_keys().map(|keys| {
//            for t in keys {
//                println!("holding: {:?}", t);
//            }
//        });

        interpreter.cycle();
        interpreter.handle_key_input(&window);
        interpreter.draw(&mut window);

//        let ten_millis = time::Duration::from_millis(100);
//
//        thread::sleep(ten_millis);
    }
    Ok(())
}
