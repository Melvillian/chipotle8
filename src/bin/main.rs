use std::io::Error;

use chipotle8::Interpreter;
use std::path::Path;

fn main() -> Result<(), Error> {
    let mut i = Interpreter::new();
    i.initialize(Path::new("./pong.ch8"));


    Ok(())
}