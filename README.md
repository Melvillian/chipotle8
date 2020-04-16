# Chipotle8

Chipotle8 is a CHIP-8 Emulator implemented in Rust, designed for networked play.

There are many CHIP-8 implementations, so this one differentiates itself by running as a client/server model so those CHIP-8 games which are multiplayer may be played with friends over the Internet. Once I implement networking you will be able to spin this up on a VPC, go to the appropriate URL and join a game lobby while you wait for a friend to join the go to the same URL and begin play.

## TODO

- [x] Implement single player windowed emulator
- [ ] Test on non-Ubuntu systems
- [ ] Implement server networking
- [ ] Implement client library in Javascript (maybe some WASM thrown in for fun)
- [ ] Play first networked Pong game!

## Usage

```rust
# Cargo.toml
[dependencies]
chipotle8 = { git = "https://github.com/Melvillian/chipotle8" }
```

## Example

`$> cargo run --example pong`

## Acknowledgements

The following guides and developers have been very helpful in inspiring me to learn about emulators/emulators

- Laurence Muller: http://www.multigesture.net/articles/how-to-write-an-emulator-chip-8-emulator/
- Wikipedia page on CHIP-8: https://en.wikipedia.org/wiki/CHIP-8
- Cowgod: http://devernay.free.fr/hacks/chip8/C8TECH10.HTM
- Matt Mikolay: https://github.com/mattmikolay/chip-8/wiki/CHIP%E2%80%908-Technical-Reference
- Ryan Levick (for when I got stuck on how to implement the FX0A instruction): https://github.com/rylev/Rust-8
