#![no_main]
#![no_std]

use heapless::String;
use lips_lang::{self, Runtime, NIL};

use core::fmt::Write;
use panic_rtt_target as _;
use rtt_target::{rprintln, rtt_init_print};

use microbit::{
    hal::prelude::*,
    hal::uarte,
    hal::uarte::{Baudrate, Parity},
};

#[cortex_m_rt::entry]
fn main() -> ! {
    rtt_init_print!();
    rprintln!("booted!");
    let board = microbit::Board::take().unwrap();

    let mut serial = uarte::Uarte::new(
        board.UARTE0,
        board.uart.into(),
        Parity::EXCLUDED,
        Baudrate::BAUD115200,
    );

    writeln!(serial, "\n\nWelcome v2").unwrap();
    write!(serial, "> ").unwrap();

    let mut runtime = Runtime::new();
    let mut input = String::<60>::new();

    let mut rx_buffer: [u8; 1] = [0];
    loop {
        serial.read(&mut rx_buffer).unwrap();
        rprintln!("{}", rx_buffer[0]);
        match rx_buffer[0] {
            b'\n' | b'\r' => {
                writeln!(serial, "").unwrap();
                match input.as_str() {
                    "\\dump" => {
                        writeln!(serial, "{}", runtime).unwrap();
                    }
                    _ => {
                        let statement = runtime.read_str(input.as_str()).unwrap();
                        let output = runtime.eval(statement, NIL).unwrap();
                        let obj = runtime.deref(output).unwrap();
                        writeln!(serial, "{}", obj).unwrap();
                    }
                }
                input.clear();
                write!(serial, "> ").unwrap();
            }
            127 => {
                if input.pop().is_some() {
                    serial.write(&rx_buffer).unwrap();
                }
            }
            _ => {
                input.push(rx_buffer[0].into());
                serial.write(&rx_buffer).unwrap();
            }
        }
    }
}
