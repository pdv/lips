#![no_main]
#![no_std]

use core::fmt::Write;

use heapless::String;
use microbit::{
    hal::uarte,
    hal::uarte::{Baudrate, Parity},
};
#[allow(unused_imports)]
use panic_rtt_target as _;
use rtt_target::{rprintln, rtt_init_print};

use lips_lang::{self, NIL, Runtime};

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

    writeln!(serial, "\r\n\nWelcome v3").unwrap();
    write!(serial, "\r> ").unwrap();

    let mut runtime = Runtime::new();
    let mut input = String::<100>::new();

    let mut rx_buffer: [u8; 1] = [0];
    loop {
        serial.read(&mut rx_buffer).unwrap();
        rprintln!("{}", rx_buffer[0]);
        match rx_buffer[0] {
            b'\n' | b'\r' => {
                writeln!(serial, "").unwrap();
                match input.as_str() {
                    "\\dump" => {
                        writeln!(serial, "\r{}", runtime).unwrap();
                    }
                    "\\gc" => {
                        runtime.gc(NIL).unwrap();
                        writeln!(serial, "").unwrap();
                    }
                    _ => match runtime.eval_str(input.as_str()) {
                        Ok(obj) => writeln!(serial, "\r{}", obj).unwrap(),
                        Err(e) => writeln!(serial, "\rError: {:?}", e).unwrap(),
                    },
                }
                input.clear();
                write!(serial, "\r> ").unwrap();
            }
            127 => {
                if input.pop().is_some() {
                    serial.write(&rx_buffer).unwrap();
                }
            }
            _ => {
                input.push(rx_buffer[0].into()).unwrap();
                serial.write(&rx_buffer).unwrap();
            }
        }
    }
}
