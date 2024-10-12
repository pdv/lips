#![no_main]
#![no_std]

use lips_lang;

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

    write!(serial, "\r\n\n\n\nWelcome v2\r\n> ").unwrap();
    // nb::block!(serial.flush()).unwrap();

    let mut rx_buffer: [u8; 1] = [0];
    loop {
        serial.read(&mut rx_buffer).unwrap();
        if rx_buffer[0] == b'\r' {
            write!(serial, "\r\n3\r\n> ").unwrap();
        } else {
            serial.write(&rx_buffer).unwrap();
        }
    }
}
