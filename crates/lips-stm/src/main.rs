#![no_std]
#![no_main]

use defmt::*;
use embassy_executor::Spawner;
use embassy_stm32::dac::{DacCh1, Value};
use embassy_stm32::dma::NoDma;
use embassy_time::Timer;
use lips_lang::Runtime;
use micromath::F32Ext;
use {defmt_rtt as _, panic_probe as _};

const V_REF: f32 = 3.3;
const BITS: u16 = 4095;
const STEP_SIZE: f32 = V_REF / BITS as f32;

fn v_to_a(v: f32) -> u16 {
    (v / STEP_SIZE).floor() as u16
}

fn n_to_f(n: u8) -> f32 {
    440.0 * (2.0_f32.powf((n as f32 - 69.0) / 12.0))
}

fn f_to_v(f: f32) -> f32 {
    f32::log2(f / 8.1758)
}

const TUNE: [u8; 5] = [60, 62, 64, 65, 67];

/**

(t)

*/

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());
    info!("Hello World!");

    let mut runtime = Runtime::new();
    let res = runtime.eval_str("(+ 1 2)").unwrap();
    let res = runtime.deref_int(res).unwrap();
    info!("{}", res);

    let mut dac = DacCh1::new(p.DAC1, NoDma, p.PA4);

    loop {
        /*
        for v in 0..=255 {
            dac.set(Value::Bit8(to_sine_wave(v)));
        }
        */
        for n in TUNE.iter() {
            let f = n_to_f(*n);
            let v = f_to_v(f);
            let a = v_to_a(v as f32);
            dac.set(Value::Bit12Right(a));
            Timer::after_millis(500).await;
        }
    }
}
