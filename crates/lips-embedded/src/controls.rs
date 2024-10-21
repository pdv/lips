use core::cell::RefCell;
use cortex_m::interrupt::free;
use cortex_m::interrupt::Mutex;
use microbit::board::Buttons;
use microbit::hal::gpiote::Gpiote;
use microbit::pac::{self, interrupt, GPIOTE};

static GPIO: Mutex<RefCell<Option<Gpiote>>> = Mutex::new(RefCell::new(None));

fn init_buttons(board_gpiote: GPIOTE, board_buttons: Buttons) {
    let gpiote = Gpiote::new(board_gpiote);

    let channel0 = gpiote.channel0();
    channel0
        .input_pin(&board_buttons.button_a.degrade())
        .hi_to_lo()
        .enable_interrupt();
    channel0.reset_events();

    let channel1 = gpiote.channel1();
    channel1
        .input_pin(&board_buttons.button_b.degrade())
        .hi_to_lo()
        .enable_interrupt();
    channel1.reset_events();

    free(move |cs| {
        *GPIO.borrow(cs).borrow_mut() = Some(gpiote);
        unsafe {
            pac::NVIC::unmask(pac::Interrupt::GPIOTE);
        }
        pac::NVIC::unpend(pac::Interrupt::GPIOTE);
    });
}

#[interrupt]
fn GPIOTE() {
    free(|cs| {
        let Some(gpiote) = GPIO.borrow(cs).borrow().as_ref() else {
            return;
        };
        let a_pressed = gpiote.channel0().is_event_triggered();
        let b_pressed = gpiote.channel1().is_event_triggered();

        let turn = match (a_pressed, b_pressed) {
            (true, false) => Turn::Left,
            (false, true) => Turn::Right,
            _ => Turn::None,
        };

        gpiote.channel0().reset_events();
        gpiote.channel1().reset_events();

        *TURN.borrow(cs).borrow_mut() = turn;
    })
}
