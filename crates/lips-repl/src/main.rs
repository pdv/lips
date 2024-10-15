use std::error::Error;

use lips_lang::{NIL, Runtime};

fn main() -> Result<(), Box<dyn Error>> {
    let mut rl = rustyline::DefaultEditor::new()?;
    let mut runtime = Runtime::new();
    loop {
        let readline = rl.readline(">> ")?;
        match readline.as_str() {
            "\\dump" => println!("{}", runtime),
            "\\gc" => {
                runtime.gc(NIL).unwrap();
                println!()
            }
            _ => match runtime.eval_str(&readline) {
                Ok(obj) => println!("{}", obj),
                Err(e) => println!("Error: {:?}", e),
            },
        }
    }
}
