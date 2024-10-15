use std::{error::Error, io::stdout};

use lips_lang::{Runtime, NIL};

fn main() -> Result<(), Box<dyn Error>> {
    let mut rl = rustyline::DefaultEditor::new()?;
    let mut runtime = Runtime::new();
    loop {
        let readline = rl.readline(">> ")?;
        match readline.as_str() {
            "\\dump" => print!("{}", runtime),
            "\\gc" => {
                runtime.gc(NIL);
            }
            _ => match runtime.eval_str(&readline) {
                Ok(obj) => println!("{}", obj),
                Err(e) => println!("Error: {:?}", e),
            },
        }
    }
}
