use std::error::Error;

use lips_lang::{NIL, Pointer, Runtime};

fn main() -> Result<(), Box<dyn Error>> {
    let mut rl = rustyline::DefaultEditor::new()?;
    let mut runtime = Runtime::new();
    loop {
        let readline = rl.readline(">> ")?;
        let (cmd, arg) = readline
            .as_str()
            .split_once(" ")
            .unwrap_or((readline.as_str(), ""));
        match cmd {
            "\\dump" => print!("{}", runtime),
            "\\gc" => {
                runtime.gc(NIL);
            }
            "\\pprint" => {
                let mut s = String::new();
                runtime.pretty_print(&mut s, Pointer(arg.parse()?))?;
                println!("{}", s);
            }
            _ => match runtime.eval_str(&readline) {
                Ok(obj) => {
                    let mut s = String::new();
                    runtime.pretty_print(&mut s, obj).unwrap();
                    println!("{}", s);
                }
                Err(e) => println!("Error: {:?}", e),
            },
        }
    }
}
