use std::borrow::Cow;
use std::env;
use std::error::Error;
use std::fs;
use std::io::{self, IsTerminal, Read};

use nu_ansi_term::{Color, Style};
use reedline::{
    Highlighter, Prompt, PromptEditMode, PromptHistorySearch, Reedline, Signal, StyledText,
};

use lips_lang::Runtime;

struct SyntaxHighlighter {}

fn paren_color(depth: usize) -> Color {
    match depth {
        0 => Color::White,
        1 => Color::Green,
        2 => Color::LightBlue,
        3 => Color::Red,
        _ => Color::LightPurple,
    }
}

fn paren_pairs(line: &str) -> Vec<(usize, usize, usize)> {
    let mut lefts = Vec::new();
    let mut pairs = Vec::new();
    for (idx, c) in line.chars().enumerate() {
        match c {
            '(' => {
                lefts.push(idx);
            }
            ')' => {
                if let Some(left) = lefts.pop() {
                    pairs.push((left, idx, lefts.len()));
                }
            }
            _ => {}
        }
    }
    pairs
}

impl Highlighter for SyntaxHighlighter {
    fn highlight(&self, line: &str, cursor: usize) -> StyledText {
        let pairs = paren_pairs(line);
        let mut s = StyledText::new();
        for (idx, c) in line.chars().enumerate() {
            let mut style = Style::default();
            if let Some((l, r, depth)) = pairs.iter().find(|(l, r, _)| *l == idx || *r == idx) {
                style.foreground = Some(paren_color(*depth));
                if (*l == cursor || *r == cursor - 1) && *l > 0 {
                    style = style.underline();
                }
            } else if c == '(' || c == ')' {
                style.background = Some(Color::Red)
            }
            s.push((style, c.to_string()))
        }
        s
    }
}

struct MyPrompt {}

impl Prompt for MyPrompt {
    fn render_prompt_left(&self) -> Cow<str> {
        Cow::from("> ".to_string())
    }

    fn render_prompt_right(&self) -> Cow<str> {
        Cow::default()
    }

    fn render_prompt_indicator(&self, _prompt_mode: PromptEditMode) -> Cow<str> {
        Cow::default()
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<str> {
        Cow::default()
    }

    fn render_prompt_history_search_indicator(
        &self,
        _history_search: PromptHistorySearch,
    ) -> Cow<str> {
        Cow::default()
    }

    fn get_prompt_color(&self) -> reedline::Color {
        reedline::Color::Reset
    }
}

fn run_repl() -> Result<(), Box<dyn Error>> {
    let mut rl = Reedline::create().with_highlighter(Box::new(SyntaxHighlighter {}));
    let prompt = MyPrompt {};
    let mut runtime = Runtime::default();
    loop {
        let Signal::Success(readline) = rl.read_line(&prompt)? else {
            panic!("readline failure")
        };
        if readline.as_str() == "\\dump" {
            print!("{}", runtime);
            continue;
        }
        let mut result = String::new();
        match runtime.eval_str(&readline) {
            Ok(res) => runtime.pprint(&mut result, res).unwrap(),
            Err(e) => print!("Error: {:?}", e),
        }
        println!("{}", result);
    }
}

fn run_source(source: &str) -> Result<(), Box<dyn Error>> {
    let mut runtime = Runtime::default();
    let mut result = String::new();
    match runtime.eval_str(source) {
        Ok(res) => runtime.pprint(&mut result, res).unwrap(),
        Err(e) => print!("Error: {:?}", e),
    }
    println!("{}", result);
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = env::args().collect();

    if args.len() > 1 {
        let source = fs::read_to_string(&args[1])?;
        return run_source(&source);
    }

    if !io::stdin().is_terminal() {
        let mut source = String::new();
        io::stdin().read_to_string(&mut source)?;
        return run_source(&source);
    }

    // Otherwise, run the interactive REPL
    run_repl()
}
