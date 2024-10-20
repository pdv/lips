use core::str::Chars;

#[derive(Debug, PartialEq, Eq)]
pub enum Token<'a> {
    OpenParen,
    CloseParen,
    Quote,
    OpenDoubleQuote,
    CloseDoubleQuote,
    Symbol(&'a str),
}

pub struct Cursor<'a> {
    chars: Chars<'a>,
    in_quote: bool,
}

impl<'a> Cursor<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars(),
            in_quote: false,
        }
    }

    fn peek(&self) -> char {
        self.chars.clone().next().unwrap_or('\0')
    }

    fn eat_one(&mut self) {
        let _ = self.chars.next();
    }

    fn eat_while(&mut self, predicate: impl Fn(char) -> bool) -> &'a str {
        let remaining = self.chars.as_str();
        let mut len = 0;
        while !self.chars.as_str().is_empty() && predicate(self.peek()) {
            let c = self.chars.next();
            len += c.unwrap().len_utf8();
        }
        &remaining[..len]
    }
}

impl<'a> Iterator for Cursor<'a> {
    type Item = Result<Token<'a>, ()>;

    fn next(&mut self) -> Option<Self::Item> {
        let token = match self.peek() {
            '\0' => return None,
            '(' => {
                self.eat_one();
                Ok(Token::OpenParen)
            }
            ')' => {
                self.eat_one();
                Ok(Token::CloseParen)
            }
            '\'' => {
                self.eat_one();
                Ok(Token::Quote)
            }
            ' ' | '\n' if !self.in_quote => {
                self.eat_one();
                return self.next();
            }
            '"' => {
                self.eat_one();
                if self.in_quote {
                    self.in_quote = false;
                    Ok(Token::CloseDoubleQuote)
                } else {
                    self.in_quote = true;
                    Ok(Token::OpenDoubleQuote)
                }
            }
            _ => {
                if self.in_quote {
                    Ok(Token::Symbol(self.eat_while(|c| c != '"')))
                } else {
                    Ok(Token::Symbol(self.eat_while(|c| {
                        !c.is_whitespace() && c != ')' && c != '(' && c != '"'
                    })))
                }
            }
        };
        Some(token)
    }
}
