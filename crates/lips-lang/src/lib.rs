// #![no_std]

use core::{fmt, str::Chars};

use heapless::Vec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pointer(u16);

pub const NIL: Pointer = Pointer(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Symbol {
    Add,
    Lambda,
    Identifier(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Object {
    Int(i32),
    Symbol(Symbol),
    Cons(Pointer, Pointer),
}

#[derive(Debug, PartialEq, Eq)]
enum Token<'a> {
    OpenParen,
    CloseParen,
    Int(i32),
    Symbol(&'a str),
}

struct Cursor<'a> {
    chars: Chars<'a>,
}

impl<'a> Cursor<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars(),
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
            let _ = self.chars.next();
            len += 1;
        }
        &remaining[..len]
    }
}

impl<'a> Iterator for Cursor<'a> {
    type Item = Result<Token<'a>, Error>;

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
            '0'..='9' => self
                .eat_while(|c| c.is_numeric())
                .parse::<i32>()
                .map(|i| Token::Int(i))
                .map_err(|_| Error::TypeError),
            ' ' => {
                self.eat_one();
                return self.next();
            }
            _ => Ok(Token::Symbol(
                self.eat_while(|c| c.is_alphanumeric() || c == '+'),
            )),
        };
        Some(token)
    }
}

#[derive(Debug)]
pub struct Runtime {
    workspace: Vec<Object, 300>,
}

#[derive(Debug)]
pub enum Error {
    EndOfFile,
    NotFound,
    OutOfMemory,
    NullPointer,
    UnknownSymbol,
    TypeError,
    SyntaxError,
    ArgCount,
}

impl Runtime {
    pub fn new() -> Self {
        let mut workspace = Vec::new();
        workspace.push(Object::Int(0)).unwrap();
        Runtime { workspace }
    }

    fn alloc(&mut self, obj: Object) -> Result<Pointer, Error> {
        self.workspace.push(obj).or(Err(Error::OutOfMemory))?;
        Ok(Pointer(self.workspace.len() as u16 - 1))
    }

    pub fn deref(&self, pointer: Pointer) -> Result<&Object, Error> {
        if pointer.0 == 0 {
            return Err(Error::NullPointer);
        }
        self.workspace
            .get(pointer.0 as usize)
            .ok_or(Error::NullPointer)
    }

    fn read_rest(&mut self, cursor: &mut Cursor) -> Result<Pointer, Error> {
        let head = self.read(cursor)?;
        if head == NIL {
            return Ok(NIL);
        }
        let tail = self.read_rest(cursor)?;
        self.alloc(Object::Cons(head, tail))
    }

    fn read(&mut self, cursor: &mut Cursor) -> Result<Pointer, Error> {
        let Some(Ok(token)) = cursor.next() else {
            return Err(Error::EndOfFile);
        };
        match token {
            Token::OpenParen => self.read_rest(cursor),
            Token::CloseParen => Ok(NIL),
            Token::Int(i) => self.alloc(Object::Int(i)),
            Token::Symbol(s) => match s {
                "+" => self.alloc(Object::Symbol(Symbol::Add)),
                "x" => self.alloc(Object::Symbol(Symbol::Identifier(b'x'))),
                "fn" => self.alloc(Object::Symbol(Symbol::Lambda)),
                _ => Err(Error::UnknownSymbol),
            },
        }
    }

    pub fn read_str(&mut self, s: &str) -> Result<Pointer, Error> {
        let mut cursor = Cursor::new(s);
        self.read(&mut cursor)
    }

    fn fst(&self, pointer: Pointer) -> Result<Pointer, Error> {
        let Object::Cons(car, _) = self.deref(pointer)? else {
            return Err(Error::TypeError);
        };
        Ok(*car)
    }

    fn snd(&self, pointer: Pointer) -> Result<Pointer, Error> {
        let Object::Cons(_, cdr) = self.deref(pointer)? else {
            return Err(Error::TypeError);
        };
        let Object::Cons(car, _) = self.deref(*cdr)? else {
            return Err(Error::TypeError);
        };
        Ok(*car)
    }

    fn lookup(&mut self, env: Pointer, id: u8) -> Result<Pointer, Error> {
        match self.deref(env)? {
            Object::Cons(car, cdr) => match self.deref(*car)? {
                Object::Cons(key, value) => {
                    if self.deref(*key)? == &Object::Symbol(Symbol::Identifier(id)) {
                        Ok(*value)
                    } else {
                        self.lookup(*cdr, id)
                    }
                }
                _ => Err(Error::TypeError),
            },
            _ => Err(Error::NotFound),
        }
    }

    pub fn eval(&mut self, form: Pointer, env: Pointer) -> Result<Pointer, Error> {
        println!("evaling {:?}", form);
        match *self.deref(form)? {
            Object::Int(_) => Ok(form),
            Object::Symbol(symbol) => match symbol {
                Symbol::Identifier(id) => self.lookup(env, id),
                _ => Ok(form),
            },
            Object::Cons(car, cdr) => {
                let car = self.eval(car, env)?;
                match *self.deref(car)? {
                    Object::Symbol(symbol) => match symbol {
                        Symbol::Add => {
                            let a = self.eval(self.fst(cdr)?, env)?;
                            let b = self.eval(self.snd(cdr)?, env)?;
                            match (self.deref(a)?, self.deref(b)?) {
                                (Object::Int(x), Object::Int(y)) => self.alloc(Object::Int(x + y)),
                                _ => Err(Error::TypeError),
                            }
                        }
                        Symbol::Lambda => {
                            let params = self.fst(cdr)?;
                            let body = self.snd(cdr)?;
                            self.alloc(Object::Cons(params, body))
                        }
                        _ => Err(Error::UnknownSymbol),
                    },
                    Object::Cons(params, body) => {
                        let mut env = env;
                        let mut params = params;
                        let mut args = cdr;
                        loop {
                            dbg!(env, params, args);
                            if (params == NIL) != (args == NIL) {
                                return Err(Error::ArgCount);
                            } else if params == NIL {
                                break;
                            }
                            let Object::Cons(param, rparams) = *self.deref(params)? else {
                                return Err(Error::TypeError);
                            };
                            let Object::Cons(arg, rargs) = *self.deref(args)? else {
                                return Err(Error::TypeError);
                            };
                            let arg = self.eval(arg, env)?;
                            let assignment = self.alloc(Object::Cons(param, arg))?;
                            env = self.alloc(Object::Cons(assignment, env))?;
                            params = rparams;
                            args = rargs;
                        }
                        self.eval(body, env)
                    }
                    _ => Err(Error::TypeError),
                }
            }
        }
    }
}

impl core::fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Int(i) => write!(f, "{}", i),
            Object::Symbol(s) => write!(f, "{:?}", s),
            Object::Cons(car, cdr) => write!(f, "({} {})", car.0, cdr.0),
        }
    }
}

impl core::fmt::Display for Runtime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, obj) in self.workspace.iter().enumerate() {
            writeln!(f, "{}: {}", idx, obj)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    #[test]
    fn test_alloc() {
        let mut runtime = Runtime::new();
        std::dbg!("foo");
        let symbol = runtime.alloc(Object::Symbol(Symbol::Add)).unwrap();
        let a = runtime.alloc(Object::Int(1)).unwrap();
        let b = runtime.alloc(Object::Int(2)).unwrap();
        let end = runtime.alloc(Object::Cons(b, Pointer(100))).unwrap();
        let next = runtime.alloc(Object::Cons(a, end)).unwrap();
        let head = runtime.alloc(Object::Cons(symbol, next)).unwrap();
        let res = runtime.eval(head, NIL).unwrap();
        assert_eq!(*runtime.deref(res).unwrap(), Object::Int(3));
    }

    #[test]
    fn test_lexer() {
        let cursor = Cursor::new("(+ 1 2)");
        let expected = [
            Token::OpenParen,
            Token::Symbol("+"),
            Token::Int(1),
            Token::Int(2),
            Token::CloseParen,
        ];
        for (idx, token) in cursor.enumerate() {
            assert_eq!(token.unwrap(), expected[idx]);
        }
    }

    #[test]
    fn test_lexer_nested() {
        let mut cursor = Cursor::new("(+ 1 (+ 2 3))");
        let expected = [
            Token::OpenParen,
            Token::Symbol("+"),
            Token::Int(1),
            Token::OpenParen,
            Token::Symbol("+"),
            Token::Int(2),
            Token::Int(3),
            Token::CloseParen,
            Token::CloseParen,
        ];
        for token in expected.into_iter() {
            assert_eq!(cursor.next().unwrap().unwrap(), token);
        }
    }

    #[test]
    fn test_read() {
        let mut runtime = Runtime::new();
        let ptr = runtime.read_str("(+ 1 2)").unwrap();
        let res = runtime.eval(ptr, NIL).unwrap();
        assert_eq!(*runtime.deref(res).unwrap(), Object::Int(3));
    }

    #[test]
    fn test_nested() {
        let mut runtime = Runtime::new();
        let ptr = runtime.read_str("(+ (+ 1 2) (+ 3 4))").unwrap();
        let res = runtime.eval(ptr, NIL).unwrap();
        assert_eq!(*runtime.deref(res).unwrap(), Object::Int(10));
    }

    #[test]
    fn test_env() {
        let mut runtime = Runtime::new();
        let symbol = runtime
            .alloc(Object::Symbol(Symbol::Identifier(b'x')))
            .unwrap();
        let value = runtime.alloc(Object::Int(42)).unwrap();
        let lookup = runtime.alloc(Object::Cons(symbol, value)).unwrap();
        let env = runtime.alloc(Object::Cons(lookup, NIL)).unwrap();
        let form = runtime.read_str("(+ x 1)").unwrap();
        let res = runtime.eval(form, env).unwrap();
        assert_eq!(*runtime.deref(res).unwrap(), Object::Int(43));
    }

    #[test]
    fn test_lambda() {
        let mut runtime = Runtime::new();
        let form = runtime.read_str("((fn (x) x) 42)").unwrap();
        std::println!("{}", runtime);
        let res = runtime.eval(form, NIL).unwrap();
        let res = *runtime.deref(res).unwrap();
        assert_eq!(res, Object::Int(42));
    }
}
