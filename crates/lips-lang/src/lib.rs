#![no_std]

use core::fmt::Debug;
use core::{
    fmt::{self, Write},
    str::Chars,
};

const WORKSPACE_SIZE: usize = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pointer(u16);

const NIL: Pointer = Pointer(u16::MAX);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Builtin {
    Def,
    Add,
    Sub,
    Lambda,
    If,
    Lt,
    Do,
    Let,
    Map,
    Print,
    Eq,
    And,
    Or,
    Not,
    Gc,
    Dump,
    Peek,
    Env,
}

impl TryFrom<&str> for Builtin {
    type Error = Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let function = match value {
            "def" => Self::Def,
            "+" => Self::Add,
            "-" => Self::Sub,
            "fn" => Self::Lambda,
            "if" => Self::If,
            "<" => Self::Lt,
            "do" => Self::Do,
            "let" => Self::Let,
            "map" => Self::Map,
            "print" => Self::Print,
            "=" => Self::Eq,
            "and" => Self::And,
            "or" => Self::Or,
            "not" => Self::Not,
            "gc" => Self::Gc,
            "dump" => Self::Dump,
            "peek" => Self::Peek,
            "env" => Self::Env,
            _ => return Err(Error::UnknownSymbol),
        };
        Ok(function)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Atom {
    Char(char),
    Int(i32),
    Builtin(Builtin),
    Identifier(u8),
}

impl TryFrom<&str> for Atom {
    type Error = Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if let Ok(n) = value.parse::<i32>() {
            Ok(Self::Int(n))
        } else if let Ok(builtin) = Builtin::try_from(value) {
            Ok(Self::Builtin(builtin))
        } else if let Some(id) = value.bytes().next() {
            Ok(Self::Identifier(id))
        } else {
            Err(Error::SyntaxError("invalid atom"))
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Object {
    Atom(Atom),
    Cons(Pointer, Pointer),
}

impl From<i32> for Object {
    fn from(value: i32) -> Self {
        Self::Atom(Atom::Int(value))
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Token<'a> {
    OpenParen,
    CloseParen,
    Quote,
    OpenDoubleQuote,
    CloseDoubleQuote,
    Symbol(&'a str),
}

struct Cursor<'a> {
    chars: Chars<'a>,
    in_quote: bool,
}

impl<'a> Cursor<'a> {
    fn new(input: &'a str) -> Self {
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

pub trait EffectHandler: Write + Debug + Sized {}

#[derive(Debug)]
pub struct Runtime<E: EffectHandler> {
    workspace: [Option<Object>; WORKSPACE_SIZE],
    marked: [bool; WORKSPACE_SIZE],
    env: Pointer,
    obj_count: u16,
    handler: E,
}

#[derive(Debug)]
pub enum Error {
    EndOfFile,
    NotFound(Pointer),
    OutOfMemory,
    NullPointer,
    UnknownSymbol,
    TypeError(&'static str),
    SyntaxError(&'static str),
    ArgCount,
    InvalidPointer,
    UseAfterFree,
    Handler(fmt::Error),
}

impl<E: EffectHandler> Runtime<E> {
    pub fn new(handler: E) -> Self {
        Runtime {
            workspace: [None; WORKSPACE_SIZE],
            marked: [false; WORKSPACE_SIZE],
            env: NIL,
            obj_count: 1,
            handler,
        }
    }
}

impl<E: EffectHandler> Runtime<E> {
    fn alloc(&mut self, obj: Object) -> Result<Pointer, Error> {
        for i in 0..self.workspace.len() {
            if self.workspace[i].is_none() {
                self.workspace[i] = Some(obj);
                self.obj_count += 1;
                return Ok(Pointer(i as u16));
            }
        }
        Err(Error::OutOfMemory)
    }

    fn deref(&self, pointer: Pointer) -> Result<Object, Error> {
        if pointer == NIL {
            return Err(Error::NullPointer);
        }
        self.workspace
            .get(pointer.0 as usize)
            .ok_or(Error::InvalidPointer)
            .copied()
            .transpose()
            .unwrap_or(Err(Error::UseAfterFree))
    }

    fn mark(&mut self, pointer: Pointer) {
        if pointer == NIL || self.marked[pointer.0 as usize] {
            return;
        }
        self.marked[pointer.0 as usize] = true;
        let Ok((car, cdr)) = self.split(pointer) else {
            return;
        };
        self.mark(car);
        self.mark(cdr);
    }

    fn gc(&mut self, env: Pointer) {
        self.marked.fill(false);
        self.mark(self.env);
        self.mark(env);
        for idx in 0..self.workspace.len() {
            if !self.marked[idx] && self.workspace[idx].is_some() {
                self.obj_count -= 1;
                self.workspace[idx] = None;
            }
        }
    }

    fn read_rest(&mut self, cursor: &mut Cursor) -> Result<Pointer, Error> {
        let head = self.read(cursor)?;
        if head == NIL {
            return Ok(NIL);
        }
        let tail = self.read_rest(cursor)?;
        self.cons(head, tail)
    }

    fn read(&mut self, cursor: &mut Cursor) -> Result<Pointer, Error> {
        let Some(Ok(token)) = cursor.next() else {
            return Err(Error::EndOfFile);
        };
        match token {
            Token::OpenParen => self.read_rest(cursor),
            Token::CloseParen => Ok(NIL),
            Token::Quote => {
                let quoted = self.read(cursor)?;
                self.cons(NIL, quoted)
            }
            Token::OpenDoubleQuote => {
                let Some(Ok(Token::Symbol(string))) = cursor.next() else {
                    return Err(Error::SyntaxError("expected string after double quote"));
                };
                let mut s = NIL;
                for c in string.chars().rev() {
                    let c = self.alloc(Object::Atom(Atom::Char(c)))?;
                    s = self.cons(c, s)?;
                }
                Ok(s)
            }
            Token::CloseDoubleQuote => Ok(NIL),
            Token::Symbol(s) => self.alloc(Object::Atom(s.try_into()?)),
        }
    }

    fn int(&mut self, n: i32) -> Result<Pointer, Error> {
        self.alloc(Object::Atom(Atom::Int(n)))
    }

    fn cons(&mut self, car: Pointer, cdr: Pointer) -> Result<Pointer, Error> {
        self.alloc(Object::Cons(car, cdr))
    }

    fn split(&self, pointer: Pointer) -> Result<(Pointer, Pointer), Error> {
        let Object::Cons(car, cdr) = self.deref(pointer)? else {
            return Err(Error::TypeError("trying to split atom"));
        };
        Ok((car, cdr))
    }

    fn car(&self, pointer: Pointer) -> Result<Pointer, Error> {
        let (car, _) = self.split(pointer)?;
        Ok(car)
    }

    fn cdr(&self, pointer: Pointer) -> Result<Pointer, Error> {
        let (_, cdr) = self.split(pointer)?;
        Ok(cdr)
    }

    fn first(&self, pointer: Pointer) -> Result<Pointer, Error> {
        self.car(pointer)
    }

    fn second(&self, pointer: Pointer) -> Result<Pointer, Error> {
        self.car(self.cdr(pointer)?)
    }

    fn third(&self, pointer: Pointer) -> Result<Pointer, Error> {
        self.car(self.cdr(self.cdr(pointer)?)?)
    }

    fn deref_int(&self, pointer: Pointer) -> Result<i32, Error> {
        let Object::Atom(Atom::Int(n)) = self.deref(pointer)? else {
            return Err(Error::TypeError("expected int"));
        };
        Ok(n)
    }

    fn lookup(&mut self, env: Pointer, id: u8) -> Result<Option<Pointer>, Error> {
        if env == NIL {
            return Ok(None);
        }
        let (entry, rest) = self.split(env)?;
        let (key, value) = self.split(entry)?;
        if self.deref(key)? == Object::Atom(Atom::Identifier(id)) {
            Ok(Some(value))
        } else {
            self.lookup(rest, id)
        }
    }

    fn builtin(&mut self, builtin: Builtin, args: Pointer, env: Pointer) -> Result<Pointer, Error> {
        use Builtin::*;
        match builtin {
            Def => {
                let key = self.first(args)?;
                let value = self.eval(self.second(args)?, env)?;
                let entry = self.cons(key, value)?;
                self.env = self.cons(entry, self.env)?;
                Ok(key)
            }
            Add => {
                let a = self.eval(self.first(args)?, env)?;
                let b = self.eval(self.second(args)?, env)?;
                self.int(self.deref_int(a)? + self.deref_int(b)?)
            }
            Sub => {
                let a = self.eval(self.first(args)?, env)?;
                let b = self.eval(self.second(args)?, env)?;
                self.int(self.deref_int(a)? - self.deref_int(b)?)
            }
            Lambda => {
                let params = self.first(args)?;
                let body = self.second(args)?;
                self.cons(params, body)
            }
            If => {
                let cond = self.eval(self.first(args)?, env)?;
                if cond != NIL {
                    self.eval(self.second(args)?, env)
                } else {
                    self.eval(self.third(args)?, env)
                }
            }
            Lt => {
                let a = self.eval(self.first(args)?, env)?;
                let b = self.eval(self.second(args)?, env)?;
                if self.deref_int(a)? < self.deref_int(b)? {
                    self.first(args)
                } else {
                    Ok(NIL)
                }
            }
            Do => {
                let times = self.eval(self.first(args)?, env)?;
                let body = self.second(args)?;
                let mut res = NIL;
                for _ in 0..self.deref_int(times)? {
                    res = self.apply(NIL, NIL, body, env)?;
                }
                Ok(res)
            }
            Map => {
                let function = self.eval(self.first(args)?, env)?;
                let (params, body) = self.split(function)?;
                let list = self.eval(self.second(args)?, env)?;
                self.map(params, body, list, env)
            }
            Let => {
                let mut bindings = self.first(args)?;
                let mut env = env;
                while bindings != NIL {
                    let (binding, rest) = self.split(bindings)?;
                    let key = self.first(binding)?;
                    let value = self.second(binding)?;
                    let evaled_value = self.eval(value, env)?;
                    let evaled_binding = self.cons(key, evaled_value)?;
                    env = self.cons(evaled_binding, env)?;
                    bindings = rest;
                }
                let body = self.second(args)?;
                self.eval(body, env)
            }
            Print => {
                let res = self.eval(self.first(args)?, env)?;
                self.pprint(res)?;
                self.write("\n")?;
                Ok(NIL)
            }
            Eq => {
                let a = self.eval(self.first(args)?, env)?;
                let b = self.eval(self.second(args)?, env)?;
                if self.deref(a)? == self.deref(b)? {
                    self.int(1) // TODO: true?
                } else {
                    Ok(NIL)
                }
            }
            And => {
                let a = self.eval(self.first(args)?, env)?;
                if a == NIL {
                    return Ok(NIL);
                }
                self.eval(self.second(args)?, env)
            }
            Or => {
                let a = self.eval(self.first(args)?, env)?;
                if a != NIL {
                    return Ok(a);
                }
                self.eval(self.second(args)?, env)
            }
            Not => {
                let a = self.eval(self.first(args)?, env)?;
                if a == NIL {
                    self.int(1)
                } else {
                    Ok(NIL)
                }
            }
            Dump => {
                for (idx, obj) in self.workspace.iter().enumerate() {
                    if let Some(obj) = obj {
                        writeln!(self.handler, "\r{}: {}", idx, obj).map_err(Error::Handler)?;
                    }
                }
                Ok(NIL)
            }
            Gc => {
                self.gc(env);
                Ok(NIL)
            }
            Env => Ok(self.env),
            Peek => {
                let a = self.eval(self.first(args)?, env)?;
                let p = Pointer(self.deref_int(a)? as u16);
                self.pprint(p)?;
                Ok(p)
            }
        }
    }

    fn map(
        &mut self,
        params: Pointer,
        body: Pointer,
        list: Pointer,
        env: Pointer,
    ) -> Result<Pointer, Error> {
        if list == NIL {
            return Ok(NIL);
        }
        let (arg, rest) = self.split(list)?;
        let args = self.cons(arg, NIL)?;
        let res = self.apply(params, args, body, env)?;
        let tail = self.map(params, body, rest, env)?;
        self.cons(res, tail)
    }

    fn apply(
        &mut self,
        params: Pointer,
        args: Pointer,
        body: Pointer,
        env: Pointer,
    ) -> Result<Pointer, Error> {
        let mut env = env;
        let mut params = params;
        let mut args = args;
        while params != NIL {
            if args == NIL {
                return Err(Error::ArgCount);
            }
            let param = self.car(params)?;
            let arg = self.eval(self.car(args)?, env)?;
            let assignment = self.cons(param, arg)?;
            env = self.cons(assignment, env)?;
            params = self.cdr(params)?;
            args = self.cdr(args)?;
        }
        self.eval(body, env)
    }

    fn eval(&mut self, form: Pointer, env: Pointer) -> Result<Pointer, Error> {
        if self.obj_count > self.workspace.len() as u16 - 100 {
            self.gc(env);
        }
        match self.deref(form)? {
            Object::Atom(atom) => match atom {
                Atom::Identifier(id) => self
                    .lookup(env, id)?
                    .or(self.lookup(self.env, id)?)
                    .ok_or(Error::NotFound(form)),
                _ => Ok(form),
            },
            Object::Cons(func, args) => {
                if func == NIL {
                    return Ok(args);
                }
                let func = self.eval(func, env)?;
                match self.deref(func)? {
                    Object::Atom(Atom::Char(_)) => Ok(form),
                    Object::Atom(Atom::Builtin(builtin)) => self.builtin(builtin, args, env),
                    Object::Cons(params, body) => self.apply(params, args, body, env),
                    _ => Err(Error::TypeError("eval")),
                }
            }
        }
    }

    fn write(&mut self, s: impl fmt::Display) -> Result<(), Error> {
        write!(&mut self.handler, "{}", s).map_err(Error::Handler)
    }
}

impl<E: EffectHandler> Runtime<E> {
    fn is_str(&self, pointer: Pointer) -> Result<bool, Error> {
        match self.deref(pointer) {
            Ok(Object::Atom(_)) => Ok(false),
            Ok(Object::Cons(car, _)) => match self.deref(car) {
                Ok(Object::Atom(Atom::Char(_))) => Ok(true),
                Ok(_) => Ok(false),
                Err(Error::NullPointer) => Ok(false),
                Err(e) => Err(e),
            },
            Err(Error::NullPointer) => Ok(false),
            Err(e) => Err(e),
        }
    }

    fn pprint_str(&mut self, s: Pointer) -> Result<(), Error> {
        let mut head = s;
        while head != NIL {
            let (first, rest) = self.split(head)?;
            let Object::Atom(Atom::Char(c)) = self.deref(first)? else {
                return Err(Error::TypeError("pprint_str expected string"));
            };
            self.write(c)?;
            head = rest;
        }
        Ok(())
    }

    pub fn pprint(&mut self, form: Pointer) -> Result<(), Error> {
        if form == NIL {
            return self.write("nil");
        }
        if self.is_str(form)? {
            return self.pprint_str(form);
        }
        match self.deref(form).unwrap() {
            Object::Atom(a) => self.write(a),
            Object::Cons(car, cdr) => {
                self.write("(")?;
                self.pprint(car)?;
                let mut head = cdr;
                while head != NIL {
                    self.write(" ")?;
                    if let Ok((car, cdr)) = self.split(head) {
                        self.pprint(car)?;
                        head = cdr;
                    } else {
                        self.pprint(head)?;
                    }
                }
                self.write(")")
            }
        }
    }

    pub fn eval_str(&mut self, form: &str) -> Result<Pointer, Error> {
        let mut cursor = Cursor::new(form);
        let form = self.read(&mut cursor)?;
        self.eval(form, NIL)
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Builtin(b) => write!(f, "{:?}", b),
            Atom::Identifier(x) => write!(f, "{}", *x as char),
            Atom::Int(n) => write!(f, "{}", n),
            Atom::Char(c) => write!(f, "{}", c),
        }
    }
}

impl fmt::Display for Pointer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self == &NIL {
            write!(f, "nil")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Atom(a) => write!(f, "{}", a),
            Object::Cons(car, cdr) => write!(f, "({} {})", car, cdr),
        }
    }
}

impl<E: EffectHandler> fmt::Display for Runtime<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, obj) in self.workspace.iter().enumerate() {
            if let Some(obj) = obj {
                writeln!(f, "\r{}: {}", idx, obj)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::string::String;
    use std::string::ToString;
    use std::vec::Vec;

    use super::*;

    #[derive(Debug)]
    struct TestEffectHandler {
        printed: Vec<String>,
    }

    impl TestEffectHandler {
        fn new() -> Self {
            Self {
                printed: Vec::new(),
            }
        }
    }

    impl Write for TestEffectHandler {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            self.printed.push(s.to_string());
            Ok(())
        }
    }

    impl EffectHandler for TestEffectHandler {}

    fn new_runtime() -> Runtime<TestEffectHandler> {
        let handler = TestEffectHandler::new();
        Runtime::new(handler)
    }

    #[test]
    fn test_lexer() {
        let cursor = Cursor::new("(+ 1 2)");
        let expected = [
            Token::OpenParen,
            Token::Symbol("+"),
            Token::Symbol("1"),
            Token::Symbol("2"),
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
            Token::Symbol("1"),
            Token::OpenParen,
            Token::Symbol("+"),
            Token::Symbol("2"),
            Token::Symbol("3"),
            Token::CloseParen,
            Token::CloseParen,
        ];
        for token in expected.into_iter() {
            assert_eq!(cursor.next().unwrap().unwrap(), token);
        }
    }

    fn assert_int(form: &str, expected: i32) {
        let mut runtime = new_runtime();
        let res = runtime.eval_str(form).unwrap();
        let res = runtime.deref(res).unwrap();
        assert_eq!(res, Object::Atom(Atom::Int(expected)));
    }

    #[test]
    fn test_nested() {
        assert_int("(+ (+ 1 2) (+ 3 4))", 10);
    }

    #[test]
    fn test_lambda() {
        assert_int("((fn (x) x) 42)", 42);
    }

    #[test]
    fn test_fn() {
        assert_int("((fn (x) (x 1)) (fn (x) x))", 1);
    }

    #[test]
    fn test_if() {
        assert_int("(if (< 99 0) 1 2)", 2);
        assert_int("(if 99 1 2)", 1);
    }

    #[test]
    fn test_math() {
        assert_int("(if (< 2 (- 8 3)) 1 4)", 1);
    }

    #[test]
    fn test_def() {
        let mut runtime = new_runtime();
        let _ = runtime.eval_str("(def x 2)").unwrap();
        let res = runtime.eval_str("(+ x 1)").unwrap();
        let res = runtime.deref(res).unwrap();
        assert_eq!(res, 3.into());
    }

    #[test]
    fn test_fib() {
        let mut runtime = new_runtime();
        let _ = runtime
            .eval_str("(def fib (fn (n) (if (< n 3) 1 (+ (fib (- n 1)) (fib (- n 2))))))")
            .unwrap();
        let res = runtime.eval_str("(fib 10)").unwrap();
        let res = runtime.deref(res).unwrap();
        assert_eq!(res, 55.into());
    }

    #[test]
    fn test_tco() {
        let mut runtime = new_runtime();
        let _ = runtime
            .eval_str("(def f (fn (n) (if (< n 3) 1 (f (- n 1)))))")
            .unwrap();
        let res = runtime.eval_str("(f 100)").unwrap();
        let res = runtime.deref(res).unwrap();
        assert_eq!(res, 1.into());
    }

    #[test]
    fn test_do() {
        let mut runtime = new_runtime();
        let _ = runtime.eval_str("(def x 0)").unwrap();
        let _ = runtime.eval_str("(do 5 (def x (+ x 1)))").unwrap();
        let res = runtime.eval_str("x").unwrap();
        let res = runtime.deref(res).unwrap();
        assert_eq!(res, 5.into());
    }
}
