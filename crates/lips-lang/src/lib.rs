#![no_std]

use core::fmt::{self, Debug};

use arena::{Arena, Cell, Pointer, NIL};
use heapless::String;
use lexer::{Cursor, Token};

mod arena;
mod lexer;

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Builtin {
    Def = 0,
    Defn = 1,
    Add = 2,
    Sub = 3,
    Mul = 4,
    Div = 5,
    Lambda = 6,
    If = 7,
    Lt = 8,
    Do = 9,
    Let = 10,
    Map = 11,
    Apply = 12,
    Eq = 13,
    And = 14,
    Or = 15,
    Not = 16,
    Gc = 17,
    Env = 18,
    Eval = 19,
    List = 20,
    Cons = 21,
    Car = 22,
    Cdr = 23,
    First = 24,
    Second = 25,
    Third = 26,
}

impl Builtin {
    fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::Def),
            1 => Some(Self::Defn),
            2 => Some(Self::Add),
            3 => Some(Self::Sub),
            4 => Some(Self::Mul),
            5 => Some(Self::Div),
            6 => Some(Self::Lambda),
            7 => Some(Self::If),
            8 => Some(Self::Lt),
            9 => Some(Self::Do),
            10 => Some(Self::Let),
            11 => Some(Self::Map),
            12 => Some(Self::Apply),
            13 => Some(Self::Eq),
            14 => Some(Self::And),
            15 => Some(Self::Or),
            16 => Some(Self::Not),
            17 => Some(Self::Gc),
            18 => Some(Self::Env),
            19 => Some(Self::Eval),
            20 => Some(Self::List),
            21 => Some(Self::Cons),
            22 => Some(Self::Car),
            23 => Some(Self::Cdr),
            24 => Some(Self::First),
            25 => Some(Self::Second),
            26 => Some(Self::Third),
            _ => None,
        }
    }

    fn to_u8(self) -> u8 {
        self as u8
    }
}

impl TryFrom<&str> for Builtin {
    type Error = Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let function = match value {
            "def" => Self::Def,
            "defn" => Self::Defn,
            "+" => Self::Add,
            "-" => Self::Sub,
            "*" => Self::Mul,
            "/" => Self::Div,
            "fn" => Self::Lambda,
            "if" => Self::If,
            "<" => Self::Lt,
            "do" => Self::Do,
            "let" => Self::Let,
            "map" => Self::Map,
            "apply" => Self::Apply,
            "=" => Self::Eq,
            "and" => Self::And,
            "or" => Self::Or,
            "not" => Self::Not,
            "gc" => Self::Gc,
            "env" => Self::Env,
            "eval" => Self::Eval,
            "list" => Self::List,
            "cons" => Self::Cons,
            "car" => Self::Car,
            "cdr" => Self::Cdr,
            "first" => Self::First,
            "second" => Self::Second,
            "third" => Self::Third,
            _ => return Err(Error::UnknownSymbol),
        };
        Ok(function)
    }
}

#[derive(Debug)]
pub struct Runtime {
    arena: Arena,
    symbol_buffer: String<1000>,
    env: Pointer,
}

#[derive(Debug)]
pub enum Error {
    Arena(arena::Error),
    EndOfFile,
    NotFound(Pointer),
    UnknownSymbol,
    TypeError(&'static str),
    SyntaxError(&'static str),
    ArgCount,
    InvalidPointer,
    UseAfterFree,
    Handler(fmt::Error),
    EndOfList,
    SymbolTableFull,
    InvalidSymbol,
}

impl Default for Runtime {
    fn default() -> Self {
        Self::new()
    }
}

impl Runtime {
    fn new() -> Self {
        Runtime {
            arena: Arena::new(),
            symbol_buffer: String::new(),
            env: NIL,
        }
    }

    fn alloc(&mut self, cell: Cell) -> Result<Pointer, Error> {
        self.arena.alloc(cell).map_err(Error::Arena)
    }

    fn deref(&self, pointer: Pointer) -> Result<Cell, Error> {
        self.arena.deref(pointer).ok_or(Error::InvalidPointer)
    }

    fn read_rest(&mut self, cursor: &mut Cursor) -> Result<Pointer, Error> {
        match self.read(cursor) {
            Ok(head) => {
                let tail = self.read_rest(cursor)?;
                self.cons(head, tail)
            }
            Err(Error::EndOfList) => Ok(NIL),
            e => e,
        }
    }

    fn read(&mut self, cursor: &mut Cursor) -> Result<Pointer, Error> {
        let Some(Ok(token)) = cursor.next() else {
            return Err(Error::EndOfFile);
        };
        match token {
            Token::OpenParen => self.read_rest(cursor),
            Token::CloseParen => Err(Error::EndOfList), // I do not like this
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
                    let c = self.alloc(Cell::char(c))?;
                    s = self.cons(c, s)?;
                }
                let _ = cursor.next(); // close quote
                Ok(s)
            }
            Token::CloseDoubleQuote => Err(Error::EndOfList),
            Token::Symbol(s) => {
                let cell = if let Ok(n) = s.parse::<i32>() {
                    Cell::int(n)
                } else if let Ok(builtin) = Builtin::try_from(s) {
                    Cell::builtin(builtin.to_u8())
                } else {
                    // Search for existing symbol in buffer
                    let mut offset = 0;
                    let buffer_bytes = self.symbol_buffer.as_bytes();
                    while offset < buffer_bytes.len() {
                        let start = offset;
                        while offset < buffer_bytes.len() && buffer_bytes[offset] != 0 {
                            offset += 1;
                        }
                        let symbol = core::str::from_utf8(&buffer_bytes[start..offset])
                            .map_err(|_| Error::InvalidSymbol)?;
                        if symbol == s {
                            return self.alloc(Cell::symbol(start as u16));
                        }
                        offset += 1; // skip null byte
                    }

                    // Symbol not found, add it
                    let new_offset = self.symbol_buffer.len() as u16;
                    self.symbol_buffer.push_str(s).map_err(|_| Error::SymbolTableFull)?;
                    self.symbol_buffer.push('\0').map_err(|_| Error::SymbolTableFull)?;
                    Cell::symbol(new_offset)
                };
                self.alloc(cell)
            }
        }
    }

    fn int(&mut self, n: i32) -> Result<Pointer, Error> {
        self.alloc(Cell::int(n))
    }

    fn cons(&mut self, car: Pointer, cdr: Pointer) -> Result<Pointer, Error> {
        self.alloc(Cell::cons(car, cdr))
    }

    fn split(&self, pointer: Pointer) -> Result<(Pointer, Pointer), Error> {
        let cell = self.deref(pointer)?;
        cell.as_cons().ok_or(Error::TypeError("trying to split atom"))
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

    pub fn deref_int(&self, pointer: Pointer) -> Result<i32, Error> {
        let cell = self.deref(pointer)?;
        cell.as_int().ok_or(Error::TypeError("expected int"))
    }

    fn lookup(&self, env: Pointer, id: u16) -> Result<Option<Pointer>, Error> {
        let mut head = env;
        while head != NIL {
            let (entry, rest) = self.split(head)?;
            let (key, value) = self.split(entry)?;
            let key_cell = self.deref(key)?;
            if let Some(key_id) = key_cell.as_symbol() {
                if key_id == id {
                    return Ok(Some(value));
                }
            }
            head = rest;
        }
        Ok(None)
    }

    fn eval_all(&mut self, list: Pointer, env: Pointer) -> Result<Pointer, Error> {
        if list == NIL {
            return Ok(NIL);
        }
        let (car, cdr) = self.split(list)?;
        let head = self.eval(car, env)?;
        let tail = self.eval_all(cdr, env)?;
        self.cons(head, tail)
    }

    fn builtin(&mut self, builtin: Builtin, args: Pointer, env: Pointer) -> Result<Pointer, Error> {
        use Builtin::*;
        match builtin {
            Def => {
                let key = self.first(args)?;
                let value = self.eval(self.second(args)?, env)?;
                let entry = self.cons(key, value)?;
                self.env = self.cons(entry, self.env)?;
                Ok(NIL)
            }
            Defn => {
                let key = self.first(args)?;
                let params = self.second(args)?;
                let body = self.cons(self.third(args)?, NIL)?;
                let function = self.cons(params, body)?;
                let entry = self.cons(key, function)?;
                self.env = self.cons(entry, self.env)?;
                Ok(NIL)
            }
            Add => {
                let mut sum = 0;
                let mut head = args;
                while head != NIL {
                    let (car, cdr) = self.split(head)?;
                    let arg = self.eval(car, env)?;
                    sum += self.deref_int(arg)?;
                    head = cdr;
                }
                self.int(sum)
            }
            Sub => {
                let a = self.eval(self.first(args)?, env)?;
                let b = self.eval(self.second(args)?, env)?;
                self.int(self.deref_int(a)? - self.deref_int(b)?)
            }
            Mul => {
                let mut product = 1;
                let mut head = args;
                while head != NIL {
                    let (car, cdr) = self.split(head)?;
                    let arg = self.eval(car, env)?;
                    product *= self.deref_int(arg)?;
                    head = cdr;
                }
                self.int(product)
            }
            Div => {
                let a = self.eval(self.first(args)?, env)?;
                let b = self.eval(self.second(args)?, env)?;
                self.int(self.deref_int(a)? / self.deref_int(b)?)
            }
            Lambda => {
                let params = self.first(args)?;
                let body = self.cons(self.second(args)?, NIL)?;
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
                let body = self.cons(self.second(args)?, NIL)?;
                let function = self.cons(NIL, body)?;
                let mut res = NIL;
                for _ in 0..self.deref_int(times)? {
                    res = self.apply(function, NIL, env)?;
                }
                Ok(res)
            }
            Map => {
                let function = self.eval(self.first(args)?, env)?;
                let list = self.eval(self.second(args)?, env)?;
                self.map(function, list, env)
            }
            Apply => {
                let function = self.eval(self.first(args)?, env)?;
                let args = self.eval(self.second(args)?, env)?;
                self.apply(function, args, env)
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
            Gc => {
                self.arena.gc(self.env);
                Ok(NIL)
            }
            Env => Ok(self.env),
            Eval => {
                let a = self.eval(self.first(args)?, env)?;
                self.eval(a, env)
            }
            List => self.eval_all(args, env),
            Cons => {
                let a = self.eval(self.first(args)?, env)?;
                let b = self.eval(self.second(args)?, env)?;
                self.cons(a, b)
            }
            Car => {
                let list = self.eval(self.first(args)?, env)?;
                self.car(list)
            }
            Cdr => {
                let list = self.eval(self.first(args)?, env)?;
                self.cdr(list)
            }
            First => {
                let list = self.eval(self.first(args)?, env)?;
                self.first(list)
            }
            Second => {
                let list = self.eval(self.first(args)?, env)?;
                self.second(list)
            }
            Third => {
                let list = self.eval(self.first(args)?, env)?;
                self.third(list)
            }
        }
    }

    fn map(&mut self, function: Pointer, list: Pointer, env: Pointer) -> Result<Pointer, Error> {
        if list == NIL {
            return Ok(NIL);
        }
        let (arg, rest) = self.split(list)?;
        let args = self.cons(arg, NIL)?;
        let res = self.apply(function, args, env)?;
        let tail = self.map(function, rest, env)?;
        self.cons(res, tail)
    }

    fn apply(&mut self, function: Pointer, args: Pointer, env: Pointer) -> Result<Pointer, Error> {
        let cell = self.deref(function)?;
        if let Some(builtin_id) = cell.as_builtin() {
            let builtin = Builtin::from_u8(builtin_id).ok_or(Error::TypeError("invalid builtin"))?;
            self.builtin(builtin, args, env)
        } else if let Some((params, body)) = cell.as_cons() {
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
            let body = self.car(body)?;
            self.eval(body, env)
        } else {
            Err(Error::TypeError("not a function"))
        }
    }

    fn eval(&mut self, form: Pointer, env: Pointer) -> Result<Pointer, Error> {
        let cell = self.deref(form)?;
        if let Some(id) = cell.as_symbol() {
            self.lookup(env, id)?
                .or(self.lookup(self.env, id)?)
                .ok_or(Error::NotFound(form))
        } else if let Some((func, args)) = cell.as_cons() {
            if func == NIL {
                return Ok(args);
            }
            let func = self.eval(func, env)?;
            let func_cell = self.deref(func)?;
            if func_cell.as_char().is_some() {
                Ok(form)
            } else {
                self.apply(func, args, env)
            }
        } else {
            Ok(form)
        }
    }

    fn write(writer: &mut impl fmt::Write, s: impl fmt::Display) -> Result<(), Error> {
        write!(writer, "{}", s).map_err(Error::Handler)
    }

    fn is_str(&self, pointer: Pointer) -> Result<bool, Error> {
        match self.deref(pointer) {
            Ok(cell) if cell.is_cons() => {
                let (car, _) = cell.as_cons().unwrap();
                match self.deref(car) {
                    Ok(car_cell) => Ok(car_cell.as_char().is_some()),
                    Err(Error::InvalidPointer) => Ok(false),
                    Err(e) => Err(e),
                }
            }
            Ok(_) => Ok(false),
            Err(Error::InvalidPointer) => Ok(false),
            Err(e) => Err(e),
        }
    }

    fn pprint_str(&self, writer: &mut impl fmt::Write, s: Pointer) -> Result<(), Error> {
        let mut head = s;
        while head != NIL {
            let (first, rest) = self.split(head)?;
            let cell = self.deref(first)?;
            let c = cell.as_char().ok_or(Error::TypeError("pprint_str expected string"))?;
            Self::write(writer, c)?;
            head = rest;
        }
        Ok(())
    }

    pub fn pprint(&self, writer: &mut impl fmt::Write, form: Pointer) -> Result<(), Error> {
        if form == NIL {
            return Self::write(writer, "nil");
        }
        if self.is_str(form)? {
            return self.pprint_str(writer, form);
        }
        let cell = self.deref(form).unwrap();
        if let Some(offset) = cell.as_symbol() {
            let buffer_bytes = self.symbol_buffer.as_bytes();
            let start = offset as usize;
            let mut end = start;
            while end < buffer_bytes.len() && buffer_bytes[end] != 0 {
                end += 1;
            }
            let symbol = core::str::from_utf8(&buffer_bytes[start..end])
                .map_err(|_| Error::InvalidSymbol)?;
            write!(writer, "{}", symbol).map_err(Error::Handler)
        } else if let Some(n) = cell.as_int() {
            write!(writer, "{}", n).map_err(Error::Handler)
        } else if let Some(builtin_id) = cell.as_builtin() {
            let builtin = Builtin::from_u8(builtin_id).ok_or(Error::TypeError("invalid builtin"))?;
            write!(writer, "{:?}", builtin).map_err(Error::Handler)
        } else if let Some(ch) = cell.as_char() {
            write!(writer, "{}", ch).map_err(Error::Handler)
        } else if let Some((car, cdr)) = cell.as_cons() {
            Self::write(writer, "(")?;
            self.pprint(writer, car)?;
            let mut head = cdr;
            while head != NIL {
                Self::write(writer, " ")?;
                if let Ok((car, cdr)) = self.split(head) {
                    self.pprint(writer, car)?;
                    head = cdr;
                } else {
                    Self::write(writer, ". ")?;
                    self.pprint(writer, head)?;
                    head = NIL;
                }
            }
            Self::write(writer, ")")
        } else {
            write!(writer, "unknown").map_err(Error::Handler)
        }
    }

    pub fn eval_str(&mut self, form: &str) -> Result<Pointer, Error> {
        let mut cursor = Cursor::new(form);
        let form = self.read(&mut cursor)?;
        self.eval(form, NIL)
    }
}

impl fmt::Display for Runtime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "==== ENV ====")?;
        let mut head = self.env;
        while head != NIL {
            let (entry, tail) = self.split(head).expect("invalid env entry");
            let (key, value) = self.split(entry).expect("invalid env entry");
            self.pprint(f, key).expect("writing key");
            write!(f, ": ")?;
            self.pprint(f, value).expect("writing value");
            writeln!(f)?;
            head = tail;
        }
        writeln!(f, "==== ARENA ====")?;
        write!(f, "{}", self.arena)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

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
        let mut runtime = Runtime::new();
        let res = runtime.eval_str(form).unwrap();
        let actual = runtime.deref_int(res).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_read_simple() {
        let mut runtime = Runtime::new();
        let mut cursor = Cursor::new("(+ 1 2)");
        let _form = runtime.read(&mut cursor).unwrap();
        // Just test that we can read it without crashing
    }

    #[test]
    fn test_eval_int() {
        let mut runtime = Runtime::new();
        let ptr = runtime.int(42).unwrap();
        let result = runtime.eval(ptr, NIL).unwrap();
        assert_eq!(runtime.deref_int(result).unwrap(), 42);
    }

    #[test]
    fn test_eval_builtin() {
        let mut runtime = Runtime::new();
        let mut cursor = Cursor::new("+");
        let ptr = runtime.read(&mut cursor).unwrap();
        let result = runtime.eval(ptr, NIL).unwrap();
        // Builtin should eval to itself
        assert_eq!(ptr, result);
    }

    #[test]
    fn test_eval_cons() {
        let mut runtime = Runtime::new();
        let mut cursor = Cursor::new("(+ 1 2)");
        let ptr = runtime.read(&mut cursor).unwrap();
        let _result = runtime.eval(ptr, NIL).unwrap();
    }

    #[test]
    fn test_simple_add() {
        assert_int("(+ 1 2)", 3);
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
        let mut runtime = Runtime::new();
        let _ = runtime.eval_str("(def x 2)").unwrap();
        let res = runtime.eval_str("(+ x 1)").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 3);
    }

    #[test]
    fn test_fib() {
        let mut runtime = Runtime::new();
        let _ = runtime
            .eval_str("(def fib (fn (n) (if (< n 3) 1 (+ (fib (- n 1)) (fib (- n 2))))))")
            .unwrap();
        let res = runtime.eval_str("(fib 10)").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 55);
    }

    #[test]
    fn test_tco() {
        let mut runtime = Runtime::new();
        let _ = runtime
            .eval_str("(def f (fn (n) (if (< n 3) 1 (f (- n 1)))))")
            .unwrap();
        let res = runtime.eval_str("(f 100)").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 1);
    }

    #[test]
    fn test_do() {
        let mut runtime = Runtime::new();
        let _ = runtime.eval_str("(def x 0)").unwrap();
        let _ = runtime.eval_str("(do 5 (def x (+ x 1)))").unwrap();
        let res = runtime.eval_str("x").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 5);
    }

    #[test]
    fn test_map_and_sum() {
        let mut runtime = Runtime::new();
        let _ = runtime
            .eval_str("(def sum (fn (lst) (if lst (+ (first lst) (sum (cdr lst))) 0)))")
            .unwrap();
        let _ = runtime.eval_str("(def double (fn (x) (* x 2)))").unwrap();
        let _ = runtime.eval_str("(def square (fn (x) (* x x)))").unwrap();

        let res = runtime.eval_str("(sum (map square (list 1 2 3 4)))").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 30);

        let res = runtime.eval_str("(sum (map double (list 5 10 15)))").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 60);
    }

    #[test]
    fn test_factorial_with_map() {
        let mut runtime = Runtime::new();
        let _ = runtime
            .eval_str("(def fact (fn (n) (if (< n 2) 1 (* n (fact (- n 1))))))")
            .unwrap();
        let _ = runtime
            .eval_str("(def sum (fn (lst) (if lst (+ (first lst) (sum (cdr lst))) 0)))")
            .unwrap();
        let _ = runtime.eval_str("(def double (fn (x) (* x 2)))").unwrap();

        let _ = runtime.eval_str("(def factorials (list (fact 3) (fact 4) (fact 5))))").unwrap();
        let res = runtime.eval_str("(sum (map double factorials))").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 300);
    }

    #[test]
    fn test_nested_let() {
        let mut runtime = Runtime::new();
        let res = runtime
            .eval_str("(let ((x 10) (y 20)) (+ (* x 2) (/ y 2)))")
            .unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 30);

        let _ = runtime.eval_str("(def double (fn (x) (* x 2)))").unwrap();
        let res = runtime
            .eval_str("(let ((nums (list 5 10 15))) (let ((doubled (map double nums))) (first doubled)))")
            .unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 10);
    }

    #[test]
    fn test_logical_operators() {
        let mut runtime = Runtime::new();

        let res = runtime.eval_str("(if (and (< 5 10) (not (= 3 4))) (+ 7 8) 0)").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 15);

        let res = runtime.eval_str("(if (or (< 100 50) (and (< 3 5) (< 7 9))) (+ 10 20) 0)").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 30);

        let res = runtime.eval_str("(if (and (< 10 5) (< 3 5)) 1 2)").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 2);

        let res = runtime.eval_str("(if (or (< 10 5) (< 10 5)) 1 2)").unwrap();
        assert_eq!(runtime.deref_int(res).unwrap(), 2);
    }
}
