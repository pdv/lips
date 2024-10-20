#![no_std]

use core::{
    fmt::{self, Debug, Write},
    ops::Index,
    str::FromStr,
};

use arena::{Arena, Object, Pointer, NIL};
use heapless::{String, Vec};
use lexer::{Cursor, Token};

mod arena;
mod lexer;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Builtin {
    Def,
    Defn,
    Add,
    Sub,
    Mul,
    Div,
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
    Env,
    Eval,
    List,
    Cons,
    Car,
    Cdr,
    First,
    Second,
    Third,
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
            "print" => Self::Print,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Atom {
    Char(char),
    Int(i32),
    Builtin(Builtin),
    Identifier(u16),
}

pub trait EffectHandler: Write + Debug + Sized {}

#[derive(Debug)]
pub struct Runtime<E> {
    arena: Arena<Atom>,
    symbols: Vec<String<10>, 100>,
    env: Pointer,
    handler: E,
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

impl<E: EffectHandler> Runtime<E> {
    pub fn new(handler: E) -> Self {
        Runtime {
            arena: Arena::new(),
            symbols: Vec::new(),
            env: NIL,
            handler,
        }
    }

    fn alloc_inner(&mut self, object: Object<Atom>) -> Result<Pointer, Error> {
        self.arena.alloc(object).map_err(Error::Arena)
    }

    fn deref_inner(&self, pointer: Pointer) -> Result<Object<Atom>, Error> {
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
                    let c = self.alloc_inner(Object::Atom(Atom::Char(c)))?;
                    s = self.cons(c, s)?;
                }
                let _ = cursor.next(); // close quote
                Ok(s)
            }
            Token::CloseDoubleQuote => Err(Error::EndOfList),
            Token::Symbol(s) => {
                let atom = if let Ok(n) = s.parse::<i32>() {
                    Atom::Int(n)
                } else if let Ok(builtin) = Builtin::try_from(s) {
                    Atom::Builtin(builtin)
                } else {
                    if let Some(idx) = self.symbols.iter().position(|symbol| symbol.as_str() == s) {
                        Atom::Identifier(idx as u16)
                    } else {
                        let symbol = String::from_str(s).map_err(|_| Error::InvalidSymbol)?;
                        self.symbols
                            .push(symbol)
                            .map_err(|_| Error::SymbolTableFull)?;
                        Atom::Identifier(self.symbols.len() as u16 - 1)
                    }
                };
                self.alloc_inner(Object::Atom(atom))
            }
        }
    }

    fn int(&mut self, n: i32) -> Result<Pointer, Error> {
        self.alloc_inner(Object::Atom(Atom::Int(n)))
    }

    fn cons(&mut self, car: Pointer, cdr: Pointer) -> Result<Pointer, Error> {
        self.alloc_inner(Object::Cons(car, cdr))
    }

    fn split(&self, pointer: Pointer) -> Result<(Pointer, Pointer), Error> {
        let Object::Cons(car, cdr) = self.deref_inner(pointer)? else {
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
        let Object::Atom(Atom::Int(n)) = self.deref_inner(pointer)? else {
            return Err(Error::TypeError("expected int"));
        };
        Ok(n)
    }

    fn lookup(&mut self, env: Pointer, id: u16) -> Result<Option<Pointer>, Error> {
        if env == NIL {
            return Ok(None);
        }
        let (entry, rest) = self.split(env)?;
        let (key, value) = self.split(entry)?;
        if self.deref_inner(key)? == Object::Atom(Atom::Identifier(id)) {
            Ok(Some(value))
        } else {
            self.lookup(rest, id)
        }
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
                let body = self.third(args)?;
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
                if self.deref_inner(a)? == self.deref_inner(b)? {
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
        match self.deref_inner(form)? {
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
                match self.deref_inner(func)? {
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
        match self.deref_inner(pointer) {
            Ok(Object::Atom(_)) => Ok(false),
            Ok(Object::Cons(car, _)) => match self.deref_inner(car) {
                Ok(Object::Atom(Atom::Char(_))) => Ok(true),
                Ok(_) => Ok(false),
                Err(Error::InvalidPointer) => Ok(false),
                Err(e) => Err(e),
            },
            Err(Error::InvalidPointer) => Ok(false),
            Err(e) => Err(e),
        }
    }

    fn pprint_str(&mut self, s: Pointer) -> Result<(), Error> {
        let mut head = s;
        while head != NIL {
            let (first, rest) = self.split(head)?;
            let Object::Atom(Atom::Char(c)) = self.deref_inner(first)? else {
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
        match self.deref_inner(form).unwrap() {
            Object::Atom(a) => match a {
                Atom::Identifier(id) => {
                    let symbol = self.symbols.get(id as usize).ok_or(Error::UnknownSymbol)?;
                    write!(&mut self.handler, "{}", symbol).map_err(Error::Handler)
                }
                _ => self.write(a),
            },
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
                        self.write(". ")?;
                        self.pprint(head)?;
                        head = NIL;
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
            Atom::Identifier(x) => write!(f, "{}", x),
            Atom::Int(n) => write!(f, "{}", n),
            Atom::Char(c) => write!(f, "{}", c),
        }
    }
}

impl<E: EffectHandler> fmt::Display for Runtime<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.arena)
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
        let res = runtime.deref_inner(res).unwrap();
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
        let res = runtime.deref_inner(res).unwrap();
        assert_eq!(res, Object::Atom(Atom::Int(3)));
    }

    #[test]
    fn test_fib() {
        let mut runtime = new_runtime();
        let _ = runtime
            .eval_str("(def fib (fn (n) (if (< n 3) 1 (+ (fib (- n 1)) (fib (- n 2))))))")
            .unwrap();
        let res = runtime.eval_str("(fib 10)").unwrap();
        let res = runtime.deref_inner(res).unwrap();
        assert_eq!(res, Object::Atom(Atom::Int(55)));
    }

    #[test]
    fn test_tco() {
        let mut runtime = new_runtime();
        let _ = runtime
            .eval_str("(def f (fn (n) (if (< n 3) 1 (f (- n 1)))))")
            .unwrap();
        let res = runtime.eval_str("(f 100)").unwrap();
        let res = runtime.deref_inner(res).unwrap();
        assert_eq!(res, Object::Atom(Atom::Int(1)));
    }

    #[test]
    fn test_do() {
        let mut runtime = new_runtime();
        let _ = runtime.eval_str("(def x 0)").unwrap();
        let _ = runtime.eval_str("(do 5 (def x (+ x 1)))").unwrap();
        let res = runtime.eval_str("x").unwrap();
        let res = runtime.deref_inner(res).unwrap();
        assert_eq!(res, Object::Atom(Atom::Int(5)));
    }
}
