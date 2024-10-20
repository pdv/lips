use core::{fmt::Formatter, u16};
use heapless::Vec;

const WORKSPACE_SIZE: usize = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pointer(u16);

pub const NIL: Pointer = Pointer(u16::MAX);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Object<T> {
    Atom(T),
    Cons(Pointer, Pointer),
}

#[derive(Debug)]
pub struct Arena<T> {
    workspace: Vec<Object<T>, WORKSPACE_SIZE>,
    marked: [bool; WORKSPACE_SIZE],
    free: Pointer,
}

#[derive(Debug)]
pub enum Error {
    OutOfMemory,
}

impl<T: Copy + core::fmt::Debug> Arena<T> {
    pub fn new() -> Self {
        Self {
            workspace: Vec::new(),
            marked: [false; WORKSPACE_SIZE],
            free: NIL,
        }
    }

    pub fn deref(&self, ptr: Pointer) -> Option<Object<T>> {
        self.workspace.get(ptr.0 as usize).copied()
    }

    pub fn alloc(&mut self, object: Object<T>) -> Result<Pointer, Error> {
        if self.free == NIL {
            self.workspace
                .push(object)
                .map_err(|_| Error::OutOfMemory)?;
            Ok(Pointer(self.workspace.len() as u16 - 1))
        } else {
            match self.deref(self.free) {
                Some(Object::Cons(car, cdr)) => {
                    self.workspace[self.free.0 as usize] = object;
                    self.free = cdr;
                    Ok(car)
                }
                _ => panic!("free is not cons"),
            }
        }
    }

    fn mark(&mut self, ptr: Pointer) {
        if ptr == NIL || self.marked[ptr.0 as usize] {
            return;
        }
        self.marked[ptr.0 as usize] = true;
        if let Some(Object::Cons(car, cdr)) = self.deref(ptr) {
            self.mark(car);
            self.mark(cdr);
        }
    }

    pub fn gc(&mut self, env: Pointer) {
        self.marked.fill(false);
        self.mark(env);
        for idx in 0..self.workspace.len() {
            if !self.marked[idx] {
                let freed = Pointer(idx as u16);
                self.workspace[idx] = Object::Cons(freed, self.free);
                self.free = freed;
            }
        }
    }
}

impl core::fmt::Display for Pointer {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self == &NIL {
            write!(f, "nil")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl<T: core::fmt::Display> core::fmt::Display for Object<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Object::Atom(a) => write!(f, "{}", a),
            Object::Cons(car, cdr) => write!(f, "({} {})", car, cdr),
        }
    }
}

impl<T: core::fmt::Display> core::fmt::Display for Arena<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        for (idx, obj) in self.workspace.iter().enumerate() {
            writeln!(f, "{}: {}", idx, obj)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc() {
        let mut arena = Arena::new();
        let a = arena.alloc(Object::Atom(1)).unwrap();
        let b = arena.alloc(Object::Atom(2)).unwrap();
        let c = arena.alloc(Object::Cons(a, b)).unwrap();
        match arena.deref(c).unwrap() {
            Object::Cons(car, _) => match arena.deref(car).unwrap() {
                Object::Atom(actual) => assert_eq!(actual, 1),
                _ => assert!(false),
            },
            _ => assert!(false),
        }
    }
}
