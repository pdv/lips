use core::fmt::Formatter;
use heapless::Vec;

const WORKSPACE_SIZE: usize = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pointer(u16);

pub const NIL: Pointer = Pointer(0xFEFF);

const MARKER_INT: u16 = 0xFF00;
const MARKER_CHAR: u16 = 0xFF01;
const MARKER_SYMBOL: u16 = 0xFF02;
const MARKER_BUILTIN: u16 = 0xFF03;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Object(u16, u16);

impl Object {
    // Constructors
    pub fn cons(car: Pointer, cdr: Pointer) -> Self {
        Object(car.0, cdr.0)
    }

    pub fn int(value: i16) -> Self {
        Object(MARKER_INT, value as u16)
    }

    pub fn symbol(index: u16) -> Self {
        Object(MARKER_SYMBOL, index)
    }

    pub fn builtin(id: u8) -> Self {
        Object(MARKER_BUILTIN, id as u16)
    }

    pub fn char(ch: char) -> Self {
        Object(MARKER_CHAR, ch as u16)
    }

    // Type checking
    pub fn is_atom(&self) -> bool {
        self.0 >= MARKER_INT
    }

    pub fn is_cons(&self) -> bool {
        !self.is_atom()
    }

    pub fn is_int(&self) -> bool {
        self.0 == MARKER_INT
    }

    pub fn is_symbol(&self) -> bool {
        self.0 == MARKER_SYMBOL
    }

    // Decoders
    pub fn as_cons(&self) -> Option<(Pointer, Pointer)> {
        if self.is_cons() {
            Some((Pointer(self.0), Pointer(self.1)))
        } else {
            None
        }
    }

    pub fn as_int(&self) -> Option<i32> {
        if self.is_int() {
            Some(self.1 as i16 as i32)
        } else {
            None
        }
    }

    pub fn as_symbol(&self) -> Option<u16> {
        if self.is_symbol() {
            Some(self.1)
        } else {
            None
        }
    }

    pub fn as_builtin(&self) -> Option<u8> {
        if self.0 == MARKER_BUILTIN {
            Some(self.1 as u8)
        } else {
            None
        }
    }

    pub fn as_char(&self) -> Option<char> {
        if self.0 == MARKER_CHAR {
            char::from_u32(self.1 as u32)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct Arena {
    workspace: Vec<Object, WORKSPACE_SIZE>,
    marked: [bool; WORKSPACE_SIZE],
    free: Pointer,
    obj_count: usize,
}

#[derive(Debug)]
pub enum Error {
    OutOfMemory,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            workspace: Vec::new(),
            marked: [false; WORKSPACE_SIZE],
            free: NIL,
            obj_count: 0,
        }
    }

    pub fn deref(&self, ptr: Pointer) -> Option<Object> {
        if ptr == NIL {
            return None;
        }
        self.workspace.get(ptr.0 as usize).copied()
    }

    pub fn alloc(&mut self, cell: Object) -> Result<Pointer, Error> {
        self.obj_count += 1;
        if self.free == NIL {
            self.workspace.push(cell).map_err(|_| Error::OutOfMemory)?;
            Ok(Pointer(self.workspace.len() as u16 - 1))
        } else {
            match self.deref(self.free) {
                Some(freed_cell) if freed_cell.is_cons() => {
                    let (_car, cdr) = freed_cell.as_cons().unwrap();
                    let result = self.free;
                    self.workspace[self.free.0 as usize] = cell;
                    self.free = cdr;
                    Ok(result)
                }
                _ => panic!("free is not cons"),
            }
        }
    }

    fn mark(&mut self, ptr: Pointer) {
        if ptr == NIL {
            return;
        }
        let idx = ptr.0 as usize;
        if idx >= self.workspace.len() || self.marked[idx] {
            return;
        }
        self.marked[idx] = true;
        if let Some(cell) = self.deref(ptr) {
            if let Some((car, cdr)) = cell.as_cons() {
                self.mark(car);
                self.mark(cdr);
            }
        }
    }

    pub fn gc(&mut self, env: Pointer) {
        self.marked.fill(false);
        self.mark(env);
        for idx in 0..self.workspace.len() {
            if !self.marked[idx] {
                self.obj_count -= 1;
                let freed = Pointer(idx as u16);
                self.workspace[idx] = Object::cons(freed, self.free);
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

impl core::fmt::Display for Object {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Some((car, cdr)) = self.as_cons() {
            write!(f, "({} {})", car, cdr)
        } else if let Some(n) = self.as_int() {
            write!(f, "{}", n)
        } else if let Some(idx) = self.as_symbol() {
            write!(f, "sym:{}", idx)
        } else if let Some(id) = self.as_builtin() {
            write!(f, "builtin:{}", id)
        } else if let Some(ch) = self.as_char() {
            write!(f, "'{}'", ch)
        } else {
            write!(f, "unknown")
        }
    }
}

impl core::fmt::Display for Arena {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "{}/{}", self.obj_count, WORKSPACE_SIZE)?;
        for (idx, cell) in self.workspace.iter().enumerate() {
            if let Some((car, _)) = cell.as_cons() {
                if car.0 == idx as u16 {
                    continue;
                }
            }
            writeln!(f, "{}: {}", idx, cell)?;
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
        let a = arena.alloc(Object::int(1)).unwrap();
        let b = arena.alloc(Object::int(2)).unwrap();
        let c = arena.alloc(Object::cons(a, b)).unwrap();
        let cell = arena.deref(c).unwrap();
        assert!(cell.is_cons());
        let (car, _) = cell.as_cons().unwrap();
        let car_cell = arena.deref(car).unwrap();
        assert_eq!(car_cell.as_int().unwrap(), 1);
    }

    #[test]
    fn test_int() {
        let cell = Object::int(42);
        assert_eq!(cell.as_int().unwrap(), 42);

        let cell = Object::int(-42);
        assert_eq!(cell.as_int().unwrap(), -42);
    }

    #[test]
    fn test_cons() {
        let cell = Object::cons(Pointer(10), Pointer(20));
        let (car, cdr) = cell.as_cons().unwrap();
        assert_eq!(car, Pointer(10));
        assert_eq!(cdr, Pointer(20));

        // Test cons with different values
        let cell = Object::cons(Pointer(0), Pointer(1));
        let (car, cdr) = cell.as_cons().unwrap();
        assert_eq!(car, Pointer(0));
        assert_eq!(cdr, Pointer(1));

        // Test cons with NIL
        let cell = Object::cons(Pointer(5), NIL);
        let (car, cdr) = cell.as_cons().unwrap();
        assert_eq!(car, Pointer(5));
        assert_eq!(cdr, NIL);
    }

    #[test]
    fn test_atoms() {
        let cell = Object::symbol(100);
        assert_eq!(cell.as_symbol().unwrap(), 100);

        let cell = Object::builtin(5);
        assert_eq!(cell.as_builtin().unwrap(), 5);

        let cell = Object::char('A');
        assert_eq!(cell.as_char().unwrap(), 'A');
    }
}
