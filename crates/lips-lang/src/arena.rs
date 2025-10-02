use core::fmt::Formatter;
use heapless::Vec;

const WORKSPACE_SIZE: usize = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pointer(u16);

// NIL must fit in 15 bits since cons cells use 15-bit pointers
pub const NIL: Pointer = Pointer(0x7FFF);

// Cell encoding: 32-bit tagged union
// Tag (2 bits): 00=Cons, 01=Int, 10=Symbol, 11=Atom
const TAG_CONS: u32 = 0b00;
const TAG_INT: u32 = 0b01;
const TAG_SYMBOL: u32 = 0b10;
const TAG_ATOM: u32 = 0b11;
const TAG_MASK: u32 = 0b11;

// Atom subtypes (3 bits when tag=11)
const ATOM_BUILTIN: u32 = 0b000;
const ATOM_CHAR: u32 = 0b001;
const ATOM_SUBTYPE_MASK: u32 = 0b111;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cell(u32);

impl Cell {
    // Constructors
    pub fn cons(car: Pointer, cdr: Pointer) -> Self {
        let car_bits = (car.0 as u32) << 17;
        let cdr_bits = (cdr.0 as u32) << 2;
        Cell(TAG_CONS | cdr_bits | car_bits)
    }

    pub fn int(value: i32) -> Self {
        // Encode 30-bit signed int
        let bits = ((value as u32) << 2) & 0xFFFF_FFFC;
        Cell(TAG_INT | bits)
    }

    pub fn symbol(index: u16) -> Self {
        let bits = (index as u32) << 2;
        Cell(TAG_SYMBOL | bits)
    }

    pub fn builtin(id: u8) -> Self {
        let subtype = ATOM_BUILTIN << 2;
        let value = (id as u32) << 5;
        Cell(TAG_ATOM | subtype | value)
    }

    pub fn char(ch: char) -> Self {
        let subtype = ATOM_CHAR << 2;
        let value = (ch as u32) << 5;
        Cell(TAG_ATOM | subtype | value)
    }

    // Decoders
    pub fn tag(&self) -> u32 {
        self.0 & TAG_MASK
    }

    pub fn is_cons(&self) -> bool {
        self.tag() == TAG_CONS
    }

    pub fn is_int(&self) -> bool {
        self.tag() == TAG_INT
    }

    pub fn is_symbol(&self) -> bool {
        self.tag() == TAG_SYMBOL
    }

    pub fn is_atom(&self) -> bool {
        self.tag() == TAG_ATOM
    }

    pub fn as_cons(&self) -> Option<(Pointer, Pointer)> {
        if self.is_cons() {
            let car = ((self.0 >> 17) & 0x7FFF) as u16;
            let cdr = ((self.0 >> 2) & 0x7FFF) as u16;
            Some((Pointer(car), Pointer(cdr)))
        } else {
            None
        }
    }

    pub fn as_int(&self) -> Option<i32> {
        if self.is_int() {
            // Extract 30-bit signed value
            let bits = (self.0 >> 2) & 0x3FFF_FFFF;
            // Sign extend from 30 bits to 32 bits
            let value = if bits & 0x2000_0000 != 0 {
                (bits | 0xC000_0000) as i32
            } else {
                bits as i32
            };
            Some(value)
        } else {
            None
        }
    }

    pub fn as_symbol(&self) -> Option<u16> {
        if self.is_symbol() {
            Some(((self.0 >> 2) & 0x3FFF_FFFF) as u16)
        } else {
            None
        }
    }

    pub fn atom_subtype(&self) -> Option<u32> {
        if self.is_atom() {
            Some((self.0 >> 2) & ATOM_SUBTYPE_MASK)
        } else {
            None
        }
    }

    pub fn as_builtin(&self) -> Option<u8> {
        if self.atom_subtype()? == ATOM_BUILTIN {
            Some(((self.0 >> 5) & 0x7F_FFFF) as u8)
        } else {
            None
        }
    }

    pub fn as_char(&self) -> Option<char> {
        if self.atom_subtype()? == ATOM_CHAR {
            let code = (self.0 >> 5) & 0x1F_FFFF;
            char::from_u32(code)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct Arena {
    workspace: Vec<Cell, WORKSPACE_SIZE>,
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

    pub fn deref(&self, ptr: Pointer) -> Option<Cell> {
        self.workspace.get(ptr.0 as usize).copied()
    }

    pub fn alloc(&mut self, cell: Cell) -> Result<Pointer, Error> {
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
        if ptr == NIL || self.marked[ptr.0 as usize] {
            return;
        }
        self.marked[ptr.0 as usize] = true;
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
                self.workspace[idx] = Cell::cons(freed, self.free);
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

impl core::fmt::Display for Cell {
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
        let a = arena.alloc(Cell::int(1)).unwrap();
        let b = arena.alloc(Cell::int(2)).unwrap();
        let c = arena.alloc(Cell::cons(a, b)).unwrap();
        let cell = arena.deref(c).unwrap();
        assert!(cell.is_cons());
        let (car, _) = cell.as_cons().unwrap();
        let car_cell = arena.deref(car).unwrap();
        assert_eq!(car_cell.as_int().unwrap(), 1);
    }

    #[test]
    fn test_int() {
        let cell = Cell::int(42);
        assert_eq!(cell.as_int().unwrap(), 42);

        let cell = Cell::int(-42);
        assert_eq!(cell.as_int().unwrap(), -42);
    }

    #[test]
    fn test_cons() {
        let cell = Cell::cons(Pointer(10), Pointer(20));
        let (car, cdr) = cell.as_cons().unwrap();
        assert_eq!(car, Pointer(10));
        assert_eq!(cdr, Pointer(20));

        // Test cons with different values
        let cell = Cell::cons(Pointer(0), Pointer(1));
        let (car, cdr) = cell.as_cons().unwrap();
        assert_eq!(car, Pointer(0));
        assert_eq!(cdr, Pointer(1));

        // Test cons with NIL
        let cell = Cell::cons(Pointer(5), NIL);
        let (car, cdr) = cell.as_cons().unwrap();
        assert_eq!(car, Pointer(5));
        assert_eq!(cdr, NIL);
    }

    #[test]
    fn test_atoms() {
        let cell = Cell::symbol(100);
        assert_eq!(cell.as_symbol().unwrap(), 100);

        let cell = Cell::builtin(5);
        assert_eq!(cell.as_builtin().unwrap(), 5);

        let cell = Cell::char('A');
        assert_eq!(cell.as_char().unwrap(), 'A');
    }
}
