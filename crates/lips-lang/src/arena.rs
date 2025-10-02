use core::fmt::Formatter;
use heapless::Vec;

const WORKSPACE_SIZE: usize = 1000;

// Bit layout for Object (u32):
// Bit 31:    Mark bit (GC)
// Bits 30-3: Payload (28 bits)
// Bits 2-0:  Type tag (3 bits)

const MARK_BIT: u32 = 1 << 31;
const TAG_MASK: u32 = 0x7;
const PAYLOAD_SHIFT: u32 = 3;

const TAG_CONS: u32 = 0;
const TAG_INT: u32 = 1;
const TAG_SYMBOL: u32 = 2;
const TAG_BUILTIN: u32 = 3;
const TAG_CHAR: u32 = 4;

// For cons cells: 14-bit car (bits 16-3) + 14-bit cdr (bits 30-17)
const PTR_MASK: u32 = 0x3FFF;
const CAR_SHIFT: u32 = 3;
const CDR_SHIFT: u32 = 17;

const NIL_PTR: u16 = 0x3FFF; // Max 14-bit value

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pointer(u16);

pub const NIL: Pointer = Pointer(NIL_PTR);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Object(u32);

impl Object {
    pub fn cons(car: Pointer, cdr: Pointer) -> Self {
        let payload = ((cdr.0 as u32) << CDR_SHIFT) | ((car.0 as u32) << CAR_SHIFT);
        Object(payload | TAG_CONS)
    }

    pub fn int(value: i32) -> Self {
        Object((((value << PAYLOAD_SHIFT) as u32) & !MARK_BIT) | TAG_INT)
    }

    pub fn symbol(index: u16) -> Self {
        Object(((index as u32) << PAYLOAD_SHIFT) | TAG_SYMBOL)
    }

    pub fn builtin(id: u8) -> Self {
        Object(((id as u32) << PAYLOAD_SHIFT) | TAG_BUILTIN)
    }

    pub fn char(ch: char) -> Self {
        Object(((ch as u32) << PAYLOAD_SHIFT) | TAG_CHAR)
    }

    // Type checking
    fn tag(&self) -> u32 {
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

    // Mark bit operations
    pub fn is_marked(&self) -> bool {
        (self.0 & MARK_BIT) != 0
    }

    pub fn mark(&mut self) {
        self.0 |= MARK_BIT;
    }

    pub fn unmark(&mut self) {
        self.0 &= !MARK_BIT;
    }

    // Decoders
    pub fn as_cons(&self) -> Option<(Pointer, Pointer)> {
        if self.is_cons() {
            let val = self.0 & !MARK_BIT;
            let car = Pointer(((val >> CAR_SHIFT) & PTR_MASK) as u16);
            let cdr = Pointer(((val >> CDR_SHIFT) & PTR_MASK) as u16);
            Some((car, cdr))
        } else {
            None
        }
    }

    pub fn as_int(&self) -> Option<i32> {
        if self.is_int() {
            // Mask mark bit, shift left to move bit 30->31, then arithmetic shift right
            // This sign-extends from bit 30 (the actual sign bit of our 28-bit value)
            let val = (self.0 & !MARK_BIT) as i32;
            Some((val << 1) >> (PAYLOAD_SHIFT + 1))
        } else {
            None
        }
    }

    pub fn as_symbol(&self) -> Option<u16> {
        if self.is_symbol() {
            Some(((self.0 & !MARK_BIT) >> PAYLOAD_SHIFT) as u16)
        } else {
            None
        }
    }

    pub fn as_builtin(&self) -> Option<u8> {
        if self.tag() == TAG_BUILTIN {
            Some(((self.0 & !MARK_BIT) >> PAYLOAD_SHIFT) as u8)
        } else {
            None
        }
    }

    pub fn as_char(&self) -> Option<char> {
        if self.tag() == TAG_CHAR {
            char::from_u32((self.0 & !MARK_BIT) >> PAYLOAD_SHIFT)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct Arena {
    workspace: Vec<Object, WORKSPACE_SIZE>,
    free: Pointer,
}

#[derive(Debug)]
pub enum Error {
    OutOfMemory,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            workspace: Vec::new(),
            free: NIL,
        }
    }

    pub fn deref(&self, ptr: Pointer) -> Option<Object> {
        if ptr == NIL {
            return None;
        }
        self.workspace.get(ptr.0 as usize).copied()
    }

    pub fn alloc(&mut self, cell: Object) -> Result<Pointer, Error> {
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
        if idx >= self.workspace.len() {
            return;
        }
        if self.workspace[idx].is_marked() {
            return;
        }
        self.workspace[idx].mark();
        if let Some((car, cdr)) = self.workspace[idx].as_cons() {
            self.mark(car);
            self.mark(cdr);
        }
    }

    pub fn gc(&mut self, env: Pointer) {
        for obj in self.workspace.iter_mut() {
            obj.unmark();
        }
        self.mark(env);
        for idx in 0..self.workspace.len() {
            if !self.workspace[idx].is_marked() {
                let freed = Pointer(idx as u16);
                self.workspace[idx] = Object::cons(freed, self.free);
                self.free = freed;
            }
        }
    }

    pub fn cell_count(&self) -> usize {
        self.workspace.len()
    }

    pub fn free_count(&self) -> usize {
        let mut count = 0;
        let mut ptr = self.free;
        while ptr != NIL {
            count += 1;
            if let Some(cell) = self.deref(ptr) {
                if let Some((_, cdr)) = cell.as_cons() {
                    ptr = cdr;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        count
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

        // Test larger values (28-bit)
        let cell = Object::int(1_000_000);
        assert_eq!(cell.as_int().unwrap(), 1_000_000);

        let cell = Object::int(-1_000_000);
        assert_eq!(cell.as_int().unwrap(), -1_000_000);
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

    #[test]
    fn test_mark_bit() {
        let mut cell = Object::int(42);
        assert!(!cell.is_marked());

        cell.mark();
        assert!(cell.is_marked());
        assert_eq!(cell.as_int().unwrap(), 42); // Value unchanged

        cell.unmark();
        assert!(!cell.is_marked());
        assert_eq!(cell.as_int().unwrap(), 42);
    }
}
