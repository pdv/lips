use crate::arena2::Value::Cons;
use heapless::Vec;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Handle {
    index: u16,
    generation: u16,
}

const NIL: Handle = Handle {
    index: 0,
    generation: 0,
};

#[derive(Copy, Clone, Debug)]
enum Value {
    Int(i32),
    Char(char),
    Cons(Handle, Handle),
}

impl Value {
    fn car(&self) -> Result<Handle> {
        match self {
            Cons(car, _) => Ok(*car),
            _ => Err(Error::TypeError),
        }
    }

    fn cdr(&self) -> Result<Handle> {
        match self {
            Cons(_, car) => Ok(*car),
            _ => Err(Error::TypeError),
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct Slot {
    generation: u16,
    marked: bool,
    value: Value,
}

#[derive(Debug)]
struct Arena {
    slots: Vec<Slot, 100>,
    free: Handle,
}

impl Arena {
    fn new() -> Self {
        Self {
            slots: Vec::new(),
            free: NIL,
        }
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
enum Error {
    OutOfMemory,
    TypeError,
    InvalidHandle,
}

type Result<T> = core::result::Result<T, Error>;

impl Arena {
    fn alloc(&mut self, value: Value) -> Result<Handle> {
        if self.free == NIL {
            self.slots
                .push(Slot {
                    generation: 1,
                    marked: false,
                    value,
                })
                .map_err(|_| Error::OutOfMemory)?;
            Ok(Handle {
                generation: 1,
                index: self.slots.len() as u16 - 1,
            })
        } else if let Some(free_slot) = self.slots.get_mut(self.free.index as usize) {
            let index = self.free.index;
            self.free = free_slot.value.cdr()?;
            free_slot.value = value;
            free_slot.generation += 1;
            Ok(Handle {
                generation: free_slot.generation,
                index,
            })
        } else {
            Err(Error::OutOfMemory)
        }
    }

    fn get(&self, handle: Handle) -> Option<&Value> {
        let slot = self.slots.get(handle.index as usize)?;
        if slot.generation == handle.generation {
            Some(&slot.value)
        } else {
            None
        }
    }

    fn mark(&mut self, root: Handle) -> Result<()> {
        let mut worklist: Vec<Handle, 100> = Vec::new();
        worklist.push(root).map_err(|_| Error::OutOfMemory)?;

        while let Some(handle) = worklist.pop() {
            let slot = self
                .slots
                .get_mut(handle.index as usize)
                .ok_or(Error::InvalidHandle)?;

            if slot.marked {
                continue;
            }

            slot.marked = true;

            if let Cons(car, cdr) = slot.value {
                if car != NIL {
                    worklist.push(car).map_err(|_| Error::OutOfMemory)?;
                }
                if cdr != NIL {
                    worklist.push(cdr).map_err(|_| Error::OutOfMemory)?;
                }
            }
        }
        Ok(())
    }

    fn sweep(&mut self) {
        for (index, slot) in self.slots.iter_mut().enumerate() {
            if !slot.marked {
                slot.value = Cons(NIL, self.free);
                self.free = Handle {
                    index: index as u16,
                    generation: slot.generation,
                }
            }
            slot.marked = false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc_and_get() {
        let mut arena = Arena::new();
        let h1 = arena.alloc(Value::Int(10)).unwrap();
        let h2 = arena.alloc(Value::Char('a')).unwrap();

        match arena.get(h1) {
            Some(Value::Int(10)) => (),
            _ => panic!("test_alloc_and_get failed: h1"),
        }

        match arena.get(h2) {
            Some(Value::Char('a')) => (),
            _ => panic!("test_alloc_and_get failed: h2"),
        }
    }

    #[test]
    fn test_out_of_memory() {
        let mut arena = Arena::new();
        for _ in 0..100 {
            arena.alloc(Value::Int(0)).unwrap();
        }
        match arena.alloc(Value::Int(0)) {
            Err(Error::OutOfMemory) => (),
            _ => panic!("test_out_of_memory failed"),
        }
    }

    #[test]
    fn test_gc_simple() {
        let mut arena = Arena::new();
        let _h1 = arena.alloc(Value::Int(10)).unwrap();
        let root = arena.alloc(Value::Int(20)).unwrap();

        // Mark and sweep
        arena.mark(root).unwrap();
        arena.sweep();

        // After GC, the slot for h1 should be on the free list.
        // The free list head should point to index 0 (h1's slot).
        assert_eq!(arena.free.index, 0);

        // Allocate again, it should reuse the slot from h1.
        let h3 = arena.alloc(Value::Int(30)).unwrap();
        assert_eq!(h3.index, 0);

        // The generation should be incremented.
        assert_eq!(h3.generation, 2);
    }

    #[test]
    fn test_gc_list() {
        let mut arena = Arena::new();
        let h1 = arena.alloc(Value::Int(10)).unwrap();
        let h2 = arena.alloc(Value::Cons(h1, NIL)).unwrap();
        let root = arena.alloc(Value::Cons(h2, NIL)).unwrap();

        // Mark and sweep with root.
        arena.mark(root).unwrap();
        arena.sweep();

        // Nothing should be on the free list.
        assert_eq!(arena.free, NIL);

        // Get all values
        assert!(arena.get(h1).is_some());
        assert!(arena.get(h2).is_some());
        assert!(arena.get(root).is_some());
    }

    #[test]
    fn test_gc_reclaims_unreachable() {
        let mut arena = Arena::new();
        let h1 = arena.alloc(Value::Int(10)).unwrap();
        let h2 = arena.alloc(Value::Cons(h1, NIL)).unwrap();
        let root = arena.alloc(Value::Cons(h2, NIL)).unwrap();

        // now, let's make h1 and h2 unreachable by only marking root's cdr (which is NIL)
        // but we will only mark root
        let dead_root = arena.alloc(Value::Int(100)).unwrap();

        arena.mark(root).unwrap();
        arena.sweep();

        // The slot for dead_root should be on the free list.
        assert_eq!(arena.free.index, dead_root.index);

        // The other handles should still be valid.
        assert!(arena.get(h1).is_some());
        assert!(arena.get(h2).is_some());
        assert!(arena.get(root).is_some());
    }
}
