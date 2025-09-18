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
        } else if let Some(free_slot) = self.slots.get_mut(self.free.index) {
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
        let slot = self
            .slots
            .get_mut(root.index as usize)
            .ok_or(Error::InvalidHandle)?;
        slot.marked = true;
        if let Cons(car, cdr) = slot.value {
            self.mark(*car)?;
            self.mark(*cdr)?;
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
