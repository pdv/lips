//! A `no_std` Arena allocator for Lips values.

use core::fmt;

// --- Public API ---

/// A handle to a value allocated in the Arena.
/// It consists of an index and a generation count to prevent use-after-free bugs.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Handle {
    index: u16,
    generation: u16,
}

impl fmt::Debug for Handle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "H({}:{})", self.index, self.generation)
    }
}

/// The canonical handle to the Nil value.
/// It points to the special, pre-allocated Nil object at index 0.
pub const NIL_HANDLE: Handle = Handle {
    index: 0,
    generation: 1,
};

/// An 8-byte, pointer-sized value.
/// It uses a bit-packing scheme to store either an immediate value (Nil, Int, Char)
/// or a Cons cell containing two Handles.
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct Value(u64);

/// The main arena allocator. Manages a fixed-size buffer of `Slot`s.
pub struct Arena<'a> {
    slots: &'a mut [Slot],
    free_list_head: Option<u16>,
}

// --- Value Implementation ---

const TAG_IMMEDIATE: u64 = 0xFFFFFFFF_00000000;
const MASK_IMMEDIATE_TYPE: u64 = 0x00000000_FF000000;

#[repr(u32)]
enum ImmediateType {
    Nil = 0,
    Int = 1,
    Char = 2,
}

impl Value {
    pub fn new_nil() -> Self {
        Value(TAG_IMMEDIATE | ((ImmediateType::Nil as u64) << 32))
    }

    pub fn new_int(n: i32) -> Self {
        Value(TAG_IMMEDIATE | ((ImmediateType::Int as u64) << 32) | (n as u32 as u64))
    }

    pub fn new_char(c: char) -> Self {
        Value(TAG_IMMEDIATE | ((ImmediateType::Char as u64) << 32) | (c as u32 as u64))
    }

    pub fn new_cons(car: Handle, cdr: Handle) -> Self {
        let car_u32 = (car.index as u32) << 16 | (car.generation as u32);
        let cdr_u32 = (cdr.index as u32) << 16 | (cdr.generation as u32);
        Value((car_u32 as u64) << 32 | (cdr_u32 as u64))
    }

    pub fn is_nil(&self) -> bool {
        self.0 == Self::new_nil().0
    }

    fn is_immediate(&self) -> bool {
        (self.0 >> 48) == 0xFFFF
    }

    pub fn is_cons(&self) -> bool {
        !self.is_immediate()
    }

    pub fn as_cons(&self) -> Option<(Handle, Handle)> {
        if self.is_cons() {
            let car_u32 = (self.0 >> 32) as u32;
            let cdr_u32 = self.0 as u32;
            let car = Handle {
                index: (car_u32 >> 16) as u16,
                generation: car_u32 as u16,
            };
            let cdr = Handle {
                index: (cdr_u32 >> 16) as u16,
                generation: cdr_u32 as u16,
            };
            Some((car, cdr))
        } else {
            None
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_immediate() {
            let imm_type = (self.0 & 0x0000_FFFF_0000_0000) >> 32;
            match imm_type {
                x if x == ImmediateType::Nil as u64 => write!(f, "Nil"),
                x if x == ImmediateType::Int as u64 => write!(f, "Int({})", self.0 as i32),
                x if x == ImmediateType::Char as u64 => {
                    write!(
                        f,
                        "Char('{}')",
                        char::from_u32(self.0 as u32).unwrap_or('?')
                    )
                }
                _ => write!(f, "Immediate(?)"),
            }
        } else {
            let (car, cdr) = self.as_cons().unwrap();
            write!(f, "Cons({:?}, {:?})", car, cdr)
        }
    }
}

// --- Arena Implementation ---

#[derive(Copy, Clone)]
union SlotData {
    value: Value,
    next_free: Option<u16>,
}

#[derive(Copy, Clone)]
pub struct Slot {
    data: SlotData,
    generation: u16,
}

impl Slot {
    pub const fn new() -> Self {
        Slot {
            data: SlotData { next_free: None },
            generation: 0,
        }
    }
}

#[derive(Debug)]
pub enum AllocError {
    OutOfMemory,
}

impl<'a> Arena<'a> {
    pub fn new(buffer: &'a mut [Slot]) -> Self {
        // Initialize all slots and build the free list
        for i in 0..buffer.len() {
            buffer[i] = Slot {
                generation: 0,
                data: SlotData {
                    next_free: Some((i + 1) as u16),
                },
            };
        }
        // The last slot terminates the list
        if !buffer.is_empty() {
            let last_idx = buffer.len() - 1;
            buffer[last_idx].data = SlotData { next_free: None };
        }

        let mut arena = Arena {
            slots: buffer,
            free_list_head: Some(1), // Slot 0 is reserved for Nil
        };

        // Allocate the canonical Nil value at index 0.
        let nil_slot = &mut arena.slots[0];
        nil_slot.generation = 1;
        nil_slot.data = SlotData {
            value: Value::new_nil(),
        };

        arena
    }

    pub fn alloc(&mut self, value: Value) -> Result<Handle, AllocError> {
        let free_index = self.free_list_head.ok_or(AllocError::OutOfMemory)?;

        let slot = &mut self.slots[free_index as usize];
        self.free_list_head = unsafe { slot.data.next_free };

        if slot.generation == u16::MAX {
            slot.generation = 1; // Wrap around, but skip 0
        } else {
            slot.generation += 1;
        }
        slot.data.value = value;

        Ok(Handle {
            index: free_index,
            generation: slot.generation,
        })
    }

    pub fn get(&self, handle: Handle) -> Option<&Value> {
        let slot = self.slots.get(handle.index as usize)?;
        if slot.generation == handle.generation {
            // Safety: If generation matches, we know `data` holds a `value`.
            Some(unsafe { &slot.data.value })
        } else {
            None // Stale handle
        }
    }

    pub fn free(&mut self, handle: Handle) -> bool {
        if let Some(slot) = self.slots.get_mut(handle.index as usize) {
            if slot.generation == handle.generation {
                slot.data.next_free = self.free_list_head;
                self.free_list_head = Some(handle.index);
                return true;
            }
        }
        false
    }
}
