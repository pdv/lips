#![no_std]
extern crate alloc;

mod arena;
mod arena2;

#[derive(Copy, Clone, Debug)]
struct Handle {
    index: u16,
    generation: u16,
}

#[derive(Copy, Clone, Debug)]
enum Value {
    Int(i32),
    Char(char),
    Cons(Handle, Handle),
}

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
