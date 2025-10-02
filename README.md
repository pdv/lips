# Lips

A Lisp-like language in no_std Rust, inspired by [ulisp](https://github.com/technoblogy/ulisp)

## Usage

`cargo repl`

## Examples

### Quicksort

```lisp
(defn qsort (lst)
  (if (and lst (cdr lst))
    (let ((pivot (car lst))
          (tail (cdr lst)))
      (append
        (qsort (filter (fn (x) (< x pivot)) tail))
        (list pivot)
        (qsort (filter (fn (x) (not (< x pivot))) tail))))
    lst))

(qsort (list 3 1 2))
; => (1 2 3)
```

## Memory Layout

All values are encoded as 32-bit tagged cells:

```
Cons (tag 000):
┌───┬─────────────────┬─────────────────┬─────┐
│ M │  cdr (14 bits)  │  car (14 bits)  │ 000 │
└───┴─────────────────┴─────────────────┴─────┘
 31  30             17  16             3   2 0

Int (tag 001):
┌───┬───────────────────────────────────┬─────┐
│ M │     signed integer (28 bits)      │ 001 │
└───┴───────────────────────────────────┴─────┘
 31  30                                3   2 0

Symbol (tag 010):
┌───┬───────────────────────────────────┬─────┐
│ M │      symbol index (28 bits)       │ 010 │
└───┴───────────────────────────────────┴─────┘
 31  30                                3   2 0

Builtin (tag 011):
┌───┬───────────────────────────────────┬─────┐
│ M │       builtin id (28 bits)        │ 011 │
└───┴───────────────────────────────────┴─────┘
 31  30                                3   2 0

Char (tag 100):
┌───┬───────────────────────────────────┬─────┐
│ M │      unicode char (28 bits)       │ 100 │
└───┴───────────────────────────────────┴─────┘
 31  30                                3   2 0
```

- **M**: Mark bit for garbage collection (bit 31)
- Pointers are 14-bit indices into arena (max 16,384 cells)
- NIL represented as max pointer value `0x3FFF`
- Symbol table: null-terminated strings in flat buffer
