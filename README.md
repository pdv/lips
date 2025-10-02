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
