# Gemini Workspace Documentation

This document provides an overview of the `lips` project, its structure, and how to work with its different components.

## Project Overview

`lips` is a Rust workspace that contains a custom language interpreter and its implementations for different targets. The core language logic is separated from the platform-specific code, allowing it to be used in a variety of environments, from a desktop REPL to embedded devices.

The workspace is composed of the following crates:

- `lips-lang`: The core language crate.
- `lips-repl`: A REPL (Read-Eval-Print Loop) for interacting with the language.
- `lips-embedded`: An implementation of the language for the micro:bit v2.
- `lips-stm`: An implementation of the language for the STM32L476RG microcontroller.

## Crate Details

### `lips-lang`

- **Purpose:** This crate contains the core logic of the `lips` language, including the parser, and interpreter. It is designed to be a portable library with minimal dependencies.
- **Path:** `crates/lips-lang`

### `lips-repl`

- **Purpose:** A command-line REPL for the `lips` language. This crate allows for interactive testing and development of `lips` programs on a desktop computer.
- **Path:** `crates/lips-repl`
- **To Run:** 
  ```sh
  cargo run -p lips-repl
  ```

### `lips-embedded`

- **Purpose:** An implementation of the `lips` language for the micro:bit v2. This crate demonstrates how to integrate the `lips-lang` core with an embedded platform.
- **Path:** `crates/lips-embedded`
- **To Build:**
  ```sh
  cargo build -p lips-embedded --target thumbv7em-none-eabihf 
  ```
  *(Note: Building for embedded targets may require installing the appropriate Rust target and other tools.)*

### `lips-stm`

- **Purpose:** An implementation of the `lips` language for the STM32L476RG microcontroller using the Embassy framework.
- **Path:** `crates/lips-stm`
- **To Build:**
  ```sh
  cargo build -p lips-stm --target thumbv7em-none-eabihf
  ```
  *(Note: Building for embedded targets may require installing the appropriate Rust target and other tools.)*
