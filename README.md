# luadec

A Lua 5.1 bytecode decompiler written in Rust.

**luadec** takes compiled Lua 5.1 bytecode (`.luac` files) and reconstructs readable Lua source code. It performs control-flow analysis, dominator-tree construction, loop detection, and liveness analysis to produce structured output with proper `if`/`elseif`/`while`/`for` constructs.

## Features

- Decompiles Lua 5.1 bytecode to readable Lua source
- Reconstructs control flow: `if`/`elseif`/`else`, `while`, `repeat`/`until`, numeric `for`, generic `for`
- Handles local variable recovery (with or without debug info)
- Supports varargs, closures, and table constructors
- Usable as a library or via the CLI tool

## Installation

### From Source

```sh
git clone <repo-url>
cd luadecng-rs
cargo build --release
```

The binary will be at `target/release/luadec`.

## Usage

### Command Line

```sh
# Decompile a .luac file and print to stdout
luadec input.luac

# Decompile and write to a file
luadec input.luac output.lua

# Read from stdin
cat input.luac | luadec -
```

### As a Library

Add `luadec-rust` to your `Cargo.toml`:

```toml
[dependencies]
luadec-rust = "1"
```

Simple usage:

```rust
let bytecode = std::fs::read("input.luac").unwrap();
let source = luadec::decompile(&bytecode).unwrap();
println!("{}", source);
```

For more control over the decompilation pipeline:

```rust
use luac_parser::lua_bytecode;
use luadec::lua51::lifter::Lifter;
use luadec::lua51::emit;

let data = std::fs::read("input.luac").unwrap();
let (_, bytecode) = lua_bytecode(&data).unwrap();

// Decompile to AST
let func = Lifter::decompile(&bytecode.main_chunk);

// Emit as Lua source
let source = emit::emit_chunk(&func);
```

## Project Structure

| Crate | Description |
|-------|-------------|
| `luadec-rust` | Core decompiler library. Exposes `luadec::decompile()` and the `lua51` module for fine-grained access. |
| `luadec-cli` | Command-line interface. Thin wrapper around the library. |

### Internal Modules (`luadec::lua51`)

| Module | Purpose |
|--------|---------|
| `opcodes` | Lua 5.1 opcode definitions |
| `instruction` | Instruction decoding and representation |
| `cfg` | Control-flow graph construction |
| `dominator` | Dominator tree and natural loop detection |
| `liveness` | Register liveness analysis |
| `ast` | AST node types for decompiled output |
| `lifter` | Bytecode → AST decompilation |
| `emit` | AST → Lua source code generation |

## Acknowledgments

The bytecode parser uses [luac-parser-rs](https://github.com/metaworm/luac-parser-rs) by [metaworm](https://github.com/metaworm). Thank you for the excellent work on Lua bytecode parsing.

## License

MIT
