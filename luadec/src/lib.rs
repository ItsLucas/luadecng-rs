//! # luadec
//!
//! A Lua 5.1 bytecode decompiler library.
//!
//! This crate takes compiled Lua 5.1 bytecode and produces readable Lua source code.
//!
//! ## Quick Start
//!
//! ```no_run
//! let bytecode = std::fs::read("input.luac").unwrap();
//! let source = luadec::decompile(&bytecode).unwrap();
//! println!("{}", source);
//! ```
//!
//! ## Advanced Usage
//!
//! For more control, use the [`lua51`] module directly:
//!
//! ```no_run
//! use luac_parser::lua_bytecode;
//! use luadec::lua51::lifter::Lifter;
//! use luadec::lua51::emit;
//!
//! let data = std::fs::read("input.luac").unwrap();
//! let (_, bytecode) = lua_bytecode(&data).unwrap();
//! let func = Lifter::decompile(&bytecode.main_chunk);
//! let source = emit::emit_chunk(&func);
//! ```

pub mod lua51;

/// Decompile Lua 5.1 bytecode into Lua source code.
///
/// Takes raw bytecode bytes (e.g. from a `.luac` file) and returns
/// the decompiled Lua source as a `String`.
///
/// # Errors
///
/// Returns an error string if the bytecode cannot be parsed.
///
/// # Example
///
/// ```no_run
/// let bytecode = std::fs::read("compiled.luac").unwrap();
/// let source = luadec::decompile(&bytecode).unwrap();
/// println!("{}", source);
/// ```
pub fn decompile(bytecode: &[u8]) -> Result<String, String> {
    let (_, bc) = luac_parser::lua_bytecode(bytecode)
        .map_err(|e| format!("failed to parse bytecode: {:?}", e))?;
    let func = lua51::lifter::Lifter::decompile(&bc.main_chunk);
    Ok(lua51::emit::emit_chunk(&func))
}
