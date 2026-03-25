use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::process;

use luac_parser::{lua_bytecode, LuaChunk};
use luadec_rust::lua51::cfg::ControlFlowGraph;
use luadec_rust::lua51::emit;
use luadec_rust::lua51::instruction::Instruction;
use luadec_rust::lua51::lifter::Lifter;

#[derive(Default)]
struct DumpOptions {
    instructions: bool,
    cfg: bool,
    ast: bool,
    source: bool,
}

impl DumpOptions {
    fn any(&self) -> bool {
        self.instructions || self.cfg || self.ast || self.source
    }

    fn enable_all(&mut self) {
        self.instructions = true;
        self.cfg = true;
        self.ast = true;
        self.source = true;
    }
}

fn print_usage(program: &str) {
    eprintln!("Usage: {} [--dump-instructions] [--dump-cfg] [--dump-ast] [--dump-source] <input.luac> [output.lua]", program);
    eprintln!("       {} --dump-all <input.luac>", program);
    eprintln!("       {} -              (read from stdin)", program);
}

fn dump_instructions(label: &str, chunk: &LuaChunk) {
    println!("== Instructions: {label} ==");
    println!(
        "params={} upvalues={} max_stack={} prototypes={}",
        chunk.num_params,
        chunk.num_upvalues,
        chunk.max_stack,
        chunk.prototypes.len()
    );
    for (pc, raw) in chunk.instructions.iter().copied().enumerate() {
        match Instruction::decode(raw) {
            Some(inst) => println!("[{pc:4}] {inst}"),
            None => println!("[{pc:4}] <invalid: {raw:#010x}>"),
        }
    }
    println!();

    for (idx, proto) in chunk.prototypes.iter().enumerate() {
        dump_instructions(&format!("{label}/closure[{idx}]"), proto);
    }
}

fn dump_cfg(label: &str, chunk: &LuaChunk) {
    let cfg = ControlFlowGraph::build(&chunk.instructions);
    println!("== CFG: {label} ==");
    println!("{cfg}");

    for (idx, proto) in chunk.prototypes.iter().enumerate() {
        dump_cfg(&format!("{label}/closure[{idx}]"), proto);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage(&args[0]);
        process::exit(1);
    }

    let mut dump = DumpOptions::default();
    let mut positional = Vec::new();

    for arg in args.iter().skip(1) {
        match arg.as_str() {
            "--dump-instructions" => dump.instructions = true,
            "--dump-cfg" => dump.cfg = true,
            "--dump-ast" => dump.ast = true,
            "--dump-source" => dump.source = true,
            "--dump-all" => dump.enable_all(),
            "-h" | "--help" => {
                print_usage(&args[0]);
                return;
            }
            _ => positional.push(arg.as_str()),
        }
    }

    if positional.is_empty() {
        print_usage(&args[0]);
        process::exit(1);
    }

    if dump.any() && positional.len() > 1 {
        eprintln!("Error: output path is not supported with dump flags");
        process::exit(1);
    }

    if positional.len() > 2 {
        print_usage(&args[0]);
        process::exit(1);
    }

    let input_path = positional[0];
    let data = if input_path == "-" {
        let mut buf = Vec::new();
        io::stdin().read_to_end(&mut buf).unwrap_or_else(|e| {
            eprintln!("Error reading stdin: {}", e);
            process::exit(1);
        });
        buf
    } else {
        fs::read(input_path).unwrap_or_else(|e| {
            eprintln!("Error reading '{}': {}", input_path, e);
            process::exit(1);
        })
    };

    if dump.any() {
        let (_, bc) = lua_bytecode(&data).unwrap_or_else(|e| {
            eprintln!("Error: failed to parse bytecode: {:?}", e);
            process::exit(1);
        });

        let func = Lifter::decompile(&bc.main_chunk);

        if dump.instructions {
            dump_instructions("main", &bc.main_chunk);
        }

        if dump.cfg {
            dump_cfg("main", &bc.main_chunk);
        }

        if dump.ast {
            println!("== AST ==");
            println!("{func:#?}");
            println!();
        }

        if dump.source {
            println!("== Source ==");
            println!("{}", emit::emit_chunk(&func));
        }

        return;
    }

    let source = match luadec_rust::decompile(&data) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    };

    if positional.len() >= 2 {
        let output_path = positional[1];
        fs::write(output_path, &source).unwrap_or_else(|e| {
            eprintln!("Error writing '{}': {}", output_path, e);
            process::exit(1);
        });
        eprintln!("Decompiled to '{}'", output_path);
    } else {
        io::stdout().write_all(source.as_bytes()).unwrap_or_else(|e| {
            eprintln!("Error writing output: {}", e);
            process::exit(1);
        });
    }
}

