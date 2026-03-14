use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <input.luac> [output.lua]", args[0]);
        eprintln!("       {} -              (read from stdin)", args[0]);
        process::exit(1);
    }

    let input_path = &args[1];
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

    let source = match luadec::decompile(&data) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    };

    if args.len() >= 3 {
        let output_path = &args[2];
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

