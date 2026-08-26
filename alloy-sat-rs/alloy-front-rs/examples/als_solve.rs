//! Native CLI: parse and solve an .als file entirely in Rust.
//!
//! Usage: cargo run -p alloy-front-rs --release --example als_solve -- \
//!          <file.als> [command-name | command-index]

use alloy_front_rs::{parse_module, run_command, CommandKind};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: als_solve <file.als> [command]");
        std::process::exit(2);
    }
    let text = match std::fs::read_to_string(&args[1]) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {}: {e}", args[1]);
            std::process::exit(2);
        }
    };
    let module = match parse_module(&text) {
        Ok(m) => m,
        Err(e) => {
            println!("Error\n  0. {e}");
            std::process::exit(1);
        }
    };
    let pick: Option<String> = args.get(2).cloned();
    for (i, cmd) in module.commands.iter().enumerate() {
        let name = match &cmd.kind {
            CommandKind::Run(n) => n.clone().unwrap_or_else(|| format!("run${}", i + 1)),
            CommandKind::Check(n) => n.clone().unwrap_or_else(|| format!("check${}", i + 1)),
        };
        let kind = if matches!(cmd.kind, CommandKind::Run(_)) {
            "run"
        } else {
            "check"
        };
        if let Some(p) = &pick {
            if p != &name && p.parse::<usize>().map(|k| k != i).unwrap_or(true) {
                continue;
            }
        }
        match run_command(&module, i) {
            Ok(sol) => {
                let tag = if sol.satisfiable { "SAT" } else { "UNSAT" };
                let models = if sol.satisfiable { "1/1" } else { "0" };
                println!("{i:02}. {kind:<6} {name:<20} {models} {tag}");
            }
            Err(e) => {
                println!("{i:02}. {kind:<6} {name:<20} !{e}");
            }
        }
    }
}
