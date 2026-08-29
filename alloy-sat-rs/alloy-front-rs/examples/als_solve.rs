//! Native CLI: parse and solve an .als file entirely in Rust.
//!
//! Usage: cargo run -p alloy-front-rs --release --example als_solve -- \
//!          <file.als> [command-name | command-index] [--timing] [--help]

use alloy_front_rs::{parse_and_run_timed, parse_module, run_command, CommandKind};

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn print_usage() {
    eprintln!("als_solve {VERSION} — Alloy model solver (Rust native)");
    eprintln!();
    eprintln!("USAGE:");
    eprintln!("  als_solve <file.als> [command] [OPTIONS]");
    eprintln!();
    eprintln!("ARGS:");
    eprintln!("  <file.als>              .als model file to solve");
    eprintln!("  [command]               Run specific command by name or 0-based index");
    eprintln!();
    eprintln!("OPTIONS:");
    eprintln!("      --timing            Print per-phase timing (parse/lower/solve)");
    eprintln!("  -h, --help              Print this help message");
    eprintln!("  -V, --version           Print version");
}

fn fmt_dur(d: std::time::Duration) -> String {
    let us = d.as_micros();
    if us < 1000 {
        format!("{us} µs")
    } else if us < 1_000_000 {
        format!("{:.1} ms", us as f64 / 1000.0)
    } else {
        format!("{:.2} s", d.as_secs_f64())
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.iter().any(|a| a == "--help" || a == "-h") {
        print_usage();
        std::process::exit(0);
    }
    if args.iter().any(|a| a == "--version" || a == "-V") {
        println!("als_solve {VERSION}");
        std::process::exit(0);
    }

    if args.len() < 2 {
        print_usage();
        std::process::exit(2);
    }

    let timing = args.iter().any(|a| a == "--timing");
    let positional: Vec<&String> = args.iter().skip(1).filter(|a| !a.starts_with('-')).collect();

    let path = match positional.first() {
        Some(p) => p.as_str(),
        None => {
            eprintln!("error: no input file specified");
            eprintln!();
            print_usage();
            std::process::exit(2);
        }
    };
    let pick = positional.get(1).cloned();

    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {}: {e}", path);
            std::process::exit(2);
        }
    };

    if timing {
        let module = match parse_module(&text) {
            Ok(m) => m,
            Err(e) => {
                println!("Error\n  0. {e}");
                std::process::exit(1);
            }
        };
        let mut total_parse = std::time::Duration::ZERO;
        let mut total_lower = std::time::Duration::ZERO;
        let mut total_solve = std::time::Duration::ZERO;

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
                if **p != name && p.parse::<usize>().map(|k| k != i).unwrap_or(true) {
                    continue;
                }
            }
            let timed = parse_and_run_timed(&text, i);
            total_parse += timed.parse;
            total_lower += timed.lower;
            total_solve += timed.solve;
            match timed.solution {
                Ok(sol) => {
                    let tag = if sol.satisfiable { "SAT" } else { "UNSAT" };
                    let models = if sol.satisfiable { "1/1" } else { "0" };
                    println!(
                        "{i:02}. {kind:<6} {name:<20} {models} {tag}  parse={} lower={} solve={}",
                        fmt_dur(timed.parse),
                        fmt_dur(timed.lower),
                        fmt_dur(timed.solve),
                    );
                }
                Err(e) => {
                    println!("{i:02}. {kind:<6} {name:<20} !{e}");
                }
            }
        }
        println!(
            "--- total  parse={} lower={} solve={}",
            fmt_dur(total_parse),
            fmt_dur(total_lower),
            fmt_dur(total_solve),
        );
    } else {
        let module = match parse_module(&text) {
            Ok(m) => m,
            Err(e) => {
                println!("Error\n  0. {e}");
                std::process::exit(1);
            }
        };
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
                if **p != name && p.parse::<usize>().map(|k| k != i).unwrap_or(true) {
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
}
