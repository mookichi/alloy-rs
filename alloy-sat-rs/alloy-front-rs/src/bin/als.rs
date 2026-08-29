use std::process;

use alloy_front_rs::{parse_and_run_timed, parse_module, run_command, CommandKind};
use clap::Parser as ClapParser;

#[derive(ClapParser)]
#[command(name = "als", about = "Alloy model solver (Rust native)")]
struct Cli {
    /// .als file path (optional when using -c)
    file: Option<String>,

    /// Run inline Alloy code
    #[arg(short = 'c')]
    code: Option<String>,

    /// Evaluate expression after solving (wraps in `run { expr }`)
    #[arg(short = 'e')]
    eval: Option<String>,

    /// Print per-phase timing (parse/lower/solve)
    #[arg(long)]
    timing: bool,

    /// Run specific command by name or 0-based index
    command: Option<String>,
}

fn main() {
    let cli = Cli::parse();

    // Determine source text
    let (source, source_desc) = if let Some(code) = &cli.code {
        (code.clone(), "<-c>".to_string())
    } else if let Some(path) = &cli.file {
        match std::fs::read_to_string(path) {
            Ok(t) => (t, path.clone()),
            Err(e) => {
                eprintln!("cannot read {path}: {e}");
                process::exit(2);
            }
        }
    } else {
        eprintln!("usage: als <file.als> [-c \"code\"] [-e \"expr\"] [--timing] [command]");
        process::exit(2)
    };

    if cli.timing {
        run_with_timing(&source, &source_desc, &cli);
    } else {
        run_normal(&source, &source_desc, &cli);
    }
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

fn run_with_timing(source: &str, source_desc: &str, cli: &Cli) {
    let pick = cli.command.as_deref();
    let mut last_solution = None;
    let mut ran_any = false;
    let mut total_parse = std::time::Duration::ZERO;
    let mut total_lower = std::time::Duration::ZERO;
    let mut total_solve = std::time::Duration::ZERO;

    // Parse once to enumerate commands
    let module = match parse_module(source) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Error\n  0. {e}");
            process::exit(1);
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

        if let Some(p) = pick {
            if p != &name && p.parse::<usize>().map(|k| k != i).unwrap_or(true) {
                continue;
            }
        }

        ran_any = true;
        let timed = parse_and_run_timed(source, i);
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
                if sol.satisfiable {
                    if let Some(ref inst) = sol.instance {
                        println!("    {inst}");
                    }
                    if let Some(ref ti) = sol.temporal {
                        for (s, state) in ti.states().iter().enumerate() {
                            let tag = if s == ti.loop_state() { " (loop)" } else { "" };
                            println!("    state {s}{tag}: {state}");
                        }
                    }
                }
                last_solution = Some(sol);
            }
            Err(e) => {
                println!("{i:02}. {kind:<6} {name:<20} !{e}");
            }
        }
    }

    if ran_any {
        println!(
            "--- total  parse={} lower={} solve={}",
            fmt_dur(total_parse),
            fmt_dur(total_lower),
            fmt_dur(total_solve),
        );
    }

    if !ran_any && !module.commands.is_empty() {
        eprintln!("no matching command in {source_desc}");
        process::exit(1);
    }

    // -e: evaluate expression
    if let Some(expr_src) = &cli.eval {
        let eval_src = if let Some(code) = &cli.code {
            format!("{code}\nrun {{ {expr_src} }}")
        } else if let Some(path) = &cli.file {
            let orig = std::fs::read_to_string(path).unwrap_or_default();
            format!("{orig}\nrun {{ {expr_src} }}")
        } else {
            format!("run {{ {expr_src} }}")
        };

        let eval_idx = parse_module(&eval_src)
            .and_then(|m| {
                let idx = m.commands.len() - 1;
                Ok((m, idx))
            });

        match eval_idx {
            Ok((_, idx)) => {
                let timed = parse_and_run_timed(&eval_src, idx);
                match timed.solution {
                    Ok(sol) => {
                        let tag = if sol.satisfiable { "true" } else { "false" };
                        println!(
                            "eval: {tag}  parse={} lower={} solve={}",
                            fmt_dur(timed.parse),
                            fmt_dur(timed.lower),
                            fmt_dur(timed.solve),
                        );
                        if sol.satisfiable {
                            if let Some(ref inst) = sol.instance {
                                println!("    {inst}");
                            }
                        }
                        last_solution = Some(sol);
                    }
                    Err(e) => {
                        eprintln!("eval error: {e}");
                        process::exit(1);
                    }
                }
            }
            Err(e) => {
                eprintln!("eval parse error: {e}");
                process::exit(1);
            }
        }
    }

    match last_solution {
        Some(sol) if sol.satisfiable => process::exit(0),
        _ => process::exit(1),
    }
}

fn run_normal(source: &str, source_desc: &str, cli: &Cli) {
    // Parse
    let module = match parse_module(source) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Error\n  0. {e}");
            process::exit(1);
        }
    };

    // Run commands
    let pick = cli.command.as_deref();
    let mut last_solution = None;
    let mut ran_any = false;

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

        if let Some(p) = pick {
            if p != name && p.parse::<usize>().map(|k| k != i).unwrap_or(true) {
                continue;
            }
        }

        ran_any = true;
        match run_command(&module, i) {
            Ok(sol) => {
                let tag = if sol.satisfiable { "SAT" } else { "UNSAT" };
                let models = if sol.satisfiable { "1/1" } else { "0" };
                println!("{i:02}. {kind:<6} {name:<20} {models} {tag}");
                if sol.satisfiable {
                    if let Some(ref inst) = sol.instance {
                        println!("    {inst}");
                    }
                    if let Some(ref ti) = sol.temporal {
                        for (s, state) in ti.states().iter().enumerate() {
                            let tag = if s == ti.loop_state() { " (loop)" } else { "" };
                            println!("    state {s}{tag}: {state}");
                        }
                    }
                }
                last_solution = Some(sol);
            }
            Err(e) => {
                println!("{i:02}. {kind:<6} {name:<20} !{e}");
            }
        }
    }

    if !ran_any && module.commands.is_empty() && cli.eval.is_some() {
        // Nothing to solve, but we can still try eval
    } else if !ran_any && !module.commands.is_empty() {
        eprintln!("no matching command in {source_desc}");
        process::exit(1);
    }

    // -e: evaluate expression
    if let Some(expr_src) = &cli.eval {
        let eval_src = if let Some(code) = &cli.code {
            format!("{code}\nrun {{ {expr_src} }}")
        } else if let Some(path) = &cli.file {
            let orig = std::fs::read_to_string(path).unwrap_or_default();
            format!("{orig}\nrun {{ {expr_src} }}")
        } else {
            format!("run {{ {expr_src} }}")
        };

        let eval_module = match parse_module(&eval_src) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("eval parse error: {e}");
                process::exit(1);
            }
        };

        let eval_idx = eval_module.commands.len() - 1;
        match run_command(&eval_module, eval_idx) {
            Ok(sol) => {
                let tag = if sol.satisfiable { "true" } else { "false" };
                println!("eval: {tag}");
                if sol.satisfiable {
                    if let Some(ref inst) = sol.instance {
                        println!("    {inst}");
                    }
                }
                last_solution = Some(sol);
            }
            Err(e) => {
                eprintln!("eval error: {e}");
                process::exit(1);
            }
        }
    }

    match last_solution {
        Some(sol) if sol.satisfiable => process::exit(0),
        _ => process::exit(1),
    }
}
