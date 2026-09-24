use std::process;

use alloy_front_rs::{
    check as build_check_cnf,
    display::{format_instance, format_query_value, query_exit_ok},
    parse_and_run_timed, parse_module,
    run as build_run_cnf,
    run_command, run_opt_command,
    snippet::{query_value, QueryValue},
    CnfKind, CommandKind, Instance, Module, Scope,
};

/// Print a solved instance with EReal decoding.
fn print_solution(inst: &Instance) {
    println!("    {}", format_instance(inst));
}

/// Query `-e` against an already-solved instance (`:query` semantics: no
/// re-solve, so the answer always belongs to the displayed solution).
/// Rebuilds the command's Cnf as query context (lowering scratch + int
/// bounds + bitwidth only). Returns the rendered value and whether the
/// process should exit 0 (`false` solely for `false` answers, mirroring
/// the old `run {expr}` UNSAT exit code so `-e` keeps working as a
/// scripted assertion).
fn query_last(
    module: &Module,
    idx: usize,
    kind: CnfKind,
    inst: &Instance,
    expr_src: &str,
) -> Result<(String, bool), alloy_front_rs::FrontError> {
    let cnf = match kind {
        CnfKind::Run => build_run_cnf(module, idx)?,
        _ => build_check_cnf(module, idx)?,
    };
    let scope = module
        .commands
        .get(idx)
        .map(|c| &c.scope)
        .ok_or_else(|| alloy_front_rs::FrontError::Resolve(format!("no command #{idx}")))?;
    let v: QueryValue = query_value(module, scope, &cnf, expr_src, inst)?;
    Ok((format_query_value(inst, &v), query_exit_ok(&v)))
}
use clap::Parser as ClapParser;

#[derive(ClapParser)]
#[command(name = "als", about = "Alloy model solver (Rust native)")]
struct Cli {
    /// .als file path (optional when using -c)
    file: Option<String>,

    /// Run inline Alloy code
    #[arg(short = 'c')]
    code: Option<String>,

    /// Query expression against the last solution (`:query`; falls back to
    /// `run { expr }` when no plain static solution exists). A `false`
    /// answer exits 1, so `-e` doubles as a scripted assertion.
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

/// Display name + kind word for a command (opt commands included).
fn command_label(cmd: &alloy_front_rs::Command, i: usize) -> (String, &'static str) {
    match &cmd.kind {
        CommandKind::Run(n) => (
            n.clone().unwrap_or_else(|| format!("run${}", i + 1)),
            "run",
        ),
        CommandKind::Check(n) => (
            n.clone().unwrap_or_else(|| format!("check${}", i + 1)),
            "check",
        ),
        CommandKind::Maximize { name: n, .. } => (
            n.clone().unwrap_or_else(|| format!("maximize${}", i + 1)),
            "maximize",
        ),
        CommandKind::Minimize { name: n, .. } => (
            n.clone().unwrap_or_else(|| format!("minimize${}", i + 1)),
            "minimize",
        ),
    }
}

fn is_opt_command(cmd: &alloy_front_rs::Command) -> bool {
    matches!(
        cmd.kind,
        CommandKind::Maximize { .. } | CommandKind::Minimize { .. }
    )
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


/// Give the trailing `-e` eval command the last executed command's scope so
/// ad-hoc evaluation solves under an identical profile (widths/atoms).
fn inherit_eval_scope(eval_module: &mut Module, scope: &Option<Scope>) {
    if let (Some(s), Some(cmd)) = (scope, eval_module.commands.last_mut()) {
        cmd.scope = s.clone();
    }
}

fn run_with_timing(source: &str, source_desc: &str, cli: &Cli) {
    let pick = cli.command.as_deref();
    let mut last_solution = None;
    let mut last_opt_sat = false;
    let mut ran_any = false;
    // Profile for `-e`: the last executed command's scope, so ad-hoc
    // evaluation solves under identical widths/atoms (same precedent as
    // REPL `:eval` inheriting the default Cnf's scope).
    let mut last_scope: Option<Scope> = None;
    // Target for `-e` query semantics: the last plain (non-opt) command
    // with a static satisfiable instance. Opt/temporal/UNSAT commands
    // clear it, falling back to `run {expr}`.
    let mut last_plain: Option<(usize, CnfKind, Instance)> = None;
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
        let (name, kind) = command_label(cmd, i);

        if let Some(p) = pick {
            if p != name && p.parse::<usize>().map(|k| k != i).unwrap_or(true) {
                continue;
            }
        }

        ran_any = true;
        last_scope = Some(module.commands[i].scope.clone());
        if is_opt_command(cmd) || alloy_front_rs::command_needs_opt(&module, i) {
            let t0 = std::time::Instant::now();
            let result = run_opt_command(&module, i);
            let dt = t0.elapsed();
            total_solve += dt;
            match result {
                Ok(sol) => {
                    let tag = if sol.satisfiable { "SAT" } else { "UNSAT" };
                    let models = if sol.satisfiable { "1/1" } else { "0" };
                    let cost = sol
                        .cost
                        .map(|c| format!(" cost={c}"))
                        .unwrap_or_default();
                    println!("{i:02}. {kind:<8} {name:<20} {models} {tag}{cost}  solve={}", fmt_dur(dt));
                    if let Some(ref inst) = sol.instance {
                        print_solution(inst);
                    }
                    if sol.satisfiable {
                        last_opt_sat = true;
                    }
                }
                Err(e) => {
                    println!("{i:02}. {kind:<8} {name:<20} !{e}");
                }
            }
            last_plain = None;
            continue;
        }
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
                        print_solution(inst);
                    }
                    if let Some(ref ti) = sol.temporal {
                        for (s, state) in ti.states().iter().enumerate() {
                            let tag = if s == ti.loop_state() { " (loop)" } else { "" };
                            println!("    state {s}{tag}: {state}");
                        }
                    }
                }
                last_plain = match (&sol.instance, &sol.temporal) {
                    (Some(inst), None) => {
                        let cnf_kind = match &cmd.kind {
                            CommandKind::Run(_) => CnfKind::Run,
                            _ => CnfKind::Check,
                        };
                        Some((i, cnf_kind, inst.clone()))
                    }
                    _ => None,
                };
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

    // -e: query against the last solution when one exists (`:query`
    // semantics: no re-solve), else solve `run {expr}` (`:eval` fallback).
    if let Some(expr_src) = &cli.eval {
        if let Some((idx, cnf_kind, ref inst)) = last_plain {
            let t0 = std::time::Instant::now();
            let q = query_last(&module, idx, cnf_kind, inst, expr_src);
            let dur = t0.elapsed();
            match q {
                Ok((rendered, ok)) => {
                    println!("query: {expr_src} = {rendered}  eval={}", fmt_dur(dur));
                    if !ok {
                        process::exit(1);
                    }
                }
                Err(e) => {
                    eprintln!("eval error: {e}");
                    process::exit(1);
                }
            }
        } else {
        let eval_src = if let Some(code) = &cli.code {
            format!("{code}\nrun {{ {expr_src} }}")
        } else if let Some(path) = &cli.file {
            let orig = std::fs::read_to_string(path).unwrap_or_default();
            format!("{orig}\nrun {{ {expr_src} }}")
        } else {
            format!("run {{ {expr_src} }}")
        };

        let t0 = std::time::Instant::now();
        let eval_parsed = parse_module(&eval_src).map(|mut m| {
            inherit_eval_scope(&mut m, &last_scope);
            m
        });
        let parse_dur = t0.elapsed();

        match eval_parsed {
            Ok(m) => {
                let idx = m.commands.len() - 1;
                let mut timed = alloy_front_rs::run_timed(&m, idx);
                timed.parse = parse_dur;
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
                                print_solution(inst);
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
        } // end fallback (no queryable solution)
    }

    match last_solution {
        Some(sol) if sol.satisfiable => process::exit(0),
        _ if last_opt_sat => process::exit(0),
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
    let mut last_opt_sat = false;
    let mut ran_any = false;
    // Profile for `-e`: the last executed command's scope, so ad-hoc
    // evaluation solves under identical widths/atoms (same precedent as
    // REPL `:eval` inheriting the default Cnf's scope).
    let mut last_scope: Option<Scope> = None;
    // Target for `-e` query semantics (see `run_with_timing`).
    let mut last_plain: Option<(usize, CnfKind, Instance)> = None;

    for (i, cmd) in module.commands.iter().enumerate() {
        let (name, kind) = command_label(cmd, i);

        if let Some(p) = pick {
            if p != name && p.parse::<usize>().map(|k| k != i).unwrap_or(true) {
                continue;
            }
        }

        ran_any = true;
        last_scope = Some(module.commands[i].scope.clone());
        if is_opt_command(cmd) || alloy_front_rs::command_needs_opt(&module, i) {
            match run_opt_command(&module, i) {
                Ok(sol) => {
                    let tag = if sol.satisfiable { "SAT" } else { "UNSAT" };
                    let models = if sol.satisfiable { "1/1" } else { "0" };
                    let cost = sol
                        .cost
                        .map(|c| format!(" cost={c}"))
                        .unwrap_or_default();
                    println!("{i:02}. {kind:<8} {name:<20} {models} {tag}{cost}");
                    if let Some(ref inst) = sol.instance {
                        print_solution(inst);
                    }
                    if sol.satisfiable {
                        last_opt_sat = true;
                    }
                }
                Err(e) => {
                    println!("{i:02}. {kind:<8} {name:<20} !{e}");
                }
            }
            last_plain = None;
            continue;
        }
        match run_command(&module, i) {
            Ok(sol) => {
                let tag = if sol.satisfiable { "SAT" } else { "UNSAT" };
                let models = if sol.satisfiable { "1/1" } else { "0" };
                println!("{i:02}. {kind:<6} {name:<20} {models} {tag}");
                if sol.satisfiable {
                    if let Some(ref inst) = sol.instance {
                        print_solution(inst);
                    }
                    if let Some(ref ti) = sol.temporal {
                        for (s, state) in ti.states().iter().enumerate() {
                            let tag = if s == ti.loop_state() { " (loop)" } else { "" };
                            println!("    state {s}{tag}: {state}");
                        }
                    }
                }
                last_plain = match (&sol.instance, &sol.temporal) {
                    (Some(inst), None) => {
                        let cnf_kind = match &cmd.kind {
                            CommandKind::Run(_) => CnfKind::Run,
                            _ => CnfKind::Check,
                        };
                        Some((i, cnf_kind, inst.clone()))
                    }
                    _ => None,
                };
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

    // -e: query against the last solution when one exists (`:query`
    // semantics: no re-solve), else solve `run {expr}` (`:eval` fallback).
    if let Some(expr_src) = &cli.eval {
        if let Some((idx, cnf_kind, ref inst)) = last_plain {
            match query_last(&module, idx, cnf_kind, inst, expr_src) {
                Ok((rendered, ok)) => {
                    println!("query: {expr_src} = {rendered}");
                    if !ok {
                        process::exit(1);
                    }
                }
                Err(e) => {
                    eprintln!("eval error: {e}");
                    process::exit(1);
                }
            }
        } else {
        let eval_src = if let Some(code) = &cli.code {
            format!("{code}\nrun {{ {expr_src} }}")
        } else if let Some(path) = &cli.file {
            let orig = std::fs::read_to_string(path).unwrap_or_default();
            format!("{orig}\nrun {{ {expr_src} }}")
        } else {
            format!("run {{ {expr_src} }}")
        };

        let mut eval_module = match parse_module(&eval_src) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("eval parse error: {e}");
                process::exit(1);
            }
        };
        inherit_eval_scope(&mut eval_module, &last_scope);

        let eval_idx = eval_module.commands.len() - 1;
        match run_command(&eval_module, eval_idx) {
            Ok(sol) => {
                let tag = if sol.satisfiable { "true" } else { "false" };
                println!("eval: {tag}");
                if sol.satisfiable {
                    if let Some(ref inst) = sol.instance {
                        print_solution(inst);
                    }
                }
                last_solution = Some(sol);
            }
            Err(e) => {
                eprintln!("eval error: {e}");
                process::exit(1);
            }
        }
        } // end fallback (no queryable solution)
    }

    match last_solution {
        Some(sol) if sol.satisfiable => process::exit(0),
        _ if last_opt_sat => process::exit(0),
        _ => process::exit(1),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eval_inherits_command_scope() {
        let src = "one sig x extends EReal {} run for 10 int";
        let module = parse_module(src).expect("parse");
        assert_eq!(module.commands.len(), 1);
        let eval_src = format!("{src}\nrun {{ x }}");
        let mut eval_module = parse_module(&eval_src).expect("parse");
        assert_eq!(eval_module.commands.len(), 2);
        // Default scope before inheritance.
        inherit_eval_scope(&mut eval_module, &None);
        // Inherit the executed command's profile.
        let scope = Some(module.commands[0].scope.clone());
        inherit_eval_scope(&mut eval_module, &scope);
        assert_eq!(
            format!("{:?}", eval_module.commands[1].scope),
            format!("{:?}", module.commands[0].scope)
        );
    }
}
