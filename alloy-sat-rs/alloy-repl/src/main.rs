//! alloy-repl: interactive REPL for Alloy (Rust native).
//!
//! - `run` / `check` build a `Cnf` value (no solving).
//! - `solve` inspects the current `Cnf` and returns instance or nothing.
//! - `validate` checks the last instance against the current `Cnf`.
//! - `sig`/`fact`/`pred`/`fun`/`assert`/`run`/`check` lines accumulate as
//!   model fragments (re-enter a name to replace it); multi-line input
//!   continues on `... ` until braces balance.
//! - `:eval <expr|formula>` checks satisfiability (`run { ... }` wrap).
//! - `:query <expr>` evaluates against the last solved instance.
//! - Bare expression lines do `:query` when an instance is ready,
//!   else `:eval`. `let` bindings work inside bodies and expressions.

use alloy_front_rs::{
    check, eval, fragment_keys, parse_module, query, run, solve, validate, Cnf, CnfKind,
    CommandKind, Instance, Module,
};

mod fmt;
use clap::Parser as ClapParser;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

#[derive(ClapParser)]
#[command(name = "alloy-repl", about = "Alloy REPL (Rust): declare, run/check -> Cnf, solve/eval/query")]
struct Cli {
    /// .als file to preload
    file: Option<String>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum InputKind {
    Decl,
    Bare,
    Eval,
    Query,
}

struct Pending {
    kind: InputKind,
    text: String,
    depth: i32,
}

struct Session {
    base_src: String,
    fragments: Vec<(Vec<String>, String)>,
    current_src: String,
    module: Option<Module>,
    source_desc: String,
    current: Option<Cnf>,
    last_sat: Option<bool>,
    last_instance: Option<Instance>,
    pending: Option<Pending>,
}

impl Session {
    fn new() -> Self {
        Session {
            base_src: String::new(),
            fragments: Vec::new(),
            current_src: String::new(),
            module: None,
            source_desc: String::new(),
            current: None,
            last_sat: None,
            last_instance: None,
            pending: None,
        }
    }

    fn joined_source(&self) -> String {
        let mut src = self.base_src.clone();
        for (_, text) in &self.fragments {
            if !src.is_empty() && !src.ends_with('\n') {
                src.push('\n');
            }
            src.push_str(text);
            src.push('\n');
        }
        src
    }

    /// Parse `src`, committing it (and `frags`) only on success.
    fn commit_source(
        &mut self,
        src: String,
        frags: Vec<(Vec<String>, String)>,
        desc: String,
        note: &str,
    ) -> bool {
        match parse_module(&src) {
            Ok(m) => {
                let n = m.commands.len();
                self.fragments = frags;
                self.current_src = src;
                self.module = Some(m);
                self.source_desc = desc;
                self.current = None;
                self.last_sat = None;
                self.last_instance = None;
                println!("{note} ({n} commands)");
                true
            }
            Err(e) => {
                println!("parse error: {e}");
                false
            }
        }
    }

    fn rebuild(&mut self, note: &str) {
        let src = self.joined_source();
        let frags = self.fragments.clone();
        let desc = self.source_desc.clone();
        self.commit_source(src, frags, desc, note);
    }

    fn load_file(&mut self, path: &str) {
        match std::fs::read_to_string(path) {
            Ok(src) => {
                let mut sess = Session::new();
                sess.base_src = src;
                let joined = sess.joined_source();
                // Commit into self only on success, keeping the old session otherwise.
                match parse_module(&joined) {
                    Ok(m) => {
                        let n = m.commands.len();
                        self.base_src = sess.base_src;
                        self.fragments = Vec::new();
                        self.current_src = joined;
                        self.module = Some(m);
                        self.source_desc = path.to_string();
                        self.current = None;
                        self.last_sat = None;
                        self.last_instance = None;
                        self.pending = None;
                        println!("loaded ({n} commands)");
                    }
                    Err(e) => println!("parse error: {e}"),
                }
            }
            Err(e) => println!("cannot read {path}: {e}"),
        }
    }

    fn add_fragment(&mut self, text: &str) {
        if first_token(text) == "module" {
            println!("hint: no `module` header needed in the REPL (use :load for files)");
            return;
        }
        let keys = match fragment_keys(text) {
            Ok(k) => k,
            Err(e) => {
                println!("parse error: {e}");
                return;
            }
        };
        let mut frags = self.fragments.clone();
        let mut replaced = 0;
        if !keys.is_empty() {
            let before = frags.len();
            frags.retain(|(ks, _)| ks.iter().all(|k| !keys.contains(k)));
            replaced = before - frags.len();
        }
        frags.push((keys, text.to_string()));
        let mut src = self.base_src.clone();
        for (_, t) in &frags {
            if !src.is_empty() && !src.ends_with('\n') {
                src.push('\n');
            }
            src.push_str(t);
            src.push('\n');
        }
        let desc = self.source_desc.clone();
        let note = if replaced > 0 {
            format!("replaced {replaced} fragment(s), rebuilt")
        } else {
            "added fragment, rebuilt".to_string()
        };
        self.commit_source(src, frags, desc, &note);
    }

    fn list_commands(&self) {
        match &self.module {
            None => println!("no module loaded (use :load <file> or type declarations)"),
            Some(m) if m.commands.is_empty() => println!("no commands in module"),
            Some(m) => {
                for (i, c) in m.commands.iter().enumerate() {
                    let (kind, name) = match &c.kind {
                        CommandKind::Run(n) => ("run", n.clone().unwrap_or_default()),
                        CommandKind::Check(n) => ("check", n.clone().unwrap_or_default()),
                    };
                    let cur = match &self.current {
                        Some(cnf) if cnf.command_index == i => " *",
                        _ => "",
                    };
                    println!("{i:02}. {kind:<6} {name}{cur}");
                }
            }
        }
    }

    fn list_fragments(&self) {
        if self.fragments.is_empty() {
            println!("no fragments (model comes from :load file)");
            return;
        }
        for (i, (keys, text)) in self.fragments.iter().enumerate() {
            let first = text.lines().next().unwrap_or("");
            let key = if keys.is_empty() {
                "append".to_string()
            } else {
                keys.join(",")
            };
            println!("{i:02}. [{key}] {first}");
        }
    }

    fn resolve_index(&self, arg: Option<&str>) -> Result<usize, String> {
        let m = self.module.as_ref().ok_or("no module loaded")?;
        match arg {
            None => {
                if m.commands.len() == 1 {
                    Ok(0)
                } else {
                    Err("usage: :run|:check <index|name> (module has several commands)".into())
                }
            }
            Some(a) => {
                if let Ok(i) = a.parse::<usize>() {
                    if i < m.commands.len() {
                        return Ok(i);
                    }
                    return Err(format!("no command #{i}"));
                }
                m.find_command(a)
                    .ok_or_else(|| format!("no command named `{a}`"))
            }
        }
    }

    fn do_build(&mut self, kind: CnfKind, arg: Option<&str>) {
        let idx = match self.resolve_index(arg) {
            Ok(i) => i,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        let m = self.module.as_ref().expect("checked");
        let built = match kind {
            CnfKind::Run => run(m, idx),
            CnfKind::Check => check(m, idx),
        };
        match built {
            Ok(cnf) => {
                println!("built cnf: {}", cnf.summary());
                self.current = Some(cnf);
                self.last_sat = None;
                self.last_instance = None;
                println!("hint: :solve to inspect, :show to view cnf");
            }
            Err(e) => println!("build error: {e}"),
        }
    }

    fn print_solution(&self, inst: &Option<Instance>, is_check: bool) {
        match inst {
            Some(i) => {
                if is_check {
                    println!("SAT -- counterexample found:");
                } else {
                    println!("SAT -- example found:");
                }
                println!("{}", fmt::instance_alloy(i));
            }
            None => {
                if is_check {
                    println!("UNSAT -- no counterexample (assertion holds; empty)");
                } else {
                    println!("UNSAT -- no example (empty)");
                }
            }
        }
    }

    fn do_solve(&mut self) {
        let cnf = match &self.current {
            Some(c) => c.clone(),
            None => {
                println!("no cnf built (use :run|:check first)");
                return;
            }
        };
        match solve(&cnf) {
            Ok(inst) => {
                self.last_sat = Some(inst.is_some());
                self.print_solution(&inst, cnf.is_check());
                self.last_instance = inst;
            }
            Err(e) => println!("solve error: {e}"),
        }
    }

    fn do_eval_text(&self, expr: &str) {
        if self.module.is_none() {
            println!("no module loaded");
            return;
        }
        match eval(&self.current_src, expr) {
            Ok(sol) => {
                self.print_solution(&sol.instance, false);
            }
            Err(e) => println!("eval error: {e}"),
        }
    }

    fn query_ready(&self) -> bool {
        self.current.is_some() && self.last_instance.is_some()
    }

    fn do_query_text(&self, expr: &str) {
        let (m, cnf, inst) = match (&self.module, &self.current, &self.last_instance) {
            (Some(m), Some(c), Some(i)) => (m, c, i),
            _ => {
                println!(":query needs a solved instance (use :run then :solve first)");
                return;
            }
        };
        let scope = match m.commands.get(cnf.command_index) {
            Some(c) => &c.scope,
            None => {
                println!("current command is gone (rebuild with :run|:check)");
                return;
            }
        };
        match query(m, scope, cnf, expr, inst) {
            Ok((arity, ts)) => println!("{}", fmt::set_alloy(ts.universe(), arity, &ts)),
            Err(e) => println!("query error: {e}"),
        }
    }

    fn do_bare_expr(&self, expr: &str) {
        if self.query_ready() {
            self.do_query_text(expr);
        } else {
            if self.module.is_none() {
                println!("no module loaded");
                return;
            }
            if self.current.is_none() {
                println!("(no solved instance; falling back to :eval)");
            }
            self.do_eval_text(expr);
        }
    }

    fn do_validate(&self) {
        let cnf = match &self.current {
            Some(c) => c,
            None => {
                println!("no cnf built (use :run|:check first)");
                return;
            }
        };
        let inst = match &self.last_instance {
            Some(i) => i,
            None => {
                println!("no instance to validate (use :solve first)");
                return;
            }
        };
        match validate(cnf, inst) {
            Some(back) => {
                println!("valid -- instance is a model, returned as-is:");
                println!("{}", fmt::instance_alloy(&back));
            }
            None => println!("invalid -- not a model of current cnf (none/empty)"),
        }
    }

    fn do_show(&self, arg: Option<&str>) {
        let cnf = match &self.current {
            Some(c) => c,
            None => {
                println!("no cnf built");
                return;
            }
        };
        println!("cnf: {}", cnf.summary());
        println!("  bitwidth={} skolemize={}", cnf.bitwidth, cnf.skolemize);
        let limit: usize = arg.and_then(|a| a.parse().ok()).unwrap_or(10);
        for (i, cl) in cnf.clauses.iter().take(limit).enumerate() {
            let line: Vec<String> = cl.iter().map(|l| l.to_string()).collect();
            println!("  c{i}: {}", line.join(" "));
        }
        if cnf.clauses.len() > limit {
            println!("  ... ({} more clauses)", cnf.clauses.len() - limit);
        }
        match (self.last_sat, &self.last_instance) {
            (Some(true), Some(inst)) => println!("last: SAT\n{}", fmt::instance_alloy(inst)),
            (Some(false), _) => println!("last: UNSAT (none / empty)"),
            _ => println!("last: not solved yet (:solve)"),
        }
    }

    fn submit_pending(&mut self, pending: Pending) {
        match pending.kind {
            InputKind::Decl => self.add_fragment(&pending.text),
            InputKind::Bare => self.do_bare_expr(&pending.text),
            InputKind::Eval => self.do_eval_text(&pending.text),
            InputKind::Query => self.do_query_text(&pending.text),
        }
    }
}

fn print_help() {
    println!("declare (accumulate into the model; re-enter a name to replace):");
    println!("  sig ... / fact ... / pred ... / fun ... / assert ... / open ...");
    println!("  run ... / check ...      as a fragment when it names no command");
    println!("  multi-line continues on `... ` until braces balance;");
    println!("  blank line or a `:command` line submits pending input first");
    println!("commands:");
    println!("  :load <file>        load .als model (fragments cleared)");
    println!("  :list               list run/check commands (* = current cnf)");
    println!("  :fragments          list entered fragments");
    println!("  :reset              drop entered fragments, keep :load file");
    println!("  :run [i|name]       build Cnf from run (returns cnf value)");
    println!("  :check [i|name]     build Cnf from check (negated; returns cnf value)");
    println!("  :solve              inspect current Cnf -> instance | none(empty)");
    println!("  :eval <expr|formula> satisfiability check (bare expr lifts with some)");
    println!("  :query <expr>       evaluate against last solved instance");
    println!("  <expr>              bare line: :query when ready, else :eval");
    println!("  :validate           validate last instance vs current Cnf -> as-is | none");
    println!("  :show [N]           show current Cnf (first N clauses) + last result");
    println!("  :help               this help");
    println!("  :quit               exit (Ctrl-D also exits)");
    println!("notes: `let` works inside pred/fun bodies and :eval/:query expressions.");
}

fn first_token(s: &str) -> &str {
    s.split_whitespace().next().unwrap_or("")
}

fn second_token(s: &str) -> &str {
    s.split_whitespace().nth(1).unwrap_or("")
}

/// `sig`/`pred`/…-style declaration (excluding bare `run`/`check`, which go
/// through build-or-add). `one`/`lone`/`some`/`var` count only before `sig`.
fn looks_like_decl(s: &str) -> bool {
    match first_token(s) {
        "sig" | "abstract" | "fact" | "pred" | "fun" | "assert" | "open" => true,
        "one" | "lone" | "some" | "var" => second_token(s) == "sig",
        _ => false,
    }
}

fn brace_delta(s: &str) -> i32 {
    let code = s.split("//").next().unwrap_or("");
    let code = code.split("--").next().unwrap_or(code);
    code.chars().filter(|&c| c == '{').count() as i32
        - code.chars().filter(|&c| c == '}').count() as i32
}

const BARE_COMMANDS: &[&str] = &[
    "help", "h", "?", "quit", "exit", "q", "load", "l", "list", "ls", "fragments", "solve",
    "s", "validate", "v", "show", "reset",
];

fn main() {
    let cli = Cli::parse();
    let mut sess = Session::new();
    if let Some(path) = cli.file {
        sess.load_file(&path);
    } else {
        println!("alloy-repl: type declarations, :load <file>, :help for commands.");
    }

    let mut rl = DefaultEditor::new().unwrap_or_else(|e| {
        eprintln!("rustyline init failed: {e}");
        std::process::exit(1);
    });
    let _ = rl.load_history(".alloy_repl_history");

    loop {
        let prompt = if sess.pending.is_some() { "... " } else { "alloy> " };
        let line = match rl.readline(prompt) {
            Ok(l) => l,
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("read error: {e}");
                break;
            }
        };
        let trimmed = line.trim();
        // Blank line submits a pending multi-line input, else ignored.
        if trimmed.is_empty() {
            if let Some(pending) = sess.pending.take() {
                let _ = rl.add_history_entry(pending.text.clone());
                sess.submit_pending(pending);
            }
            continue;
        }
        if sess.pending.is_none()
            && (trimmed.starts_with("--") || trimmed.starts_with("//"))
        {
            continue;
        }
        let _ = rl.add_history_entry(line.clone());

        // A `:command` line submits any pending input first, then runs.
        if sess.pending.is_some() && trimmed.starts_with(':') {
            if let Some(pending) = sess.pending.take() {
                sess.submit_pending(pending);
            }
        }
        // Continuation of a pending multi-line input.
        if let Some(mut pending) = sess.pending.take() {
            pending.text.push('\n');
            pending.text.push_str(trimmed);
            pending.depth += brace_delta(trimmed);
            if pending.depth <= 0 {
                sess.submit_pending(pending);
            } else {
                sess.pending = Some(pending);
            }
            continue;
        }

        // Explicit `:command`.
        if let Some(body) = trimmed.strip_prefix(':') {
            let mut parts = body.split_whitespace();
            let cmd = parts.next().unwrap_or("");
            // NOTE: parts borrows body; collect the rest before &mut sess calls.
            let rest: Vec<&str> = parts.collect();
            let arg = rest.first().copied();
            match cmd {
                "help" | "h" | "?" => print_help(),
                "quit" | "exit" | "q" => break,
                "load" | "l" => match arg {
                    Some(p) => sess.load_file(p),
                    None => println!("usage: :load <file.als>"),
                },
                "list" | "ls" => sess.list_commands(),
                "fragments" => sess.list_fragments(),
                "reset" => {
                    sess.fragments.clear();
                    sess.rebuild("reset");
                }
                "run" => sess.do_build(CnfKind::Run, arg),
                "check" => sess.do_build(CnfKind::Check, arg),
                "solve" | "s" => sess.do_solve(),
                "validate" | "v" => sess.do_validate(),
                "show" => sess.do_show(arg),
                "eval" => {
                    let expr = body["eval".len()..].trim();
                    if expr.is_empty() {
                        println!("usage: :eval <expr|formula>");
                    } else {
                        start_or_submit(&mut sess, InputKind::Eval, expr);
                    }
                }
                "query" => {
                    let expr = body["query".len()..].trim();
                    if expr.is_empty() {
                        println!("usage: :query <expr>");
                    } else {
                        start_or_submit(&mut sess, InputKind::Query, expr);
                    }
                }
                _ => println!("unknown command `:{cmd}` (:help for list)"),
            }
            continue;
        }

        // Bare line: explicit command name without colon (legacy).
        let head = first_token(trimmed);
        if BARE_COMMANDS.contains(&head) {
            let mut parts = trimmed.split_whitespace();
            let cmd = parts.next().unwrap_or("");
            let rest: Vec<&str> = parts.collect();
            let arg = rest.first().copied();
            match cmd {
                "help" | "h" | "?" => print_help(),
                "quit" | "exit" | "q" => break,
                "load" | "l" => match arg {
                    Some(p) => sess.load_file(p),
                    None => println!("usage: :load <file.als>"),
                },
                "list" | "ls" => sess.list_commands(),
                "fragments" => sess.list_fragments(),
                "reset" => {
                    sess.fragments.clear();
                    sess.rebuild("reset");
                }
                "solve" | "s" => sess.do_solve(),
                "validate" | "v" => sess.do_validate(),
                "show" => sess.do_show(arg),
                _ => println!("unknown command `{cmd}` (:help for list)"),
            }
            continue;
        }

        // Bare `run`/`check`: build when it names a command, else a fragment.
        if head == "run" || head == "check" {
            // Re-split to own the arg before &mut sess calls below.
            let arg_owned: Option<String> = trimmed
                .split_whitespace()
                .nth(1)
                .map(|s| s.to_string());
            let kind = if head == "run" {
                CnfKind::Run
            } else {
                CnfKind::Check
            };
            if sess.module.is_some() && sess.resolve_index(arg_owned.as_deref()).is_ok() {
                sess.do_build(kind, arg_owned.as_deref());
            } else if sess.module.is_none() {
                println!("no module loaded");
            } else {
                start_or_submit(&mut sess, InputKind::Decl, trimmed);
            }
            continue;
        }

        // Declaration fragment vs bare expression.
        if looks_like_decl(trimmed) {
            start_or_submit(&mut sess, InputKind::Decl, trimmed);
        } else {
            start_or_submit(&mut sess, InputKind::Bare, trimmed);
        }
    }
    let _ = rl.save_history(".alloy_repl_history");
    println!("bye");
}

/// Begin (or immediately submit) a multi-line input.
fn start_or_submit(sess: &mut Session, kind: InputKind, text: &str) {
    let depth = brace_delta(text);
    if depth <= 0 {
        let pending = Pending {
            kind,
            text: text.to_string(),
            depth: 0,
        };
        sess.submit_pending(pending);
    } else {
        sess.pending = Some(Pending {
            kind,
            text: text.to_string(),
            depth,
        });
    }
}
