//! alloy-repl: interactive REPL for Alloy (Rust native).
//!
//! Named stores (explicit, no hidden slots):
//! - `:run`/`:check` build a `Cnf` and save it under a name.
//! - `:solve` solves a named `Cnf` and saves the solution under a name.
//! - `:query`/`:validate`/`:show` take explicit names; bare forms fall back
//!   to the visible defaults (`*` in `:cnfs`/`:sols`, switched via `:use`).
//! - `sig`/`fact`/`pred`/`fun`/`assert`/`run`/`check` lines accumulate as
//!   model fragments (re-enter a name to replace it); multi-line input
//!   continues on `... ` until braces balance.
//! - `:eval <expr|formula>` checks satisfiability (`run { ... }` wrap).
//! - Bare expression lines follow the bare mode (`:mode eval|query`,
//!   default `eval`): `:eval` in eval mode, `:query` against the default
//!   solution in query mode (never stored either way).
//! - `:psave <file>` writes a solution as a binary partial instance
//!   (`.apin`); `:ppin`/`:pavoid` apply it to a Cnf. Partial instances
//!   transfer tuple indices directly, so no atom-name text is involved.

use std::collections::{HashMap, HashSet};

use alloy_front_rs::{
    build_cnf_with, check, command_needs_opt, eval, fragment_keys, optimize, optimize_with,
    parse_int_expr, parse_module, query_value, run, run_opt_command_with, solve,
    solve_temporal, validate, validate_temporal, Cnf, CnfKind, CommandKind, Expr,
    IncrementalSession, Instance, KkOptSense, Lowerer, Module, OptSolution, OptTarget,
    OverflowMode, PartialInstance, QueryValue,
};
use alloy_kodkod_rs::eval::Evaluator;
use alloy_kodkod_rs::temporal::TemporalEval;
use alloy_kodkod_rs::TemporalInstance;

mod fmt;
mod mepk_cmd;
use clap::Parser as ClapParser;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

#[derive(ClapParser)]
#[command(
    name = "alloy-repl",
    about = "Alloy REPL (Rust): declare, run/check -> Cnf, solve/eval/query"
)]
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

/// How a bare expression line is interpreted.
#[derive(Clone, Copy, PartialEq, Eq)]
enum BareMode {
    /// Satisfiability check (default; never stored).
    Eval,
    /// Evaluate against the default solution (`:query <expr>`).
    Query,
}

impl BareMode {
    fn prompt(self) -> &'static str {
        match self {
            BareMode::Eval => "alloy> ",
            BareMode::Query => "alloy?> ",
        }
    }
}

struct Pending {
    kind: InputKind,
    text: String,
    depth: i32,
    /// For `Eval`: solution save name (`as <sol>`).
    /// For `Query`: solution reference name (`in <sol>`, None = default).
    target: Option<String>,
}

struct StoredSol {
    sat: bool,
    instance: Option<Instance>,
    /// Full lasso trace for temporal Cnfs (`None` for static / `:eval` /
    /// optimizer solutions). `instance` still holds `states[0]` so `:query`
    /// / `:psave` keep working on the first state.
    temporal: Option<TemporalInstance>,
    /// Optimum cost for `:max`/`:min`/`:maxw`/`:minw` solutions.
    cost: Option<i64>,
    /// Origin Cnf store name; empty for `:eval` solutions (no Cnf context).
    from_cnf: String,
}

/// Incremental enumeration state for one Cnf (`:next`).
///
/// The session owns a persistent CaDiCaL backend with the Cnf clauses
/// loaded once; each `:next` permanently blocks all known solutions from
/// that Cnf and re-solves. `blocked` tracks which stored solution names
/// already have blocking clauses so repeated `:next` calls (and branched
/// `:solve`s) never exclude the same model twice.
struct EnumSession {
    session: IncrementalSession,
    blocked: HashSet<String>,
}

struct Session {
    base_src: String,
    fragments: Vec<(Vec<String>, String)>,
    current_src: String,
    module: Option<Module>,
    source_desc: String,
    cnfs: HashMap<String, Cnf>,
    sols: HashMap<String, StoredSol>,
    enum_sessions: HashMap<String, EnumSession>,
    cnf_order: Vec<String>,
    sol_order: Vec<String>,
    default_cnf: Option<String>,
    default_sol: Option<String>,
    pending: Option<Pending>,
    bare: BareMode,
}

impl Session {
    fn new() -> Self {
        Session {
            base_src: String::new(),
            fragments: Vec::new(),
            current_src: String::new(),
            module: None,
            source_desc: String::new(),
            cnfs: HashMap::new(),
            sols: HashMap::new(),
            enum_sessions: HashMap::new(),
            cnf_order: Vec::new(),
            sol_order: Vec::new(),
            default_cnf: None,
            default_sol: None,
            pending: None,
            bare: BareMode::Eval,
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
                self.clear_stores();
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
                        self.clear_stores();
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

    fn clear_stores(&mut self) {
        let nc = self.cnfs.len();
        let ns = self.sols.len();
        self.cnfs.clear();
        self.sols.clear();
        self.enum_sessions.clear();
        self.cnf_order.clear();
        self.sol_order.clear();
        self.default_cnf = None;
        self.default_sol = None;
        if nc + ns > 0 {
            println!("model changed: dropped {nc} cnfs, {ns} solutions");
        }
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
                        CommandKind::Maximize { name: n, .. } => {
                            ("maximize", n.clone().unwrap_or_default())
                        }
                        CommandKind::Minimize { name: n, .. } => {
                            ("minimize", n.clone().unwrap_or_default())
                        }
                    };
                    println!("{i:02}. {kind:<6} {name}");
                }
            }
        }
    }

    fn list_cnfs(&self) {
        if self.cnf_order.is_empty() {
            println!("no cnfs (use :run|:check first; :help for forms)");
            return;
        }
        for name in &self.cnf_order {
            let mark = match &self.default_cnf {
                Some(d) if d == name => "*",
                _ => " ",
            };
            match self.cnfs.get(name) {
                Some(cnf) => println!("{mark} {name}  ({})", cnf.summary()),
                None => println!("{mark} {name}  (gone)"),
            }
        }
    }

    fn list_sols(&self) {
        if self.sol_order.is_empty() {
            println!("no solutions (use :solve first; :help for forms)");
            return;
        }
        for name in &self.sol_order {
            let mark = match &self.default_sol {
                Some(d) if d == name => "*",
                _ => " ",
            };
            match self.sols.get(name) {
                Some(s) => {
                    let st = if s.sat { "SAT" } else { "UNSAT" };
                    let cost = s
                        .cost
                        .map(|c| format!(" cost={c}"))
                        .unwrap_or_default();
                    let trace = s
                        .temporal
                        .as_ref()
                        .map(|t| format!(" temporal steps={} loop={}", t.len(), t.loop_state()))
                        .unwrap_or_default();
                    if s.from_cnf.is_empty() {
                        println!("{mark} {name}  {st}{cost}{trace} (from :eval)");
                    } else {
                        println!("{mark} {name}  {st}{cost}{trace} <- {}", s.from_cnf);
                    }
                }
                None => println!("{mark} {name}  (gone)"),
            }
        }
    }

    fn do_use(&mut self, name: &str) {
        if self.cnfs.contains_key(name) && self.sols.contains_key(name) {
            self.default_cnf = Some(name.to_string());
            self.default_sol = Some(name.to_string());
            println!("default: cnf `{name}` + solution `{name}`");
        } else if self.cnfs.contains_key(name) {
            self.default_cnf = Some(name.to_string());
            // Point the solution default at the newest solution from this cnf, if any.
            let mut best: Option<String> = None;
            for s in &self.sol_order {
                if let Some(st) = self.sols.get(s) {
                    if st.from_cnf == name {
                        best = Some(s.clone());
                    }
                }
            }
            if let Some(b) = best {
                self.default_sol = Some(b.clone());
                println!("default cnf `{name}` (+ solution `{b}`)");
            } else {
                println!("default cnf `{name}`");
            }
        } else if self.sols.contains_key(name) {
            let from = self
                .sols
                .get(name)
                .map(|s| s.from_cnf.clone())
                .unwrap_or_default();
            self.default_sol = Some(name.to_string());
            if !from.is_empty() && self.cnfs.contains_key(&from) {
                self.default_cnf = Some(from.clone());
                println!("default solution `{name}` (+ cnf `{from}`)");
            } else {
                println!("default solution `{name}`");
            }
        } else {
            println!("no cnf or solution named `{name}` (:cnfs / :sols to list)");
        }
    }

    fn list_fragments(&self) {
        if self.fragments.is_empty() {
            println!("no fragments (model comes from :load file)");
            return;
        }
        for (i, (keys, text)) in self.fragments.iter().enumerate() {
            let first = text
                .lines()
                .map(str::trim)
                .find(|l| !l.is_empty() && !l.starts_with("--") && !l.starts_with("//"))
                .unwrap_or("");
            let key = if keys.is_empty() {
                "append".to_string()
            } else {
                keys.join(",")
            };
            println!("{i:02}. [{key}] {first}");
        }
    }

    /// Delete one entered fragment by `:fragments` index, then rebuild.
    /// The rebuild invalidates saved Cnfs/solutions (model changed).
    fn drop_fragment(&mut self, arg: Option<&str>) {
        let idx: usize = match arg {
            Some(a) => match a.parse() {
                Ok(i) => i,
                Err(_) => {
                    println!("usage: :drop <fragment-index> (:fragments to list)");
                    return;
                }
            },
            None => {
                println!("usage: :drop <fragment-index> (:fragments to list)");
                return;
            }
        };
        if idx >= self.fragments.len() {
            println!("no fragment #{idx} (:fragments to list)");
            return;
        }
        let mut frags = self.fragments.clone();
        let (_, text) = frags.remove(idx);
        let first = text.lines().next().unwrap_or("").to_string();
        let mut src = self.base_src.clone();
        for (_, t) in &frags {
            if !src.is_empty() && !src.ends_with('\n') {
                src.push('\n');
            }
            src.push_str(t);
            src.push('\n');
        }
        let desc = self.source_desc.clone();
        self.commit_source(
            src,
            frags,
            desc,
            &format!("dropped fragment {idx:02} [{first}], rebuilt"),
        );
    }

    fn resolve_index(&self, arg: Option<&str>) -> Result<usize, String> {
        let m = self.module.as_ref().ok_or("no module loaded")?;
        match arg {
            None => {
                if m.commands.len() == 1 {
                    Ok(0)
                } else if m.commands.is_empty() {
                    Err("no commands in module (add a run/check/maximize line)".into())
                } else {
                    Err(
                        "usage: :run|:check <index|name> [as <cnf>] (module has several commands)"
                            .into(),
                    )
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

    /// Save `cnf` under `name` (auto-suffixed on collision) or overwrite an
    /// explicit `as` name. Returns the final name.
    fn store_cnf(&mut self, cnf: Cnf, want: Option<&str>) -> String {
        match want {
            Some(n) => {
                let overwrote = self.cnfs.contains_key(n);
                if !overwrote {
                    self.cnf_order.push(n.to_string());
                }
                self.cnfs.insert(n.to_string(), cnf);
                self.default_cnf = Some(n.to_string());
                if overwrote {
                    println!("overwrote cnf `{n}`");
                }
                n.to_string()
            }
            None => {
                let base = cnf
                    .command_name
                    .clone()
                    .filter(|s| !s.is_empty())
                    .unwrap_or_else(|| format!("{}{}", cnf.kind, cnf.command_index));
                let mut name = base.clone();
                let mut k = 2;
                while self.cnfs.contains_key(&name) {
                    name = format!("{base}_{k}");
                    k += 1;
                }
                self.cnf_order.push(name.clone());
                self.cnfs.insert(name.clone(), cnf);
                self.default_cnf = Some(name.clone());
                name
            }
        }
    }

    /// Save a solution; auto name inherits the Cnf store name.
    fn store_sol(
        &mut self,
        want: Option<&str>,
        from_cnf: &str,
        sat: bool,
        instance: Option<Instance>,
        cost: Option<i64>,
        temporal: Option<TemporalInstance>,
    ) -> String {
        match want {
            Some(n) => {
                let overwrote = self.sols.contains_key(n);
                if !overwrote {
                    self.sol_order.push(n.to_string());
                }
                self.sols.insert(
                    n.to_string(),
                    StoredSol {
                        sat,
                        instance,
                        temporal,
                        cost,
                        from_cnf: from_cnf.to_string(),
                    },
                );
                self.default_sol = Some(n.to_string());
                if overwrote {
                    println!("overwrote solution `{n}`");
                }
                n.to_string()
            }
            None => {
                let mut name = from_cnf.to_string();
                let mut k = 2;
                while self.sols.contains_key(&name) {
                    name = format!("{from_cnf}_{k}");
                    k += 1;
                }
                self.sol_order.push(name.clone());
                self.sols.insert(
                    name.clone(),
                    StoredSol {
                        sat,
                        instance,
                        temporal,
                        cost,
                        from_cnf: from_cnf.to_string(),
                    },
                );
                self.default_sol = Some(name.clone());
                name
            }
        }
    }

    fn do_build(
        &mut self,
        kind: CnfKind,
        target: Option<&str>,
        as_name: Option<&str>,
    ) -> Option<String> {
        if let Some(n) = as_name {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return None;
            }
        }
        let idx = match self.resolve_index(target) {
            Ok(i) => i,
            Err(e) => {
                println!("{e}");
                return None;
            }
        };
        let m = self.module.as_ref().expect("checked");
        let built = match kind {
            CnfKind::Run => run(m, idx),
            CnfKind::Check => check(m, idx),
        };
        match built {
            Ok(cnf) => {
                let summary = cnf.summary();
                for w in &cnf.warnings {
                    println!("{w}");
                }
                let name = self.store_cnf(cnf, as_name);
                println!("saved cnf `{name}` ({summary}) *default");
                println!("hint: :solve {name} to solve, :show {name} to view cnf");
                Some(name)
            }
            Err(e) => {
                println!("build error: {e}");
                None
            }
        }
    }

    /// Display hints for integer rendering: Signed-rooted sigs plus
    /// `Owner.field` keys whose declared type mentions `Signed`.
    fn display_hints(&self) -> fmt::DisplayHints {
        let mut hints = fmt::DisplayHints::default();
        let Some(module) = self.module.as_ref() else {
            return hints;
        };
        for sd in &module.sigs {
            for n in &sd.names {
                let mut cur = n.as_str();
                let mut seen = HashSet::new();
                loop {
                    if !seen.insert(cur) {
                        break;
                    }
                    let parent = module
                        .sigs
                        .iter()
                        .find(|s| s.names.iter().any(|x| x == cur))
                        .and_then(|s| s.extends.as_deref());
                    match parent {
                        Some("Signed") => {
                            hints.signed_sigs.insert(n.clone());
                            break;
                        }
                        Some(p) => cur = p,
                        None => break,
                    }
                }
            }
            for owner in &sd.names {
                for d in &sd.fields {
                    if expr_is_signed(&d.expr) {
                        for fname in &d.names {
                            hints.signed_fields.insert(format!("{owner}.{fname}"));
                        }
                    }
                    if expr_is_ereal(&d.expr) {
                        for fname in &d.names {
                            hints.ereal_fields.insert(format!("{owner}.{fname}"));
                        }
                    }
                }
            }
        }
        hints
    }

    fn print_solution(&self, inst: &Option<Instance>, is_check: bool) {        match inst {
            Some(i) => {
                if is_check {
                    println!("SAT -- counterexample found:");
                } else {
                    println!("SAT -- example found:");
                }
                println!("{}", fmt::instance_alloy_hinted(i, &self.display_hints()));
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

    fn print_temporal_solution(&self, trace: &Option<TemporalInstance>, is_check: bool) {
        match trace {
            Some(ti) => {
                if is_check {
                    println!("SAT -- counterexample found: temporal trace");
                } else {
                    println!("SAT -- example found: temporal trace");
                }
                println!("trace: steps={} loop={}", ti.len(), ti.loop_state());
                for (i, st) in ti.states().iter().enumerate() {
                    println!("--- state {i} ---");
                    println!("{}", fmt::instance_alloy_hinted(st, &self.display_hints()));
                }
                println!("note: :query/:psave see state 0; :show <sol> reprints the trace");
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
    fn resolve_cnf(&self, name: &str) -> Option<&Cnf> {
        self.cnfs.get(name)
    }

    fn default_cnf_name(&self) -> Option<String> {
        self.default_cnf.clone()
    }

    fn default_sol_name(&self) -> Option<String> {
        self.default_sol.clone()
    }

    fn do_solve(&mut self, cnf_arg: Option<&str>, as_name: Option<&str>) {
        if let Some(n) = as_name {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let mut cnf_name = match cnf_arg {
            Some(n) => n.to_string(),
            None => match self.default_cnf_name() {
                Some(n) => n,
                None => {
                    println!("no cnf selected (use :run|:check first, :cnfs to list)");
                    return;
                }
            },
        };
        let cnf = match self.resolve_cnf(&cnf_name) {
            Some(c) => c.clone(),
            None => {
                // Auto-build: `:solve <command>` builds the Cnf on the fly
                // so `:run` beforehand is optional. An explicit Cnf name
                // still takes precedence when both exist.
                let idx = match self.module.as_ref().and(self.resolve_index(Some(&cnf_name)).ok()) {
                    Some(i) => i,
                    None => {
                        println!("no cnf named `{cnf_name}` (:cnfs to list)");
                        return;
                    }
                };
                let module = self.module.as_ref().expect("checked");
                if let Some(CommandKind::Maximize { .. } | CommandKind::Minimize { .. }) =
                    &module.commands.get(idx).map(|c| &c.kind)
                {
                    println!(
                        "command `{cnf_name}` is maximize/minimize (use :optimize {cnf_name} instead of :solve)"
                    );
                    return;
                }
                if command_needs_opt(module, idx) {
                    println!(
                        "command `{cnf_name}` carries an objective/soft constraints (use :optimize {cnf_name} instead of :solve)"
                    );
                    return;
                }
                let kind = match &module.commands.get(idx).map(|c| &c.kind) {
                    Some(CommandKind::Check(_)) => CnfKind::Check,
                    _ => CnfKind::Run,
                };
                let built = match kind {
                    CnfKind::Run => run(module, idx),
                    CnfKind::Check => check(module, idx),
                };
                match built {
                    Ok(cnf) => {
                        for w in &cnf.warnings {
                            println!("{w}");
                        }
                        let auto = self.store_cnf(cnf, None);
                        println!("auto-built cnf `{auto}` from command `{cnf_name}`");
                        cnf_name = auto;
                        self.cnfs.get(&cnf_name).cloned().expect("just stored")
                    }
                    Err(e) => {
                        println!("build error: {e}");
                        return;
                    }
                }
            }
        };
        if cnf.is_check() {
            self.do_solve_check(&cnf_name, &cnf, as_name);
        } else {
            self.do_solve_run(&cnf_name, &cnf, as_name);
        }
    }

    /// Transient wrapping rebuild of a stored Cnf (overflow prohibition
    /// OFF). Used for `run` fallback and `check` first phase. `None`
    /// when the module is gone (caller falls back to the stored Cnf).
    fn rebuild_wrapping(&self, cnf: &Cnf) -> Option<Cnf> {
        let module = self.module.as_ref()?;
        if cnf.command_index >= module.commands.len() {
            return None;
        }
        build_cnf_with(module, cnf.command_index, cnf.kind, false).ok()
    }

    /// `run`: overflow-free model first (stored gated Cnf); only when
    /// that is UNSAT, fall back to a wrapping model (transient rebuild).
    /// An explicit `no Overflow` marker disables the fallback (it would
    /// violate the marker); `some Overflow` Cnfs already solve wrapping
    /// via a CEGAR loop, so they never reach the fallback either.
    fn do_solve_run(&mut self, cnf_name: &str, cnf: &Cnf, as_name: Option<&str>) {
        // `some Overflow` models use overflow by construction: note them
        // as such instead of "overflow-free".
        let some_mode = cnf.overflow == Some(OverflowMode::Some);
        if cnf.is_temporal {
            match solve_temporal(cnf) {
                Ok(Some(trace)) => {
                    self.print_temporal_solution(&Some(trace.clone()), false);
                    if some_mode {
                        println!("note: overflowing model (some Overflow)");
                    } else {
                        println!("note: overflow-free model");
                    }
                    let first = trace.states().first().cloned();
                    let sol_name =
                        self.store_sol(as_name, cnf_name, true, first, None, Some(trace));
                    println!("saved solution `{sol_name}` <- `{cnf_name}` *default");
                }
                Ok(None) => {
                    // Explicit markers fix the search mode: no fallback.
                    if cnf.overflow.is_some() {
                        self.print_temporal_solution(&None, false);
                        return;
                    }
                    match self.rebuild_wrapping(cnf) {
                    Some(wrap) => match solve_temporal(&wrap) {
                        Ok(Some(trace)) => {
                            self.print_temporal_solution(&Some(trace.clone()), false);
                            println!(
                                "note: wrapping model (no overflow-free model at bitwidth {}; try a larger 'for N Int')",
                                cnf.bitwidth
                            );
                            let first = trace.states().first().cloned();
                            let sol_name =
                                self.store_sol(as_name, cnf_name, true, first, None, Some(trace));
                            println!("saved solution `{sol_name}` <- `{cnf_name}` *default");
                        }
                        Ok(None) => self.print_temporal_solution(&None, false),
                        Err(e) => println!("solve error: {e}"),
                    },
                    None => self.print_temporal_solution(&None, false),
                    }
                },
                Err(e) => println!("solve error: {e}"),
            }
            return;
        }
        match solve(cnf) {
            Ok(Some(inst)) => {
                self.print_solution(&Some(inst.clone()), false);
                if some_mode {
                    println!("note: overflowing model (some Overflow)");
                } else {
                    println!("note: overflow-free model");
                }
                let sol_name = self.store_sol(as_name, cnf_name, true, Some(inst), None, None);
                println!("saved solution `{sol_name}` <- `{cnf_name}` *default");
            }
            Ok(None) => {
                // Explicit markers fix the search mode: no fallback.
                if cnf.overflow.is_some() {
                    self.print_solution(&None, false);
                    return;
                }
                match self.rebuild_wrapping(cnf) {
                Some(wrap) => match solve(&wrap) {
                    Ok(Some(inst)) => {
                        self.print_solution(&Some(inst.clone()), false);
                        println!(
                            "note: wrapping model (no overflow-free model at bitwidth {}; try a larger 'for N Int')",
                            cnf.bitwidth
                        );
                        let sol_name =
                            self.store_sol(as_name, cnf_name, true, Some(inst), None, None);
                        println!("saved solution `{sol_name}` <- `{cnf_name}` *default");
                    }
                    Ok(None) => self.print_solution(&None, false),
                    Err(e) => println!("solve error: {e}"),
                },
                None => self.print_solution(&None, false),
                }
            },
            Err(e) => println!("solve error: {e}"),
        }
    }

    /// `check`: wrapping model first (surprising counterexamples surface);
    /// UNSAT here means the assertion holds, no second phase needed
    /// (gates only remove models). Counterexamples using overflow get a note.
    fn do_solve_check(&mut self, cnf_name: &str, cnf: &Cnf, as_name: Option<&str>) {
        // Prefer the wrapping search; fall back to the stored (gated) Cnf
        // only when the module is gone and no rebuild is possible.
        let owned;
        let target = match self.rebuild_wrapping(cnf) {
            Some(w) => {
                owned = w;
                &owned
            }
            None => cnf,
        };
        if target.is_temporal {
            match solve_temporal(target) {
                Ok(trace) => {
                    let sat = trace.is_some();
                    self.print_temporal_solution(&trace, true);
                    if let Some(t) = trace.as_ref() {
                        self.print_overflow_note_temporal(target, t);
                    }
                    let first = trace.as_ref().and_then(|t| t.states().first().cloned());
                    let sol_name =
                        self.store_sol(as_name, cnf_name, sat, first, None, trace);
                    println!("saved solution `{sol_name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
            return;
        }
        match solve(target) {
            Ok(inst) => {
                let sat = inst.is_some();
                self.print_solution(&inst, true);
                if let Some(i) = inst.as_ref() {
                    self.print_overflow_note(target, i);
                }
                let sol_name = self.store_sol(as_name, cnf_name, sat, inst, None, None);
                println!("saved solution `{sol_name}` <- `{cnf_name}` *default");
            }
            Err(e) => println!("solve error: {e}"),
        }
    }

    /// Evaluator-based overflow note for a static model: set when any
    /// integer operation overflows the problem bitwidth (div-by-zero
    /// included, which also surfaces as [`EvalError::DivideByZero`]).
    fn print_overflow_note(&self, cnf: &Cnf, inst: &Instance) {
        let ev = Evaluator::new(inst).with_bitwidth(cnf.bitwidth);
        let empty_env = Vec::new();
        let _ = ev.formula_bool(&cnf.arena, cnf.formula, &empty_env);
        if ev.overflowed() {
            println!(
                "note: counterexample uses integer overflow (re-check with a larger 'for N Int' to confirm)"
            );
        }
    }

    /// Temporal variant of [`Self::print_overflow_note`].
    fn print_overflow_note_temporal(&self, cnf: &Cnf, trace: &TemporalInstance) {
        let Some(orig) = cnf.orig_formula else {
            return;
        };
        let ev = TemporalEval::new(trace).with_bitwidth(cnf.bitwidth);
        let _ = ev.holds(&cnf.arena, orig);
        if ev.overflowed() {
            println!(
                "note: counterexample uses integer overflow (re-check with a larger 'for N Int' to confirm)"
            );
        }
    }

    /// Enumerate the next model (`:next [sol] [as <sol>]`).
    ///
    /// Opens (or reuses) a persistent incremental session on the target
    /// solution's origin Cnf, permanently blocks every known SAT solution
    /// from that Cnf, and solves again. A fresh model is saved under
    /// `as <sol>` (or an auto name) and becomes the default; exhaustion
    /// prints UNSAT without storing anything.
    fn do_next(&mut self, sol_arg: Option<&str>, as_name: Option<&str>) {
        if let Some(n) = as_name {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let sol_name = match sol_arg {
            Some(n) => n.to_string(),
            None => match self.default_sol_name() {
                Some(n) => n,
                None => {
                    println!("no solution saved yet (use :solve first)");
                    return;
                }
            },
        };
        let stored = match self.sols.get(&sol_name) {
            Some(s) => s,
            None => {
                println!("no solution named `{sol_name}` (:sols to list)");
                return;
            }
        };
        if !stored.sat || stored.instance.is_none() {
            println!("solution `{sol_name}` is UNSAT (nothing to enumerate past)");
            return;
        }
        if stored.from_cnf.is_empty() {
            println!("solution `{sol_name}` is from :eval (no Cnf context for :next)");
            return;
        }
        let cnf_name = stored.from_cnf.clone();
        let cnf = match self.cnfs.get(&cnf_name) {
            Some(c) => c.clone(),
            None => {
                println!("command for `{sol_name}` is gone (rebuild with :run|:check)");
                return;
            }
        };
        if !self.enum_sessions.contains_key(&cnf_name) {
            match IncrementalSession::open(&cnf) {
                Ok(session) => {
                    self.enum_sessions.insert(
                        cnf_name.clone(),
                        EnumSession {
                            session,
                            blocked: HashSet::new(),
                        },
                    );
                }
                Err(e) => {
                    println!("solve error: {e}");
                    return;
                }
            }
        }
        // Block every known SAT solution from this Cnf that is not blocked
        // yet (covers branched `:solve`s alongside the linear `:next` chain).
        let already = self
            .enum_sessions
            .get(&cnf_name)
            .map(|e| e.blocked.clone())
            .unwrap_or_default();
        let mut pending: Vec<(String, Instance)> = Vec::new();
        for name in &self.sol_order {
            if already.contains(name) {
                continue;
            }
            if let Some(st) = self.sols.get(name) {
                if st.from_cnf == cnf_name && st.sat {
                    if let Some(inst) = st.instance.clone() {
                        pending.push((name.clone(), inst));
                    }
                }
            }
        }
        if pending.is_empty() {
            println!("note: no stored solutions left to block (use :solve first)");
            return;
        }
        let es = match self.enum_sessions.get_mut(&cnf_name) {
            Some(e) => e,
            None => {
                println!("solve error: enumeration session lost");
                return;
            }
        };
        let mut excludable = 0;
        for (name, inst) in pending.iter() {
            match es.session.block_instance(inst) {
                Ok(true) => {
                    excludable += 1;
                    es.blocked.insert(name.clone());
                }
                Ok(false) => {
                    println!(
                        "note: solution `{name}` covers no primary variables; cannot exclude it"
                    );
                    es.blocked.insert(name.clone());
                }
                Err(e) => {
                    println!("solve error: {e}");
                    return;
                }
            }
        }
        if excludable == 0 {
            println!("cannot enumerate: no excludable model (formula has no primary variables)");
            return;
        }
        let next = match es.session.solve(&[]) {
            Ok(v) => v,
            Err(e) => {
                println!("solve error: {e}");
                return;
            }
        };
        if cnf.is_temporal {
            match next {
                Some(flat) => {
                    let exp = match cnf.temporal.as_ref() {
                        Some(e) => e,
                        None => {
                            println!("solve error: temporal Cnf lacks expansion metadata");
                            return;
                        }
                    };
                    match alloy_kodkod_rs::temporal::extract_temporal_instance(&flat, exp) {
                        Ok(ti) => {
                            let first = ti.states().first().cloned();
                            self.print_temporal_solution(&Some(ti.clone()), cnf.is_check());
                            let name =
                                self.store_sol(as_name, &cnf_name, true, first, None, Some(ti));
                            println!("saved solution `{name}` <- `{cnf_name}` *default");
                        }
                        Err(e) => println!("solve error: {e}"),
                    }
                }
                None => self.print_temporal_solution(&None, cnf.is_check()),
            }
            return;
        }
        match next {
            Some(inst) => {
                self.print_solution(&Some(inst.clone()), cnf.is_check());
                let name = self.store_sol(as_name, &cnf_name, true, Some(inst), None, None);
                println!("saved solution `{name}` <- `{cnf_name}` *default");
            }
            None => self.print_solution(&None, cnf.is_check()),
        }
    }

    /// Optimize over a stored Cnf (`:max`/`:min`/`:maxw`/`:minw`).
    /// Prints the optimum cost with the model and saves the solution
    /// (with cost) under `as_name` or an auto name.
    fn do_optimize(&mut self, target: OptTarget, cnf_arg: Option<&str>, as_name: Option<&str>) {
        if let Some(n) = as_name {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let module = match &self.module {
            Some(m) => m,
            None => {
                println!("no module loaded");
                return;
            }
        };
        let cnf_name = match cnf_arg {
            Some(n) => n.to_string(),
            None => match self.default_cnf_name() {
                Some(n) => n,
                None => {
                    println!("no cnf selected (use :run|:check first, :cnfs to list)");
                    return;
                }
            },
        };
        let cnf = match self.resolve_cnf(&cnf_name) {
            Some(c) => c.clone(),
            None => {
                println!("no cnf named `{cnf_name}` (:cnfs to list)");
                return;
            }
        };
        if cnf.is_temporal {
            println!("temporal cnf `{cnf_name}` is not supported by :max/:min (objectives over traces are undefined; solve the trace with :solve instead)");
            return;
        }
        // `some Overflow` Cnfs are built wrapping: a single wrapping
        // search (the OLL loop has no CEGAR). `no Overflow` pins gated.
        if cnf.overflow == Some(OverflowMode::Some) {
            match optimize_with(module, &cnf, &target, false) {
                Ok(sol) => {
                    let mut note = String::from("note: wrapping optimum (some Overflow)");
                    if sol.satisfiable && optimum_uses_overflow(&cnf, &sol) {
                        note.push_str("; optimum uses integer overflow");
                    }
                    self.print_store_opt_solution(&sol, &cnf_name, as_name, Some(&note));
                }
                Err(e) => println!("optimize error: {e}"),
            }
            return;
        }
        match optimize(module, &cnf, &target) {
            Ok(sol) => {
                if sol.satisfiable {
                    self.print_store_opt_solution(&sol, &cnf_name, as_name, None);
                    if cnf.overflow.is_none() {
                        println!("note: overflow-free optimum");
                    }
                    return;
                }
                // Gated optimum UNSAT: fall back to wrapping unless an
                // explicit marker pins the mode.
                if cnf.overflow.is_some() {
                    self.print_store_opt_solution(&sol, &cnf_name, as_name, None);
                    return;
                }
                match self.rebuild_wrapping(&cnf) {
                    Some(wrap) => match optimize_with(module, &wrap, &target, false) {
                        Ok(sol2) => {
                            let note = Self::wrapping_optimum_note(cnf.bitwidth, &sol2);
                            self.print_store_opt_solution(
                                &sol2,
                                &cnf_name,
                                as_name,
                                note.as_deref(),
                            );
                        }
                        Err(e) => println!("optimize error: {e}"),
                    },
                    None => self.print_store_opt_solution(&sol, &cnf_name, as_name, None),
                }
            }
            Err(e) => println!("optimize error: {e}"),
        }
    }

    /// Run a stored maximize/minimize (or soft-bearing run/check) command
    /// through the optimizer (`:optimize` and bare `minimize <ref>`).
    fn do_optimize_command(&mut self, target: Option<&str>, as_name: Option<&str>) {
        if let Some(n) = as_name {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let module = match &self.module {
            Some(m) => m,
            None => {
                println!("no module loaded");
                return;
            }
        };
        let idx = match self.resolve_index(target) {
            Ok(i) => i,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        if !command_needs_opt(module, idx) {
            println!("command is a plain run/check (no optimum to find; use :solve)");
            return;
        }
        // Label for the saved solution: explicit `as` name, else the
        // command name (or index) with an `opt` marker.
        let from_label = match module.commands.get(idx) {
            Some(c) => match &c.kind {
                CommandKind::Maximize { name: n, .. } | CommandKind::Minimize { name: n, .. } => {
                    n.clone().unwrap_or_else(|| format!("opt{idx}"))
                }
                _ => format!("opt{idx}"),
            },
            None => format!("opt{idx}"),
        };
        // `some`/`no Overflow` marker mode of the command body, if any:
        // `No` pins the gated search, `Some` the wrapping one, absent
        // means two-phase (gated optimum first, wrapping fallback).
        // The second tuple element is the problem bitwidth for notes.
        let (mode, bitwidth) = self.command_overflow(idx);
        match run_opt_command_with(module, idx, mode != Some(OverflowMode::Some)) {
            Ok(sol) => {
                if sol.satisfiable {
                    let note: Option<String> = match mode {
                        Some(OverflowMode::Some) => {
                            Some("note: wrapping optimum (some Overflow)".to_string())
                        }
                        _ => Some("note: overflow-free optimum".to_string()),
                    };
                    self.print_store_opt_solution(&sol, &from_label, as_name, note.as_deref());
                    return;
                }
                // Gated optimum UNSAT: fall back to wrapping unless an
                // explicit marker pins the mode.
                if mode.is_some() {
                    self.print_store_opt_solution(&sol, &from_label, as_name, None);
                    return;
                }
                match run_opt_command_with(module, idx, false) {
                    Ok(sol2) => {
                        let note = Self::wrapping_optimum_note(bitwidth, &sol2);
                        self.print_store_opt_solution(&sol2, &from_label, as_name, note.as_deref());
                    }
                    Err(e) => println!("optimize error: {e}"),
                }
            }
            Err(e) => println!("optimize error: {e}"),
        }
    }

    /// `some`/`no Overflow` marker mode of a command body (`None` when
    /// absent) plus the problem bitwidth (0 when the body does not
    /// lower). Re-lowers the command; used only for mode/note decisions,
    /// the actual searches lower again themselves.
    fn command_overflow(&self, idx: usize) -> (Option<OverflowMode>, u32) {
        let Some(module) = self.module.as_ref() else {
            return (None, 0);
        };
        match Lowerer::new(module).prepare_command(idx) {
            Ok(p) => (p.overflow, p.bitwidth),
            Err(_) => (None, 0),
        }
    }

    /// Print an optimization result and save it as a solution.
    /// `from_label` names the origin (a Cnf name, or a command label for
    /// `:optimize`, which carries no Cnf context like `:eval` solutions).
    /// Temporal optima carry the projected lasso trace: it is printed and
    /// stored (with state 0 kept as the queryable instance).
    fn print_store_opt_solution(
        &mut self,
        sol: &OptSolution,
        from_label: &str,
        as_name: Option<&str>,
        note: Option<&str>,
    ) {
        if sol.satisfiable {
            match sol.cost {
                Some(c) => println!("SAT -- optimum found: cost={c}"),
                None => println!("SAT -- optimum found"),
            }
            if let Some(ref ti) = sol.temporal {
                println!("trace: steps={} loop={}", ti.len(), ti.loop_state());
                for (i, st) in ti.states().iter().enumerate() {
                    println!("--- state {i} ---");
                    println!("{}", fmt::instance_alloy_hinted(st, &self.display_hints()));
                }
                println!("note: :query/:psave see state 0; :show <sol> reprints the trace");
            } else if let Some(ref inst) = sol.instance {
                println!("{}", fmt::instance_alloy_hinted(inst, &self.display_hints()));
            }
            if let Some(n) = note {
                println!("{n}");
            }
        } else {
            println!("UNSAT -- no model (empty)");
        }
        let sat = sol.satisfiable;
        let (instance, temporal) = match sol.temporal.clone() {
            Some(ti) => (ti.states().first().cloned(), Some(ti)),
            None => (sol.instance.clone(), None),
        };
        let sol_name = self.store_sol(as_name, from_label, sat, instance, sol.cost, temporal);
        println!("saved solution `{sol_name}` <- `{from_label}` *default");
    }

/// Wrapping-optimum note for the two-phase fallback (Phase 2): the
/// cost itself may be a wrapping artifact. `None` when unsatisfiable.
fn wrapping_optimum_note(bitwidth: u32, sol: &OptSolution) -> Option<String> {
    if !sol.satisfiable {
        return None;
    }
    Some(match sol.cost {
        Some(c) => format!(
            "note: wrapping optimum cost={c} (no overflow-free optimum at bitwidth {bitwidth}; cost may reflect wrapping; try a larger 'for N Int')"
        ),
        None => format!(
            "note: wrapping optimum (no overflow-free optimum at bitwidth {bitwidth}; try a larger 'for N Int')"
        ),
    })
}

    fn do_eval_text(&mut self, expr: &str, save_as: Option<&str>) {
        if let Some(n) = save_as {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        if self.module.is_none() {
            println!("no module loaded");
            return;
        }
        match eval(&self.current_src, expr) {
            Ok(sol) => {
                self.print_solution(&sol.instance, false);
                if let Some(n) = save_as {
                    let sat = sol.satisfiable;
                    let name = self.store_sol(Some(n), "", sat, sol.instance, None, None);
                    println!("saved solution `{name}` (from :eval; no Cnf context) *default");
                }
            }
            Err(e) => println!("eval error: {e}"),
        }
    }

    fn do_query_text(&self, expr: &str, sol_arg: Option<&str>) {
        let sol_name = match sol_arg {
            Some(n) => n.to_string(),
            None => match self.default_sol_name() {
                Some(n) => n,
                None => {
                    println!(":query needs a solution (use :solve first; form: :query <expr> [in <sol>])");
                    return;
                }
            },
        };
        let stored = match self.sols.get(&sol_name) {
            Some(s) => (
                s.from_cnf.clone(),
                s.instance.clone(),
                s.temporal.is_some(),
            ),
            None => {
                println!("no solution named `{sol_name}` (:sols to list)");
                return;
            }
        };
        let (from_cnf, inst_owned, is_temporal) = stored;
        if is_temporal {
            println!("note: temporal solution `{sol_name}`: querying state 0");
        }
        if from_cnf.is_empty() {
            println!("solution `{sol_name}` is from :eval (no Cnf context for :query)");
            return;
        }
        let inst_owned = match inst_owned {
            Some(i) => i,
            None => {
                println!("solution `{sol_name}` is UNSAT (no instance to query)");
                return;
            }
        };
        let cnf_owned = match self.cnfs.get(&from_cnf) {
            Some(c) => c.clone(),
            None => {
                println!("solution `{sol_name}` refers to cnf `{from_cnf}` which is gone");
                return;
            }
        };
        let m = match &self.module {
            Some(m) => m,
            None => {
                println!("no module loaded");
                return;
            }
        };
        let scope = match m.commands.get(cnf_owned.command_index) {
            Some(c) => &c.scope,
            None => {
                println!("command for `{sol_name}` is gone (rebuild with :run|:check)");
                return;
            }
        };
        match query_value(m, scope, &cnf_owned, expr, &inst_owned) {
            Ok(QueryValue::Set(arity, ts)) => {
                let hints = self.display_hints();
                let expr_t = expr.trim();
                // Integer display: a bare Signed sig name reads as its
                // bitmask value, as does a dotted `Owner.field` path with
                // Signed range (arity 1 = the collapsed single row,
                // arity 2 = per-owner rows).
                let (as_int, dotted) = match expr_t.split_once('.') {
                    None => (
                        arity == 1 && hints.signed_sigs.contains(expr_t),
                        None,
                    ),
                    Some((owner, field)) => {
                        let key = format!("{}.{}", owner.trim(), field.trim());
                        (
                            hints.signed_fields.contains(&key),
                            Some((owner.trim().to_string(), field.trim().to_string())),
                        )
                    }
                };
                if as_int && arity == 2 {
                    let (owner, field) = dotted.unwrap();
                    println!(
                        "{}",
                        fmt::field_rows_alloy(&inst_owned, &owner, &field, &ts)
                    )
                } else {
                    println!(
                        "{}",
                        fmt::set_alloy_maybe_int(ts.universe(), arity, &ts, as_int)
                    )
                }
            }
            Ok(QueryValue::Int(v)) => println!("{v}"),
            Ok(QueryValue::Bool(v)) => println!("{v}"),
            Err(e) => println!("query error: {e}"),
        }
    }

    fn do_bare_expr(&mut self, expr: &str) {
        if self.module.is_none() {
            println!("no module loaded");
            return;
        }
        match self.bare {
            BareMode::Eval => self.do_eval_text(expr, None),
            BareMode::Query => self.do_query_text(expr, None),
        }
    }

    /// Switch how bare expression lines are interpreted.
    fn do_mode(&mut self, arg: Option<&str>) {
        match arg {
            // No argument toggles between the two bare modes.
            None => {
                self.bare = match self.bare {
                    BareMode::Eval => BareMode::Query,
                    BareMode::Query => BareMode::Eval,
                };
                self.print_bare_mode();
            }
            Some("eval") => {
                self.bare = BareMode::Eval;
                self.print_bare_mode();
            }
            Some("query") => {
                self.bare = BareMode::Query;
                self.print_bare_mode();
            }
            Some(other) => println!("unknown mode `{other}` (usage: :mode [eval|query])"),
        }
    }

    fn print_bare_mode(&self) {
        match self.bare {
            BareMode::Eval => println!("bare mode: eval (bare lines run :eval)"),
            BareMode::Query => {
                println!("bare mode: query (bare lines run :query against the default solution)")
            }
        }
    }

    fn do_validate(&self, sol_arg: Option<&str>, cnf_arg: Option<&str>) {
        let sol_name = match sol_arg {
            Some(n) => n,
            None => match self.default_sol.as_deref() {
                Some(n) => n,
                None => {
                    println!("usage: :validate <sol> [in <cnf>]");
                    return;
                }
            },
        };
        let stored = match self.sols.get(sol_name) {
            Some(s) => s,
            None => {
                println!("no solution named `{sol_name}` (:sols to list)");
                return;
            }
        };
        let cnf_name: &str = match cnf_arg {
            Some(n) => n,
            None => {
                if stored.from_cnf.is_empty() {
                    println!("solution `{sol_name}` is from :eval (no Cnf to validate against)");
                    return;
                }
                &stored.from_cnf
            }
        };
        let cnf = match self.cnfs.get(cnf_name) {
            Some(c) => c,
            None => {
                println!("no cnf named `{cnf_name}` (:cnfs to list)");
                return;
            }
        };
        let inst = match &stored.instance {
            Some(i) => i,
            None => {
                println!("solution `{sol_name}` is UNSAT (no instance to validate)");
                return;
            }
        };
        if cnf.is_temporal {
            match &stored.temporal {
                Some(ti) => match validate_temporal(cnf, ti) {
                    Some(_) => println!(
                        "valid -- `{sol_name}` is a model of `{cnf_name}` (temporal steps={} loop={})",
                        ti.len(),
                        ti.loop_state()
                    ),
                    None => println!(
                        "invalid -- `{sol_name}` is not a model of `{cnf_name}` (none/empty)"
                    ),
                },
                None => println!(
                    "solution `{sol_name}` has no temporal trace (re-:solve `{cnf_name}` to record one)"
                ),
            }
            return;
        }
        match validate(cnf, inst) {
            Some(back) => {
                println!("valid -- `{sol_name}` is a model of `{cnf_name}`, as-is:");
                println!("{}", fmt::instance_alloy_hinted(&back, &self.display_hints()));
            }
            None => println!("invalid -- `{sol_name}` is not a model of `{cnf_name}` (none/empty)"),
        }
    }

    /// Inspect a binary partial instance (decode + summary, no solving).
    fn do_pread(&self, file: &str) {
        let bytes = match std::fs::read(file) {
            Ok(b) => b,
            Err(e) => {
                println!("cannot read {file}: {e}");
                return;
            }
        };
        let partial = match PartialInstance::decode(&bytes) {
            Ok(p) => p,
            Err(e) => {
                println!("{file}: {e}");
                return;
            }
        };
        println!(
            "apin {file}: universe {}, {} relations, {} ints, {} bytes",
            partial.universe_size,
            partial.rels.len(),
            partial.ints.len(),
            bytes.len()
        );
        for r in &partial.rels {
            println!("  {} ({}): {} tuples", r.name, r.arity, r.indices.len());
        }
        for p in &partial.ints {
            println!("  int {} -> {}", p.value, p.tuple);
        }
    }

    /// Pin a binary partial onto a Cnf in a throwaway session and solve.
    ///
    /// `gated` wraps the units in one fresh selector (retractable shape);
    /// in a one-shot session the outcome equals permanent units — the flag
    /// exists for forward compatibility with persistent sessions.
    #[allow(clippy::too_many_arguments)]
    fn do_ppin(
        &mut self,
        file: &str,
        rels: &[&str],
        cnf_arg: Option<&str>,
        sol_arg: Option<&str>,
        gated: bool,
    ) {
        if let Some(n) = sol_arg {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let mut partial = match read_partial(file) {
            Ok(p) => p,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        if !rels.is_empty() {
            partial = match partial.project(rels) {
                Ok(p) => p,
                Err(e) => {
                    println!("{e}");
                    return;
                }
            };
        }
        let (cnf_name, cnf) = match self.resolve_cnf_owned(cnf_arg) {
            Ok(v) => v,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        if cnf.is_temporal {
            println!("temporal cnf `{cnf_name}` is not supported by :ppin yet (expanded bounds)");
            return;
        }
        let mut sess = match IncrementalSession::open(&cnf) {
            Ok(s) => s,
            Err(e) => {
                println!("session error: {e}");
                return;
            }
        };
        if gated {
            let sel = match partial.apply_gated(&mut sess) {
                Ok(sel) => sel,
                Err(e) => {
                    println!("pin error: {e}");
                    return;
                }
            };
            println!(
                "pinned {} (gated #{sel}) from {file}",
                partial_summary(&partial)
            );
            match sess.solve(&[sel]) {
                Ok(inst) => {
                    self.print_solution(&inst, cnf.is_check());
                    let sat = inst.is_some();
                    let name = self.store_sol(sol_arg, &cnf_name, sat, inst, None, None);
                    println!("saved solution `{name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
        } else {
            let n = match partial.apply_units(&mut sess) {
                Ok(n) => n,
                Err(e) => {
                    println!("pin error: {e}");
                    return;
                }
            };
            println!(
                "pinned {n} units from {file} ({})",
                partial_summary(&partial)
            );
            match sess.solve(&[]) {
                Ok(inst) => {
                    self.print_solution(&inst, cnf.is_check());
                    let sat = inst.is_some();
                    let name = self.store_sol(sol_arg, &cnf_name, sat, inst, None, None);
                    println!("saved solution `{name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
        }
    }

    /// Exclude a binary partial (nogood over its value) and solve.
    #[allow(clippy::too_many_arguments)]
    fn do_pavoid(
        &mut self,
        file: &str,
        rels: &[&str],
        cnf_arg: Option<&str>,
        sol_arg: Option<&str>,
        gated: bool,
    ) {
        if let Some(n) = sol_arg {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let partial = match read_partial(file) {
            Ok(p) => p,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        let (cnf_name, cnf) = match self.resolve_cnf_owned(cnf_arg) {
            Ok(v) => v,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        if cnf.is_temporal {
            println!("temporal cnf `{cnf_name}` is not supported by :pavoid yet (expanded bounds)");
            return;
        }
        let mut sess = match IncrementalSession::open(&cnf) {
            Ok(s) => s,
            Err(e) => {
                println!("session error: {e}");
                return;
            }
        };
        let project: Option<Vec<&str>> = if rels.is_empty() {
            None
        } else {
            Some(rels.to_vec())
        };
        let clause = match partial.avoid_clause(&sess, project.as_deref()) {
            Ok(c) => c,
            Err(e) => {
                println!("avoid error: {e}");
                return;
            }
        };
        if clause.is_empty() {
            println!("nothing to exclude (scope covers no free cells)");
            return;
        }
        if gated {
            let sel = match sess.add_gated(std::slice::from_ref(&clause)) {
                Ok(sel) => sel,
                Err(e) => {
                    println!("avoid error: {e}");
                    return;
                }
            };
            println!(
                "avoiding {} (gated #{sel}, {} lits) from {file}",
                partial_summary(&partial),
                clause.len()
            );
            match sess.solve(&[sel]) {
                Ok(inst) => {
                    self.print_solution(&inst, cnf.is_check());
                    let sat = inst.is_some();
                    let name = self.store_sol(sol_arg, &cnf_name, sat, inst, None, None);
                    println!("saved solution `{name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
        } else {
            match sess.add_clauses(std::slice::from_ref(&clause)) {
                Ok(()) => {}
                Err(e) => {
                    println!("avoid error: {e}");
                    return;
                }
            }
            println!(
                "avoiding {} ({} lits) from {file}",
                partial_summary(&partial),
                clause.len()
            );
            match sess.solve(&[]) {
                Ok(inst) => {
                    self.print_solution(&inst, cnf.is_check());
                    let sat = inst.is_some();
                    let name = self.store_sol(sol_arg, &cnf_name, sat, inst, None, None);
                    println!("saved solution `{name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
        }
    }

    /// Resolve a solution reference to an owned (name, instance) pair.
    fn sol_instance(&self, sol_arg: Option<&str>) -> Result<(String, Instance), String> {
        let sol_name = match sol_arg {
            Some(n) => n.to_string(),
            None => self
                .default_sol
                .clone()
                .ok_or_else(|| "no solution saved yet (use :solve first)".to_string())?,
        };
        let stored = self
            .sols
            .get(&sol_name)
            .ok_or_else(|| format!("no solution named `{sol_name}` (:sols to list)"))?;
        let inst = stored
            .instance
            .clone()
            .ok_or_else(|| format!("solution `{sol_name}` is UNSAT (nothing to use)"))?;
        Ok((sol_name, inst))
    }

    /// Resolve a Cnf reference to an owned (name, Cnf) pair.
    fn resolve_cnf_owned(&self, arg: Option<&str>) -> Result<(String, Cnf), String> {
        let name = match arg {
            Some(n) => n.to_string(),
            None => self.default_cnf.clone().ok_or_else(|| {
                "no cnf selected (use :run|:check first, :cnfs to list)".to_string()
            })?,
        };
        let cnf = match self.cnfs.get(&name) {
            Some(c) => c.clone(),
            None => {
                if self.module.is_some() && self.resolve_index(Some(&name)).is_ok() {
                    return Err(format!(
                        "no cnf named `{name}` (did you mean :run {name} first?)"
                    ));
                }
                return Err(format!("no cnf named `{name}` (:cnfs to list)"));
            }
        };
        Ok((name, cnf))
    }

    /// Write a (partial) instance in binary APIN form (lossless, incl. ints).
    /// Relation filter takes an exact pool name or a unique bare field; no
    /// Alloy-reference filtering applies since indices transfer directly.
    fn do_psave(&self, file: &str, sol_arg: Option<&str>, rels: &[&str]) {
        let (sol_name, inst) = match self.sol_instance(sol_arg) {
            Ok(v) => v,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        if self
            .sols
            .get(&sol_name)
            .is_some_and(|s| s.temporal.is_some())
        {
            println!("note: temporal solution `{sol_name}`: saving state 0");
        }
        let pool = inst.pool();
        let all_names: Vec<String> = inst
            .relation_tuples()
            .map(|(r, _)| pool.name(r).to_string())
            .collect();
        let only_owned: Option<Vec<String>> = if rels.is_empty() {
            None
        } else {
            let mut out = Vec::new();
            for want in rels {
                if all_names.iter().any(|n| n == want) {
                    out.push(want.to_string());
                } else if let Some(hit) = unique_bare_field(&all_names, want) {
                    out.push(hit);
                } else {
                    println!("no relation `{want}` in solution `{sol_name}`");
                    return;
                }
            }
            Some(out)
        };
        let only_refs: Option<Vec<&str>> = only_owned
            .as_ref()
            .map(|v| v.iter().map(|s| s.as_str()).collect());
        let partial = match PartialInstance::extract(&inst, only_refs.as_deref()) {
            Ok(p) => p,
            Err(e) => {
                println!("extract error: {e}");
                return;
            }
        };
        let bytes = partial.encode();
        match std::fs::write(file, &bytes) {
            Ok(()) => {
                let mut msg = format!(
                    "saved {file} (.apin from `{sol_name}`, {} relations, {} ints, {} bytes)",
                    partial.rels.len(),
                    partial.ints.len(),
                    bytes.len()
                );
                if !partial.skipped_skolem.is_empty() {
                    msg.push_str(&format!(
                        "; skipped {} skolem",
                        partial.skipped_skolem.len()
                    ));
                }
                println!("{msg}");
            }
            Err(e) => println!("cannot write {file}: {e}"),
        }
    }

    fn show_cnf(&self, name: &str, limit: usize) {
        let cnf = match self.cnfs.get(name) {
            Some(c) => c,
            None => {
                println!("no cnf named `{name}` (:cnfs to list)");
                return;
            }
        };
        println!("cnf `{name}`: {}", cnf.summary());
        println!("  bitwidth={} skolemize={}", cnf.bitwidth, cnf.skolemize);
        if cnf.is_temporal {
            println!("  temporal steps={} (expanded {} vars)", cnf.steps, cnf.num_vars);
        }
        for (i, cl) in cnf.clauses.iter().take(limit).enumerate() {
            let line: Vec<String> = cl.iter().map(|l| l.to_string()).collect();
            println!("  c{i}: {}", line.join(" "));
        }
        if cnf.clauses.len() > limit {
            println!("  ... ({} more clauses)", cnf.clauses.len() - limit);
        }
    }

    fn show_sol(&self, name: &str) {
        let s = match self.sols.get(name) {
            Some(s) => s,
            None => {
                println!("no solution named `{name}` (:sols to list)");
                return;
            }
        };
        match &s.instance {
            Some(inst) => {
                let kind = if s.from_cnf.is_empty() {
                    "SAT (from :eval)".to_string()
                } else {
                    format!("SAT <- `{}`", s.from_cnf)
                };
                if let Some(ti) = &s.temporal {
                    let mut out = format!(
                        "solution `{name}`: {kind} temporal trace steps={} loop={}",
                        ti.len(),
                        ti.loop_state()
                    );
                    for (i, st) in ti.states().iter().enumerate() {
                        out.push_str(&format!(
                            "\n--- state {i} ---\n{}",
                            fmt::instance_alloy_hinted(st, &self.display_hints())
                        ));
                    }
                    println!("{out}");
                } else {
                    println!(
                        "solution `{name}`: {kind}\n{}",
                        fmt::instance_alloy_hinted(inst, &self.display_hints())
                    );
                }
            }
            None => println!("solution `{name}`: UNSAT (none / empty)"),
        }
    }

    /// `:show [name] [N]`: no args = both defaults; numeric-only = N for the
    /// default cnf; name (+ optional N) = that entry (cnf and/or solution).
    fn do_show(&self, args: &[&str]) {
        if args.is_empty() {
            match (&self.default_cnf, &self.default_sol) {
                (None, None) => println!("nothing to show (use :run then :solve)"),
                (Some(c), _) => {
                    self.show_cnf(c, 10);
                    if let Some(s) = &self.default_sol {
                        self.show_sol(s);
                    } else {
                        println!("no solution yet (:solve {c})");
                    }
                }
                (None, Some(s)) => self.show_sol(s),
            }
            return;
        }
        if args.len() == 1 && args[0].parse::<usize>().is_ok() {
            let limit: usize = args[0].parse().unwrap_or(10);
            match &self.default_cnf {
                Some(c) => self.show_cnf(c, limit),
                None => println!("no cnf selected (:cnfs to list)"),
            }
            return;
        }
        let name = args[0];
        let limit: usize = args.get(1).and_then(|a| a.parse().ok()).unwrap_or(10);
        let has_cnf = self.cnfs.contains_key(name);
        let has_sol = self.sols.contains_key(name);
        if !has_cnf && !has_sol {
            println!("no cnf or solution named `{name}` (:cnfs / :sols to list)");
            return;
        }
        if has_cnf {
            self.show_cnf(name, limit);
        }
        if has_sol {
            self.show_sol(name);
        }
    }

    fn submit_pending(&mut self, pending: Pending) {
        match pending.kind {
            InputKind::Decl => self.add_fragment(&pending.text),
            InputKind::Bare => self.do_bare_expr(&pending.text),
            InputKind::Eval => self.do_eval_text(&pending.text, pending.target.as_deref()),
            InputKind::Query => self.do_query_text(&pending.text, pending.target.as_deref()),
        }
    }
}

fn print_help() {
    println!("declare (accumulate into the model; re-enter a name to replace):");
    println!("  sig ... / fact ... / pred ... / fun ... / assert ... / open ...");
    println!("  partial <name> {{ R = S, L in R, ... }}  named partial instance");
    println!("    (`pin <name>` / `avoid <name>` in formulas; labels `Sig$tag`)");
    println!("  run ... / check ...      as a fragment when it names no command");
    println!("  multi-line continues on `... ` until braces balance;");
    println!("  blank line or a `:command` line submits pending input first");
    println!("named stores (Cnf and solution namespaces are separate):");
    println!("  :run <i|name> [as <cnf>]    build Cnf, save it (auto: command name, else run0..)");
    println!("  :check <i|name> [as <cnf>]  build negated Cnf, save it");
    println!("  :solve [<cnf>|<i|name>] [as <sol>]   solve named Cnf (no arg = *default), save solution");
    println!("                              a command index/name auto-builds its Cnf first");
    println!("                              temporal Cnfs print the full trace (steps + loop)");
    println!("  :next [<sol>] [as <sol>]    next model: block known solutions, re-solve");
    println!("                              (no arg = *default solution's Cnf; exhaustion = UNSAT)");
    println!("  :optimize [<i|name>] [as <sol>]  run a stored objective command, save optimum");
    println!("                              (a maximize/minimize command, or a run/check whose body has");
    println!("                              a `maximize`/`minimize` marker or soft constraints)");
    println!("  minimize ... / maximize ... (bare line: reference runs optimizer, else a model fragment)");
    println!("  `pred p {{ goal (maximize X) }}` + `run {{p}}`: in-body markers register the objective;");
    println!("    initially/goal/restore pick the trace state X is evaluated at");
    println!("  :query <expr> [in <sol>]    evaluate against named solution (no in = *default)");
    println!("                              sets print as tuples, int exprs (`#A`) as numbers");
    println!("    NOTE: `in` collides with Alloy `in`; the trailing `in <sol>` is used only");
    println!("    when <sol> names a stored solution, else the whole text is the expression.");
    println!("    Use `@ <sol>` as an unambiguous alternative: `:query A @ someA`.");
    println!("  :validate <sol> [in <cnf>]  validate solution vs Cnf (no in = its origin Cnf)");
    println!("  :show [name] [N]            show Cnf clauses and/or solution (no arg = defaults)");
    println!("  :eval <expr> [as <sol>]     satisfiability check (bare expr lifts with some)
  :mepk [-v] add|sub|mul|div (<m,e,p,k>|lit <dec>) (<m,e,p,k>|lit <dec>) [p <maxp>] [n <n>]
                            result as c ± R (tau); -v adds tuples and detail
  :mepk lit <decimal> [p <maxp>] [n <intcount>]
                            decimal literal to (m,e,p,k), optimal precision
  :mepk widths [n]          show lane widths from for-n-Int rule (+MEPK_* env)");
    println!("  :max <intexpr> [in <cnf>] [as <sol>]   maximize int expr, save optimum+cost");
    println!("  :min <intexpr> [in <cnf>] [as <sol>]   minimize int expr, save optimum+cost");
    println!("  :maxw <r>:<w>[, ...] [in <cnf>] [as <sol>]  maximize Σ w·#r");
    println!("  :minw <r>:<w>[, ...] [in <cnf>] [as <sol>]  minimize Σ w·#r");
    println!("    NOTE: trailing `in <cnf>` is used only when <cnf> names a stored");
    println!("    Cnf, else the whole text is the target.");
    println!("  <expr>                    bare line: :eval in eval mode, :query in query");
    println!("                            mode (never stored; switch via :mode)");
    println!("commands:");
    println!("  :load <file>        load .als model (fragments + stores cleared)");
    println!("  :list               list run/check commands in the module");
    println!("  :cnfs               list saved Cnfs (* = default)");
    println!("  :sols               list saved solutions (* = default)");
    println!("  :use <name>         switch default to a Cnf and/or solution");
    println!("  :mode [eval|query]  toggle/switch how bare lines read (:m; no arg toggles)");
    println!("  :fragments          list entered fragments");
    println!("  :drop <i>           delete fragment by index, rebuild (stores cleared)");
    println!("  :psave <file> [in <sol>] [rels...] write solution as binary partial (.apin)");
    println!("  :pread <file>       inspect a binary partial (no solving)");
    println!("  :ppin <file> [rels...] [to <cnf>] [as <sol>] [gated]");
    println!("                       pin a binary partial onto a Cnf, solve once");
    println!("  :pavoid <file> [rels...] [to <cnf>] [as <sol>] [gated]");
    println!("                       exclude a binary partial (nogood), solve once");
    println!("  :reset              drop entered fragments, keep :load file (stores cleared)");
    println!("  :help               this help");
    println!("  :quit               exit (Ctrl-D also exits)");
    println!("notes: `let` works inside pred/fun bodies and :eval/:query expressions.");
    println!("notes: integers are bitvectors: `for W Int` gives W atoms");
    println!("  {{0, .., W-1}} (bare `Int` = command default, else 4) with");
    println!("  (W+1)-bit circuits capped at 30. Sets read as bitmask values");
    println!("  (MSB atom weight -2^(W-1)): `X = 5` iff X = {{0, 2}};");
    println!("  bare `1+2` is an integer; use `{{1, 2}}` or `{{1}}+{{2}}` for sets.");
    println!("  `sig X in Signed` mirrors `Int`. Int atoms");
    println!("  are allocated lazily: models that never use Int as a set carry");
    println!("  none (queries like `Int` then read empty; add `for N Int` to");
    println!("  materialize the range).");
    println!("notes: builtin `EReal` (m,e,p,k) error-tracking pseudo-reals:");
    println!("  `sig A {{ x: EReal }}` then `x.m`, `x.e`, `x.p`, `x.k` read lanes;");
    println!("  `erealAdd/Sub/Mul/Div[a,b,c]`, `erealWellformed[x]`, `erealDivGuard[x]`;");
    println!("  `setEReal[x, 3.14]` binds lanes to a decimal literal (same as `:mepk lit`);");
    println!("  lane widths come from `for N Int` (+MEPK_*_WIDTH); `for N EReal` scopes atoms.");
}

/// Resolve an explicit `:psave` relation argument: exact pool name first,
/// then a unique bare field name.
fn unique_bare_field(all_names: &[String], want: &str) -> Option<String> {
    let mut hits = all_names
        .iter()
        .filter(|n| n.rsplit('.').next() == Some(want) && !n.contains('/') && *n != want);
    match (hits.next(), hits.next()) {
        (Some(one), None) => Some(one.clone()),
        _ => None,
    }
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
        "sig" | "abstract" | "fact" | "pred" | "fun" | "assert" | "open" | "partial" => true,
        "one" | "lone" | "some" | "var" => second_token(s) == "sig",
        _ => false,
    }
}

/// True when a field TYPE expression mentions `Signed` (so a Signed
/// range makes rows bitmask-readable). Mirrors the lowerer's
/// `mentions_int_expr`, restricted to `Signed`.
fn expr_is_signed(e: &Expr) -> bool {
    match e {
        Expr::Name(n, _) => n == "Signed",
        Expr::Bin(_, a, b) => expr_is_signed(a) || expr_is_signed(b),
        Expr::Transpose(x)
        | Expr::TClosure(x)
        | Expr::RClosure(x)
        | Expr::ArrowMult(_, x)
        | Expr::LeadMult(_, x)
        | Expr::Prime(x)
        | Expr::AtExpr(x) => expr_is_signed(x),
        Expr::Bracket(base, args) => {
            expr_is_signed(base) || args.iter().any(|a| expr_is_signed(a))
        }
        _ => false,
    }
}

/// True when a field TYPE expression mentions `EReal` (so rows decode to
/// `c ± R`). Same shape walk as `expr_is_signed`.
fn expr_is_ereal(e: &Expr) -> bool {
    match e {
        Expr::Name(n, _) => n == "EReal",
        Expr::Bin(_, a, b) => expr_is_ereal(a) || expr_is_ereal(b),
        Expr::Transpose(x)
        | Expr::TClosure(x)
        | Expr::RClosure(x)
        | Expr::ArrowMult(_, x)
        | Expr::LeadMult(_, x)
        | Expr::Prime(x)
        | Expr::AtExpr(x) => expr_is_ereal(x),
        Expr::Bracket(base, args) => {
            expr_is_ereal(base) || args.iter().any(|a| expr_is_ereal(a))
        }
        _ => false,
    }
}

fn brace_delta(s: &str) -> i32 {
    let code = s.split("//").next().unwrap_or("");
    let code = code.split("--").next().unwrap_or(code);
    code.chars().filter(|&c| c == '{').count() as i32
        - code.chars().filter(|&c| c == '}').count() as i32
}

fn is_valid_name(n: &str) -> bool {
    !n.is_empty()
        && n.chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '#' | '-'))
}

/// Whether an optimization result uses integer overflow (E-bit
/// evaluator flag on the optimum instance or trace).
fn optimum_uses_overflow(cnf: &Cnf, sol: &OptSolution) -> bool {
    if let Some(ti) = sol.temporal.as_ref() {
        let Some(orig) = cnf.orig_formula else {
            return false;
        };
        let ev = TemporalEval::new(ti).with_bitwidth(cnf.bitwidth);
        let _ = ev.holds(&cnf.arena, orig);
        return ev.overflowed();
    }
    match sol.instance.as_ref() {
        Some(inst) => {
            let ev = Evaluator::new(inst).with_bitwidth(cnf.bitwidth);
            let empty_env = Vec::new();
            let _ = ev.formula_bool(&cnf.arena, cnf.formula, &empty_env);
            ev.overflowed()
        }
        None => false,
    }
}

/// Split trailing `as <name>`: returns (head_tokens, as_name).
fn split_as<'a>(rest: &[&'a str]) -> (Vec<&'a str>, Option<&'a str>) {
    if let Some(pos) = rest.iter().position(|&t| t == "as") {
        let head = rest[..pos].to_vec();
        let tail = &rest[pos + 1..];
        if tail.len() == 1 {
            (head, Some(tail[0]))
        } else {
            // Malformed: let the caller emit usage. Encode by returning a
            // sentinel head that cannot resolve.
            (head, Some("__bad_as__"))
        }
    } else {
        (rest.to_vec(), None)
    }
}

/// Split a `:query` body into (expr, sol). The trailing `in <sol>` / `@ <sol>`
/// is honored only when `<sol>` is a single token; ambiguity with Alloy `in`
/// is resolved by the caller checking the solution store.
fn split_query_in<'a>(sess: &Session, body: &'a str) -> (&'a str, Option<&'a str>) {
    let toks: Vec<&str> = body.split_whitespace().collect();
    // Unambiguous `@` separator first.
    if let Some(pos) = toks.iter().rposition(|&t| t == "@") {
        if pos + 1 == toks.len() - 1 && pos > 0 {
            let cut = body.rfind('@').unwrap();
            return (body[..cut].trim(), Some(toks[pos + 1]));
        }
        return (body, None);
    }
    // `in`: use only if the trailing token names a stored solution.
    if let Some(pos) = toks.iter().rposition(|&t| t == "in") {
        if pos + 1 == toks.len() - 1 && pos > 0 {
            let cand = toks[pos + 1];
            if sess.sols.contains_key(cand) {
                // Re-cut on the last " in " occurrence.
                if let Some(cut) = body.rmatch_indices(" in ").next().map(|(i, _)| i) {
                    let expr = body[..cut].trim();
                    if !expr.is_empty() {
                        return (expr, Some(cand));
                    }
                }
            }
        }
    }
    (body, None)
}

/// Split a trailing `kw <single-token>` off raw text: (head, name).
/// Returns (raw, None) when the tail does not match.
fn split_trailing_kw<'a>(raw: &'a str, kw: &str) -> (&'a str, Option<&'a str>) {
    let toks: Vec<&str> = raw.split_whitespace().collect();
    if toks.len() >= 2 && toks[toks.len() - 2] == kw {
        let name = toks[toks.len() - 1];
        let pat = format!(" {kw} ");
        if let Some((cut, _)) = raw.rmatch_indices(pat.as_str()).next() {
            let head = raw[..cut].trim();
            if !head.is_empty() {
                return (head, Some(name));
            }
        }
    }
    (raw, None)
}

/// Split a `:max`/`:min`/`:maxw`/`:minw` body into (target, cnf, sol).
/// Forms: `<target> [in <cnf>] [as <sol>]`. The trailing `in <cnf>` is
/// honored only when `<cnf>` names a stored Cnf (disambiguates Alloy `in`).
fn split_opt_args<'a>(
    sess: &Session,
    raw: &'a str,
) -> Option<(&'a str, Option<&'a str>, Option<&'a str>)> {
    if raw.is_empty() {
        return None;
    }
    let (no_as, as_name) = split_trailing_kw(raw, "as");
    if let Some(n) = as_name {
        if !is_valid_name(n) {
            return None;
        }
    }
    let (target, cnf_name) = {
        let (head, cand) = split_trailing_kw(no_as, "in");
        match cand {
            Some(c) if sess.cnfs.contains_key(c) => (head, Some(c)),
            _ => (no_as, None),
        }
    };
    if target.is_empty() {
        return None;
    }
    Some((target, cnf_name, as_name))
}

/// Parse a `:maxw`/`:minw` weight list `R1: w1, R2: w2, ...`.
fn parse_weights_arg(text: &str) -> Option<Vec<(String, i64)>> {
    let mut out = Vec::new();
    for part in text.split(',') {
        let part = part.trim();
        let (name, w) = part.split_once(':')?;
        let name = name.trim();
        if name.is_empty() || !is_valid_name(name) {
            return None;
        }
        let w: i64 = w.trim().parse().ok()?;
        out.push((name.to_string(), w));
    }
    if out.is_empty() {
        return None;
    }
    Some(out)
}

/// Split `:psave` args into (file, sol, rels).
/// Forms: `<file>`, `<file> in <sol>`, either followed by relation names
/// (`+` tokens ignored, so `A + B` and `A B` agree).
fn parse_psave_args<'a>(
    rest: &[&'a str],
) -> Result<(&'a str, Option<&'a str>, Vec<&'a str>), &'static str> {
    const USAGE: &str = "usage: :psave <file> [in <sol>] [rels...]";
    if rest.is_empty() {
        return Err(USAGE);
    }
    let file = rest[0];
    let (sol, rels) = if rest.get(1) == Some(&"in") {
        if rest.len() < 3 {
            return Err(USAGE);
        }
        (Some(rest[2]), &rest[3..])
    } else {
        (None, &rest[1..])
    };
    // Relation names may be space- and/or `+`-separated (`B f`, `B+f`,
    // `B + f` all agree); `+` never occurs inside a name.
    let rels = rels
        .iter()
        .flat_map(|t| t.split('+'))
        .filter(|t| !t.is_empty())
        .collect();
    Ok((file, sol, rels))
}

/// Read and decode a binary partial instance file.
fn read_partial(file: &str) -> Result<PartialInstance, String> {
    let bytes = std::fs::read(file).map_err(|e| format!("cannot read {file}: {e}"))?;
    PartialInstance::decode(&bytes).map_err(|e| format!("{file}: {e}"))
}

/// One-line partial summary (`A + B (3 rels, 2 ints)`).
fn partial_summary(p: &PartialInstance) -> String {
    let mut s = if p.rels.is_empty() {
        "no relations".to_string()
    } else {
        p.rels
            .iter()
            .map(|r| r.name.clone())
            .collect::<Vec<_>>()
            .join(" + ")
    };
    s.push_str(&format!(" ({} rels, {} ints)", p.rels.len(), p.ints.len()));
    s
}

/// Parsed `:ppin`/`:pavoid` arguments.
struct PpinArgs<'a> {
    file: &'a str,
    rels: Vec<&'a str>,
    cnf: Option<&'a str>,
    sol: Option<&'a str>,
    gated: bool,
}

/// Split `:ppin`/`:pavoid` args: `<file> [rels...] [to <cnf>] [as <sol>] [gated]`.
/// Relation names may be `+`-joined (`B+f`, `B + f`, `B f` all agree).
/// `to`/`as`/`gated` are reserved words here (as with `in`/`as` elsewhere).
fn parse_ppin_args<'a>(
    rest: &[&'a str],
    usage: &'static str,
) -> Result<PpinArgs<'a>, &'static str> {
    if rest.is_empty() {
        return Err(usage);
    }
    let file = rest[0];
    let mut rels = Vec::new();
    let mut cnf = None;
    let mut sol = None;
    let mut gated = false;
    let mut i = 1;
    while i < rest.len() {
        match rest[i] {
            "to" => {
                i += 1;
                cnf = Some(*rest.get(i).ok_or(usage)?);
            }
            "as" => {
                i += 1;
                sol = Some(*rest.get(i).ok_or(usage)?);
            }
            "gated" => gated = true,
            t => {
                for part in t.split('+') {
                    if !part.is_empty() {
                        rels.push(part);
                    }
                }
            }
        }
        i += 1;
    }
    Ok(PpinArgs {
        file,
        rels,
        cnf,
        sol,
        gated,
    })
}

/// Split a `:validate` body into (sol, cnf). Forms: `<sol>`, `<sol> in <cnf>`,
/// `<sol> @ <cnf>`.
fn split_validate<'a>(rest: &[&'a str]) -> (Option<&'a str>, Option<&'a str>) {
    if rest.is_empty() {
        return (None, None);
    }
    if let Some(pos) = rest.iter().position(|&t| t == "in" || t == "@") {
        if pos == 0 || rest.len() != pos + 2 {
            return (Some("__bad__"), Some("__bad__"));
        }
        (Some(rest[0]), Some(rest[pos + 1]))
    } else if rest.len() == 1 {
        (Some(rest[0]), None)
    } else {
        (Some("__bad__"), Some("__bad__"))
    }
}

const BARE_COMMANDS: &[&str] = &[
    "help",
    "h",
    "?",
    "quit",
    "exit",
    "q",
    "load",
    "l",
    "list",
    "ls",
    "fragments",
    "drop",
    "save",
    "add",
    "psave",
    "pread",
    "ppin",
    "pavoid",
    "solve",
    "s",
    "next",
    "n",
    "validate",
    "v",
    "show",
    "reset",
    "cnfs",
    "sols",
    "use",
    "mode",
    "m",
    "query",
    "eval",
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
        let prompt = if sess.pending.is_some() {
            "... "
        } else {
            sess.bare.prompt()
        };
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
        if sess.pending.is_none() && (trimmed.starts_with("--") || trimmed.starts_with("//")) {
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
                "cnfs" => sess.list_cnfs(),
                "sols" => sess.list_sols(),
                "use" => match arg {
                    Some(n) => sess.do_use(n),
                    None => println!("usage: :use <cnf|sol>"),
                },
                "mode" | "m" => sess.do_mode(arg),
                "fragments" => sess.list_fragments(),
                "drop" => {
                    if rest.len() != 1 {
                        println!("usage: :drop <fragment-index> (:fragments to list)");
                    } else {
                        sess.drop_fragment(arg);
                    }
                }
                "psave" => match parse_psave_args(&rest) {
                    Ok((file, sol, rels)) => sess.do_psave(file, sol, &rels),
                    Err(usage) => println!("{usage}"),
                },
                "pread" => match arg {
                    Some(p) => sess.do_pread(p),
                    None => println!("usage: :pread <file>"),
                },
                "ppin" => match parse_ppin_args(
                    &rest,
                    "usage: :ppin <file> [rels...] [to <cnf>] [as <sol>] [gated]",
                ) {
                    Ok(a) => sess.do_ppin(a.file, &a.rels, a.cnf, a.sol, a.gated),
                    Err(usage) => println!("{usage}"),
                },
                "pavoid" => match parse_ppin_args(
                    &rest,
                    "usage: :pavoid <file> [rels...] [to <cnf>] [as <sol>] [gated]",
                ) {
                    Ok(a) => sess.do_pavoid(a.file, &a.rels, a.cnf, a.sol, a.gated),
                    Err(usage) => println!("{usage}"),
                },
                "reset" => {
                    sess.fragments.clear();
                    sess.rebuild("reset");
                }
                "run" | "check" => {
                    let kind = if cmd == "run" {
                        CnfKind::Run
                    } else {
                        CnfKind::Check
                    };
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: :{cmd} <index|name> [as <cnf>]");
                    } else {
                        sess.do_build(kind, head.first().copied(), as_name);
                    }
                }
                "solve" | "s" => {
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: :solve [<cnf>] [as <sol>]");
                    } else {
                        sess.do_solve(head.first().copied(), as_name);
                    }
                }
                "next" | "n" => {
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: :next [<sol>] [as <sol>]");
                    } else {
                        sess.do_next(head.first().copied(), as_name);
                    }
                }
                "optimize" => {
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: :optimize [<index|name>] [as <sol>]");
                    } else {
                        sess.do_optimize_command(head.first().copied(), as_name);
                    }
                }
                "max" | "min" => {
                    let raw = body[cmd.len()..].trim();
                    let usage = "usage: :max|:min <intexpr> [in <cnf>] [as <sol>]";
                    match split_opt_args(&sess, raw) {
                        None => println!("{usage}"),
                        Some((expr, cnf, sol)) => match parse_int_expr(expr) {
                            Err(e) => println!("int expr error: {e}"),
                            Ok(ie) => {
                                let sense = if cmd == "max" {
                                    KkOptSense::Maximize
                                } else {
                                    KkOptSense::Minimize
                                };
                                sess.do_optimize(OptTarget::Int(ie, sense), cnf, sol);
                            }
                        },
                    }
                }
                "maxw" | "minw" => {
                    let raw = body[cmd.len()..].trim();
                    let usage = "usage: :maxw|:minw <rel>:<w>[, ...] [in <cnf>] [as <sol>]";
                    match split_opt_args(&sess, raw) {
                        None => println!("{usage}"),
                        Some((list, cnf, sol)) => match parse_weights_arg(list) {
                            None => println!("{usage}"),
                            Some(pairs) => {
                                let sense = if cmd == "maxw" {
                                    KkOptSense::Maximize
                                } else {
                                    KkOptSense::Minimize
                                };
                                sess.do_optimize(OptTarget::Weights(pairs, sense), cnf, sol);
                            }
                        },
                    }
                }
                "validate" | "v" => {
                    let (sol, cnf) = split_validate(&rest);
                    if sol == Some("__bad__") {
                        println!("usage: :validate <sol> [in <cnf>]");
                    } else {
                        sess.do_validate(sol, cnf);
                    }
                }
                "show" => sess.do_show(&rest),
                "mepk" => {
                    for line in mepk_cmd::run_mepk(&rest) {
                        println!("{line}");
                    }
                }
                "eval" => {
                    let raw = body["eval".len()..].trim();
                    if raw.is_empty() {
                        println!("usage: :eval <expr|formula> [as <sol>]");
                    } else {
                        // Split trailing `as <sol>` on the raw text.
                        let toks: Vec<&str> = raw.split_whitespace().collect();
                        let (_head, as_name) = split_as(&toks);
                        if as_name == Some("__bad_as__") {
                            println!("usage: :eval <expr|formula> [as <sol>]");
                        } else {
                            let cut = if as_name.is_some() {
                                raw.rmatch_indices(" as ").next().map(|(i, _)| i)
                            } else {
                                None
                            };
                            let expr = match cut {
                                Some(i) => raw[..i].trim(),
                                None => raw,
                            };
                            if expr.is_empty() {
                                println!("usage: :eval <expr|formula> [as <sol>]");
                            } else {
                                let owned = as_name.map(|s| s.to_string());
                                start_or_submit(&mut sess, InputKind::Eval, expr, owned);
                            }
                        }
                    }
                }
                "query" => {
                    let raw = body["query".len()..].trim();
                    if raw.is_empty() {
                        println!("usage: :query <expr> [in <sol>]");
                    } else {
                        let (expr, sol) = split_query_in(&sess, raw);
                        let owned = sol.map(|s| s.to_string());
                        start_or_submit(&mut sess, InputKind::Query, expr, owned);
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
            // Recompute the raw tail for query/eval (they take free-form text).
            let tail = trimmed[cmd.len()..].trim();
            match cmd {
                "help" | "h" | "?" => print_help(),
                "quit" | "exit" | "q" => break,
                "load" | "l" => match arg {
                    Some(p) => sess.load_file(p),
                    None => println!("usage: :load <file.als>"),
                },
                "list" | "ls" => sess.list_commands(),
                "cnfs" => sess.list_cnfs(),
                "sols" => sess.list_sols(),
                "use" => match arg {
                    Some(n) => sess.do_use(n),
                    None => println!("usage: :use <cnf|sol>"),
                },
                "mode" | "m" => sess.do_mode(arg),
                "fragments" => sess.list_fragments(),
                "drop" => {
                    if rest.len() != 1 {
                        println!("usage: drop <fragment-index> (:fragments to list)");
                    } else {
                        sess.drop_fragment(arg);
                    }
                }
                "psave" => match parse_psave_args(&rest) {
                    Ok((file, sol, rels)) => sess.do_psave(file, sol, &rels),
                    Err(usage) => println!("{usage}"),
                },
                "pread" => match arg {
                    Some(p) => sess.do_pread(p),
                    None => println!("usage: pread <file>"),
                },
                "ppin" => match parse_ppin_args(
                    &rest,
                    "usage: ppin <file> [rels...] [to <cnf>] [as <sol>] [gated]",
                ) {
                    Ok(a) => sess.do_ppin(a.file, &a.rels, a.cnf, a.sol, a.gated),
                    Err(usage) => println!("{usage}"),
                },
                "pavoid" => match parse_ppin_args(
                    &rest,
                    "usage: pavoid <file> [rels...] [to <cnf>] [as <sol>] [gated]",
                ) {
                    Ok(a) => sess.do_pavoid(a.file, &a.rels, a.cnf, a.sol, a.gated),
                    Err(usage) => println!("{usage}"),
                },
                "reset" => {
                    sess.fragments.clear();
                    sess.rebuild("reset");
                }
                "solve" | "s" => {
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: solve [<cnf>] [as <sol>]");
                    } else {
                        sess.do_solve(head.first().copied(), as_name);
                    }
                }
                "next" | "n" => {
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: next [<sol>] [as <sol>]");
                    } else {
                        sess.do_next(head.first().copied(), as_name);
                    }
                }
                "validate" | "v" => {
                    let (sol, cnf) = split_validate(&rest);
                    if sol == Some("__bad__") {
                        println!("usage: validate <sol> [in <cnf>]");
                    } else {
                        sess.do_validate(sol, cnf);
                    }
                }
                "show" => sess.do_show(&rest),
                "eval" => {
                    if tail.is_empty() {
                        println!("usage: eval <expr|formula> [as <sol>]");
                    } else {
                        let toks: Vec<&str> = tail.split_whitespace().collect();
                        let (_head, as_name) = split_as(&toks);
                        if as_name == Some("__bad_as__") {
                            println!("usage: eval <expr|formula> [as <sol>]");
                        } else {
                            let cut = match as_name {
                                Some(_) => tail.rmatch_indices(" as ").next().map(|(i, _)| i),
                                None => None,
                            };
                            let expr = match cut {
                                Some(i) => tail[..i].trim(),
                                None => tail,
                            };
                            let owned = as_name.map(|s| s.to_string());
                            start_or_submit(&mut sess, InputKind::Eval, expr, owned);
                        }
                    }
                }
                "query" => {
                    if tail.is_empty() {
                        println!("usage: query <expr> [in <sol>]");
                    } else {
                        let (expr, sol) = split_query_in(&sess, tail);
                        let owned = sol.map(|s| s.to_string());
                        start_or_submit(&mut sess, InputKind::Query, expr, owned);
                    }
                }
                _ => println!("unknown command `{cmd}` (:help for list)"),
            }
            continue;
        }

        // Bare `run`/`check`: build when it names a command, else a fragment.
        if head == "run" || head == "check" {
            let toks: Vec<&str> = trimmed.split_whitespace().collect();
            // toks[0] is run|check; support optional trailing `as <cnf>`.
            let tail = &toks[1..];
            let (head_t, as_name) = split_as(tail);
            let kind = if head == "run" {
                CnfKind::Run
            } else {
                CnfKind::Check
            };
            let arg_owned: Option<String> = head_t.first().map(|s| s.to_string());
            if as_name == Some("__bad_as__") || head_t.len() > 1 {
                start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
            } else if sess.module.is_some() && sess.resolve_index(arg_owned.as_deref()).is_ok() {
                sess.do_build(kind, arg_owned.as_deref(), as_name);
            } else if sess.module.is_none() {
                println!("no module loaded");
            } else {
                start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
            }
            continue;
        }

        // Bare `minimize`/`maximize`: optimize when it names a stored
        // optimization command, else a model fragment (mirrors run/check).
        // A definition tail (`:`/`{`/`weights`/`for` tokens) is always a
        // fragment (this covers `maximize: Aopt ...` where the colon sticks
        // to the keyword); anything else tries the optimizer reference.
        // Misclassified references are harmless: they would fail
        // `resolve_index` and land in `Decl` below anyway.
        if head == "minimize"
            || head == "maximize"
            || head == "minimize:"
            || head == "maximize:"
        {
            let toks: Vec<&str> = trimmed.split_whitespace().collect();
            // toks[0] is minimize|maximize[:]; support optional trailing `as <sol>`.
            let tail = &toks[1..];
            let is_def = tail
                .iter()
                .any(|t| *t == ":" || *t == "{" || *t == "weights" || *t == "for");
            if is_def {
                start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
                continue;
            }
            let (head_t, as_name) = split_as(tail);
            let arg_owned: Option<String> = head_t.first().map(|s| s.to_string());
            if as_name == Some("__bad_as__") || head_t.len() > 1 {
                start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
            } else if sess.module.is_some() && sess.resolve_index(arg_owned.as_deref()).is_ok() {
                sess.do_optimize_command(arg_owned.as_deref(), as_name);
            } else if sess.module.is_none() {
                println!("no module loaded");
            } else {
                start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
            }
            continue;
        }

        // Declaration fragment vs bare expression.
        if looks_like_decl(trimmed) {
            start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
        } else {
            start_or_submit(&mut sess, InputKind::Bare, trimmed, None);
        }
    }
    let _ = rl.save_history(".alloy_repl_history");
    println!("bye");
}

/// Begin (or immediately submit) a multi-line input.
fn start_or_submit(sess: &mut Session, kind: InputKind, text: &str, target: Option<String>) {
    let depth = brace_delta(text);
    if depth <= 0 {
        let pending = Pending {
            kind,
            text: text.to_string(),
            depth: 0,
            target,
        };
        sess.submit_pending(pending);
    } else {
        sess.pending = Some(Pending {
            kind,
            text: text.to_string(),
            depth,
            target,
        });
    }
}
