//! Structured model generator + brute-force oracle for fuzzing.
//!
//! Zero-dependency module used by `tests/fuzz_model.rs` (deterministic seeds)
//! and the libfuzzer targets. Generates tiny Alloy models biased
//! toward field multiplicities, joins, and box indexing, then checks:
//! - the model parses (generator bug otherwise),
//! - solver SAT agrees with brute-force semantic evaluation,
//! - SAT instances pass [`crate::validate`],
//! - `:query`-equivalent reads of bare sigs match the instance.
//!
//! Skipped (not failed): temporal commands, unsupported lowers, solver
//! errors, and models whose flexible bounds exceed [`MAX_FLEX_BITS`].

use std::collections::HashMap;

use alloy_kodkod_rs::eval::Evaluator;
use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::intset::IntSet;
use alloy_kodkod_rs::tupleset::TupleSet;

use crate::ast::CommandKind;
use crate::parse_module;

 /// Upper bound on flexible (upper-minus-lower) primary bits enumerated by
/// the brute-force oracle. Keeps `cargo test` seeds in the millisecond range.
pub const MAX_FLEX_BITS: usize = 20;

/// Deterministic xorshift64* PRNG (no external deps, seedable from fuzzer bytes).
#[derive(Clone, Debug)]
pub struct Rng(u64);

impl Rng {
    pub fn from_seed(seed: u64) -> Self {
        // Zero state would freeze xorshift; scramble it.
        Rng(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0x2545F4914F6CDD1D) | 1)
    }

    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut seed = 0x243F6A8885A308D3u64;
        for (i, &b) in bytes.iter().enumerate() {
            seed = seed
                .wrapping_add((b as u64).wrapping_mul(0x9E3779B97F4A7C15))
                .wrapping_add(i as u64);
            seed ^= seed >> 29;
            seed = seed.wrapping_mul(0xBF58476D1CE4E5B9);
        }
        Self::from_seed(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        assert!(n > 0);
        (self.next_u64() % n as u64) as usize
    }

    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }

    pub fn chance(&mut self, pct: u64) -> bool {
        self.next_u64() % 100 < pct
    }
}

const SIGS: &[&str] = &["A", "B", "C"];
const FNAMES: &[&str] = &["f", "g", "h"];
const PREDS: &[&str] = &["p", "q"];
const ASSERTS: &[&str] = &["a", "c"];

/// A declared field with enough typing info for template filling.
#[derive(Clone, Debug)]
struct Field {
    owner: String,
    name: String,
    /// Type-column sigs after the owner (field arity = 1 + mids.len()).
    mids: Vec<String>,
}

impl Field {
    fn arity(&self) -> u32 {
        1 + self.mids.len() as u32
    }

    fn expr(&self) -> String {
        format!("{}.{}", self.owner, self.name)
    }
}

/// Generate one tiny model source. Never emits temporal syntax, `open`,
/// `extends`/`in`, int atoms, or `disj`.
pub fn gen_model(rng: &mut Rng) -> String {
    let nsigs = 1 + rng.below(3);
    let sigs: Vec<String> = SIGS[..nsigs].iter().map(|s| s.to_string()).collect();
    // Owner sig decl lines, filled with fields below.
    let mut sig_lines: HashMap<String, (String, Vec<String>)> = HashMap::new();
    for s in &sigs {
        let mult = match rng.below(100) {
            0..=64 => "",
            65..=84 => "one ",
            _ => "lone ",
        };
        sig_lines.insert(s.clone(), (format!("{mult}sig {s}"), Vec::new()));
    }
    // --- fields ---
    let mut fields: Vec<Field> = Vec::new();
    let nfields = rng.below(3);
    for _ in 0..nfields {
        let owner = rng.pick(&sigs).clone();
        let taken: Vec<String> = fields
            .iter()
            .filter(|f| f.owner == owner)
            .map(|f| f.name.clone())
            .collect();
        let free: Vec<&&str> = FNAMES.iter().filter(|f| !taken.contains(&f.to_string())).collect();
        if free.is_empty() {
            continue;
        }
        let fname = (*rng.pick(&free)).to_string();
        let shape = rng.below(100);
        let (typ, mids): (String, Vec<String>) = match shape {
            0..=19 => {
                let ty = rsig(rng, &sigs);
                (ty.clone(), vec![ty])
            }
            20..=34 => {
                let (m, ty) = (
                    rng.pick(&["lone", "one", "some"]).to_string(),
                    rsig(rng, &sigs),
                );
                (format!("{m} {ty}"), vec![ty])
            }
            35..=49 => {
                let (n, ty) = (rsig(rng, &sigs), rsig(rng, &sigs));
                (format!("{n} -> {ty}"), vec![n, ty])
            }
            50..=62 => {
                let m = rng.pick(&["lone", "one", "some"]).to_string();
                let (n, ty) = (rsig(rng, &sigs), rsig(rng, &sigs));
                (format!("{n} -> {m} {ty}"), vec![n, ty])
            }
            63..=74 if sigs.len() >= 2 => {
                let m = rng.pick(&["lone", "one", "some"]).to_string();
                let (a, ty) = (rsig(rng, &sigs), rsig(rng, &sigs));
                (format!("{a} {m} -> {ty}"), vec![a, ty])
            }
            75..=82 if sigs.len() >= 3 => {
                let m = rng.pick(&["lone", "one", "some"]).to_string();
                let (a, b, ty) = (
                    rsig(rng, &sigs),
                    rsig(rng, &sigs),
                    rsig(rng, &sigs),
                );
                (format!("{a} -> {m} {b} -> {ty}"), vec![a, b, ty])
            }
            _ => {
                let ty = rsig(rng, &sigs);
                (format!("set {ty}"), vec![ty])
            }
        };
        sig_lines
            .get_mut(&owner)
            .expect("owner sig")
            .1
            .push(format!("{fname}: {typ}"));
        fields.push(Field {
            owner,
            name: fname,
            mids,
        });
    }
    let mut src = String::from("module fuzz\n");
    // Deterministic sig order for stable output.
    let mut names: Vec<&String> = sig_lines.keys().collect();
    names.sort();
    for name in names {
        let (decl, fs) = &sig_lines[name];
        if fs.is_empty() {
            src.push_str(&format!("{decl} {{}}\n"));
        } else {
            src.push_str(&format!("{decl} {{ {} }}\n", fs.join(", ")));
        }
    }
    // --- facts ---
    let nfacts = rng.below(3);
    for _ in 0..nfacts {
        src.push_str(&format!("fact {{ {} }}\n", gen_formula(rng, &sigs, &fields, 0)));
    }
    // --- preds ---
    let mut pred_names = Vec::new();
    let npreds = 1 + rng.below(2);
    for pname in PREDS.iter().take(npreds) {
        src.push_str(&format!(
            "pred {pname} {{ {} }}\n",
            gen_formula(rng, &sigs, &fields, 1)
        ));
        pred_names.push(pname.to_string());
    }
    // --- commands ---
    let scope_n = 1 + rng.below(2);
    let scope = if rng.chance(25) {
        format!("for exactly {scope_n}")
    } else {
        format!("for {scope_n}")
    };
    if rng.chance(25) && !pred_names.is_empty() {
        let aname = ASSERTS[rng.below(ASSERTS.len())];
        src.push_str(&format!(
            "assert {aname} {{ {} }}\ncheck {aname} {scope}\n",
            gen_formula(rng, &sigs, &fields, 1)
        ));
    }
    for pname in &pred_names {
        src.push_str(&format!("run {pname} {scope}\n"));
    }
    src
}

fn rsig(rng: &mut Rng, sigs: &[String]) -> String {
    rng.pick(sigs).clone()
}

/// Random formula over declared names. `depth` caps nesting.
fn gen_formula(rng: &mut Rng, sigs: &[String], fields: &[Field], depth: usize) -> String {
    let fexprs: Vec<String> = fields.iter().map(|f| f.expr()).collect();
    let mut atoms: Vec<String> = sigs.to_vec();
    atoms.extend(fexprs.iter().cloned());
    // Same-arity pairs for `=`/`in`: sig-vs-sig, or field-vs-field.
    let same_arity_pair = |rng: &mut Rng| -> Option<(String, String)> {
        if !sigs.is_empty() && (fields.is_empty() || rng.chance(50)) {
            let (a, b) = (rsig(rng, sigs), rsig(rng, sigs));
            Some((a, b))
        } else if fields.len() >= 2 {
            // Group fields by arity without borrow trouble: collect exprs.
            let mut by_arity: HashMap<u32, Vec<String>> = HashMap::new();
            for f in fields {
                by_arity.entry(f.arity()).or_default().push(f.expr());
            }
            let keys: Vec<u32> = by_arity.keys().copied().collect();
            let group = &by_arity[rng.pick(&keys)];
            if group.len() >= 2 {
                let (a, b) = (rng.pick(group).clone(), rng.pick(group).clone());
                Some((a, b))
            } else {
                let s = rsig(rng, sigs);
                Some((s.clone(), s))
            }
        } else {
            let s = rsig(rng, sigs);
            Some((s.clone(), s))
        }
    };
    let pick_atom = |rng: &mut Rng| rng.pick(&atoms).clone();
    match rng.below(100) {
        0..=14 => format!("some {}", pick_atom(rng)),
        15..=24 => format!("no {}", pick_atom(rng)),
        25..=31 => format!("lone {}", pick_atom(rng)),
        32..=36 => format!("one {}", pick_atom(rng)),
        37..=46 => format!("#{} = {}", pick_atom(rng), rng.below(4)),
        47..=52 => format!("#{} > {}", pick_atom(rng), rng.below(4)),
        53..=57 => format!("#{} < {}", pick_atom(rng), rng.below(4)),
        58..=64 => {
            // Quantified row/typing shapes over a field owner.
            if fields.is_empty() {
                return format!("some {}", pick_atom(rng));
            }
            let f = rng.pick(fields);
            let v = ["a", "b", "c"][rng.below(3)];
            match rng.below(100) {
                0..=39 => format!("all {v}: {} | some {v}.{}", f.owner, f.name),
                40..=69 => format!("all {v}: {} | lone {v}.{}", f.owner, f.name),
                _ if f.mids.len() >= 2 && depth > 0 => {
                    // Ternary box: (a.F)[b] with b from the middle sig.
                    let mid = f.mids[0].clone();
                    let w = if v == "a" { "b" } else { "a" };
                    format!(
                        "all {v}: {} | all {w}: {mid} | some ({v}.{})[{w}]",
                        f.owner, f.name
                    )
                }
                _ => format!("some {}.{}", f.owner, f.name),
            }
        }
        65..=72 => {
            let (a, b) = same_arity_pair(rng).expect("sigs nonempty");
            if rng.chance(50) {
                format!("{a} = {b}")
            } else {
                format!("{a} in {b}")
            }
        }
        73..=80 => {
            // `|` separator (Java parity; `in` is rejected).
            let v = ["x", "y"][rng.below(2)];
            let s = rsig(rng, sigs);
            format!("let {v} = {s} | some {v}")
        }
        81..=88 if depth > 0 => {
            let l = gen_formula(rng, sigs, fields, depth - 1);
            let r = gen_formula(rng, sigs, fields, depth - 1);
            match rng.below(3) {
                0 => format!("{l} and {r}"),
                1 => format!("{l} or {r}"),
                _ => format!("not ({l})"),
            }
        }
        _ => {
            if depth > 0 && rng.chance(40) {
                format!("not ({})", gen_formula(rng, sigs, fields, depth - 1))
            } else {
                format!("some {}", pick_atom(rng))
            }
        }
    }
}

/// Outcome of checking one model: `Skipped` (too big / unsupported / solver
/// error) or `Checked` (all invariants held).
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Skipped(&'static str),
    Checked,
}

/// Parse, solve every command, and verify against the brute-force oracle.
/// Panics on invariant violation; returns [`Outcome`] otherwise.
pub fn check_model(src: &str) -> Outcome {
    let module = match parse_module(src) {
        Ok(m) => m,
        Err(e) => panic!("generator produced unparsable model: {e}\n---\n{src}"),
    };
    if module.commands.is_empty() {
        return Outcome::Skipped("no commands");
    }
    for (idx, cmd) in module.commands.iter().enumerate() {
        if module.is_temporal_command(idx) {
            return Outcome::Skipped("temporal");
        }
        let mut lower = crate::lower::Lowerer::new(&module);
        let problem = match lower.prepare_command(idx) {
            Ok(p) => p,
            Err(_) => return Outcome::Skipped("lower unsupported"),
        };
        // Flexibility budget.
        let mut flex_bits = 0usize;
        for r in problem.bounds.relations() {
            let (lo, up) = match problem.bounds.bound_pair(r) {
                Some(v) => v,
                None => return Outcome::Skipped("unbounded relation"),
            };
            let (ln, un) = (lo.len(), up.len());
            if ln > un || !up.covers(lo) {
                return Outcome::Skipped("inconsistent bounds");
            }
            flex_bits += un - ln;
        }
        if flex_bits > MAX_FLEX_BITS {
            return Outcome::Skipped("too big to enumerate");
        }
        let expected = brute_force_sat(&problem);
        // Solver side through the split API (covers run/check + solve).
        let is_run = matches!(cmd.kind, CommandKind::Run(_));
        let cnf = match if is_run {
            crate::cnf::run(&module, idx)
        } else {
            crate::cnf::check(&module, idx)
        } {
            Ok(c) => c,
            Err(_) => return Outcome::Skipped("cnf build error"),
        };
        let got = match crate::cnf::solve(&cnf) {
            Ok(o) => o,
            Err(_) => return Outcome::Skipped("solve error"),
        };
        assert_eq!(
            expected,
            got.is_some(),
            "solver/oracle SAT mismatch (cmd {idx})\n---\n{src}"
        );
        if let Some(inst) = got {
            assert!(
                crate::cnf::validate(&cnf, &inst).is_some(),
                "solved instance must validate (cmd {idx})\n---\n{src}"
            );
            // Bare-sig reads must match the instance (relation-ID alignment).
            for s in module_sigs(&module) {
                let rid = match inst.find_relation_by_name(&s) {
                    Some(r) => r,
                    None => panic!("instance lacks sig {s} (cmd {idx})\n---\n{src}"),
                };
                let (arity, ts) = match crate::snippet::query(
                    &module,
                    &module.commands[idx].scope,
                    &cnf,
                    &s,
                    &inst,
                ) {
                    Ok(v) => v,
                    Err(e) => panic!("query failed for {s}: {e} (cmd {idx})\n---\n{src}"),
                };
                assert_eq!(arity, 1, "sig arity (cmd {idx})");
                assert_eq!(
                    ts.len(),
                    inst.tuples(rid).map(|t| t.len()).unwrap_or(0),
                    "query/instance agreement for {s} (cmd {idx})\n---\n{src}"
                );
            }
        }
    }
    Outcome::Checked
}

fn module_sigs(module: &crate::ast::Module) -> Vec<String> {
    let mut out = Vec::new();
    for sd in &module.sigs {
        out.extend(sd.names.iter().cloned());
    }
    out
}

/// Brute force over all bound-respecting instances.
fn brute_force_sat(problem: &crate::lower::LoweredProblem) -> bool {
    struct Rel {
        id: alloy_kodkod_rs::RelationId,
        arity: u32,
        lower: IntSet,
        flex: Vec<i64>,
    }
    let mut rels: Vec<Rel> = Vec::new();
    for r in problem.bounds.relations() {
        let (lo, up) = problem.bounds.bound_pair(r).unwrap();
        let arity = problem.bounds.pool().arity(r);
        let mut flex: Vec<i64> = Vec::new();
        for i in up.index_view().iter() {
            if !lo.index_view().contains(i) {
                flex.push(i);
            }
        }
        rels.push(Rel {
            id: r,
            arity,
            lower: lo.index_view().clone(),
            flex,
        });
    }
    // Mixed-radix odometer over the product space.
    let total: usize = rels.iter().map(|r| 1usize << r.flex.len()).product();
    let empty_env = Vec::new();
    for counter in 0..total {
        let mut rest = counter;
        let mut inst = Instance::new(problem.bounds.universe(), problem.bounds.pool());
        for r in &rels {
            let mut set = r.lower.clone();
            let ways = 1usize << r.flex.len();
            let pick = rest % ways;
            rest /= ways;
            for (j, idx) in r.flex.iter().enumerate() {
                if (pick >> j) & 1 == 1 {
                    set.insert(*idx);
                }
            }
            let ts = TupleSet::from_indices(inst.universe(), r.arity, set)
                .expect("flex subset within bounds");
            inst.add(r.id, &ts).expect("add");
        }
        let holds = Evaluator::new(&inst)
            .formula_bool(&problem.arena, problem.formula, &empty_env)
            .unwrap_or(false);
        if holds {
            return true;
        }
    }
    false
}
