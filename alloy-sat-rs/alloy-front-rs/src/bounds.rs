//! Scope resolution: turns a command's scope clause into concrete sig
//! population bounds and the universe atom table.
//!
//! Naming matches the Java engine (`Book$0`, int atoms `-8`..`7`) so
//! results stay comparable with the Java oracle.

use crate::ast::{Module, Scope, ScopeEntry, SigDecl, SigMult, SigRel};
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

pub const DEFAULT_SCOPE: u32 = 3;

/// Builtin sigs with no allocated atoms bind nothing (like `Int` when
/// unused): no empty shells in bounds, universe display, or warnings.
pub fn is_unallocated_builtin(res: &Resolved, name: &str) -> bool {
    matches!(name, "Real" | "EReal" | "$M" | "$E" | "$P" | "$K")
        && res.atoms_of(name).is_empty()
}

/// Builtin flat lane sigs (`$M/$E/$P/$K`): the bit-position domains.
/// User declaration is prohibited (reserved like `Real`/`EReal`/`Int`);
/// sizes come from `run ... for N $M` (else the `for W Int` rule).
pub fn is_lane_sig(n: &str) -> bool {
    matches!(n, "$M" | "$E" | "$P" | "$K")
}

/// Bit-lane group ids for the builtin `Real`/`EReal` lanes in the kodkod
/// int-bound group registry (`Bounds::bound_exactly_int_in`).
/// Group 0 stays the builtin `Int` namespace.
pub const LANE_M: u32 = 1;
pub const LANE_E: u32 = 2;
pub const LANE_P: u32 = 3;
pub const LANE_K: u32 = 4;

/// The builtin bit lanes, in `(label, group)` order: the `Real` centre
/// (`m`, `e`) and the `EReal` error lanes (`p`, `k`). Reading one is
/// `x & $LANE` through that group's int bounds (see
/// `lower::lane_partition_bits`) — there is no lane relation.
pub const BUILTIN_LANES: [(&str, u32); 4] = [
    ("m", LANE_M),
    ("e", LANE_E),
    ("p", LANE_P),
    ("k", LANE_K),
];

/// Builtin `Real` operation/predicate names that imply Real allocation
/// (exact-centre counterparts of the `ereal*` surface).
pub const REAL_OPS: &[&str] = &[
    "realAdd",
    "realSub",
    "realMul",
    "realDiv",
    "realWellformed",
    "realEq",
    "realLT",
    "realLTE",
    "realGT",
    "realGTE",
    "setReal",
    "setRealNearest",
    "setRealDown",
    "setRealUp",
    "realSucc",
    "realPred",
    "composeReal",
    "mbit",
    "ebit",
];

/// Builtin `EReal` operation/predicate names that imply EReal allocation
/// when called (mirrors the `util/mepk` library surface).
pub const EREAL_OPS: &[&str] = &[
    "erealAdd",
    "erealSub",
    "erealMul",
    "erealDiv",
    "erealWellformed",
    "erealValid",
    "erealDivGuard",
    "erealNeedsRefine",
    "erealCombineK",
    "erealLsb",
    "erealRadiusExp",
    "erealTau",
    "erealExactEq",
    "erealMayEq",
    "erealCovers",
    "erealLT",
    "erealLTE",
    "erealMayLTE",
    "erealGT",
    "erealGTE",
    "setEReal",
    "composeEReal",
    "pbit",
    "kbit",
];

#[derive(Debug)]
pub struct SigInfo {
    /// Enclosing sig, if this sig participates in an `extends`/`in` chain.
    pub parent: Option<String>,
    /// Concrete atoms allocated for THIS sig (empty for abstract parents).
    pub atoms: Vec<String>,
}

pub struct Resolved {
    pub universe: Arc<Universe>,
    /// Circuit width `E = min(W, 30)` (drives Kodkod `set_bitwidth`).
    pub bitwidth: u32,
    /// Int atom count `W` (atoms `{0, .., W-1}`).
    pub int_count: u32,
    /// Step atoms `{Step$0, ..}` (empty in static commands).
    pub step_atoms: Vec<String>,
    pub sigs: HashMap<String, SigInfo>,
    /// Atoms reachable through each sig including descendants (for typing).
    pub closure_atoms: HashMap<String, Vec<String>>,
    /// For `in` children: atoms are a subset of parent's atoms.
    pub in_children_atoms: HashMap<String, Vec<String>>,
    /// Bit-lane atoms by group (`LANE_M/E/P/K`): bit positions whose
    /// value is the index (two's-complement MSB reading via `BitsIn`).
    /// The `Real` type domain is the `M`+`E` groups and `EReal` is all
    /// four, so these atom lists *are* the real value domains.
    pub lane_atoms: HashMap<u32, Vec<String>>,
    /// Lane widths from the `for n Int` rule (+ `MEPK_*_WIDTH` overrides).
    /// Stored for lowering/display introspection.
    pub mepk_widths: alloy_kodkod_rs::mepk::MepkWidths,
}

impl Resolved {
    /// All atoms of a sig including its subtree (children, recursively).
    pub fn atoms_of(&self, name: &str) -> Vec<String> {
        self.closure_atoms.get(name).cloned().unwrap_or_default()
    }
}

fn build_scope_map(
    module: &Module,
    scope: &Scope,
) -> (HashMap<String, (u32, bool)>, u32, u32, u32, bool) {
    let mut m: HashMap<String, (u32, bool)> = HashMap::new();
    for (name, e) in &scope.entries {
        match e {
            ScopeEntry::Num(n) => {
                m.insert(name.clone(), (*n, false));
            }
            ScopeEntry::Exactly(n) => {
                m.insert(name.clone(), (*n, true));
            }
        }
    }
    let overall = scope.overall.unwrap_or(DEFAULT_SCOPE);
    // Bit-vector model: `for W Int` (else 4) gives W atoms `{0, .., W-1}`
    // with W-bit circuits capped at 30 (`E = min(W, 30)`). Int atoms are
    // allocated lazily: models that never mention Int as a set pay zero
    // universe cost.
    let bitwidth = crate::ast::effective_bitwidth(module, scope);
    let int_count = crate::ast::effective_int_count(scope);
    let needs_int = crate::ast::module_needs_int_atoms(module, scope);
    (m, overall, bitwidth, int_count, needs_int)
}

/// Transitive `extends`/`in` closure of a builtin sort: every sig reachable
/// from `root` through `extends`-links (`in_sig == false`) or additionally
/// through `in`-links (`in_sig == true`).
///
/// Fixed point, so declaration order does not matter.
fn descendants(module: &Module, root: &str, in_sig: bool) -> HashSet<String> {
    let mut out: HashSet<String> = HashSet::new();
    loop {
        let mut grew = false;
        for sd in &module.sigs {
            if (sd.rel == SigRel::In) != in_sig {
                continue;
            }
            if let Some(p) = &sd.extends {
                if p == root || out.contains(p) {
                    for n in &sd.names {
                        grew |= out.insert(n.clone());
                    }
                }
            }
        }
        if !grew {
            break;
        }
    }
    out
}

/// Sigs whose upper bound is the `EReal` type domain: `in`-children
/// transitively under `EReal` (including direct `in EReal` children).
/// `extends EReal` is rejected, so there is no own-atom population to
/// share. Fixed point so declaration order does not matter.
pub fn ereal_in_children(module: &Module) -> HashSet<String> {
    descendants(module, "EReal", true)
}

/// What counts as a "mention" of a builtin real family during the module
/// scan. The two families differ only in these leaf tests, so the
/// traversal below is written once and parameterised by this table.
#[derive(Clone, Copy)]
struct Mention {
    /// The builtin sort name. Also the `Call` name that counts as a use.
    sort: &'static str,
    /// Flat lane sigs (`$M`/`$E` vs `$P`/`$K`) counting as `Expr::Name`
    /// mentions, with the atom-name prefix of their members. A model
    /// that writes only `M$0` must still get the lane allocated, so the
    /// members count as mentions too — and only for the family that
    /// owns them (`$P`/`$K` do not imply `Real`).
    domains: &'static [&'static str],
    members: &'static [char],
    /// A decimal literal denotes a real value and so allocates the pool.
    decimal: bool,
    /// Builtin operations on this family.
    ops: &'static [&'static str],
}

impl Mention {
    fn expr_name_hits(&self, n: &str) -> bool {
        if n == self.sort || self.domains.contains(&n) {
            return true;
        }
        // A member atom name (`M$0`) implies the family that owns it.
        crate::ast::lane_atom_prefix(n).is_some_and(|p| self.members.contains(&p))
    }
    /// `Call` names: the sort itself and its operations. The lane sigs are
    /// sets, not functions, so they are not function names.
    fn call_hits(&self, n: &str) -> bool {
        n == self.sort || self.ops.contains(&n)
    }
}

/// `Real` plus the flat centre lane sigs; a decimal literal implies it.
const MENTION_REAL: Mention = Mention {
    sort: "Real",
    domains: &["$M", "$E"],
    members: &['M', 'E'],
    decimal: true,
    ops: REAL_OPS,
};

/// `EReal` plus the flat error lane sigs. A decimal literal does *not*
/// imply `EReal` (it implies `Real`; see `MENTION_REAL`).
const MENTION_EREAL: Mention = Mention {
    sort: "EReal",
    domains: &["$P", "$K"],
    members: &['P', 'K'],
    decimal: false,
    ops: EREAL_OPS,
};

/// Walks every expression, integer expression and formula of `module`
/// looking for a mention of `m`.
///
/// Conservative: any textual mention allocates (harmless
/// over-approximation); a missed mention would fail loudly at lowering
/// instead.
///
/// `sig_uses` is the extra per-sig-declaration test — a sig can reach the
/// family by extending it without ever naming it.
fn module_mentions(module: &Module, m: Mention, sig_uses: impl Fn(&SigDecl) -> bool) -> bool {
    use crate::ast::{Expr, Formula, IntExpr};

    fn expr_hits(e: &Expr, m: Mention, hit: &mut bool) {
        if *hit {
            return;
        }
        match e {
            Expr::Name(n, _) if m.expr_name_hits(n) => *hit = true,
            Expr::RealLit(..) | Expr::ApproxRealLit(..) if m.decimal => *hit = true,
            Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom
            | Expr::StepAtom | Expr::Bits(..) | Expr::RealLit(..)
            | Expr::ApproxRealLit(..) => {}
            Expr::Bin(_, a, b) => {
                expr_hits(a, m, hit);
                expr_hits(b, m, hit);
            }
            Expr::Transpose(x) | Expr::TClosure(x) | Expr::RClosure(x) | Expr::Prime(x)
            | Expr::AtExpr(x) | Expr::ArrowMult(_, x) | Expr::LeadMult(_, x) => {
                expr_hits(x, m, hit)
            }
            Expr::Comprehension(ds, body) | Expr::Find(_, ds, body) => {
                for d in ds {
                    expr_hits(&d.expr, m, hit);
                }
                formula_hits(body, m, hit);
            }
            Expr::If(c, t, el) => {
                formula_hits(c, m, hit);
                expr_hits(t, m, hit);
                expr_hits(el, m, hit);
            }
            Expr::Bracket(base, args) => {
                expr_hits(base, m, hit);
                for a in args {
                    expr_hits(a, m, hit);
                }
            }
            Expr::Call(name, args, _) => {
                if m.call_hits(name) {
                    *hit = true;
                    return;
                }
                for a in args {
                    expr_hits(a, m, hit);
                }
            }
            Expr::LetBind(binds, body) => {
                for (_, ex) in binds {
                    expr_hits(ex, m, hit);
                }
                expr_hits(body, m, hit);
            }
        }
    }

    fn intexpr_hits(e: &IntExpr, m: Mention, hit: &mut bool) {
        match e {
            IntExpr::Lit(..) => {}
            IntExpr::Card(x, _) | IntExpr::Val(x, _) | IntExpr::BitsVal(x, _)
            | IntExpr::SumOf(x, _) => expr_hits(x, m, hit),
            IntExpr::Bin(_, a, b) => {
                intexpr_hits(a, m, hit);
                intexpr_hits(b, m, hit);
            }
            IntExpr::Widen(_, a, b) => {
                intexpr_hits(a, m, hit);
                intexpr_hits(b, m, hit);
            }
            IntExpr::Sum(ds, body, _) => {
                for d in ds {
                    expr_hits(&d.expr, m, hit);
                }
                intexpr_hits(body, m, hit);
            }
        }
    }

    fn formula_hits(f: &Formula, m: Mention, hit: &mut bool) {
        if *hit {
            return;
        }
        match f {
            Formula::Const(_) | Formula::Pin(..) | Formula::BadIn(..) => {}
            Formula::Cmp(_, a, b, _) => {
                expr_hits(a, m, hit);
                expr_hits(b, m, hit);
            }
            Formula::IntCmp(_, a, b, _) => {
                intexpr_hits(a, m, hit);
                intexpr_hits(b, m, hit);
            }
            Formula::Quant(_, ds, body) | Formula::MaxSomeDecl(ds, body) => {
                for d in ds {
                    expr_hits(&d.expr, m, hit);
                }
                formula_hits(body, m, hit);
            }
            Formula::Multi(_, e, _) => expr_hits(e, m, hit),
            Formula::MaxSome(e) | Formula::MinSome(e) => expr_hits(e, m, hit),
            Formula::Maximize(e) | Formula::Minimize(e) => intexpr_hits(e, m, hit),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b)
            | Formula::Iff(a, b) | Formula::Until(a, b) | Formula::Releases(a, b)
            | Formula::Since(a, b) | Formula::Triggered(a, b) => {
                formula_hits(a, m, hit);
                formula_hits(b, m, hit);
            }
            Formula::Not(x)
            | Formula::Always(x)
            | Formula::Eventually(x)
            | Formula::Before(x)
            | Formula::Historically(x)
            | Formula::Once(x)
            | Formula::Keeping(x)
            | Formula::Goal(x)
            | Formula::Restore(x)
            | Formula::Initially(x)
            | Formula::Regularly(x)
            | Formula::Consistently(x)
            | Formula::OverflowCond(_, x) => formula_hits(x, m, hit),
            Formula::LetBind(binds, body) => {
                for (_, ex) in binds {
                    expr_hits(ex, m, hit);
                }
                formula_hits(body, m, hit);
            }
            Formula::Call(name, args, _) => {
                if m.call_hits(name) {
                    *hit = true;
                    return;
                }
                for a in args {
                    expr_hits(a, m, hit);
                }
            }
        }
    }

    let mut hit = false;
    for sd in &module.sigs {
        if sig_uses(sd) {
            return true;
        }
        for d in &sd.fields {
            expr_hits(&d.expr, m, &mut hit);
        }
        if let Some(f) = &sd.fact {
            formula_hits(f, m, &mut hit);
        }
        if hit {
            return true;
        }
    }
    for (_, f) in module.facts.iter().chain(module.soft_facts.iter()) {
        formula_hits(f, m, &mut hit);
        if hit {
            return true;
        }
    }
    for p in &module.paras {
        formula_hits(&p.body, m, &mut hit);
        if let Some(e) = &p.body_expr {
            expr_hits(e, m, &mut hit);
        }
        for d in &p.params {
            expr_hits(&d.expr, m, &mut hit);
        }
        if hit {
            return true;
        }
    }
    for pd in &module.partials {
        for e in &pd.entries {
            expr_hits(&e.left, m, &mut hit);
            expr_hits(&e.right, m, &mut hit);
        }
        if hit {
            return true;
        }
    }
    hit
}

/// True when the module mentions the builtin `EReal` (as a type, a scope
/// entry — including `for N $P`/`for N $K` — or an `ereal*` operation
/// call), or declares a sig extending it.
fn module_mentions_ereal(module: &Module, scope: &Scope) -> bool {
    if scope.entries.iter().any(|(n, _)| MENTION_EREAL.expr_name_hits(n)) {
        return true;
    }
    module_mentions(module, MENTION_EREAL, |sd| {
        sd.extends.as_deref() == Some("EReal")
    })
}

/// True when the module mentions the builtin `Real` (as a type, a scope
/// entry, or a `real*` operation call), or anything that implies the
/// `Real` closure (`EReal` mentions count: `EReal extends Real`).
fn module_mentions_real(module: &Module, scope: &Scope) -> bool {
    if scope
        .entries
        .iter()
        .any(|(n, _)| MENTION_REAL.expr_name_hits(n) || MENTION_EREAL.expr_name_hits(n))
    {
        return true;
    }
    module_mentions(module, MENTION_REAL, |sd| {
        sd.extends.as_deref() == Some("Real")
    }) || module_mentions_ereal(module, scope)
}

/// Resolves scopes into universe + per-sig atom allocations.
pub fn resolve(module: &Module, scope: &Scope) -> Result<Resolved, String> {
    let (user, overall, mut bitwidth, int_count, needs_int) = build_scope_map(module, scope);
    let mut mepk_widths =
        alloy_kodkod_rs::mepk::MepkWidths::from_env(int_count).map_err(|e| format!("mepk: {e}"))?;
    // Flat lane sigs: `for N $M` etc. override the `for W Int` rule
    // (and the `MEPK_*_WIDTH` env, which `from_env` already applied).
    // Omitted entries keep the rule-based behavior (backward compatible).
    let lane_scope = |name: &str| -> Option<u32> {
        scope
            .entries
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, e)| match e {
                ScopeEntry::Num(n) | ScopeEntry::Exactly(n) => *n,
            })
    };
    if let Some(n) = lane_scope("$M") {
        if n == 0 || n > 30 {
            return Err(format!("for {n} $M out of range 1..=30"));
        }
        mepk_widths.m_width = n;
    }
    if let Some(n) = lane_scope("$E") {
        if n == 0 || n > 30 {
            return Err(format!("for {n} $E out of range 1..=30"));
        }
        mepk_widths.e_width = n;
    }
    if let Some(n) = lane_scope("$P") {
        if n == 0 || n > 30 {
            return Err(format!("for {n} $P out of range 1..=30"));
        }
        mepk_widths.p_width = n;
    }
    if let Some(n) = lane_scope("$K") {
        if n == 0 || n > 30 {
            return Err(format!("for {n} $K out of range 1..=30"));
        }
        mepk_widths.k_width = n;
    }
    let needs_ereal = module_mentions_ereal(module, scope);
    let needs_real = module_mentions_real(module, scope);
    // An explicit `for N $M` etc. raises the problem circuit width to
    // cover it (else lane values would wrap mod 2^E). Without explicit
    // lane scopes the `for W Int` rule behavior is unchanged (too-narrow
    // rule widths still fail loudly, backward compatible).
    let lane_explicit = |names: &[&str]| {
        names
            .iter()
            .any(|n| scope.entries.iter().any(|(e, _)| e == *n))
    };
    if needs_real && lane_explicit(&["$M", "$E"]) {
        bitwidth = bitwidth.max(mepk_widths.m_width).max(mepk_widths.e_width);
    }
    if needs_ereal && lane_explicit(&["$P", "$K"]) {
        bitwidth = bitwidth
            .max(mepk_widths.p_width)
            .max(mepk_widths.k_width);
    }
    // Lane widths must fit the problem circuit width, but only when lanes
    // are actually allocated: wider lanes would misread (top bits wrap
    // mod 2^E). Point at the Int scope for relief. `M`/`E` widths are
    // shared between `Real` and `EReal` (agreed: no `REAL_*_WIDTH` split).
    if needs_real {
        for (name, w) in [
            ("MEPK_M_WIDTH", mepk_widths.m_width),
            ("MEPK_E_WIDTH", mepk_widths.e_width),
        ] {
            if w > bitwidth {
                return Err(format!(
                    "{name}={w} exceeds problem bitwidth {bitwidth}; lane values would wrap. \
                     Raise it via `for N Int` (need E >= {w}) or lower {name}"
                ));
            }
        }
    }
    if needs_ereal {
        for (name, w) in [
            ("MEPK_P_WIDTH", mepk_widths.p_width),
            ("MEPK_K_WIDTH", mepk_widths.k_width),
        ] {
            if w > bitwidth {
                return Err(format!(
                    "{name}={w} exceeds problem bitwidth {bitwidth}; lane values would wrap. \
                     Raise it via `for N Int` (need E >= {w}) or lower {name}"
                ));
            }
        }
    }
    // FLAT-EXPERIMENT: `for N Real` / `for N EReal` are rejected: both
    // are type domains whose population derives from the lane sigs (a
    // stale count would silently change meaning). Scope the lanes
    // instead (`for N $M, M $E, P $P, K $K`).
    for (name, lanes) in [("Real", "$M + $E"), ("EReal", "$M + $E + $P + $K")] {
        if scope.entries.iter().any(|(n, _)| n == name) {
            return Err(format!(
                "for N {name} is not scoped in flat mode; the {name} domain is exactly {lanes} (use `for N $M, M $E, P $P, K $K`)"
            ));
        }
    }
    // `Real`/`EReal`/`$M`/`$E`/`$P`/`$K` are reserved builtins: user
    // declarations are rejected (extension is allowed: `in` shares atoms,
    // `extends` partitions).
    for sd in &module.sigs {
        if sd
            .names
            .iter()
            .any(|n| n == "EReal" || n == "Real" || is_lane_sig(n))
        {
            return Err(
                "sig Real/EReal/$M/$E/$P/$K is reserved by the builtin Real signature".to_string(),
            );
        }
    }
    // FLAT-EXPERIMENT: user `extends Real`/`extends EReal` would add
    // value atoms outside the lane partition (junk-atom slack breaks
    // bitmask bijectivity: non-lane atoms read 0). Use `in Real` /
    // `in EReal` instead.
    for sd in &module.sigs {
        if sd.rel != SigRel::Extends {
            continue;
        }
        for parent in ["Real", "EReal"] {
            if sd.extends.as_deref() == Some(parent) {
                let n = sd.names.first().map(String::as_str).unwrap_or("sig");
                return Err(format!(
                    "sig {n} cannot extend {parent} in flat mode; use `sig {n} in {parent}` (values are bit sets)"
                ));
            }
        }
    }

    // index declarations
    let mut parents: HashMap<&str, Option<String>> = HashMap::new();
    let mut children: HashMap<String, Vec<String>> = HashMap::new();
    let mut mults: HashMap<&str, SigMult> = HashMap::new();
    let mut sig_rels: HashMap<&str, SigRel> = HashMap::new();
    let mut all_names: Vec<String> = Vec::new();
    for sd in &module.sigs {
        for n in &sd.names {
            if parents.insert(n.as_str(), sd.extends.clone()).is_some() {
                return Err(format!("duplicate sig {n}"));
            }
            mults.insert(n.as_str(), sd.mult);
            sig_rels.insert(n.as_str(), sd.rel);
            all_names.push(n.clone());
            if let Some(p) = &sd.extends {
                if p == "Int" || p == "Signed" {
                    // Java parity (verified against the Java frontend with
                    // Version.experimental=true): `extends Int` is rejected,
                    // while `in Int` (subset of the builtin Int) is accepted.
                    // `Signed` mirrors `Int` exactly (same atoms).
                    if sd.rel != SigRel::In {
                        return Err(format!(
                            "sig {n} cannot extend the builtin \"{p}\" signature"
                        ));
                    }
                    children.entry(p.clone()).or_default().push(n.clone());
                } else if p == "Real" {
                    // Builtin `Real` (abstract): `in Real` accepted (subset
                    // of the Real closure); `extends Real` children get
                    // OWN atoms distributed over the Real budget (like a
                    // normal hierarchy root; see the allocation below),
                    // with Alloy partition semantics in lower.rs
                    // (subset + disjoint + covered by extenders).
                    children.entry(p.clone()).or_default().push(n.clone());
                } else if p == "EReal" {
                    // Builtin `EReal`: `in EReal` accepted (subset of the
                    // EReal atoms); `extends EReal` accepted with Alloy
                    // partition semantics (subset + disjoint siblings +
                    // parent covered by extenders; membership constraints
                    // in lower.rs, shared upper bounds below).
                    children.entry(p.clone()).or_default().push(n.clone());
                } else {
                    if !all_names.iter().any(|x| x == p)
                        && module.sigs.iter().all(|s| !s.names.contains(p))
                    {
                        return Err(format!("sig {n} extends unknown parent {p}"));
                    }
                    children.entry(p.clone()).or_default().push(n.clone());
                }
            }
        }
    }

    // allocation: process hierarchies top-down
    // For `sig in`, the child does NOT allocate its own atoms; it shares
    // the parent's atoms (subset constraint added as formula in lower.rs).
    let mut atoms_of: HashMap<String, Vec<String>> = HashMap::new();

    fn is_root(parents: &HashMap<&str, Option<String>>, n: &str) -> bool {
        parents.get(n).map(|p| p.is_none()).unwrap_or(true)
    }

    let mut roots: Vec<String> = all_names
        .iter()
        .filter(|n| is_root(&parents, n))
        .cloned()
        .collect();

    // Per-sig 0-based numbering (Java Kodkod style: `Book$0`): each sig's
    // atoms are numbered from 0, not from a shared global counter.
    let alloc_for = |name: &str, count: u32| -> Vec<String> {
        (0..count).map(|i| format!("{name}${i}")).collect()
    };

    // iterate until fixed point so parents seen before children regardless of order
    let mut pending: Vec<String> = roots.split_off(0);
    roots = pending.clone();
    pending.clear();

    // simple queue of hierarchy roots
    roots.sort();
    for root in &roots {
        // gather subtree in BFS order
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(root.clone());
        let mut order: Vec<String> = Vec::new();
        while let Some(cur) = queue.pop_front() {
            order.push(cur.clone());
            for c in children.get(&cur).cloned().unwrap_or_default() {
                queue.push_back(c);
            }
        }
        // total for the root node itself
        let total = user.get(root.as_str()).map(|(t, _)| *t).unwrap_or(overall);
        // one/lone sigs cap at 1 atom
        let rmult = mults.get(root.as_str()).copied().unwrap_or(SigMult::None);
        let has_children = children.contains_key(root);
        let total = match rmult {
            SigMult::One | SigMult::Lone => 1,
            _ => total,
        };
        if !has_children {
            let at = alloc_for(
                root,
                total.max(if rmult == SigMult::Lone || rmult == SigMult::Some {
                    1
                } else {
                    0
                }),
            );
            atoms_of.insert(root.clone(), at);
            continue;
        }
        // Check if there are any non-in children that need atom allocation
        let kids = children[root].clone();
        let non_in_kids: Vec<&String> = kids
            .iter()
            .filter(|k| sig_rels.get(k.as_str()).copied().unwrap_or(SigRel::None) != SigRel::In)
            .collect();
        // If all children are `in` children, allocate atoms for the root itself
        // (in children share the parent's atoms, so the parent must have them)
        if non_in_kids.is_empty() {
            let at = alloc_for(
                root,
                total.max(if rmult == SigMult::Lone || rmult == SigMult::Some {
                    1
                } else {
                    0
                }),
            );
            atoms_of.insert(root.clone(), at);
            continue;
        }
        // distribute among direct children that have no user scope
        // skip `in` children - they don't allocate atoms
        let mut remaining = total;
        let mut unspecified: Vec<&String> = kids
            .iter()
            .filter(|k| {
                !user.contains_key(k.as_str())
                    && sig_rels.get(k.as_str()).copied().unwrap_or(SigRel::None) != SigRel::In
            })
            .collect();
        unspecified.sort();
        let share = if unspecified.is_empty() {
            0
        } else {
            remaining / unspecified.len() as u32
        };
        for k in &kids {
            // `in` children share parent atoms; don't allocate
            if sig_rels.get(k.as_str()).copied().unwrap_or(SigRel::None) == SigRel::In {
                continue;
            }
            if let Some((n, _)) = user.get(k) {
                let kmult = mults.get(k.as_str()).copied().unwrap_or(SigMult::None);
                let n2 = match kmult {
                    SigMult::One | SigMult::Lone => 1,
                    _ => *n,
                };
                atoms_of.insert(k.clone(), alloc_for(k, n2));
            } else {
                let kmult = mults.get(k.as_str()).copied().unwrap_or(SigMult::None);
                let take = match kmult {
                    SigMult::One | SigMult::Lone => 1,
                    _ => {
                        let t = share.min(remaining);
                        remaining -= t;
                        t
                    }
                };
                atoms_of.insert(k.clone(), alloc_for(k, take));
            }
        }
    }

    // FLAT-EXPERIMENT: no free pool and no own atoms for `Real` /
    // `EReal` — both are type domains over the bit lanes, and user
    // `extends` children are rejected. Values live in the lane
    // partition built below, held by `in`-sigs or holder fields.

    // For `in` children, their atoms are a subset of the parent's atoms.
    // Do NOT add them to atoms_of (which feeds the universe); instead
    // record the relationship so bind_sigs can set the correct upper bound.
    // Resolve transitively: if B in A in Top, B gets Top's atoms.
    let mut in_children_atoms: HashMap<String, Vec<String>> = HashMap::new();
    // First pass: collect direct in-relationships
    let mut in_direct: HashMap<String, String> = HashMap::new();
    for sd in &module.sigs {
        if sd.rel == SigRel::In {
            if let Some(p) = &sd.extends {
                for n in &sd.names {
                    in_direct.insert(n.clone(), p.clone());
                }
            }
        }
    }
    // Second pass: resolve transitively to a root with allocated atoms.
    // A builtin `Int`/`Signed` ancestor terminates at the int atoms
    // `{0, .., W-1}` for the effective atom count (same naming as the
    // universe construction below). With lazy allocation (`needs_int ==
    // false`) the range is empty; that path is unreachable for `in Int`
    // children (which set `needs_int`), so the empty case only guards
    // the type level.
    let int_atoms: Vec<String> = if needs_int {
        (0..int_count).map(|v| v.to_string()).collect()
    } else {
        Vec::new()
    };
    // FLAT-EXPERIMENT: the `Real` and `EReal` type domains ARE the bit
    // lanes (lazy like `Int`: allocated only when mentioned).
    // `Real = $M + $E` (the exact centre `c = m*2^e`) and
    // `EReal = $M + $E + $P + $K` (the same centre plus the error
    // interval). A value is the *set* of its set bits, so a value atom
    // pool is not just unnecessary — it would break the bijectivity
    // between a bit set and its lane reading. `Real` is therefore a
    // subset of `EReal` as a domain (an exact real is an `EReal` with
    // no error bits), not an Alloy parent: both are independent
    // builtins, like `Int` and `Signed`.
    let mut lane_atoms: HashMap<u32, Vec<String>> = HashMap::new();
    for (group, prefix, width) in [
        (LANE_M, "M", mepk_widths.m_width),
        (LANE_E, "E", mepk_widths.e_width),
        (LANE_P, "P", mepk_widths.p_width),
        (LANE_K, "K", mepk_widths.k_width),
    ] {
        let needed = if group == LANE_M || group == LANE_E {
            needs_real
        } else {
            needs_ereal
        };
        if needed {
            lane_atoms.insert(group, (0..width).map(|i| format!("{prefix}${i}")).collect());
        }
    }
    let domain_of = |groups: &[u32]| -> Vec<String> {
        groups
            .iter()
            .filter_map(|g| lane_atoms.get(g))
            .flatten()
            .cloned()
            .collect()
    };
    let real_domain: Vec<String> = domain_of(&[LANE_M, LANE_E]);
    let ereal_domain: Vec<String> = domain_of(&[LANE_M, LANE_E, LANE_P, LANE_K]);
    for n in &all_names {
        if let Some(parent) = in_direct.get(n) {
            let mut cur = parent.clone();
            while let Some(next_parent) = in_direct.get(&cur) {
                cur = next_parent.clone();
            }
            // cur is now the root (non-in) ancestor, or builtin
            // `Int`/`Signed`/`Real`/`EReal`
            if cur == "Int" || cur == "Signed" {
                in_children_atoms.insert(n.clone(), int_atoms.clone());
            } else if cur == "EReal" || ereal_in_children(&module).contains(&cur) {
                in_children_atoms.insert(n.clone(), ereal_domain.clone());
            } else if cur == "Real" {
                in_children_atoms.insert(n.clone(), real_domain.clone());
            } else if let Some(own) = atoms_of.get(&cur) {
                // User hierarchy root with own atoms: `in`-descendants
                // share those.
                in_children_atoms.insert(n.clone(), own.clone());
            } else {
                let root_atoms = atoms_of.get(&cur).cloned().unwrap_or_default();
                in_children_atoms.insert(n.clone(), root_atoms);
            }
        }
    }
    // NOTE: user `extends Real` children keep their OWN atoms (allocated
    // above, already in `atoms_of`); they must NOT be overwritten here.
    // The abstract cover (`Real` ⊆ extenders) is a formula in lower.rs.

    // closure atoms: include own + descendants
    let mut closure: HashMap<String, Vec<String>> = HashMap::new();
    for n in &all_names {
        let mut acc = atoms_of.get(n).cloned().unwrap_or_default();
        // `in` children's atoms are parent's atoms, already in parent's acc
        if let Some(in_atoms) = in_children_atoms.get(n) {
            acc = in_atoms.clone();
        }
        let mut queue = std::collections::VecDeque::new();
        // only add non-in children to the queue (in children don't expand further)
        if let Some(cs) = children.get(n) {
            for c in cs {
                if !in_children_atoms.contains_key(c) {
                    queue.push_back(c.clone());
                }
            }
        }
        while let Some(cur) = queue.pop_front() {
            acc.extend(atoms_of.get(&cur).cloned().unwrap_or_default());
            if let Some(cs) = children.get(&cur) {
                for c in cs {
                    if !in_children_atoms.contains_key(c) {
                        queue.push_back(c.clone());
                    }
                }
            }
        }
        closure.insert(n.clone(), acc);
    }

    // universe: every allocated atom, sorted for determinism
    let mut flat: Vec<String> = atoms_of.values().flatten().cloned().collect();
    flat.sort();
    // int atoms (lazy: omitted entirely when Int is never used as a set)
    let int_names: Vec<String> = if needs_int {
        (0..int_count).map(|v| v.to_string()).collect()
    } else {
        Vec::new()
    };
    // Step atoms: temporal step count (`for N steps`, default 4 when the
    // module carries temporal operators), else empty (static = empty set).
    let temporal = module.facts.iter().any(|(_, f)| f.has_temporal())
        || module.soft_facts.iter().any(|(_, f)| f.has_temporal())
        || module.paras.iter().any(|p| p.body.has_temporal())
        || module.sigs.iter().any(|sd| {
            sd.fact.as_ref().is_some_and(|f| f.has_temporal())
                || sd.fields.iter().any(|d| d.expr.has_temporal())
        });
    let step_n: u32 = match scope.steps {
        Some(n) => n,
        None => {
            if temporal {
                4
            } else {
                0
            }
        }
    };
    let step_atoms: Vec<String> = (0..step_n).map(|i| format!("Step${i}")).collect();
    let mut uni_atoms: Vec<String> = flat.clone();
    uni_atoms.extend(int_names.iter().cloned());
    uni_atoms.extend(step_atoms.iter().cloned());
    // Lane groups in numeric group-id order (M, E, P, K): HashMap
    // iteration order is nondeterministic across resolves, and universe
    // atom indices must agree between the solve-time universe (the
    // instance) and query-time re-resolves (atom-name lookups).
    let mut lane_groups: Vec<u32> = lane_atoms.keys().copied().collect();
    lane_groups.sort_unstable();
    for g in lane_groups {
        uni_atoms.extend(lane_atoms[&g].iter().cloned());
    }
    let refs: Vec<&str> = uni_atoms.iter().map(|s| s.as_str()).collect();
    let universe = Universe::new(refs).map_err(|e| format!("universe: {e}"))?;

    let mut sigs = HashMap::new();
    for n in &all_names {
        sigs.insert(
            n.clone(),
            SigInfo {
                parent: parents.get(n.as_str()).cloned().flatten(),
                atoms: atoms_of.get(n).cloned().unwrap_or_default(),
            },
        );
    }
    // Builtin `Step`: reserved name (lexer maps any case/plural to the
    // scope keyword, so a user `sig Step` cannot parse; rename to avoid).
    sigs.insert(
        "Step".to_string(),
        SigInfo {
            parent: None,
            atoms: step_atoms.clone(),
        },
    );
    // Builtin `Real` and `EReal`: type domains with no own atoms (the
    // lane atoms below *are* their populations, allocated lazily). They
    // are independent builtins — `EReal` is the `Real` domain plus the
    // error lanes, not an Alloy child, so it carries no parent link
    // (mirroring `Int`/`Signed`).
    sigs.insert(
        "Real".to_string(),
        SigInfo {
            parent: None,
            atoms: Vec::new(),
        },
    );
    sigs.insert(
        "EReal".to_string(),
        SigInfo {
            parent: None,
            atoms: Vec::new(),
        },
    );
    // Builtin flat lane sigs (`$M`/`$E`/`$P`/`$K`): the lane atoms
    // themselves, queryable as sets (`some $M`, `X & $M`).
    // FLAT-EXPERIMENT: `$M`/`$E` partition `Real` (`Real = $M + $E`) and
    // `$P`/`$K` partition `EReal` (`EReal = $M + $E + $P + $K`).
    for (name, group) in [
        ("$M", LANE_M),
        ("$E", LANE_E),
        ("$P", LANE_P),
        ("$K", LANE_K),
    ] {
        let atoms = lane_atoms.get(&group).cloned().unwrap_or_default();
        let parent = if matches!(name, "$M" | "$E") {
            Some("Real".to_string())
        } else {
            Some("EReal".to_string())
        };
        sigs.insert(
            name.to_string(),
            SigInfo {
                parent,
                atoms,
            },
        );
    }

    Ok(Resolved {
        universe,
        bitwidth,
        int_count,
        step_atoms: step_atoms.clone(),
        sigs,
        closure_atoms: {
            let mut c = closure;
            c.insert("Step".to_string(), step_atoms);
            c.insert("Real".to_string(), real_domain.clone());
            c.insert("EReal".to_string(), ereal_domain.clone());
            for (name, group) in [
                ("$M", LANE_M),
                ("$E", LANE_E),
                ("$P", LANE_P),
                ("$K", LANE_K),
            ] {
                c.insert(
                    name.to_string(),
                    lane_atoms.get(&group).cloned().unwrap_or_default(),
                );
            }
            c
        },
        in_children_atoms,
        lane_atoms,
        mepk_widths,
    })
}

/// Builds bounds for every sig relation on `bounds`.
///
/// Alloy semantics: a plain sig's population is FLEXIBLE up to its scope
/// (lower = empty, upper = allocated atoms); `one sig` exists exactly;
/// `lone sig` allows empty; `exactly` scopes pin lower = upper.
pub fn bind_sigs(
    module: &Module,
    res: &Resolved,
    _pool: &Arc<alloy_kodkod_rs::relation::RelationPool>,
    arena: &mut alloy_kodkod_rs::ast::AstArena,
    b: &mut Bounds,
    cmd_scope: &crate::ast::Scope,
) -> Result<(), String> {
    use std::collections::HashMap as HM;
    let mut exact: HM<String, bool> = HM::new();
    for sd in &module.sigs {
        for n in &sd.names {
            exact.insert(n.clone(), sd.mult == SigMult::One);
        }
    }
    for (name, e) in &cmd_scope.entries {
        if matches!(e, ScopeEntry::Exactly(_)) {
            exact.insert(name.clone(), true);
        }
    }
    for name in res.sigs.keys() {
        // Unallocated builtins bind nothing (no empty shells).
        if is_unallocated_builtin(res, name) {
            continue;
        }
        let rel = arena.relation(name, 1);
        let mut ts = TupleSet::new(&res.universe, 1).map_err(|e| e.to_string())?;
        // For `in` children, use parent's atoms as upper bound
        let atoms = if let Some(in_atoms) = res.in_children_atoms.get(name) {
            in_atoms.clone()
        } else {
            res.atoms_of(name)
        };
        for a in &atoms {
            let idx = res.universe.index(a).map_err(|e| e.to_string())?;
            ts.insert_index(idx as i64);
        }
        let lo = TupleSet::new(&res.universe, 1).map_err(|e| e.to_string())?;
        // FLAT-EXPERIMENT: `Real`, `EReal` and the four lane sigs are
        // type domains like `Int`/`Step`: always exactly their full atom
        // set, never a free subset.
        let is_exact = *exact.get(name).unwrap_or(&false)
            || (cmd_scope.overall_exact && !cmd_scope.entries.iter().any(|(n, _)| n == name))
            || name == "Step"
            || is_lane_sig(name)
            || name == "Real"
            || name == "EReal";
        // An `in`-sig's atoms are inherited, not its own allocation, so
        // `one`/`exactly` must not become an exact bound over them (that
        // would force the sig to hold its whole parent). The multiplicity
        // stays a cardinality formula in lower.rs, as in Java's
        // `BoundsComputer`.
        let inherits_atoms = res.in_children_atoms.contains_key(name);
        let is_exact = is_exact && !inherits_atoms;
        // `some sig` requires a non-empty lower bound.
        let has_some_mult = module
            .sigs
            .iter()
            .any(|sd| sd.mult == SigMult::Some && sd.names.iter().any(|n| n == name));
        if is_exact {
            b.bound_exactly(rel, &ts).map_err(|e| e.to_string())?;
        } else if has_some_mult {
            // lower = first atom, upper = allocated atoms
            let mut lo_set = TupleSet::new(&res.universe, 1).map_err(|e| e.to_string())?;
            if let Some(first_a) = atoms.first() {
                let idx = res.universe.index(first_a).map_err(|e| e.to_string())?;
                lo_set.insert_index(idx as i64);
            }
            b.bound(rel, &lo_set, &ts).map_err(|e| e.to_string())?;
        } else {
            b.bound(rel, &lo, &ts).map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}

/// Helper: tupleset from atom names.
pub fn ts_of(res: &Resolved, atoms: &[String]) -> Result<TupleSet, String> {
    let mut ts = TupleSet::new(&res.universe, 1).map_err(|e| e.to_string())?;
    for a in atoms {
        let idx = res.universe.index(a).map_err(|e| e.to_string())?;
        ts.insert_index(idx as i64);
    }
    Ok(ts)
}

/// Helper: singleton tuple from atom names.
pub fn tuple_of(res: &Resolved, atoms: &[String]) -> Result<Tuple, String> {
    let strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    Tuple::from_atoms(&res.universe, &strs).map_err(|e| e.to_string())
}
