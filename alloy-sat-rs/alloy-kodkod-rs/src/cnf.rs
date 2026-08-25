use crate::bool::{BoolFactory, BoolNode, BoolRef};
use crate::intset::IntSet;
use crate::sat::SatSolver;

#[derive(Debug, thiserror::Error)]
pub enum CnfError {
    #[error("boolean constant encountered inside circuit")]
    ConstantInside,
    #[error("dangling boolean reference")]
    DanglingRef,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CnfTranslation {
    pub num_vars: usize,
    pub clauses: Vec<Vec<i64>>,
}

struct Polarity {
    bits: Vec<u8>,
}

const POS: u8 = 1;
const NEG: u8 = 2;
const BOTH: u8 = 3;

impl Polarity {
    fn new() -> Polarity {
        Polarity { bits: Vec::new() }
    }

    fn ensure(&mut self, slot: u32) {
        while self.bits.len() <= slot as usize {
            self.bits.push(0);
        }
    }

    fn seen_with(&mut self, slot: u32, bit: u8) -> bool {
        self.ensure(slot);
        let prev = self.bits[slot as usize];
        let next = prev | bit;
        self.bits[slot as usize] = next;
        next == prev
    }

    fn has(&self, slot: u32, bit: u8) -> bool {
        self.bits.get(slot as usize).copied().unwrap_or(0) & bit != 0
    }

    fn toggle(bit: u8) -> u8 {
        match bit {
            POS => NEG,
            NEG => POS,
            _ => BOTH,
        }
    }
}

struct Translator<'a> {
    factory: &'a BoolFactory,
    visited: IntSet,
    polarity: Polarity,
    clauses: Vec<Vec<i64>>,
    optimize_polarity: bool,
}

impl<'a> Translator<'a> {
    fn flags(&self, slot: u32) -> (bool, bool) {
        if !self.optimize_polarity {
            return (true, true);
        }
        (self.polarity.has(slot, POS), self.polarity.has(slot, NEG))
    }
}

impl<'a> Translator<'a> {
    fn detect(&mut self, r: BoolRef, incoming_bit: u8) -> Result<(), CnfError> {
        if !self.optimize_polarity || r.is_const() {
            return Ok(());
        }
        let bit = if r.sign() {
            incoming_bit
        } else {
            Polarity::toggle(incoming_bit)
        };
        match self.factory.node(r).ok_or(CnfError::DanglingRef)? {
            BoolNode::Var => Ok(()),
            BoolNode::And(kids) | BoolNode::Or(kids) => {
                if !self.polarity.seen_with(r.slot(), bit) {
                    for &k in kids {
                        self.detect(k, bit)?;
                    }
                }
                Ok(())
            }
            BoolNode::Ite { c, t, e } => {
                if !self.polarity.seen_with(r.slot(), bit) {
                    self.detect(*c, BOTH)?;
                    self.detect(*t, bit)?;
                    self.detect(*e, bit)?;
                }
                Ok(())
            }
        }
    }

    fn emit(&mut self, clause: Vec<i64>) {
        self.clauses.push(clause);
    }

    fn visit(&mut self, r: BoolRef) -> Result<i64, CnfError> {
        if r.is_const() {
            return Err(CnfError::ConstantInside);
        }
        let node = self.factory.node(r).ok_or(CnfError::DanglingRef)?;
        let lit = match node {
            BoolNode::Var => r.slot() as i64,
            BoolNode::And(kids) => {
                let o = r.slot() as i64;
                if self.visited.insert(o) {
                    let (p, n) = self.flags(o as u32);
                    let mut last: Vec<i64> = if n {
                        Vec::with_capacity(kids.len() + 1)
                    } else {
                        Vec::new()
                    };
                    for &k in kids {
                        let il = self.visit(k)?;
                        if p {
                            self.emit(vec![il, -o]);
                        }
                        if n {
                            last.push(-il);
                        }
                    }
                    if n {
                        last.push(o);
                        self.emit(last);
                    }
                }
                o
            }
            BoolNode::Or(kids) => {
                let o = r.slot() as i64;
                if self.visited.insert(o) {
                    let (n, p) = self.flags(o as u32);
                    let mut last: Vec<i64> = if n {
                        Vec::with_capacity(kids.len() + 1)
                    } else {
                        Vec::new()
                    };
                    for &k in kids {
                        let il = self.visit(k)?;
                        if p {
                            self.emit(vec![-il, o]);
                        }
                        if n {
                            last.push(il);
                        }
                    }
                    if n {
                        last.push(-o);
                        self.emit(last);
                    }
                }
                o
            }
            BoolNode::Ite { c, t, e } => {
                let o = r.slot() as i64;
                if self.visited.insert(o) {
                    let i = self.visit(*c)?;
                    let tv = self.visit(*t)?;
                    let ev = self.visit(*e)?;
                    let (p, n) = self.flags(o as u32);
                    if p {
                        self.emit(vec![-i, tv, -o]);
                        self.emit(vec![i, ev, -o]);
                        self.emit(vec![tv, ev, -o]);
                    }
                    if n {
                        self.emit(vec![-i, -tv, o]);
                        self.emit(vec![i, -ev, o]);
                        self.emit(vec![-tv, -ev, o]);
                    }
                }
                o
            }
        };
        Ok(if r.sign() { lit } else { -lit })
    }

    fn run(mut self, root: BoolRef, max_primary_var: usize) -> Result<CnfTranslation, CnfError> {
        self.detect(root, POS)?;
        let max_lit = root.slot() as usize;
        let num_vars = max_lit.max(max_primary_var);
        let is_and_root = root.sign() && matches!(self.factory.node(root), Some(BoolNode::And(_)));
        if is_and_root {
            let kids = match self.factory.node(root).unwrap() {
                BoolNode::And(kids) => kids.clone(),
                _ => unreachable!(),
            };
            for &k in &kids {
                self.visit(k)?;
            }
            for k in &kids {
                self.emit(vec![k.0 as i64]);
            }
        } else {
            let lit = self.visit(root)?;
            self.emit(vec![lit]);
        }
        Ok(CnfTranslation {
            num_vars,
            clauses: self.clauses,
        })
    }
}

pub fn translate_to_cnf(
    factory: &BoolFactory,
    root: BoolRef,
    max_primary_var: usize,
) -> Result<CnfTranslation, CnfError> {
    if root.is_const() {
        let num_vars = max_primary_var;
        let clauses = if root.const_value() {
            Vec::new()
        } else {
            vec![Vec::new()]
        };
        return Ok(CnfTranslation { num_vars, clauses });
    }
    let t = Translator {
        factory,
        visited: IntSet::new(),
        polarity: Polarity::new(),
        clauses: Vec::new(),
        optimize_polarity: std::env::var("ALLOY_NO_POLARITY_OPT").is_err(),
    };
    t.run(root, max_primary_var)
}

pub fn translate_into_solver<S: SatSolver>(
    solver: &mut S,
    factory: &BoolFactory,
    root: BoolRef,
    max_primary_var: usize,
) -> Result<(), CnfError> {
    let cnf = translate_to_cnf(factory, root, max_primary_var)?;
    if cnf.num_vars > solver.num_variables() {
        solver.add_variables(cnf.num_vars - solver.num_variables());
    }
    for clause in &cnf.clauses {
        solver.add_clause(clause);
    }
    Ok(())
}

/// Outcome of translating one top-level conjunct without asserting it
/// ([`translate_conjunct_def`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootCnf {
    /// Conjunct simplified to constant true; nothing to assert or assume.
    TriviallyTrue,
    /// Conjunct simplified to constant false; the empty clause was emitted,
    /// so the problem is unconditionally UNSAT.
    TriviallyFalse,
    /// *Signed* root literal of the conjunct (e.g. `-7` for `not(f)` whose
    /// circuit root is gate 7). Its definitional clauses were emitted (both
    /// polarities); forcing it is up to the caller via a unit clause or —
    /// for core extraction — a SAT assumption.
    Lit(i64),
}

/// Translate `root` into `solver` as *definitions only*: every non-variable
/// gate gets its full Tseitin definition, but the root literal is neither
/// asserted nor returned as a clause. The caller decides how to force it
/// (unit axiom à la kodkod's selector axioms, or an assumption).
///
/// Polarity optimization is disabled on this path so that each gate is fully
/// defined regardless of where else it may be reused across conjuncts.
pub fn translate_conjunct_def<S: SatSolver>(
    solver: &mut S,
    factory: &BoolFactory,
    root: BoolRef,
    max_primary_var: usize,
) -> Result<RootCnf, CnfError> {
    if root.is_const() {
        return Ok(if root.const_value() {
            RootCnf::TriviallyTrue
        } else {
            solver.add_clause(&[]);
            RootCnf::TriviallyFalse
        });
    }
    let mut t = Translator {
        factory,
        visited: IntSet::new(),
        polarity: Polarity::new(),
        clauses: Vec::new(),
        // Full definitions: shared gates must behave identically in every
        // conjunct, and an assumed selector needs both definition directions.
        optimize_polarity: false,
    };
    let lit = t.emit_definitions(root)?;
    let num_vars = num_vars_of(root.slot(), max_primary_var);
    if num_vars > solver.num_variables() {
        solver.add_variables(num_vars - solver.num_variables());
    }
    for clause in &t.clauses {
        solver.add_clause(clause);
    }
    Ok(RootCnf::Lit(lit))
}

fn num_vars_of(root_slot: u32, max_primary_var: usize) -> usize {
    (root_slot as usize).max(max_primary_var)
}

impl<'a> Translator<'a> {
    /// Definitions-only traversal returning the signed root literal.
    fn emit_definitions(&mut self, root: BoolRef) -> Result<i64, CnfError> {
        let o = root.slot() as i64;
        match self.factory.node(root).ok_or(CnfError::DanglingRef)? {
            BoolNode::Var => Ok(if root.sign() { o } else { -o }),
            BoolNode::And(kids) => {
                // o <-> AND(kids), both directions, regardless of root sign:
                // an assumed selector needs a fully defined gate.
                let mut last: Vec<i64> = Vec::with_capacity(kids.len() + 1);
                for &k in kids {
                    let il = self.visit(k)?;
                    self.emit(vec![il, -o]);
                    last.push(-il);
                }
                last.push(o);
                self.emit(last);
                Ok(if root.sign() { o } else { -o })
            }
            _ => {
                // Or / Ite: visit already emits definitions; polarity flags
                // default to (true, true) because optimize_polarity is off.
                let lit = self.visit(root)?;
                Ok(lit)
            }
        }
    }
}
