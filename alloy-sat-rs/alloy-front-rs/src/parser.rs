//! Recursive-descent + Pratt parser for the supported Alloy subset.

use crate::ast::*;
use crate::lex::{Tok, Token};
use crate::types::{int_left_of_in_is_error, should_rewind_eq};
use crate::FrontError;

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
    inline_body_index: usize,
    pending_paras: Vec<Para>,
}

type PResult<T> = Result<T, FrontError>;

impl Parser {
    pub fn new(toks: Vec<Token>) -> Parser {
        Parser {
            toks,
            pos: 0,
            inline_body_index: 0,
            pending_paras: Vec::new(),
        }
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn peek_at(&self, k: usize) -> &Tok {
        let i = (self.pos + k).min(self.toks.len() - 1);
        &self.toks[i].tok
    }

    fn pos(&self) -> usize {
        self.toks[self.pos].pos
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == t {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, t: &Tok) -> PResult<Token> {
        if self.peek() == t {
            Ok(self.bump())
        } else {
            Err(self.err(&format!(
                "expected {}, found {}",
                t.describe(),
                self.peek().describe()
            )))
        }
    }

    fn err(&self, msg: &str) -> FrontError {
        FrontError::Parse {
            pos: self.pos(),
            msg: msg.to_string(),
        }
    }

    // ------------------------------------------------------------------
    // module
    // ------------------------------------------------------------------

    /// Parse a single bare relational expression (REPL `:eval`/`:query` input).
    /// `let` bindings are accepted wherever the expression grammar allows them.
    pub fn expr(mut self) -> PResult<Expr> {
        let e = self.rel_expr_top(false)?;
        self.expect(&Tok::Eof)?;
        Ok(e)
    }

    /// Parse a single top-level formula (REPL `:eval` input).
    pub fn formula_top(mut self) -> PResult<Formula> {
        let f = self.formula()?;
        self.expect(&Tok::Eof)?;
        Ok(f)
    }

    /// Parse a single bare integer expression (REPL `:query` input,
    /// e.g. `#A` or `#A + 1`).
    pub fn int_expr_top(mut self) -> PResult<IntExpr> {
        let e = self.int_expr()?;
        self.expect(&Tok::Eof)?;
        Ok(e)
    }

    pub fn module(mut self) -> PResult<Module> {
        let mut header = String::new();
        if self.eat(&Tok::Module) {
            while !matches!(self.peek(), Tok::Eof) {
                match self.peek().clone() {
                    Tok::Ident(_) => {
                        header.push_str(&match self.bump().tok {
                            Tok::Ident(n) => n,
                            _ => unreachable!(),
                        });
                    }
                    Tok::Slash => {
                        self.bump();
                        header.push('/');
                    }
                    _ => break,
                }
                // consume optional version/name suffixes until newline-ish token
                if matches!(
                    self.peek(),
                    Tok::Sig
                        | Tok::Open
                        | Tok::Fact
                        | Tok::Pred
                        | Tok::Assert
                        | Tok::Run
                        | Tok::Check
                        | Tok::Abstract
                ) {
                    break;
                }
            }
        }
        let mut opens = Vec::new();
        while self.eat(&Tok::Open) {
            let mut path = String::new();
            let mut params = Vec::new();
            let mut hit_bracket = false;
            loop {
                match self.bump().tok {
                    Tok::Ident(n) => {
                        path.push_str(&n);
                    }
                    Tok::Slash => path.push('/'),
                    Tok::LBracket => {
                        hit_bracket = true;
                        loop {
                            match self.peek() {
                                Tok::RBracket => {
                                    self.bump();
                                    break;
                                }
                                Tok::Eof => {
                                    return Err(self.err("unterminated open bracket"));
                                }
                                _ => {}
                            }
                            if self.eat(&Tok::Exactly) {
                                let name = match self.bump().tok {
                                    Tok::Ident(n) => n,
                                    other => {
                                        return Err(self.err(&format!(
                                            "expected type name after `exactly`, got {}",
                                            other.describe()
                                        )))
                                    }
                                };
                                params.push(crate::ast::OpenParam::Exactly(name));
                            } else {
                                let name = match self.bump().tok {
                                    Tok::Ident(n) => n,
                                    other => {
                                        return Err(self.err(&format!(
                                            "expected type name in open params, got {}",
                                            other.describe()
                                        )))
                                    }
                                };
                                params.push(crate::ast::OpenParam::Set(name));
                            }
                            self.eat(&Tok::Comma);
                        }
                        break;
                    }
                    Tok::As => break,
                    Tok::Eof => return Err(self.err("unexpected EOF in open")),
                    other => return Err(self.err(&format!("bad open path: {}", other.describe()))),
                }
            }
            if hit_bracket {
                self.eat(&Tok::As); // optional `as`
                let alias = match self.bump().tok {
                    Tok::Ident(n) => {
                        self.nod(&n)?;
                        n
                    }
                    other => {
                        return Err(self.err(&format!(
                            "expected alias after open params, got {}",
                            other.describe()
                        )))
                    }
                };
                opens.push(crate::ast::Open {
                    path,
                    alias,
                    params,
                });
            } else {
                let alias = match self.bump().tok {
                    Tok::Ident(n) => {
                        self.nod(&n)?;
                        n
                    }
                    other => return Err(self.err(&format!("bad open alias: {}", other.describe()))),
                };
                opens.push(crate::ast::Open {
                    path,
                    alias,
                    params: Vec::new(),
                });
            }
        }

        let mut sigs = Vec::new();
        let mut facts = Vec::new();
        let mut soft_facts = Vec::new();
        let mut paras = Vec::new();
        let mut commands = Vec::new();
        let mut partials = Vec::new();
        loop {
            match self.peek() {
                Tok::Sig => sigs.push(self.sig_decl()?),
                Tok::Abstract | Tok::One | Tok::Lone | Tok::Some | Tok::Var
                    if matches!(self.peek_at(1), Tok::Sig) =>
                {
                    sigs.push(self.sig_decl()?);
                }
                // `partial name { ... }`: named partial-instance block.
                // A bare `partial` is never valid Alloy, so the keyword
                // check needs no further lookahead.
                Tok::Ident(n) if n == "partial" => {
                    let pd = self.partial_def()?;
                    if partials.iter().any(|p: &PartialDef| p.name == pd.name) {
                        return Err(self.err(&format!("duplicate partial '{}'", pd.name)));
                    }
                    partials.push(pd);
                }
                Tok::Fact => {
                    self.bump();
                    let name = if let Tok::Ident(_) = self.peek() {
                        Some(match self.bump().tok {
                            Tok::Ident(n) => {
                                self.nod(&n)?;
                                n
                            }
                            _ => unreachable!(),
                        })
                    } else {
                        None
                    };
                    let body = self.braced_formula()?;
                    facts.push((name, body));
                }
                // AlloyMax `soft fact [name] { ... }`: collected as soft
                // constraints (optimized, not asserted).
                Tok::Soft => {
                    self.bump();
                    self.expect(&Tok::Fact)?;
                    let name = if let Tok::Ident(_) = self.peek() {
                        Some(match self.bump().tok {
                            Tok::Ident(n) => {
                                self.nod(&n)?;
                                n
                            }
                            _ => unreachable!(),
                        })
                    } else {
                        None
                    };
                    let body = self.braced_formula()?;
                    soft_facts.push((name, body));
                }
                Tok::Pred => paras.push(self.para(false)?),
                Tok::Fun => paras.push(self.para(true)?),
                Tok::Assert => {
                    self.bump();
                    let name = match self.bump().tok {
                        Tok::Ident(n) => {
                            self.nod(&n)?;
                            n
                        }
                        other => {
                            return Err(self
                                .err(&format!("expected assert name, got {}", other.describe())))
                        }
                    };
                    let body = self.braced_formula()?;
                    // store asserts as zero-param paras named by the assert;
                    // commands reference them by name
                    paras.push(Para {
                        name,
                        params: Vec::new(),
                        body,
                        body_expr: None,
                        is_fun: false,
                        ret: None,
                    });
                }
                Tok::Run | Tok::Check | Tok::Maximize | Tok::Minimize => {
                    commands.push(self.command()?)
                }
                Tok::Eof => break,
                other => {
                    return Err(
                        self.err(&format!("unexpected {} at module level", other.describe()))
                    )
                }
            }
        }
        paras.append(&mut self.pending_paras);
        Ok(Module {
            header,
            sigs,
            facts,
            soft_facts,
            paras,
            commands,
            opens,
            partials,
        })
    }

    /// `partial name { R = S, L in R, ... }`: a named partial-instance
    /// block (diagram). Entries compare a relation side against a
    /// label-set side with `=` (exact) or `in` (lower/upper by orientation).
    fn partial_def(&mut self) -> PResult<PartialDef> {
        let pos = self.pos();
        match self.bump().tok {
            Tok::Ident(n) if n == "partial" => {}
            _ => unreachable!(),
        }
        let name = self.bind_name()?;
        self.expect(&Tok::LBrace)?;
        let mut entries = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            loop {
                entries.push(self.partial_entry()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RBrace)?;
        if entries.is_empty() {
            return Err(self.err("partial block must have at least one entry"));
        }
        Ok(PartialDef { name, entries, pos })
    }

    /// One `partial` entry: `<expr> (=|in) <expr>`. Both sides must use
    /// the restricted label-set shape; which side is the relation is
    /// decided at lowering by label presence and comparison orientation.
    fn partial_entry(&mut self) -> PResult<PartialEntry> {
        let pos = self.pos();
        let left = self.rel_expr_top(false)?;
        let op =
            match self.peek() {
                Tok::Eq => {
                    self.bump();
                    PartialOp::Eq
                }
                Tok::In => {
                    self.bump();
                    PartialOp::In
                }
                Tok::NotEq => {
                    return Err(self.err(
                        "partial entries use `=` or `in` only (`!=` is not supported; use `avoid`)",
                    ))
                }
                Tok::Not => return Err(self.err(
                    "partial entries use `=` or `in` only (`not in` is not supported; use `avoid`)",
                )),
                other => {
                    return Err(self.err(&format!(
                        "expected `=` or `in` in partial entry, got {}",
                        other.describe()
                    )))
                }
            };
        let right = self.rel_expr_top(false)?;
        for side in [&left, &right] {
            if !partial_set_shape(side) {
                return Err(self.err(
                    "partial entries allow only labels (`A$x`), int literals, `none`, `{}`, `+`, `->`",
                ));
            }
        }
        Ok(PartialEntry {
            op,
            left,
            right,
            pos,
        })
    }

    fn sig_decl(&mut self) -> PResult<SigDecl> {
        let pos = self.pos();
        let mut mult = SigMult::None;
        // Consume optional var/abstract/one/lone modifiers (any order, at most once each)
        let mut saw_var = false;
        loop {
            match self.peek() {
                Tok::Var if !saw_var => {
                    self.bump();
                    saw_var = true;
                }
                Tok::Abstract => {
                    mult = SigMult::Abstract;
                    self.bump();
                }
                Tok::One => {
                    mult = SigMult::One;
                    self.bump();
                }
                Tok::Lone => {
                    mult = SigMult::Lone;
                    self.bump();
                }
                Tok::Some => {
                    mult = SigMult::Some;
                    self.bump();
                }
                _ => break,
            }
        }
        self.expect(&Tok::Sig)?;
        let mut names = vec![self.bind_name()?];
        while self.eat(&Tok::Comma) {
            names.push(self.bind_name()?);
        }
        let mut extends = None;
        let mut rel = SigRel::None;
        if self.eat(&Tok::Colon) {
            // rare `sig X : ext Y` form? not supported
            return Err(self.err("sig inheritance via ':' unsupported"));
        }
        if matches!(self.peek(), Tok::Extends) {
            self.bump();
            extends = Some(self.sig_parent()?);
            rel = SigRel::Extends;
        } else if matches!(self.peek(), Tok::In) {
            self.bump();
            extends = Some(self.sig_parent()?);
            rel = SigRel::In;
        }
        let mut fields = Vec::new();
        if self.eat(&Tok::LBrace) {
            if !matches!(self.peek(), Tok::RBrace) {
                loop {
                    let d = self.decl(true)?;
                    fields.push(d);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
            }
            self.expect(&Tok::RBrace)?;
        }
        // Optional sig fact block: `sig A { fields } { formula }`
        let fact = if self.eat(&Tok::LBrace) {
            let mut parts: Vec<Formula> = Vec::new();
            loop {
                if self.eat(&Tok::RBrace) {
                    break;
                }
                if matches!(self.peek(), Tok::Eof) {
                    return Err(self.err("unterminated sig fact block"));
                }
                parts.push(self.formula()?);
            }
            let f = if parts.is_empty() {
                Formula::Const(true)
            } else {
                parts
                    .into_iter()
                    .reduce(|a, b| Formula::And(Box::new(a), Box::new(b)))
                    .unwrap()
            };
            Some(f)
        } else {
            None
        };
        let _ = pos;
        Ok(SigDecl {
            mult,
            names,
            extends,
            rel,
            fields,
            fact,
            is_var: saw_var,
        })
    }

    /// Parent name in a sig header: a plain identifier or the builtin
    /// `Int` (Java accepts `sig X in Int` / `sig X extends Int` at parse
    /// time; `extends Int` is rejected later with a Java-compatible error).
    fn sig_parent(&mut self) -> PResult<String> {
        match self.peek() {
            Tok::IntKw => {
                self.bump();
                Ok("Int".to_string())
            }
            _ => self.ident(),
        }
    }

    fn ident(&mut self) -> PResult<String> {
        let mut n = match self.bump().tok {
            Tok::Ident(n) => n,
            other => {
                return Err(self.err(&format!("expected identifier, got {}", other.describe())))
            }
        };
        // qualified reference through an opened module alias: `ord/first`
        while matches!(self.peek(), Tok::Slash) && matches!(self.peek_at(1), Tok::Ident(_)) {
            self.bump();
            match self.bump().tok {
                Tok::Ident(m) => {
                    n.push('/');
                    n.push_str(&m);
                }
                _ => unreachable!(),
            }
        }
        Ok(n)
    }

    /// Java parity (`Alloy.cup` `nod`): declaration-bound names may not
    /// contain `$`. Atom names (`A$0`) are universe members, not language
    /// bindings; only references (expressions, `:query`) may use them.
    fn nod(&self, name: &str) -> PResult<()> {
        if name.contains('$') {
            return Err(self.err("The name cannot contain the '$' symbol."));
        }
        Ok(())
    }

    /// A binding occurrence of a name: `ident` plus the `$` check.
    fn bind_name(&mut self) -> PResult<String> {
        let n = self.ident()?;
        // Only the head segment is user-declared (`alias/name` qualified
        // references never occur in binding position).
        self.nod(n.split('/').next().unwrap_or(&n))?;
        Ok(n)
    }

    // ------------------------------------------------------------------
    // declarations: names : [mult] type-expr (with arrow multiplicities)
    // ------------------------------------------------------------------

    fn decl(&mut self, in_sig: bool) -> PResult<Decl> {
        let pos = self.pos();
        let mut is_var = false;
        if self.eat(&Tok::Var) {
            is_var = true;
        }
        let mut disj = false;
        loop {
            if self.eat(&Tok::Disj) {
                disj = true;
            } else {
                break;
            }
        }
        let mut names = vec![self.bind_name()?];
        while matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::Ident(_))
            && (matches!(self.peek_at(2), Tok::Colon) || matches!(self.peek_at(2), Tok::Comma))
        {
            self.bump();
            names.push(self.bind_name()?);
        }
        if self.eat(&Tok::Colon) {
            let expr = self.arrow_type()?;
            Ok(Decl {
                disj,
                names,
                expr,
                pos,
                is_var,
            })
        } else if in_sig {
            Err(self.err("field declaration requires ':'"))
        } else {
            Err(self.err("declaration requires ':'"))
        }
    }

    /// Parses a declaration type expression: sequence of `[mult] atom`
    /// joined by `->`. Leading multiplicity allowed.
    /// Alloy also allows trailing multiplicities: `Field lone -> lone Slot`.
    fn arrow_type(&mut self) -> PResult<Expr> {
        let lead_pos = self.pos();
        let lead_mult = self.opt_mult_kw();
        let lead_had_mult = lead_mult.is_some();
        // Segments exclude arrows structurally: force the `in_sig` gate so
        // `A -> lone B` still reaches this function's own loop (with its
        // multiplicity placement), even in `decl(false)` contexts. Union and
        // friends stay available inside segments (`f: A + B`).
        let mut acc = self.parse_plusminus(true)?;
        // Trailing multiplicity overrides leading (e.g. `Field lone` or `lone Field lone`)
        let m = self.opt_mult_kw().or(lead_mult);
        if let Some(m) = m {
            acc = Expr::LeadMult(mult3(&m), Box::new(acc));
        }
        // Java parity: a multiplicity BEFORE the first segment of a
        // multi-segment arrow (`lone A -> B`) is a type error; the
        // marking must follow its segment (`A lone -> B`). (`set` is
        // consumed without marking, so it never triggers this.)
        if lead_had_mult && matches!(self.peek(), Tok::Arrow) {
            return Err(FrontError::Parse {
                pos: lead_pos,
                msg: "multiplicity must follow its type in `A m -> B` (Java parity)".to_string(),
            });
        }
        // Parse subsequent `-> [mult] type [mult]` parts
        while self.eat(&Tok::Arrow) {
            let pre_mult = self.opt_mult_kw();
            let rhs = self.parse_plusminus(true)?;
            let post_mult = self.opt_mult_kw();
            let m = post_mult.or(pre_mult);
            acc = Expr::Bin(BinOp::Product, Box::new(acc), Box::new(rhs));
            if let Some(kw) = m {
                acc = Expr::ArrowMult(mult3(&kw), Box::new(acc));
            }
        }
        Ok(acc)
    }

    fn opt_mult_kw(&mut self) -> Option<Tok> {
        match self.peek() {
            Tok::SetKw => {
                self.bump();
                None
            }
            Tok::Some | Tok::Lone | Tok::One => {
                let t = self.bump().tok;
                Some(t)
            }
            _ => None,
        }
    }

    fn braced_formula(&mut self) -> PResult<Formula> {
        // A brace block holds zero or more formulas, implicitly conjoined.
        self.expect(&Tok::LBrace)?;
        let mut parts: Vec<Formula> = Vec::new();
        loop {
            if self.eat(&Tok::RBrace) {
                break;
            }
            if matches!(self.peek(), Tok::Eof) {
                return Err(self.err("unterminated block"));
            }
            parts.push(self.formula()?);
        }
        Ok(if parts.is_empty() {
            Formula::Const(true)
        } else {
            parts
                .into_iter()
                .reduce(|a, b| Formula::And(Box::new(a), Box::new(b)))
                .unwrap()
        })
    }

    fn para(&mut self, is_fun: bool) -> PResult<Para> {
        self.expect(if is_fun { &Tok::Fun } else { &Tok::Pred })?;
        let name = self.bind_name()?;
        let mut params = Vec::new();
        let open = if self.eat(&Tok::LParen) {
            Some(Tok::RParen)
        } else if self.eat(&Tok::LBracket) {
            Some(Tok::RBracket)
        } else {
            None
        };
        if let Some(close) = open {
            if !matches!(self.peek(), Tok::RParen | Tok::RBracket) {
                loop {
                    params.push(self.decl(false)?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
            }
            self.expect(&close)?;
        }
        let ret = if is_fun {
            self.expect(&Tok::Colon)?;
            let _m = self.opt_mult_kw(); // set/one/lone/some on return type
            Some(self.rel_expr_top(false)?)
        } else {
            None
        };
        if is_fun {
            self.expect(&Tok::LBrace)?;
            let e = self.rel_expr_top(false)?;
            self.expect(&Tok::RBrace)?;
            return Ok(Para {
                name,
                params,
                body: Formula::Const(true),
                body_expr: Some(e),
                is_fun,
                ret,
            });
        }
        let body = self.braced_formula()?;
        Ok(Para {
            name,
            params,
            body,
            body_expr: None,
            is_fun,
            ret,
        })
    }

    fn command(&mut self) -> PResult<Command> {
        let pos = self.pos();
        #[derive(Clone, Copy, PartialEq)]
        enum Head {
            Run,
            Check,
            Maximize,
            Minimize,
        }
        let head = if self.eat(&Tok::Run) {
            Head::Run
        } else if self.eat(&Tok::Check) {
            Head::Check
        } else if self.eat(&Tok::Maximize) {
            Head::Maximize
        } else if self.eat(&Tok::Minimize) {
            Head::Minimize
        } else {
            return Err(self.err(&format!(
                "expected 'run', 'check', 'maximize' or 'minimize', found {}",
                self.peek().describe()
            )));
        };
        let head_word = match head {
            Head::Run => "run",
            Head::Check => "check",
            Head::Maximize => "maximize",
            Head::Minimize => "minimize",
        };
        let mut name: Option<String> = if let Tok::Ident(_) = self.peek() {
            Some(self.ident()?)
        } else {
            None
        };
        // inline braced body: `run { F } for ..`, `maximize { F } : e for ..`
        if matches!(self.peek(), Tok::LBrace) {
            self.inline_body_index += 1;
            let auto = name
                .clone()
                .unwrap_or_else(|| format!("{}${}", head_word, self.inline_body_index));
            let body = self.braced_formula()?;
            self.pending_paras.push(Para {
                name: auto.clone(),
                params: Vec::new(),
                body,
                body_expr: None,
                is_fun: false,
                ret: None,
            });
            name = Some(auto);
        }
        // Optimization target: `weights { r: w, ... }` (either side of the
        // body) or `: <intexpr>`. Run/check commands have neither.
        let mut objective: Option<OptSpec> = None;
        if matches!(head, Head::Maximize | Head::Minimize) && matches!(self.peek(), Tok::Weights) {
            objective = Some(OptSpec::Weights(self.weights_block()?));
        }
        if matches!(head, Head::Maximize | Head::Minimize) && objective.is_none() {
            if self.eat(&Tok::Colon) {
                objective = Some(OptSpec::Int(self.int_expr()?));
            } else if matches!(self.peek(), Tok::Weights) {
                objective = Some(OptSpec::Weights(self.weights_block()?));
            } else {
                return Err(self.err(&format!(
                    "expected ':' <intexpr> or 'weights {{...}}' after '{head_word}' command"
                )));
            }
        }
        // `maximize weights {...} { F }` order: body after the weights block.
        if matches!(head, Head::Maximize | Head::Minimize)
            && name.is_none()
            && matches!(self.peek(), Tok::LBrace)
        {
            self.inline_body_index += 1;
            let auto = format!("{}${}", head_word, self.inline_body_index);
            let body = self.braced_formula()?;
            self.pending_paras.push(Para {
                name: auto.clone(),
                params: Vec::new(),
                body,
                body_expr: None,
                is_fun: false,
                ret: None,
            });
            name = Some(auto);
        }
        let mut scope = Scope::default();
        if self.eat(&Tok::For) {
            self.scope_clause(&mut scope)?;
        }
        if self.eat(&Tok::Expect) {
            // accept and ignore expect clauses (sat/unsat + optional number)
            if matches!(self.peek(), Tok::Ident(_) | Tok::Int(_)) {
                self.bump();
            }
        }
        let kind = match head {
            Head::Run => CommandKind::Run(name),
            Head::Check => CommandKind::Check(name),
            Head::Maximize => CommandKind::Maximize {
                name,
                objective: objective.expect("opt objective parsed"),
            },
            Head::Minimize => CommandKind::Minimize {
                name,
                objective: objective.expect("opt objective parsed"),
            },
        };
        Ok(Command { kind, scope, pos })
    }

    /// `weights { rel: w, ... }` — relation-weight map of a
    /// maximize/minimize command. Weights are (possibly negative) integer
    /// literals.
    fn weights_block(&mut self) -> PResult<Vec<(String, i64)>> {
        self.expect(&Tok::Weights)?;
        self.expect(&Tok::LBrace)?;
        let mut out: Vec<(String, i64)> = Vec::new();
        if matches!(self.peek(), Tok::RBrace) {
            return Err(self.err("empty 'weights {...}' block"));
        }
        loop {
            let rel = self.ident()?;
            self.expect(&Tok::Colon)?;
            let neg = self.eat(&Tok::Minus);
            let w = match self.peek() {
                Tok::Int(v) => {
                    let v = *v;
                    self.bump();
                    v
                }
                _ => {
                    return Err(self.err(&format!(
                        "expected integer weight for '{rel}', found {}",
                        self.peek().describe()
                    )))
                }
            };
            out.push((rel, if neg { -w } else { w }));
            if self.eat(&Tok::Comma) {
                continue;
            }
            break;
        }
        self.expect(&Tok::RBrace)?;
        Ok(out)
    }

    fn scope_clause(&mut self, scope: &mut Scope) -> PResult<()> {
        if self.eat(&Tok::Exactly) {
            // `for exactly Int 8`: bitwidth form (exactness is meaningless
            // for bitwidth, accepted for symmetry with `for exactly 8 Int`).
            if matches!(self.peek(), Tok::IntKw | Tok::IntTy) {
                self.bump();
                let n = self.int_lit()? as u32;
                scope.int_scope = Some(n);
                return Ok(());
            }
            let n = self.int_lit()? as u32;
            if matches!(self.peek(), Tok::Ident(_)) {
                let name = self.ident()?;
                scope.entries.push((name, ScopeEntry::Exactly(n)));
            } else if matches!(self.peek(), Tok::IntKw | Tok::IntTy) {
                // `for exactly 8 Int`: bitwidth form.
                self.bump();
                scope.int_scope = Some(n);
            } else {
                scope.overall = Some(n);
                scope.overall_exact = true;
            }
            return Ok(());
        }
        // `for Int 8`: bitwidth form, mirroring the comma/`but` entry style.
        if matches!(self.peek(), Tok::IntKw | Tok::IntTy) {
            self.bump();
            let n = self.int_lit()? as u32;
            scope.int_scope = Some(n);
            // Fall through to comma-separated entries below.
            return self.scope_rest(scope, 0);
        }
        let first = self.int_lit()? as u32;
        // `for 10 steps` form: temporal step count
        if matches!(self.peek(), Tok::Steps) {
            self.bump();
            scope.steps = Some(first);
        } else if matches!(self.peek(), Tok::IntKw | Tok::IntTy) {
            // `for 8 Int`: bitwidth form. This is a width, not a scope, so
            // `overall` is left untouched.
            self.bump();
            scope.int_scope = Some(first);
        } else if matches!(self.peek(), Tok::Ident(_)) {
            // `for 8 State` form: a bare trailing name scopes that one sig
            let name = self.ident()?;
            scope.entries.push((name, ScopeEntry::Num(first)));
        } else {
            scope.overall = Some(first);
        }
        self.scope_rest(scope, first)
    }

    /// Comma-separated scope entries and the `but` clause shared by the
    /// non-`exactly` bare forms. `first` feeds `, steps` (mirroring the
    /// existing comma-entry behavior).
    fn scope_rest(&mut self, scope: &mut Scope, first: u32) -> PResult<()> {
        // handle comma-separated entries: `for 2 State, 1 Assignment, ...`
        while self.eat(&Tok::Comma) {
            let exact = self.eat(&Tok::Exactly);
            if matches!(self.peek(), Tok::IntKw) {
                self.bump();
                let n = self.int_lit()? as u32;
                scope.int_scope = Some(n);
            } else if matches!(self.peek(), Tok::Steps) {
                self.bump();
                let n = first;
                scope.steps = Some(n);
            } else {
                let n = self.int_lit()? as u32;
                if matches!(self.peek(), Tok::IntKw | Tok::IntTy) {
                    // `, 8 Int`: bitwidth form (a width, not a scope).
                    self.bump();
                    scope.int_scope = Some(n);
                } else if matches!(self.peek(), Tok::Ident(_)) {
                    let name = self.ident()?;
                    scope.entries.push((
                        name,
                        if exact {
                            ScopeEntry::Exactly(n)
                        } else {
                            ScopeEntry::Num(n)
                        },
                    ));
                } else {
                    scope.overall = Some(n);
                    if exact {
                        scope.overall_exact = true;
                    }
                }
            }
        }
        if self.eat(&Tok::But) {
            loop {
                let exact = self.eat(&Tok::Exactly);
                if matches!(self.peek(), Tok::IntKw) {
                    self.bump();
                    let n = self.int_lit()? as u32;
                    scope.int_scope = Some(n);
                } else {
                    let name = self.ident()?;
                    let n = self.int_lit()? as u32;
                    scope.entries.push((
                        name,
                        if exact {
                            ScopeEntry::Exactly(n)
                        } else {
                            ScopeEntry::Num(n)
                        },
                    ));
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        Ok(())
    }

    fn int_lit(&mut self) -> PResult<i64> {
        match self.peek().clone() {
            Tok::Minus => {
                self.bump();
                match self.bump().tok {
                    Tok::Int(v) => Ok(-v),
                    other => Err(self.err(&format!("expected number, got {}", other.describe()))),
                }
            }
            Tok::Int(v) => {
                self.bump();
                Ok(v)
            }
            other => Err(self.err(&format!("expected number, got {}", other.describe()))),
        }
    }

    // ------------------------------------------------------------------
    // expressions
    // ------------------------------------------------------------------

    /// Top-level relational expression (union/difference loosest).
    ///
    /// Alloy6 precedence, loosest first: `+ -`, then `++`, then `&`, then
    /// `->` (and the reverse products `<->`, `-<`), then `<:`,
    /// then unary/`'`/`.`/`[]`. All binary operators are left-associative.
    fn rel_expr_top(&mut self, in_sig: bool) -> PResult<Expr> {
        let e = self.parse_plusminus(in_sig)?;
        Ok(e)
    }

    fn parse_arrow(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_colon_lt(in_sig)?;
        // `<->` and `-<` are non-standard reverse products: a <-> b and
        // a -< b both mean b -> a. They share `->`'s level and left
        // associativity.
        // In sig-field types (`in_sig`, via `arrow_type`) arrows belong to
        // `arrow_type`'s own loop (multiplicity placement like `A lone -> B`),
        // so stop here and let it consume them.
        if in_sig {
            return Ok(l);
        }
        loop {
            if self.eat(&Tok::Arrow) {
                let r = self.parse_colon_lt(in_sig)?;
                l = Expr::Bin(BinOp::Product, Box::new(l), Box::new(r));
            } else if matches!(self.peek(), Tok::ShArrow | Tok::RevArrow) {
                self.bump();
                let r = self.parse_colon_lt(in_sig)?;
                l = Expr::Bin(BinOp::Product, Box::new(r), Box::new(l));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_override(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_amp(in_sig)?;
        loop {
            if self.eat(&Tok::PlusPlus) {
                let r = self.parse_amp(in_sig)?;
                l = Expr::Bin(BinOp::Override, Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_plusminus(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_override(in_sig)?;
        loop {
            match self.peek() {
                Tok::Plus => {
                    self.bump();
                    let r = self.parse_override(in_sig)?;
                    l = Expr::Bin(BinOp::Union, Box::new(l), Box::new(r));
                }
                Tok::Minus => {
                    self.bump();
                    let r = self.parse_override(in_sig)?;
                    l = Expr::Bin(BinOp::Difference, Box::new(l), Box::new(r));
                }
                _ => break,
            }
        }
        Ok(l)
    }

    fn parse_amp(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_arrow(in_sig)?;
        while self.eat(&Tok::Amp) {
            let r = self.parse_arrow(in_sig)?;
            l = Expr::Bin(BinOp::Intersect, Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn parse_colon_lt(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_unary(in_sig)?;
        loop {
            if self.eat(&Tok::ColonLt) {
                let r = self.parse_unary(in_sig)?;
                l = Expr::Bin(BinOp::DomainRestrict, Box::new(l), Box::new(r));
            } else if self.eat(&Tok::ColonGt) {
                let r = self.parse_unary(in_sig)?;
                l = Expr::Bin(BinOp::RangeRestrict, Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_unary(&mut self, in_sig: bool) -> PResult<Expr> {
        match self.peek() {
            Tok::Tilde => {
                self.bump();
                let at = self.eat(&Tok::At);
                let inner = self.parse_unary(in_sig)?;
                let inner = if at {
                    Expr::AtExpr(Box::new(inner))
                } else {
                    inner
                };
                Ok(Expr::Transpose(Box::new(inner)))
            }
            Tok::Hat => {
                self.bump();
                let at = self.eat(&Tok::At);
                let inner = self.parse_unary(in_sig)?;
                let inner = if at {
                    Expr::AtExpr(Box::new(inner))
                } else {
                    inner
                };
                Ok(Expr::TClosure(Box::new(inner)))
            }
            Tok::Star => {
                self.bump();
                let at = self.eat(&Tok::At);
                let inner = self.parse_unary(in_sig)?;
                let inner = if at {
                    Expr::AtExpr(Box::new(inner))
                } else {
                    inner
                };
                Ok(Expr::RClosure(Box::new(inner)))
            }
            Tok::After => {
                self.bump();
                Ok(Expr::Prime(Box::new(self.parse_unary(in_sig)?)))
            }
            _ => self.parse_join(in_sig),
        }
    }

    fn parse_join(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_primary(in_sig)?;
        loop {
            match self.peek() {
                Tok::Dot => {
                    self.bump();
                    let at = self.eat(&Tok::At);
                    // right side may carry prefix closures: n.^next
                    let r = self.parse_unary(in_sig)?;
                    let r = if at { Expr::AtExpr(Box::new(r)) } else { r };
                    l = Expr::Bin(BinOp::Join, Box::new(l), Box::new(r));
                }
                Tok::LBracket => {
                    self.bump();
                    let mut args = Vec::new();
                    loop {
                        args.push(Box::new(self.rel_expr_top(in_sig)?));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(&Tok::RBracket)?;
                    l = Expr::Bracket(Box::new(l), args);
                }
                _ => break,
            }
        }
        Ok(l)
    }

    /// One `{...}` set-literal element: pure literal arithmetic folds to
    /// its value (`{1+1}` is `{2}`, not the `{1}` union), anything else
    /// parses as a relational expression.
    fn set_literal_element(&mut self, in_sig: bool) -> PResult<Expr> {
        let save = self.pos;
        let byte = self.pos();
        if let Ok(ie) = self.int_expr() {
            if matches!(self.peek(), Tok::Comma | Tok::RBrace) {
                if let Some(v) = fold_int_literal(&ie) {
                    return Ok(Expr::Name(v.to_string(), byte));
                }
            }
            self.pos = save;
        }
        self.rel_expr_top(in_sig)
    }

    /// `{x: D | F}` / `{x: D}` comprehension, or `{a, b, ...}` set
    /// literal (extension: Java rejects the latter). Declarations win
    /// when parseable (`{x: X, y: Y}` binds two names); otherwise rewind
    /// and read a union list. `{}` is the empty set literal (needed so
    /// the REPL's `{...}` display/save format round-trips); `none` stays
    /// accepted as before. Called with `{` as the pending token.
    fn braced_set(&mut self, in_sig: bool) -> PResult<Expr> {
        self.bump();
        if self.eat(&Tok::RBrace) {
            return Ok(Expr::None_);
        }
        let after_brace = self.pos;
        match self.quant_decls() {
            Ok(ds) => {
                let f = if self.eat(&Tok::Bar) {
                    self.formula()?
                } else {
                    Formula::Const(true)
                };
                self.expect(&Tok::RBrace)?;
                Ok(Expr::Comprehension(ds, Box::new(f)))
            }
            Err(_) => {
                self.pos = after_brace;
                let mut e = self.set_literal_element(in_sig)?;
                while self.eat(&Tok::Comma) {
                    let r = self.set_literal_element(in_sig)?;
                    e = Expr::Bin(BinOp::Union, Box::new(e), Box::new(r));
                }
                self.expect(&Tok::RBrace)?;
                Ok(e)
            }
        }
    }

    fn parse_primary(&mut self, in_sig: bool) -> PResult<Expr> {
        let pos = self.pos();
        // let binding in expression context: `let x = expr | expr`
        // (Java parity: `|` separator like the formula level; `in` is rejected).
        if matches!(self.peek(), Tok::Let) {
            self.bump();
            let mut binds = Vec::new();
            loop {
                let name = self.bind_name()?;
                self.expect(&Tok::Eq)?;
                let e = self.rel_expr_top(in_sig)?;
                binds.push((name, e));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.eat(&Tok::Bar);
            let body = self.rel_expr_top(in_sig)?;
            return Ok(Expr::LetBind(binds, Box::new(body)));
        }
        match self.peek().clone() {
            Tok::Univ => {
                self.bump();
                Ok(Expr::Univ)
            }
            Tok::None_ => {
                self.bump();
                Ok(Expr::None_)
            }
            Tok::Iden => {
                self.bump();
                Ok(Expr::Iden)
            }
            Tok::Steps => {
                // Builtin `Step` (any case, singular/plural).
                self.bump();
                Ok(Expr::StepAtom)
            }
            Tok::IntTy | Tok::IntKw => {
                self.bump();
                // Bit-vector model: `Int[w]` per-occurrence widths are gone.
                // A bracket after `Int` falls through to the join/bracket
                // path below, where `Int[8]` (i.e. `8.Int`, arity 1 joined
                // with arity 1) fails as an arity error.
                Ok(Expr::IntAtom)
            }
            Tok::Int(v) => {
                // Integer literal in set position: a singleton int-atom set
                // (Java: literals are singleton sets of int atoms, so
                // `x = 5` typechecks relationally).
                self.bump();
                Ok(Expr::Name(v.to_string(), pos))
            }
            Tok::Minus if matches!(self.peek_at(1), Tok::Int(_)) => {
                // Negative literal in set position (`-5` = `{-5}`).
                self.bump();
                match self.bump().tok {
                    Tok::Int(v) => Ok(Expr::Name(v.wrapping_neg().to_string(), pos)),
                    _ => unreachable!(),
                }
            }
            Tok::LBrace => self.braced_set(in_sig),
            Tok::If => {
                self.bump();
                let c = self.formula()?;
                self.expect(&Tok::Then)?;
                let t = self.rel_expr_top(in_sig)?;
                self.expect(&Tok::Else)?;
                let e = self.rel_expr_top(in_sig)?;
                Ok(Expr::If(Box::new(c), Box::new(t), Box::new(e)))
            }
            Tok::LParen => {
                self.bump();
                let e = self.rel_expr_top(in_sig)?;
                self.expect(&Tok::RParen)?;
                Ok(e)
            }
            Tok::Ident(_) => {
                let n = self.ident()?;
                // Handle prime (next-state) operator: strip trailing `'` and wrap in Prime
                if let Some(base) = n.strip_suffix('\'') {
                    if !base.is_empty() {
                        let inner = Expr::Name(base.to_string(), pos);
                        // call with prime: name'[args]
                        if matches!(self.peek(), Tok::LBracket) {
                            self.bump();
                            let mut args = Vec::new();
                            if !matches!(self.peek(), Tok::RBracket) {
                                loop {
                                    args.push(self.rel_expr_top(false)?);
                                    if !self.eat(&Tok::Comma) {
                                        break;
                                    }
                                }
                            }
                            self.expect(&Tok::RBracket)?;
                            return Ok(Expr::Prime(Box::new(Expr::Call(
                                base.to_string(),
                                args,
                                pos,
                            ))));
                        }
                        return Ok(Expr::Prime(Box::new(inner)));
                    }
                }
                // call: name[args] (pred/fun application)
                if matches!(self.peek(), Tok::LBracket) {
                    self.bump();
                    let mut args = Vec::new();
                    if !matches!(self.peek(), Tok::RBracket) {
                        loop {
                            args.push(self.rel_expr_top(false)?);
                            if !self.eat(&Tok::Comma) {
                                break;
                            }
                        }
                    }
                    self.expect(&Tok::RBracket)?;
                    return Ok(Expr::Call(n, args, pos));
                }
                Ok(Expr::Name(n, pos))
            }
            Tok::This => {
                self.bump();
                Ok(Expr::Name("this".into(), pos))
            }
            other => Err(self.err(&format!("expected expression, got {}", other.describe()))),
        }
    }

    // ------------------------------------------------------------------
    // formulas
    // ------------------------------------------------------------------

    /// Top-level formula.
    ///
    /// Alloy6 precedence, loosest first: binary temporal connectives, then
    /// `||`/`or`, then `<=>`/`iff`, then `=>`/`implies`, then `&&`/`and`,
    /// then unary/`!`/`not`/multiplicities/comparisons. All binary operators
    /// are left-associative, except `=>` (right) and the binary temporal
    /// connectives (non-associative: chaining them is a parse error).
    ///
    /// Two deliberate deviations from Alloy6 proper: binary temporal
    /// connectives sit at the very bottom (weakest) instead of above `&&`
    /// (`a until b || c` reads as `a until (b || c)`), and the `;` sequence
    /// operator is not supported (still a parse error).
    fn formula(&mut self) -> PResult<Formula> {
        self.parse_temporal_bin()
    }

    fn parse_iff(&mut self) -> PResult<Formula> {
        let mut l = self.parse_implies()?;
        loop {
            if self.eat(&Tok::Iff) || self.eat(&Tok::IffKw) {
                let r = self.parse_implies()?;
                l = Formula::Iff(Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_implies(&mut self) -> PResult<Formula> {
        let l = self.parse_and()?;
        if self.eat(&Tok::Implies) || self.eat(&Tok::ImpliesKw) {
            let r = self.parse_implies()?;
            // legacy `A => B else C` form
            if self.eat(&Tok::Else) {
                let c = self.parse_implies()?;
                let ab = Formula::And(Box::new(l.clone()), Box::new(r));
                let nc = Formula::And(Box::new(Formula::Not(Box::new(l))), Box::new(c));
                return Ok(Formula::Or(Box::new(ab), Box::new(nc)));
            }
            return Ok(Formula::Implies(Box::new(l), Box::new(r)));
        }
        Ok(l)
    }

    fn parse_temporal_bin(&mut self) -> PResult<Formula> {
        let l = self.parse_or()?;
        let mk = if self.eat(&Tok::Until) {
            Formula::Until as fn(Box<Formula>, Box<Formula>) -> Formula
        } else if self.eat(&Tok::Releases) {
            Formula::Releases as fn(Box<Formula>, Box<Formula>) -> Formula
        } else if self.eat(&Tok::Since) {
            Formula::Since as fn(Box<Formula>, Box<Formula>) -> Formula
        } else if self.eat(&Tok::Triggered) {
            Formula::Triggered as fn(Box<Formula>, Box<Formula>) -> Formula
        } else {
            return Ok(l);
        };
        let r = self.parse_or()?;
        // Binary temporal connectives are non-associative (Alloy6): chaining
        // them without parentheses is rejected rather than guessed.
        if matches!(
            self.peek(),
            Tok::Until | Tok::Releases | Tok::Since | Tok::Triggered
        ) {
            return Err(
                self.err("temporal connectives are non-associative; parenthesize the nesting")
            );
        }
        Ok(mk(Box::new(l), Box::new(r)))
    }

    fn parse_or(&mut self) -> PResult<Formula> {
        let mut l = self.parse_iff()?;
        while matches!(self.peek(), Tok::OrOp | Tok::OrKw) {
            self.bump();
            let r = self.parse_iff()?;
            l = Formula::Or(Box::new(l), Box::new(r));
        }
        // Alloy also accepts single '|' for or in some grammars; keep '||' only.
        Ok(l)
    }

    fn parse_and(&mut self) -> PResult<Formula> {
        let mut l = self.parse_not_level()?;
        while matches!(self.peek(), Tok::AndOp | Tok::AndKw) {
            self.bump();
            let r = self.parse_not_level()?;
            l = Formula::And(Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn parse_not_level(&mut self) -> PResult<Formula> {
        // `pin P` / `avoid P`: partial-instance embedding (AST-level).
        // Every formula position funnels through here. Two adjacent
        // identifiers are never valid Alloy, so `pin|avoid` followed by a
        // bare name is unambiguous (`pin[x]`, `pin in A`, a `sig pin`,
        // etc. keep their existing readings).
        if let Tok::Ident(kw) = self.peek() {
            if (kw == "pin" || kw == "avoid") && matches!(self.peek_at(1), Tok::Ident(_)) {
                let pos = self.pos();
                let neg = kw == "avoid";
                self.bump();
                let name = match self.bump().tok {
                    Tok::Ident(n) => n,
                    _ => unreachable!(),
                };
                let pin = Formula::Pin(name, pos);
                return Ok(if neg {
                    Formula::Not(Box::new(pin))
                } else {
                    pin
                });
            }
        }
        // parenthesized formula: try, rewind on failure so set-comparison
        // paths like `(a + b) = c` still work.
        if matches!(self.peek(), Tok::LParen) {
            let save = self.pos;
            self.bump();
            match self.formula() {
                Ok(f) if self.eat(&Tok::RParen) => return Ok(f),
                _ => self.pos = save,
            }
        }
        if matches!(self.peek(), Tok::Let) {
            self.bump();
            let mut binds = Vec::new();
            loop {
                let n = self.bind_name()?;
                self.expect(&Tok::Eq)?;
                let e = self.rel_expr_top(false)?;
                binds.push((n, e));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.eat(&Tok::Bar);
            let body = if matches!(self.peek(), Tok::LBrace) {
                self.braced_formula()?
            } else {
                self.formula()?
            };
            return Ok(Formula::LetBind(binds, Box::new(body)));
        }
        match self.peek() {
            Tok::Not | Tok::No if self.starts_negation() => {
                // `not` negates a formula; `no` can also quantify — handled below
                if matches!(self.peek(), Tok::Not) {
                    self.bump();
                    return Ok(Formula::Not(Box::new(self.parse_not_level()?)));
                }
                self.parse_quant_or_cmp()
            }
            Tok::Always => {
                self.bump();
                Ok(Formula::Always(Box::new(self.parse_not_level()?)))
            }
            Tok::Eventually => {
                self.bump();
                Ok(Formula::Eventually(Box::new(self.parse_not_level()?)))
            }
            Tok::Before => {
                self.bump();
                Ok(Formula::Before(Box::new(self.parse_not_level()?)))
            }
            Tok::Historically => {
                self.bump();
                Ok(Formula::Historically(Box::new(self.parse_not_level()?)))
            }
            Tok::Once => {
                self.bump();
                Ok(Formula::Once(Box::new(self.parse_not_level()?)))
            }
            Tok::Keeping => {
                self.bump();
                Ok(Formula::Keeping(Box::new(self.parse_not_level()?)))
            }
            Tok::Goal => {
                self.bump();
                Ok(Formula::Goal(Box::new(self.parse_not_level()?)))
            }
            Tok::Restore => {
                self.bump();
                Ok(Formula::Restore(Box::new(self.parse_not_level()?)))
            }
            Tok::Initially => {
                self.bump();
                Ok(Formula::Initially(Box::new(self.parse_not_level()?)))
            }
            Tok::Regularly => {
                self.bump();
                Ok(Formula::Regularly(Box::new(self.parse_not_level()?)))
            }
            Tok::Consistently => {
                self.bump();
                Ok(Formula::Consistently(Box::new(self.parse_not_level()?)))
            }
            Tok::All | Tok::Some | Tok::No | Tok::Lone | Tok::One => self.parse_quant_or_cmp(),
            Tok::MaxSome | Tok::MinSome => self.parse_maxsome(),
            Tok::Maximize | Tok::Minimize => self.parse_opt_marker(),
            Tok::Sum => {
                // sum formula? not a formula starter; error out naturally
                self.parse_quant_or_cmp()
            }
            Tok::LBrace => {
                // A `{` in formula position usually opens a brace block,
                // but it can also open a comprehension expression
                // (`{x: X} = X`, `some {x: A}` via quantifiers): try the
                // comparison route first, rewind to a block on failure.
                let save = self.pos;
                match self.parse_comparison() {
                    Ok(f) => Ok(f),
                    Err(_) => {
                        self.pos = save;
                        self.braced_formula()
                    }
                }
            }
            _ => self.parse_comparison(),
        }
    }

    fn starts_negation(&self) -> bool {
        matches!(self.peek(), Tok::Not)
    }

    /// In-formula optimization marker: `maximize <intexpr>` /
    /// `minimize <intexpr>` (an optional `:` mirrors the command form).
    /// Always-true formula; the target is collected at lowering and
    /// becomes the enclosing command's objective.
    fn parse_opt_marker(&mut self) -> PResult<Formula> {
        let is_max = matches!(self.peek(), Tok::Maximize);
        let kw = if is_max { "maximize" } else { "minimize" };
        self.bump();
        if matches!(self.peek(), Tok::Weights) {
            return Err(self.err(&format!(
                "'{kw} weights {{...}}' is a command form; in formula position \
                 write '{kw} <intexpr>' (e.g. '{kw} #A')"
            )));
        }
        self.eat(&Tok::Colon);
        let ie = self.int_expr()?;
        Ok(if is_max {
            Formula::Maximize(ie)
        } else {
            Formula::Minimize(ie)
        })
    }

    /// AlloyMax `maxsome e` / `minsome e`: soft set optimization.
    /// Declaration form (`maxsome x: T | F`) and priorities
    /// (`maxsome[n]`) are rejected with explicit errors.
    fn parse_maxsome(&mut self) -> PResult<Formula> {
        let is_max = matches!(self.peek(), Tok::MaxSome);
        let kw = if is_max { "maxsome" } else { "minsome" };
        self.bump();
        if matches!(self.peek(), Tok::LBracket) {
            return Err(self.err(&format!(
                "'{kw}[n]' priorities are not supported (all softs share weight 1)"
            )));
        }
        if matches!(self.peek(), Tok::Ident(_)) && matches!(self.peek_at(1), Tok::Colon) {
            // Declaration form: parse (sibling commands keep working),
            // reject at lowering with a clear error. Domains tolerate a
            // leading multiplicity keyword (AlloyMax `set Course`).
            let mut decls = Vec::new();
            loop {
                let name = self.ident()?;
                self.expect(&Tok::Colon)?;
                // Skip a leading multiplicity keyword on the domain.
                if matches!(self.peek(), Tok::SetKw | Tok::Some | Tok::Lone | Tok::One) {
                    self.bump();
                }
                let expr = self.rel_expr_top(false)?;
                let pos = self.pos();
                decls.push(Decl {
                    disj: false,
                    names: vec![name],
                    expr,
                    pos,
                    is_var: false,
                });
                if self.eat(&Tok::Comma) {
                    continue;
                }
                break;
            }
            let body = if matches!(self.peek(), Tok::Bar) {
                self.bump();
                self.formula()?
            } else if matches!(self.peek(), Tok::LBrace) {
                self.braced_formula()?
            } else {
                return Err(self.err("expected '|' or '{' after maxsome declarations"));
            };
            return Ok(Formula::MaxSomeDecl(decls, Box::new(body)));
        }
        let e = self.rel_expr_top(false)?;
        Ok(if is_max {
            Formula::MaxSome(Box::new(e))
        } else {
            Formula::MinSome(Box::new(e))
        })
    }

    fn parse_quant_or_cmp(&mut self) -> PResult<Formula> {
        let pos = self.pos();
        match self.peek() {
            Tok::All | Tok::Some | Tok::No | Tok::Lone | Tok::One => {
                let qk = match self.peek() {
                    Tok::All => QuantKind::All,
                    Tok::Some => QuantKind::Some,
                    Tok::No => QuantKind::No,
                    Tok::Lone => QuantKind::Lone,
                    _ => QuantKind::One,
                };
                self.bump();
                // `some Overflow { F }` / `no Overflow { F }` (also `| F`):
                // search-mode markers. `Overflow` is reserved here; a sig
                // actually named `Overflow` cannot use multiplicity syntax.
                if matches!(qk, QuantKind::Some | QuantKind::No)
                    && matches!(self.peek(), Tok::Ident(n) if n == "Overflow")
                {
                    self.bump(); // consume `Overflow`
                    let body = if matches!(self.peek(), Tok::Bar) {
                        self.bump(); // consume |
                        self.formula()?
                    } else if matches!(self.peek(), Tok::LBrace) {
                        self.braced_formula()?
                    } else {
                        return Err(
                            self.err("expected '|' or '{' after `some/no Overflow`")
                        );
                    };
                    let mode = if qk == QuantKind::Some {
                        crate::ast::OverflowMode::Some
                    } else {
                        crate::ast::OverflowMode::No
                    };
                    return Ok(Formula::OverflowCond(mode, Box::new(body)));
                }
                // multiplicity formula like `some b.f` has no decl colon;
                // a decl starts with name ':' or a name group 'x, y:'
                let is_decl = match self.peek() {
                    Tok::Disj => true,
                    _ => {
                        // name ':'  |  name ',' name (:|,)...
                        matches!(self.peek(), Tok::Ident(_))
                            && (matches!(self.peek_at(1), Tok::Colon)
                                || (matches!(self.peek_at(1), Tok::Comma)
                                    && matches!(self.peek_at(2), Tok::Ident(_))
                                    && (matches!(self.peek_at(3), Tok::Colon)
                                        || matches!(self.peek_at(3), Tok::Comma))))
                    }
                };
                if !is_decl {
                    let e = self.rel_expr_top(false)?;
                    return Ok(Formula::Multi(qk, e, pos));
                }
                let ds = self.quant_decls()?;
                // both `all x: D | F` and `all x: D { F }` forms
                let body = if matches!(self.peek(), Tok::Bar) {
                    self.bump(); // consume |
                    self.formula()?
                } else if matches!(self.peek(), Tok::LBrace) {
                    self.braced_formula()?
                } else {
                    return Err(self.err("expected '|' or '{' after quantifier declarations"));
                };
                if qk == QuantKind::No {
                    let some = Formula::Quant(QuantKind::Some, ds, Box::new(body));
                    return Ok(Formula::Not(Box::new(some)));
                }
                Ok(Formula::Quant(qk, ds, Box::new(body)))
            }
            _ => {
                let _ = pos;
                self.parse_comparison()
            }
        }
    }

    fn quant_decls(&mut self) -> PResult<Vec<Decl>> {
        let mut out = Vec::new();
        loop {
            let d = self.decl_names_then_domain()?;
            out.push(d);
            if matches!(self.peek(), Tok::Comma) {
                self.bump();
                continue;
            }
            break;
        }
        Ok(out)
    }

    /// names [: domain] — domain optional only in `all x` (unsupported);
    /// here domain is required.
    fn decl_names_then_domain(&mut self) -> PResult<Decl> {
        let pos = self.pos();
        let mut disj = false;
        while self.eat(&Tok::Disj) {
            disj = true;
        }
        let mut names = vec![self.bind_name()?];
        // continue the SAME group only when a comma joins two bare names
        // (`x, y: S`); a group boundary looks like `x: S, y: T` where the
        // colon arrives before any comma.
        while matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::Ident(_))
            && (matches!(self.peek_at(2), Tok::Colon) || matches!(self.peek_at(2), Tok::Comma))
        {
            self.bump(); // comma
                         // If the token after the name we're about to read is Colon,
                         // it means the group ends with this name: `x, y: S`
                         // But if peek_at(1) (after the comma) is a name followed by Colon
                         // and we've already consumed a Colon for a prior name, stop.
            names.push(self.bind_name()?);
            // If next is Colon, the group is complete — don't add more
            if matches!(self.peek(), Tok::Colon) {
                break;
            }
        }
        self.expect(&Tok::Colon)?;
        let expr = self.quant_domain()?;
        Ok(Decl {
            disj,
            names,
            expr,
            pos,
            is_var: false,
        })
    }

    /// Binding domain (`x: D` in quantifiers, comprehensions, `sum`):
    /// pure literal arithmetic folds (`x: 1+2` binds `{3}`), anything
    /// else parses relationally (`x: A + B` stays a union).
    fn quant_domain(&mut self) -> PResult<Expr> {
        let save = self.pos;
        let byte = self.pos();
        if let Ok(ie) = self.int_expr() {
            if matches!(
                self.peek(),
                Tok::Comma | Tok::Bar | Tok::RBrace | Tok::LBrace
            ) {
                if let Some(v) = fold_int_literal(&ie) {
                    return Ok(Expr::Name(v.to_string(), byte));
                }
            }
            self.pos = save;
        }
        self.rel_expr_top(false)
    }

    fn parse_comparison(&mut self) -> PResult<Formula> {
        // Int vs set comparisons are disambiguated by shape; for ambiguous
        // leading '(' try int first, then rewind to set parsing.
        // `=`/`!=` stay relational (Java: no int casts since [AM]); an int
        // attempt that used a set-typed operand (`Val`) is rewound so e.g.
        // `x = 5` parses as set equality against the `{5}` singleton.
        // `<`/`>`/`<=`/`>=` are never set operators (Java casts both sides
        // via `typecheck_as_int`), so they always take the int route.
        if self.starts_int_expr() || matches!(self.peek(), Tok::LParen) {
            let save = self.pos;
            match self.int_cmp_tail() {
                // Rewind when the right side is NOT a genuine int (it has a
                // set reading) and the left is not a bare integer either
                // (`{x: X} = X`, `(A + B) = S`), or when both sides are
                // brace-pure set shapes (`{0}+{1} = {0,1}`, `{A} = {B}`):
                // the relational reading wins. A bare-int left
                // (`5 = X`, `sum X = Y`, `MSB = 3`) commits bitmask
                // semantics.
                Ok(Formula::IntCmp(IntCmpOp::Eq | IntCmpOp::Neq, ref l, ref r, _))
                    if should_rewind_eq(l, r) =>
                {
                    self.pos = save;
                }
                Ok(f) => return Ok(f),
                Err(_) => self.pos = save,
            }
        }
        let start = self.pos;
        let pos = self.pos();
        // Int-typed LHS in `=`/`!=` (Java `toSet`: the int side becomes
        // the singleton set). `sum X = Y` desugars to `#Y = 1 and
        // sum(Y) = sum(X)`. Full int comparisons (`#A = 4`) commit above
        // and never reach here; literals keep the singleton path below.
        // Parenthesized int heads (`(sum Y) = X`) are covered as well;
        // anything else rewinds untouched.
        if matches!(self.peek(), Tok::Hash | Tok::Sum | Tok::LParen) {
            let save = self.pos;
            if let Ok(ie) = self.int_expr() {
                if crate::types::is_int_query(&ie)
                    && !matches!(ie, IntExpr::Lit(..))
                    && matches!(self.peek(), Tok::Eq | Tok::NotEq)
                {
                    let neg = matches!(self.peek(), Tok::NotEq);
                    self.bump();
                    if let Ok(r) = self.rel_expr_top(false) {
                        return Ok(set_eq_int(r, ie, pos, neg));
                    }
                }
            }
            self.pos = save;
        }
        // dotted call chain in formula position: a.b.P[x, y] == P[a, b, x, y]
        // (also plain P[x]); resolution decides pred vs field later.
        if matches!(self.peek(), Tok::Ident(_)) {
            let save = self.pos;
            let pos = self.pos();
            let mut segs: Vec<String> = vec![self.ident()?];
            let mut is_call = false;
            loop {
                if matches!(self.peek(), Tok::Dot)
                    && matches!(self.peek_at(1), Tok::Ident(_))
                    && matches!(self.peek_at(2), Tok::LBracket)
                {
                    self.bump();
                    segs.push(self.ident()?);
                    continue;
                }
                if matches!(self.peek(), Tok::LBracket) && !segs.is_empty() {
                    is_call = true;
                }
                break;
            }
            if is_call {
                self.bump(); // [
                let mut args: Vec<Expr> = Vec::new();
                for s in &segs[..segs.len() - 1] {
                    args.push(Expr::Name(s.clone(), pos));
                }
                if !matches!(self.peek(), Tok::RBracket) {
                    loop {
                        args.push(self.rel_expr_top(false)?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                self.expect(&Tok::RBracket)?;
                return Ok(Formula::Call(segs.last().unwrap().clone(), args, pos));
            }
            self.pos = save;
        }
        let l = self.rel_expr_top(false)?;
        // `<`/`>`/`<=`/`>=` can never continue a set comparison: rewind and
        // take the integer route (operands lower via the SUM cast).
        if matches!(self.peek(), Tok::Lt | Tok::Gt | Tok::LtEq | Tok::GtEq) {
            self.pos = start;
            return self.int_cmp_tail();
        }
        if let Expr::Name(n, ppos) = &l {
            // bare identifier in formula position: zero-arg predicate call,
            // valid when a formula operator follows (=> <=> || and or,
            // temporal connectives, } ) ...) as well as at `)`/EOF.
            if matches!(
                self.peek(),
                Tok::Implies
                    | Tok::ImpliesKw
                    | Tok::Iff
                    | Tok::IffKw
                    | Tok::OrOp
                    | Tok::OrKw
                    | Tok::AndOp
                    | Tok::AndKw
                    | Tok::Until
                    | Tok::Releases
                    | Tok::Since
                    | Tok::Triggered
                    | Tok::RBrace
                    | Tok::RParen
                    | Tok::Eof
            ) {
                return Ok(Formula::Call(n.clone(), Vec::new(), *ppos));
            }
        }
        let kind = match self.peek() {
            Tok::Eq => CmpKind::Eq,
            Tok::NotEq => CmpKind::Neq,
            Tok::In => CmpKind::In,
            Tok::Not => {
                self.bump();
                self.expect(&Tok::In)?;
                CmpKind::NotIn
            }
            other => {
                // `*`/`/`/`%` have no relational reading (only prefix `*`
                // for closure). A bare-`Ident` LHS (e.g. `A in Signed`)
                // commits to the set path above, leaving `A * A = 9`
                // stranded here. Rewind and retry as integer arithmetic,
                // like `+` is already usable in both positions.
                // `A+B=5` keeps its legacy `BitsVal(union)` path; this
                // fallback only triggers when the relational continuation
                // is impossible.
                let desc = other.describe();
                let is_arith = matches!(other, Tok::Star | Tok::Slash | Tok::Percent);
                if is_arith {
                    self.pos = start;
                    if let Ok(f) = self.int_cmp_tail() {
                        return Ok(f);
                    }
                    // Also surface `A*A in B` as the standard int-left-of-
                    // `in` type error instead of a bare parse error.
                    self.pos = start;
                    if let Ok(ie) = self.int_expr() {
                        // `*`/`/`/`%` have no set reading, so `A*A in B`
                        // is definitely integer-typed even though `Val`
                        // leaves `int_typed()` false (same reason the
                        // `int_cmp_tail` retry above succeeds for `=`).
                        if matches!(self.peek(), Tok::In)
                            && (int_left_of_in_is_error(&ie)
                                || int_expr_has_mul_div_rem(&ie))
                        {
                            return Err(self.err(
                                "type mismatch: integer expression cannot appear left of `in` (both sides must be sets, e.g. `{0, 2} in X`)",
                            ));
                        }
                    }
                }
                return Err(self.err(&format!("expected comparison, got {desc}")))
            }
        };
        // Bit-vector model: an integer expression left of `in` is a type
        // error (`in` requires set operands on both sides). Probe the
        // LHS from the comparison start: a genuine int tree (not a
        // brace-pure set shape, e.g. `{1}+{2}`) commits the error;
        // `{1}+{2} in X` and `x in X` stay relational.
        if matches!(kind, CmpKind::In | CmpKind::NotIn) {
            let at_op = self.pos;
            self.pos = start;
            if let Ok(ie) = self.int_expr() {
                if int_left_of_in_is_error(&ie) {
                    self.pos = start;
                    return Err(self.err(
                        "type mismatch: integer expression cannot appear left of `in` (both sides must be sets, e.g. `{0, 2} in X`)",
                    ));
                }
            }
            self.pos = at_op;
        }
        // `set = int-expr` (bit-vector model: the set side reads as its
        // bitmask value, so `X = 5` holds iff X = {0, 2}).
        // `#`/`sum`/`(`/literals never start a set expression, so
        // attempting int-first here cannot regress: on failure or brace
        // rewind the original relational path surfaces unchanged.
        // A bare-`Ident` RHS gets the same probe so `X = A - 0` and
        // `X = 0 - A` agree: a lone `Val` (`X = A`) rewinds (mixed_int
        // is false), while a mixed tree (`0 - A`, `2 * A`) commits to
        // integer semantics with the set operand read as its bitmask
        // value (the lowerer's flavor gate rejects non-Int sets).
        if matches!(kind, CmpKind::Eq | CmpKind::Neq)
            && matches!(
                self.peek_at(1),
                Tok::Hash
                    | Tok::Sum
                    | Tok::LParen
                    | Tok::Int(_)
                    | Tok::Minus
                    | Tok::Ident(_)
            )
        {
            let save = self.pos;
            self.bump(); // consume `=` / `!=`
            if let Ok(ie) = self.int_expr() {
                if ie.mixed_int() && !ie.brace_pure() {
                    let neg = matches!(kind, CmpKind::Neq);
                    return Ok(set_eq_int(l, ie, pos, neg));
                }
            }
            self.pos = save;
        }
        self.bump();
        let r = self.rel_expr_top(false)?;
        Ok(Formula::Cmp(kind, l, r, pos))
    }

    fn int_cmp_tail(&mut self) -> PResult<Formula> {
        let l = self.int_expr()?;
        let op = match self.peek() {
            Tok::Eq => IntCmpOp::Eq,
            Tok::NotEq => IntCmpOp::Neq,
            Tok::Lt => IntCmpOp::Lt,
            Tok::Gt => IntCmpOp::Gt,
            Tok::LtEq => IntCmpOp::Lte,
            Tok::GtEq => IntCmpOp::Gte,
            other => {
                return Err(self.err(&format!(
                    "expected int comparison operator, got {}",
                    other.describe()
                )))
            }
        };
        self.bump();
        let r = self.int_expr()?;
        Ok(Formula::IntCmp(op, l, r, 0))
    }

    fn starts_int_expr(&self) -> bool {
        match self.peek() {
            Tok::Hash | Tok::Sum | Tok::Int(_) | Tok::Minus | Tok::LBrace => true,
            // MSB reads as a scalar (its bitmask value) in int positions.
            Tok::Ident(n) => n == "MSB",
            _ => false,
        }
    }

    fn int_expr(&mut self) -> PResult<IntExpr> {
        self.int_additive()
    }

    fn int_additive(&mut self) -> PResult<IntExpr> {
        let mut l = self.int_mul()?;
        loop {
            match self.peek() {
                Tok::Plus => {
                    self.bump();
                    let r = self.int_mul()?;
                    l = IntExpr::Bin(IntBinOp::Add, Box::new(l), Box::new(r));
                }
                Tok::Minus => {
                    self.bump();
                    let r = self.int_mul()?;
                    l = IntExpr::Bin(IntBinOp::Sub, Box::new(l), Box::new(r));
                }
                _ => break,
            }
        }
        Ok(l)
    }

    fn int_mul(&mut self) -> PResult<IntExpr> {
        let mut l = self.int_primary()?;
        loop {
            match self.peek() {
                Tok::Star => {
                    self.bump();
                    let r = self.int_primary()?;
                    l = IntExpr::Bin(IntBinOp::Mul, Box::new(l), Box::new(r));
                }
                Tok::Slash => {
                    self.bump();
                    let r = self.int_primary()?;
                    l = IntExpr::Bin(IntBinOp::Div, Box::new(l), Box::new(r));
                }
                Tok::Percent => {
                    self.bump();
                    let r = self.int_primary()?;
                    l = IntExpr::Bin(IntBinOp::Rem, Box::new(l), Box::new(r));
                }
                _ => break,
            }
        }
        Ok(l)
    }

    fn int_primary(&mut self) -> PResult<IntExpr> {
        let pos = self.pos();
        match self.peek().clone() {
            Tok::Int(v) => {
                self.bump();
                Ok(IntExpr::Lit(v, pos))
            }
            Tok::Minus => {
                // Unary minus. A literal folds immediately (`-8` is one
                // literal, so bitwidth range checks see `-8`, not `8`);
                // anything else desugars to `0 - x` (no Neg node exists).
                self.bump();
                match self.int_primary()? {
                    IntExpr::Lit(v, _) => Ok(IntExpr::Lit(v.wrapping_neg(), pos)),
                    inner => Ok(IntExpr::Bin(
                        IntBinOp::Sub,
                        Box::new(IntExpr::Lit(0, pos)),
                        Box::new(inner),
                    )),
                }
            }
            Tok::Hash => {
                self.bump();
                let e = self.parse_unary(false)?;
                Ok(IntExpr::Card(Box::new(e), pos))
            }
            Tok::Sum => {
                self.bump();
                // Quantified `sum x: D | ie`, or `sum e` over a unary set
                // (Java accepts both; the latter is the SUM cast).
                let save = self.pos;
                match self.quant_decls() {
                    Ok(ds) => {
                        self.expect(&Tok::Bar)?;
                        let ie = self.int_expr()?;
                        Ok(IntExpr::Sum(ds, Box::new(ie), pos))
                    }
                    Err(_) => {
                        self.pos = save;
                        let e = self.parse_unary(false)?;
                        Ok(IntExpr::SumOf(Box::new(e), pos))
                    }
                }
            }
            Tok::LParen => {
                self.bump();
                let e = self.int_expr()?;
                self.expect(&Tok::RParen)?;
                Ok(e)
            }
            Tok::LBrace => {
                // Bit-vector value of a braced set in integer position
                // (`{0, 1} * 2` reads `{0, 1}` as 3 = Σ 2^i). Unlike
                // `sum e` (Σ atom values), this is Σ 2^value over the
                // int members; anything else in the set contributes 0.
                let e = self.braced_set(false)?;
                Ok(IntExpr::BitsVal(Box::new(e), pos))
            }
            // Set-typed operand in integer position (variable, join, ...):
            // Java casts it via `typecheck_as_int` (Kodkod SUM cast).
            Tok::Ident(_)
            | Tok::Univ
            | Tok::None_
            | Tok::Iden
            | Tok::IntTy
            | Tok::IntKw
            | Tok::This
            | Tok::At
            | Tok::Tilde
            | Tok::Hat
            | Tok::Star => {
                let e = self.parse_unary(false)?;
                Ok(IntExpr::Val(Box::new(e), pos))
            }
            other => Err(self.err(&format!(
                "expected int expression, got {}",
                other.describe()
            ))),
        }
    }
}

/// Restricted label-set shape for `partial` entries: bare names (labels,
/// relation references, int literals), `none`/`{}`, dotted relation
/// references (`B.f`), and `+`/`->` combinations thereof. Everything
/// else (quantifiers, `#`, `sum`, closures, calls, label-carrying joins,
/// ...) is rejected here; label-vs-relation roles are decided at lowering.
fn partial_set_shape(e: &crate::ast::Expr) -> bool {
    match e {
        crate::ast::Expr::Name(..) | crate::ast::Expr::None_ => true,
        crate::ast::Expr::Bin(crate::ast::BinOp::Union | crate::ast::BinOp::Product, a, b) => {
            partial_set_shape(a) && partial_set_shape(b)
        }
        // Dotted pool reference (`B.f`): joins of label-free plain names.
        crate::ast::Expr::Bin(crate::ast::BinOp::Join, a, b) => {
            dotted_rel_shape(a) && dotted_rel_shape(b)
        }
        _ => false,
    }
}

/// A dotted relation reference: plain names (no labels, no int
/// literals) joined by `.`. Label-carrying joins (`A$x.f`) are not
/// partial shapes.
fn dotted_rel_shape(e: &crate::ast::Expr) -> bool {
    match e {
        crate::ast::Expr::Name(n, _) => {
            !n.contains('$') && n != "none" && n.parse::<i64>().is_err()
        }
        crate::ast::Expr::Bin(crate::ast::BinOp::Join, a, b) => {
            dotted_rel_shape(a) && dotted_rel_shape(b)
        }
        _ => false,
    }
}

/// `set = int` (bit-vector model: the set side reads as its bitmask
/// value, Σ signed-MSB weights — `X = 5` holds iff X = {0, 2}).
/// Desugared as `bits(set) = int`; the set side keeps its Expr so the
/// lowerer can check it denotes int atoms.
fn set_eq_int(set: Expr, ie: IntExpr, pos: usize, neg: bool) -> Formula {
    let cmp = Formula::IntCmp(IntCmpOp::Eq, IntExpr::BitsVal(Box::new(set), pos), ie, pos);
    if neg {
        Formula::Not(Box::new(cmp))
    } else {
        cmp
    }
}

/// Fold pure literal integer arithmetic to its value (`{1+1}` is `{2}`)./// Anything needing a solution (`#A`, `sum`, variables) yields `None`, as
/// does division by zero (the caller falls back to relational parsing).
fn fold_int_literal(ie: &crate::ast::IntExpr) -> Option<i64> {
    match ie {
        crate::ast::IntExpr::Lit(v, _) => Some(*v),
        crate::ast::IntExpr::Bin(op, a, b) => {
            let (x, y) = (fold_int_literal(a)?, fold_int_literal(b)?);
            Some(match op {
                crate::ast::IntBinOp::Add => x.wrapping_add(y),
                crate::ast::IntBinOp::Sub => x.wrapping_sub(y),
                crate::ast::IntBinOp::Mul => x.wrapping_mul(y),
                crate::ast::IntBinOp::Div => x.checked_div(y)?,
                crate::ast::IntBinOp::Rem => x.checked_rem(y)?,
            })
        }
        _ => None,
    }
}

/// True when an integer tree uses `*`/`/`/`%`: operators with no
/// relational (set) reading, so the tree can only be arithmetic
/// (`A*A in B` is a type error, never a set).
fn int_expr_has_mul_div_rem(ie: &crate::ast::IntExpr) -> bool {
    match ie {
        crate::ast::IntExpr::Bin(op, a, b) => {
            matches!(
                op,
                crate::ast::IntBinOp::Mul | crate::ast::IntBinOp::Div | crate::ast::IntBinOp::Rem
            ) || int_expr_has_mul_div_rem(a) || int_expr_has_mul_div_rem(b)
        }
        crate::ast::IntExpr::Sum(_, body, _) => int_expr_has_mul_div_rem(body),
        _ => false,
    }
}

fn mult3(t: &Tok) -> crate::ast::Mult3 {
    match t {
        Tok::Lone => crate::ast::Mult3::Lone,
        Tok::One => crate::ast::Mult3::One,
        _ => crate::ast::Mult3::Some,
    }
}
