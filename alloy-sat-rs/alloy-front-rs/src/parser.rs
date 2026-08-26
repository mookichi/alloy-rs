//! Recursive-descent + Pratt parser for the supported Alloy subset.

use crate::ast::*;
use crate::lex::{Tok, Token};
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
                    Tok::Ident(n) => n,
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
                    Tok::Ident(n) => n,
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
        let mut paras = Vec::new();
        let mut commands = Vec::new();
        loop {
            match self.peek() {
                Tok::Sig => sigs.push(self.sig_decl()?),
                Tok::Abstract | Tok::One | Tok::Lone | Tok::Some | Tok::Var
                    if matches!(self.peek_at(1), Tok::Sig) =>
                {
                    sigs.push(self.sig_decl()?);
                }
                Tok::Fact => {
                    self.bump();
                    let name = if let Tok::Ident(_) = self.peek() {
                        Some(match self.bump().tok {
                            Tok::Ident(n) => n,
                            _ => unreachable!(),
                        })
                    } else {
                        None
                    };
                    let body = self.braced_formula()?;
                    facts.push((name, body));
                }
                Tok::Pred => paras.push(self.para(false)?),
                Tok::Fun => paras.push(self.para(true)?),
                Tok::Assert => {
                    self.bump();
                    let name = match self.bump().tok {
                        Tok::Ident(n) => n,
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
                Tok::Run | Tok::Check => commands.push(self.command()?),
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
            paras,
            commands,
            opens,
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
        let mut names = vec![self.ident()?];
        while self.eat(&Tok::Comma) {
            names.push(self.ident()?);
        }
        let mut extends = None;
        let mut rel = SigRel::None;
        if self.eat(&Tok::Colon) {
            // rare `sig X : ext Y` form? not supported
            return Err(self.err("sig inheritance via ':' unsupported"));
        }
        if matches!(self.peek(), Tok::Extends) {
            self.bump();
            extends = Some(self.ident()?);
            rel = SigRel::Extends;
        } else if matches!(self.peek(), Tok::In) {
            self.bump();
            extends = Some(self.ident()?);
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
            let f = self.formula()?;
            self.expect(&Tok::RBrace)?;
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
        let mut names = vec![self.ident()?];
        while matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::Ident(_))
            && (matches!(self.peek_at(2), Tok::Colon) || matches!(self.peek_at(2), Tok::Comma))
        {
            self.bump();
            names.push(self.ident()?);
        }
        if self.eat(&Tok::Colon) {
            let expr = self.arrow_type(in_sig)?;
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
    fn arrow_type(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut parts: Vec<(Option<Tok>, Expr)> = Vec::new();
        let lead_mult = self.opt_mult_kw();
        parts.push((lead_mult.clone(), self.parse_rproduct(in_sig)?));
        while self.eat(&Tok::Arrow) {
            let m = self.opt_mult_kw();
            parts.push((m, self.parse_rproduct(in_sig)?));
        }
        // fold right-assoc: a -> b -> c == a -> (b -> c)
        let mut iter = parts.into_iter().rev();
        let (_, mut acc) = iter.next().unwrap();
        for (m, lhs) in iter {
            acc = Expr::Bin(BinOp::Product, Box::new(lhs), Box::new(acc));
            if let Some(kw) = m {
                // multiplicity marker; the lowerer reads ArrowMult nodes
                acc = Expr::ArrowMult(mult3(&kw), Box::new(acc));
            }
        }
        if let Some(m) = lead_mult {
            acc = Expr::LeadMult(mult3(&m), Box::new(acc));
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
        let name = self.ident()?;
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
        let kind = if self.eat(&Tok::Run) {
            CommandKind::Run(None)
        } else {
            self.expect(&Tok::Check)?;
            CommandKind::Check(None)
        };
        let mut kind = if let Tok::Ident(_) = self.peek() {
            let n = self.ident()?;
            match kind {
                CommandKind::Run(_) => CommandKind::Run(Some(n)),
                CommandKind::Check(_) => CommandKind::Check(Some(n)),
            }
        } else {
            kind
        };
        // inline braced body: `run { F } for ..`, `check name { F } for ..`
        if matches!(self.peek(), Tok::LBrace) {
            let auto =
                matches!(kind, CommandKind::Run(None)) || matches!(kind, CommandKind::Check(None));
            self.inline_body_index += 1;
            let name = match &kind {
                CommandKind::Run(Some(n)) | CommandKind::Check(Some(n)) => n.clone(),
                _ => format!(
                    "{}${}",
                    if matches!(kind, CommandKind::Run(_)) {
                        "run"
                    } else {
                        "check"
                    },
                    self.inline_body_index
                ),
            };
            let _ = auto;
            let body = self.braced_formula()?;
            self.pending_paras.push(Para {
                name: name.clone(),
                params: Vec::new(),
                body,
                body_expr: None,
                is_fun: false,
                ret: None,
            });
            kind = match kind {
                CommandKind::Run(_) => CommandKind::Run(Some(name)),
                CommandKind::Check(_) => CommandKind::Check(Some(name)),
            };
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
        Ok(Command { kind, scope, pos })
    }

    fn scope_clause(&mut self, scope: &mut Scope) -> PResult<()> {
        if self.eat(&Tok::Exactly) {
            let n = self.int_lit()? as u32;
            if matches!(self.peek(), Tok::Ident(_)) {
                let name = self.ident()?;
                scope.entries.push((name, ScopeEntry::Exactly(n)));
            } else {
                scope.overall = Some(n);
                scope.overall_exact = true;
            }
            return Ok(());
        }
        let first = self.int_lit()? as u32;
        // `for 10 steps` form: temporal step count
        if matches!(self.peek(), Tok::Steps) {
            self.bump();
            scope.steps = Some(first);
        } else if matches!(self.peek(), Tok::Ident(_)) {
            // `for 8 State` form: a bare trailing name scopes that one sig
            let name = self.ident()?;
            scope.entries.push((name, ScopeEntry::Num(first)));
        } else {
            scope.overall = Some(first);
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

    /// Top-level relational expression (arrow lowest).
    fn rel_expr_top(&mut self, in_sig: bool) -> PResult<Expr> {
        let e = self.parse_arrow(in_sig)?;
        Ok(e)
    }

    fn parse_arrow(&mut self, in_sig: bool) -> PResult<Expr> {
        let l = self.parse_rproduct(in_sig)?;
        if self.eat(&Tok::Arrow) {
            let r = self.parse_arrow(in_sig)?;
            return Ok(Expr::Bin(BinOp::Product, Box::new(l), Box::new(r)));
        }
        Ok(l)
    }

    fn parse_rproduct(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_override(in_sig)?;
        // `<->` is the reverse product: a <-> b == b -> a
        while matches!(self.peek(), Tok::ShArrow) {
            self.bump();
            let r = self.parse_override(in_sig)?;
            l = Expr::Bin(BinOp::Product, Box::new(r), Box::new(l));
        }
        Ok(l)
    }

    fn parse_override(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_plusminus(in_sig)?;
        loop {
            if self.eat(&Tok::PlusPlus) {
                let r = self.parse_plusminus(in_sig)?;
                l = Expr::Bin(BinOp::Override, Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_plusminus(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_amp(in_sig)?;
        loop {
            match self.peek() {
                Tok::Plus => {
                    self.bump();
                    let r = self.parse_amp(in_sig)?;
                    l = Expr::Bin(BinOp::Union, Box::new(l), Box::new(r));
                }
                Tok::Minus => {
                    self.bump();
                    let r = self.parse_amp(in_sig)?;
                    l = Expr::Bin(BinOp::Difference, Box::new(l), Box::new(r));
                }
                _ => break,
            }
        }
        Ok(l)
    }

    fn parse_amp(&mut self, in_sig: bool) -> PResult<Expr> {
        let mut l = self.parse_unary(in_sig)?;
        while self.eat(&Tok::Amp) {
            let r = self.parse_unary(in_sig)?;
            l = Expr::Bin(BinOp::Intersect, Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn parse_unary(&mut self, in_sig: bool) -> PResult<Expr> {
        match self.peek() {
            Tok::Tilde => {
                self.bump();
                Ok(Expr::Transpose(Box::new(self.parse_unary(in_sig)?)))
            }
            Tok::Hat => {
                self.bump();
                Ok(Expr::TClosure(Box::new(self.parse_unary(in_sig)?)))
            }
            Tok::Star => {
                self.bump();
                Ok(Expr::RClosure(Box::new(self.parse_unary(in_sig)?)))
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
                    // right side may carry prefix closures: n.^next
                    let r = self.parse_unary(in_sig)?;
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

    fn parse_primary(&mut self, in_sig: bool) -> PResult<Expr> {
        let pos = self.pos();
        // let binding in expression context: `let x = expr in expr`
        if matches!(self.peek(), Tok::Let) {
            self.bump();
            let mut binds = Vec::new();
            loop {
                let name = self.ident()?;
                self.expect(&Tok::Eq)?;
                let e = self.rel_expr_top(in_sig)?;
                binds.push((name, e));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::In)?;
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
            Tok::IntTy | Tok::IntKw => {
                self.bump();
                Ok(Expr::IntAtom)
            }
            Tok::LBrace => {
                // comprehension without keyword
                self.bump();
                let ds = self.quant_decls()?;
                self.expect(&Tok::Bar)?;
                let f = self.formula()?;
                self.expect(&Tok::RBrace)?;
                Ok(Expr::Comprehension(ds, Box::new(f)))
            }
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

    fn formula(&mut self) -> PResult<Formula> {
        self.parse_iff()
    }

    fn parse_iff(&mut self) -> PResult<Formula> {
        let l = self.parse_implies()?;
        if self.eat(&Tok::Iff) || self.eat(&Tok::IffKw) {
            let r = self.parse_iff()?;
            return Ok(Formula::Iff(Box::new(l), Box::new(r)));
        }
        Ok(l)
    }

    fn parse_implies(&mut self) -> PResult<Formula> {
        let l = self.parse_temporal_bin()?;
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
        if self.eat(&Tok::Until) {
            let r = self.parse_temporal_bin()?;
            return Ok(Formula::Until(Box::new(l), Box::new(r)));
        }
        if self.eat(&Tok::Releases) {
            let r = self.parse_temporal_bin()?;
            return Ok(Formula::Releases(Box::new(l), Box::new(r)));
        }
        if self.eat(&Tok::Since) {
            let r = self.parse_temporal_bin()?;
            return Ok(Formula::Since(Box::new(l), Box::new(r)));
        }
        if self.eat(&Tok::Triggered) {
            let r = self.parse_temporal_bin()?;
            return Ok(Formula::Triggered(Box::new(l), Box::new(r)));
        }
        Ok(l)
    }

    fn parse_or(&mut self) -> PResult<Formula> {
        let mut l = self.parse_and()?;
        while matches!(self.peek(), Tok::OrOp | Tok::OrKw) {
            self.bump();
            let r = self.parse_and()?;
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
                let n = self.ident()?;
                self.expect(&Tok::Eq)?;
                let e = self.rel_expr_top(false)?;
                binds.push((n, e));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::Bar)?;
            let body = self.formula()?;
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
                Ok(Formula::Always(Box::new(self.formula()?)))
            }
            Tok::Eventually => {
                self.bump();
                Ok(Formula::Eventually(Box::new(self.formula()?)))
            }
            Tok::Before => {
                self.bump();
                Ok(Formula::Before(Box::new(self.formula()?)))
            }
            Tok::Historically => {
                self.bump();
                Ok(Formula::Historically(Box::new(self.formula()?)))
            }
            Tok::Once => {
                self.bump();
                Ok(Formula::Once(Box::new(self.formula()?)))
            }
            Tok::Keeping => {
                self.bump();
                Ok(Formula::Keeping(Box::new(self.formula()?)))
            }
            Tok::Goal => {
                self.bump();
                Ok(Formula::Goal(Box::new(self.formula()?)))
            }
            Tok::Restore => {
                self.bump();
                Ok(Formula::Restore(Box::new(self.formula()?)))
            }
            Tok::Initially => {
                self.bump();
                Ok(Formula::Initially(Box::new(self.formula()?)))
            }
            Tok::Regularly => {
                self.bump();
                Ok(Formula::Regularly(Box::new(self.formula()?)))
            }
            Tok::Consistently => {
                self.bump();
                Ok(Formula::Consistently(Box::new(self.formula()?)))
            }
            Tok::All | Tok::Some | Tok::No | Tok::Lone | Tok::One => self.parse_quant_or_cmp(),
            Tok::Sum => {
                // sum formula? not a formula starter; error out naturally
                self.parse_quant_or_cmp()
            }
            _ => self.parse_comparison(),
        }
    }

    fn starts_negation(&self) -> bool {
        matches!(self.peek(), Tok::Not)
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
                let body = if matches!(self.peek(), Tok::LBrace) {
                    self.braced_formula()?
                } else {
                    self.expect(&Tok::Bar)?;
                    if matches!(self.peek(), Tok::LBrace) {
                        self.braced_formula()?
                    } else {
                        self.formula()?
                    }
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
        let mut names = vec![self.ident()?];
        // continue the SAME group only when a comma joins two bare names
        // (`x, y: S`); a group boundary looks like `x: S, y: T` where the
        // colon arrives before any comma.
        while matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::Ident(_))
            && (matches!(self.peek_at(2), Tok::Colon) || matches!(self.peek_at(2), Tok::Comma))
        {
            self.bump(); // comma
            names.push(self.ident()?);
        }
        self.expect(&Tok::Colon)?;
        let expr = self.rel_expr_top(false)?;
        Ok(Decl {
            disj,
            names,
            expr,
            pos,
            is_var: false,
        })
    }

    fn parse_comparison(&mut self) -> PResult<Formula> {
        // Int vs set comparisons are disambiguated by shape; for ambiguous
        // leading '(' try int first, then rewind to set parsing.
        if self.starts_int_expr() || matches!(self.peek(), Tok::LParen) {
            let save = self.pos;
            match self.int_cmp_tail() {
                Ok(f) => return Ok(f),
                Err(_) => self.pos = save,
            }
        }
        let pos = self.pos();
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
        if let Expr::Name(n, ppos) = &l {
            // bare identifier in formula position: zero-arg predicate call,
            // valid when a formula operator follows (=> <=> || and or } ...)
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
                    | Tok::RBrace
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
                return Err(self.err(&format!("expected comparison, got {}", other.describe())))
            }
        };
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
        matches!(self.peek(), Tok::Hash | Tok::Sum | Tok::Int(_))
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
            Tok::Hash => {
                self.bump();
                let e = self.parse_unary(false)?;
                Ok(IntExpr::Card(Box::new(e), pos))
            }
            Tok::Sum => {
                self.bump();
                let ds = {
                    // sum x: D | ie   or   sum[...] unsupported bracket form
                    self.quant_decls()?
                };
                self.expect(&Tok::Bar)?;
                let ie = self.int_expr()?;
                Ok(IntExpr::Sum(ds, Box::new(ie), pos))
            }
            Tok::LParen => {
                self.bump();
                let e = self.int_expr()?;
                self.expect(&Tok::RParen)?;
                Ok(e)
            }
            other => Err(self.err(&format!(
                "expected int expression, got {}",
                other.describe()
            ))),
        }
    }
}

fn mult3(t: &Tok) -> crate::ast::Mult3 {
    match t {
        Tok::Lone => crate::ast::Mult3::Lone,
        Tok::One => crate::ast::Mult3::One,
        _ => crate::ast::Mult3::Some,
    }
}
