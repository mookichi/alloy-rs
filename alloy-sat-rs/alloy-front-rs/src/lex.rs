//! Tokenizer for Alloy source text.

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Ident(String),
    Int(i64),
    // keywords
    Module,
    Sig,
    Abstract,
    Lone,
    One,
    Some,
    Fact,
    Pred,
    Fun,
    Assert,
    Check,
    Run,
    All,
    No,
    Univ,
    None_,
    Iden,
    IntTy,
    IntKw,
    Sum,
    Let,
    If,
    Else,
    Disj,
    In,
    Not,
    For,
    But,
    Exactly,
    Expect,
    Open,
    As,
    This,
    Extends,
    Then,
    AndKw,
    OrKw,
    SetKw,
    IffKw,
    ImpliesKw,
    DefaultKw,
    // temporal keywords
    Always,
    Eventually,
    Until,
    Releases,
    After,
    Before,
    Historically,
    Once,
    Since,
    Triggered,
    Keeping,
    Goal,
    Restore,
    Initially,
    Regularly,
    Consistently,
    Var,
    Steps,
    // symbols
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LParen,
    RParen,
    Colon,
    Comma,
    Dot,
    Arrow,
    Bar,
    Semi,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Hash,
    Tilde,
    Hat,
    PlusPlus,
    Eq,
    NotEq,
    LtEq,
    GtEq,
    Lt,
    Gt,
    Implies,
    Iff,
    OrOp,
    AndOp,
    ShArrow,
    Eof,
}

impl Tok {
    pub fn describe(&self) -> &'static str {
        match self {
            Tok::Ident(_) => "identifier",
            Tok::Int(_) => "integer",
            Tok::Module => "'module'",
            Tok::Sig => "'sig'",
            Tok::Abstract => "'abstract'",
            Tok::Lone => "'lone'",
            Tok::One => "'one'",
            Tok::Some => "'some'",
            Tok::Fact => "'fact'",
            Tok::Pred => "'pred'",
            Tok::Fun => "'fun'",
            Tok::Assert => "'assert'",
            Tok::Check => "'check'",
            Tok::Run => "'run'",
            Tok::All => "'all'",
            Tok::No => "'no'",
            Tok::Univ => "'univ'",
            Tok::None_ => "'none'",
            Tok::Iden => "'iden'",
            Tok::IntTy => "'int'",
            Tok::IntKw => "'Int'",
            Tok::Sum => "'sum'",
            Tok::Let => "'let'",
            Tok::If => "'if'",
            Tok::Else => "'else'",
            Tok::Disj => "'disj'",
            Tok::In => "'in'",
            Tok::Not => "'not'",
            Tok::For => "'for'",
            Tok::But => "'but'",
            Tok::Exactly => "'exactly'",
            Tok::Expect => "'expect'",
            Tok::Open => "'open'",
            Tok::As => "'as'",
            Tok::This => "'this'",
            Tok::Extends => "'extends'",
            Tok::AndKw => "'and'",
            Tok::SetKw => "'set'",
            Tok::OrKw => "'or'",
            Tok::IffKw => "'iff'",
            Tok::Then => "'then'",
            Tok::ImpliesKw => "'implies'",
            Tok::DefaultKw => "'default'",
            Tok::Always => "'always'",
            Tok::Eventually => "'eventually'",
            Tok::Until => "'until'",
            Tok::Releases => "'releases'",
            Tok::After => "'after'",
            Tok::Before => "'before'",
            Tok::Historically => "'historically'",
            Tok::Once => "'once'",
            Tok::Since => "'since'",
            Tok::Triggered => "'triggered'",
            Tok::Keeping => "'keeping'",
            Tok::Goal => "'goal'",
            Tok::Restore => "'restore'",
            Tok::Initially => "'initially'",
            Tok::Regularly => "'regularly'",
            Tok::Consistently => "'consistently'",
            Tok::Var => "'var'",
            Tok::Steps => "'steps'",
            Tok::LBrace => "'{'",
            Tok::RBrace => "'}'",
            Tok::LBracket => "'['",
            Tok::RBracket => "']'",
            Tok::LParen => "'('",
            Tok::RParen => "')'",
            Tok::Colon => "':'",
            Tok::Comma => "','",
            Tok::Dot => "'.'",
            Tok::Arrow => "'->'",
            Tok::Bar => "'|'",
            Tok::Semi => "';'",
            Tok::Plus => "'+'",
            Tok::Minus => "'-'",
            Tok::Star => "'*'",
            Tok::Slash => "'/'",
            Tok::Percent => "'%'",
            Tok::Amp => "'&'",
            Tok::Hash => "'#'",
            Tok::Tilde => "'~'",
            Tok::Hat => "'^'",
            Tok::PlusPlus => "'++'",
            Tok::Eq => "'='",
            Tok::NotEq => "'!='",
            Tok::LtEq => "'<='",
            Tok::GtEq => "'>='",
            Tok::Lt => "'<'",
            Tok::Gt => "'>'",
            Tok::Implies => "'=>'",
            Tok::Iff => "'<=>'",
            Tok::OrOp => "'||'",
            Tok::AndOp => "'&&'",
            Tok::ShArrow => "'=>'",
            Tok::Eof => "end of input",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tok: Tok,
    pub pos: usize,
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || c == '$'
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\'' || c == '"'
}

/// Tokenizes `src`. Comments (`//`, `--`, `/* */`) and whitespace are
/// skipped. Positions are byte offsets into the original source.
pub fn lex(src: &str) -> Result<Vec<Token>, crate::FrontError> {
    let b = src.as_bytes();
    let mut i = 0usize;
    let mut out = Vec::new();
    while i < b.len() {
        let c = b[i] as char;
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if b[i..].starts_with(b"//") || b[i..].starts_with(b"--") {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if b[i..].starts_with(b"/*") {
            let start = i;
            i += 2;
            while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                i += 1;
            }
            if i + 1 >= b.len() {
                return Err(crate::FrontError::Lex {
                    pos: start,
                    msg: "unterminated block comment".into(),
                });
            }
            i += 2;
            continue;
        }
        let start = i;
        // two-char symbols first
        let three = &b[i..];
        let two = |a: u8, bb: u8| three.len() >= 2 && three[0] == a && three[1] == bb;
        let sym: Option<(Tok, &'static str)> =
            if two(b'<', b'=') && three.len() >= 3 && three[2] == b'>' {
                i += 3;
                Some((Tok::Iff, "<=>"))
            } else if two(b'<', b'=') {
                i += 2;
                Some((Tok::LtEq, "<="))
            } else if two(b'>', b'=') {
                i += 2;
                Some((Tok::GtEq, ">="))
            } else if two(b'=', b'>') {
                i += 2;
                Some((Tok::Implies, "=>"))
            } else if two(b'<', b'-') && three.len() >= 3 && three[2] == b'>' {
                i += 3;
                Some((Tok::ShArrow, "<->"))
            } else if two(b'!', b'=') {
                i += 2;
                Some((Tok::NotEq, "!="))
            } else if two(b'|', b'|') {
                i += 2;
                Some((Tok::OrOp, "||"))
            } else if two(b'&', b'&') {
                i += 2;
                Some((Tok::AndOp, "&&"))
            } else if two(b'+', b'+') {
                i += 2;
                Some((Tok::PlusPlus, "++"))
            } else if two(b'-', b'>') {
                i += 2;
                Some((Tok::Arrow, "->"))
            } else {
                None
            };
        if let Some((tok, txt)) = sym {
            out.push(Token { tok, pos: start });
            let _ = txt;
            continue;
        }
        match c {
            '{' => push(&mut out, Tok::LBrace, start, &mut i),
            '}' => push(&mut out, Tok::RBrace, start, &mut i),
            '[' => push(&mut out, Tok::LBracket, start, &mut i),
            ']' => push(&mut out, Tok::RBracket, start, &mut i),
            '(' => push(&mut out, Tok::LParen, start, &mut i),
            ')' => push(&mut out, Tok::RParen, start, &mut i),
            ':' => push(&mut out, Tok::Colon, start, &mut i),
            ',' => push(&mut out, Tok::Comma, start, &mut i),
            '.' => push(&mut out, Tok::Dot, start, &mut i),
            '|' => push(&mut out, Tok::Bar, start, &mut i),
            ';' => push(&mut out, Tok::Semi, start, &mut i),
            '+' => push(&mut out, Tok::Plus, start, &mut i),
            '-' => push(&mut out, Tok::Minus, start, &mut i),
            '*' => push(&mut out, Tok::Star, start, &mut i),
            '/' => push(&mut out, Tok::Slash, start, &mut i),
            '%' => push(&mut out, Tok::Percent, start, &mut i),
            '&' => push(&mut out, Tok::Amp, start, &mut i),
            '#' => push(&mut out, Tok::Hash, start, &mut i),
            '~' => push(&mut out, Tok::Tilde, start, &mut i),
            '^' => push(&mut out, Tok::Hat, start, &mut i),
            '=' => push(&mut out, Tok::Eq, start, &mut i),
            '<' => push(&mut out, Tok::Lt, start, &mut i),
            '!' => push(&mut out, Tok::Not, start, &mut i),
            '>' => push(&mut out, Tok::Gt, start, &mut i),
            _ if c.is_ascii_digit() => {
                let mut v: i64 = 0;
                while i < b.len() && (b[i] as char).is_ascii_digit() {
                    v = v * 10 + (b[i] - b'0') as i64;
                    i += 1;
                }
                out.push(Token {
                    tok: Tok::Int(v),
                    pos: start,
                });
            }
            _ if is_ident_start(c) => {
                while i < b.len() && is_ident_char(b[i] as char) {
                    i += 1;
                }
                let word = &src[start..i];
                let kw = match word {
                    "module" => Tok::Module,
                    "sig" => Tok::Sig,
                    "abstract" => Tok::Abstract,
                    "lone" => Tok::Lone,
                    "one" => Tok::One,
                    "some" => Tok::Some,
                    "fact" => Tok::Fact,
                    "pred" => Tok::Pred,
                    "fun" => Tok::Fun,
                    "assert" => Tok::Assert,
                    "check" => Tok::Check,
                    "run" => Tok::Run,
                    "all" => Tok::All,
                    "no" => Tok::No,
                    "univ" => Tok::Univ,
                    "none" => Tok::None_,
                    "iden" => Tok::Iden,
                    "int" => Tok::IntTy,
                    "Int" => Tok::IntKw,
                    "sum" => Tok::Sum,
                    "let" => Tok::Let,
                    "if" => Tok::If,
                    "else" => Tok::Else,
                    "disj" => Tok::Disj,
                    "in" => Tok::In,
                    "not" => Tok::Not,
                    "for" => Tok::For,
                    "but" => Tok::But,
                    "exactly" => Tok::Exactly,
                    "expect" => Tok::Expect,
                    "open" => Tok::Open,
                    "as" => Tok::As,
                    "this" => Tok::This,
                    "set" => Tok::SetKw,
                    "and" => Tok::AndKw,
                    "or" => Tok::OrKw,
                    "iff" => Tok::IffKw,
                    "extends" => Tok::Extends,
                    "then" => Tok::Then,
                    "implies" => Tok::ImpliesKw,
                    "default" => Tok::DefaultKw,
                    "always" => Tok::Always,
                    "eventually" => Tok::Eventually,
                    "until" => Tok::Until,
                    "releases" => Tok::Releases,
                    "after" => Tok::After,
                    "before" => Tok::Before,
                    "historically" => Tok::Historically,
                    "once" => Tok::Once,
                    "since" => Tok::Since,
                    "triggered" => Tok::Triggered,
                    "keeping" => Tok::Keeping,
                    "goal" => Tok::Goal,
                    "restore" => Tok::Restore,
                    "initially" => Tok::Initially,
                    "regularly" => Tok::Regularly,
                    "consistently" => Tok::Consistently,
                    "var" => Tok::Var,
                    "steps" => Tok::Steps,
                    _ => Tok::Ident(word.to_string()),
                };
                out.push(Token {
                    tok: kw,
                    pos: start,
                });
            }
            _ => {
                return Err(crate::FrontError::Lex {
                    pos: start,
                    msg: format!("unexpected character {c:?}"),
                })
            }
        }
    }
    out.push(Token {
        tok: Tok::Eof,
        pos: b.len(),
    });
    Ok(out)
}

fn push(out: &mut Vec<Token>, tok: Tok, pos: usize, i: &mut usize) {
    out.push(Token { tok, pos });
    *i += 1;
}
