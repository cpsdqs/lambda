#[macro_use]
extern crate lazy_static;

use std::io::{self, BufRead};

fn main() {
    let stdin = io::stdin();

    let mut index = LambdaIndex::new();

    for line in stdin.lock().lines() {
        let line = line.unwrap();
        eval_expr(&line, &mut index);
    }
}

use std::sync::Mutex;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone)]
pub struct LambdaIndex {
    lambdas: HashMap<String, Lambda>,
}

impl LambdaIndex {
    pub fn new() -> LambdaIndex {
        LambdaIndex {
            lambdas: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<&Lambda> {
        self.lambdas.get(name.into())
    }
}

lazy_static! {
    static ref ARGUMENT_ID: Mutex<u64> = Mutex::new(0);
    static ref ARGUMENT_NAMES: Mutex<HashMap<u64, String>> = Mutex::new(HashMap::new());
}

fn next_argument_id(named: String) -> u64 {
    let mut id = ARGUMENT_ID.lock().unwrap();
    *id += 1;
    ARGUMENT_NAMES.lock().unwrap().insert(*id, named);
    *id
}

fn argument_name(id: u64) -> Option<String> {
    ARGUMENT_NAMES.lock().unwrap().get(&id).map(|x| x.clone())
}

type ArgumentMap = HashMap<String, u64>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LambdaItem {
    Value(String),
    Argument(u64),
    Call(Box<LambdaItem>, Box<LambdaItem>),
    Lambda(Box<Lambda>),
}

impl LambdaItem {
    /// Args must have been reduced.
    pub fn reduce(&self, args: &HashMap<u64, LambdaItem>, index: &LambdaIndex) -> LambdaItem {
        match self {
            &LambdaItem::Value(ref name) => LambdaItem::Value(name.clone()),
            &LambdaItem::Argument(id) => args.get(&id).unwrap_or(&LambdaItem::Argument(id)).clone(),
            &LambdaItem::Lambda(ref lambda) => LambdaItem::Lambda(Box::new(lambda.subst_args(args))),
            &LambdaItem::Call(ref callee, ref arg) => {
                let arg = arg.reduce(args, index);

                match callee.as_ref().reduce(args, index) {
                    LambdaItem::Value(ref name) => {
                        match index.get(name) {
                            Some(lambda) => lambda.reduce(args.clone(), Some(arg), index),
                            None => LambdaItem::Call(Box::new(LambdaItem::Value(name.clone())), Box::new(arg)),
                        }
                    }
                    LambdaItem::Argument(id) => {
                        // callee has been reduced above; this argument can't be resolved
                        // for some reason
                        let name = argument_name(id).expect("Argument has no name");
                        eprintln!("Unresolved argument {}", name);
                        LambdaItem::Call(Box::new(LambdaItem::Value(name)), Box::new(arg))
                    }
                    LambdaItem::Call(a, b) => {
                        // this call can't be reduced for some reason
                        LambdaItem::Call(Box::new(LambdaItem::Call(a, b)), Box::new(arg))
                    }
                    LambdaItem::Lambda(lambda) => lambda.reduce(args.clone(), Some(arg), index),
                }
            }
        }
    }

    fn subst_args(&self, args: &HashMap<u64, LambdaItem>) -> LambdaItem {
        match self {
            &LambdaItem::Value(..) => self.clone(),
            &LambdaItem::Argument(id) => args.get(&id).unwrap_or(&LambdaItem::Argument(id)).clone(),
            &LambdaItem::Lambda(ref l) => LambdaItem::Lambda(Box::new(l.subst_args(args))),
            &LambdaItem::Call(ref a, ref b) => LambdaItem::Call(Box::new(a.subst_args(args)), Box::new(b.subst_args(args))),
        }
    }

    fn needs_display_parens(&self) -> bool {
        match self {
            &LambdaItem::Value(..) => false,
            &LambdaItem::Argument(..) => false,
            &LambdaItem::Lambda(..) => true,
            &LambdaItem::Call(..) => true,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lambda {
    argument: u64,
    contents: LambdaItem,
}

impl Lambda {
    pub fn new(argument: u64, contents: LambdaItem) -> Lambda {
        Lambda { argument, contents }
    }

    pub fn reduce(&self, mut args: HashMap<u64, LambdaItem>, arg: Option<LambdaItem>, index: &LambdaIndex) -> LambdaItem {
        if let Some(arg) = arg {
            args.insert(self.argument, arg);
        }
        self.contents.reduce(&args, index)
    }

    fn subst_args(&self, args: &HashMap<u64, LambdaItem>) -> Lambda {
        Lambda { argument: self.argument, contents: self.contents.subst_args(args) }
    }
}

impl fmt::Display for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "λ{}.{}", argument_name(self.argument).unwrap(), self.contents)
    }
}

impl fmt::Display for LambdaItem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &LambdaItem::Value(ref name) => write!(f, "{}", name),
            &LambdaItem::Argument(id) => write!(f, "{}", argument_name(id).unwrap()),
            &LambdaItem::Lambda(ref lambda) => write!(f, "{}", lambda),
            &LambdaItem::Call(ref a, ref b) => {
                if let &LambdaItem::Call(ref c, ref d) = &**a {
                    if d.needs_display_parens() {
                        write!(f, "{} ({}) {}", c, d, b)
                    } else {
                        write!(f, "{} {} {}", c, d, b)
                    }
                } else if a.needs_display_parens() {
                    write!(f, "({}) {}", a, b)
                } else {
                    write!(f, "{} {}", a, b)
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LexToken {
    /// λ
    Lambda,
    /// .
    Dot,
    /// ( .. tokens .. )
    Parens(Vec<LexToken>),
    /// A word, character, or literally anything not whitespace
    Identifier(String),
    /// :=
    Define,
}

impl LexToken {
    pub fn is_identifier(&self) -> bool {
        match self {
            &LexToken::Identifier(_) => true,
            _ => false,
        }
    }
}

fn lex_expr(expr: &str) -> Vec<LexToken> {
    let mut in_parens = 0;
    let mut string = String::new();
    let mut tokens = Vec::new();
    let mut had_lambda = false;

    let chars: Vec<char> = expr.chars().collect();

    let mut i = 0;
    while i < chars.len() {
        let ch = chars[i];

        if in_parens > 0 {
            if ch == '(' {
                in_parens += 1;
            } else if ch == ')' {
                in_parens -= 1;
            }
            if in_parens > 0 {
                string.push(ch);
            } else {
                tokens.push(LexToken::Parens(lex_expr(&string)));
                string.clear();
            }
            i += 1;
            continue;
        }
        if ch == '(' {
            if !string.is_empty() {
                tokens.push(LexToken::Identifier(string.clone()));
            }
            string.clear();
            in_parens = 1;
        } else if ch == 'λ' {
            if !string.is_empty() {
                tokens.push(LexToken::Identifier(string.clone()));
            }
            string.clear();
            had_lambda = true;
            tokens.push(LexToken::Lambda);
        } else if ch == '.' {
            if !string.is_empty() {
                tokens.push(LexToken::Identifier(string.clone()));
            }
            string.clear();
            tokens.push(LexToken::Dot);
        } else if !had_lambda && ch == ':' && chars.get(i + 1).unwrap_or(&'?') == &'=' {
            if !string.is_empty() {
                tokens.push(LexToken::Identifier(string.clone()));
            }
            string.clear();
            tokens.push(LexToken::Define);
            i += 1;
        } else if ch.is_whitespace() {
            if !string.is_empty() {
                tokens.push(LexToken::Identifier(string.clone()));
            }
            string.clear();
        } else {
            string.push(ch);
        }

        i += 1;
    }

    if !string.is_empty() {
        tokens.push(LexToken::Identifier(string));
    }

    tokens
}

#[derive(Debug, Clone)]
enum ParseIdent {
    Named(String),
    Arg(u64),
}

impl From<String> for ParseIdent {
    fn from(v: String) -> Self {
        ParseIdent::Named(v)
    }
}

impl Into<LambdaItem> for ParseIdent {
    fn into(self) -> LambdaItem {
        match self {
            ParseIdent::Named(name) => LambdaItem::Value(name),
            ParseIdent::Arg(arg) => LambdaItem::Argument(arg),
        }
    }
}

#[derive(Debug, Clone)]
enum ParseToken {
    None,
    /// `a := b`
    Define(String, Box<ParseToken>),
    /// `(a) b` or `(a)`
    Call(ParseIdent, Option<Box<ParseToken>>),
    /// `(a) b` or `(a)`
    CallParens(Box<ParseToken>, Option<Box<ParseToken>>),
    /// `λa.b`
    Lambda(u64, Box<ParseToken>),
}

impl ParseToken {
    fn ident(name: String) -> ParseToken {
        ParseToken::Call(name.into(), None)
    }
}

#[derive(Debug)]
enum ParseError {
    InvalidToken(String),
    UnexpectedDefine,
}

/// a := λa.b λc.c a
/// a := parse(λa.b λc.c a)
/// a := parse(λa.parse(b λc.c a))
/// a := parse(λa.parse(b parse(λc.c a)))
/// a := parse(λa.parse(b parse(λc.parse(c a))))
/// a := parse(λa.parse(b parse(λc.parse(c parse(a)))))
/// a := λ
///      |--.
///      a  *
///         |--.
///         b  λ--.
///            c  *
///               |--.
///               c  a

fn parse_lex(mut tokens: Vec<LexToken>, arg_map: ArgumentMap) -> Result<ParseToken, ParseError> {
    let mut define = None;

    if tokens.len() >= 3 {
        if tokens[0].is_identifier() && tokens[1] == LexToken::Define {
            define = match tokens.remove(0) {
                LexToken::Identifier(n) => Some(n),
                _ => panic!(),
            };
            tokens.remove(0);
        }
    }

    let mut node = ParseToken::None;

    let mut i = 0;

    while i < tokens.len() {
        let token = tokens[i].clone();

        match token {
            LexToken::Lambda => {
                let arg = if let Some(next) = tokens.get(i + 1) {
                    match next {
                        &LexToken::Identifier(ref ident) => ident.clone(),
                        _ => {
                            return Err(ParseError::InvalidToken(
                                "Lambda must be followed by an identifier".into(),
                            ))
                        }
                    }
                } else {
                    return Err(ParseError::InvalidToken(
                        "Lambda must be followed by something".into(),
                    ));
                };

                if let Some(next) = tokens.get(i + 2) {
                    match next {
                        &LexToken::Dot => (),
                        _ => {
                            return Err(ParseError::InvalidToken(
                                "Lambda argument must be followed by a dot".into(),
                            ))
                        }
                    }
                } else {
                    return Err(ParseError::InvalidToken(
                        "Lambda argument must be followed by something".into(),
                    ));
                }

                let body: Vec<LexToken> = tokens.drain((i + 3)..).collect();

                let mut arg_map = arg_map.clone();
                let arg_id = next_argument_id(arg.clone());
                arg_map.insert(arg.clone(), arg_id);

                node = ParseToken::Lambda(arg_id, Box::new(parse_lex(body, arg_map)?));

                i += 2;
            }
            LexToken::Dot => return Err(ParseError::InvalidToken("Unexpected dot".into())),
            LexToken::Parens(body) => {
                let body = parse_lex(body, arg_map.clone())?;
                match node {
                    ParseToken::None => node = body,
                    ParseToken::Call(a, b) => if b.is_some() {
                        node = ParseToken::CallParens(
                            Box::new(ParseToken::Call(a, b)),
                            Some(Box::new(body)),
                        )
                    } else {
                        node = ParseToken::Call(a, Some(Box::new(body)))
                    },
                    ParseToken::CallParens(a, b) => if b.is_some() {
                        node = ParseToken::CallParens(
                            Box::new(ParseToken::CallParens(a, b)),
                            Some(Box::new(body)),
                        )
                    } else {
                        node = ParseToken::CallParens(a, Some(Box::new(body)))
                    },
                    ParseToken::Lambda(..) => {
                        node = ParseToken::CallParens(Box::new(node), Some(Box::new(body)))
                    }
                    ParseToken::Define(..) => return Err(ParseError::UnexpectedDefine),
                }
            }
            LexToken::Identifier(ident) => {
                let token = if let Some(arg) = arg_map.get(&ident) {
                    ParseToken::Call(ParseIdent::Arg(*arg), None)
                } else {
                    ParseToken::ident(ident)
                };

                match node {
                    ParseToken::None => node = token,
                    ParseToken::Call(a, b) => if b.is_some() {
                        node = ParseToken::CallParens(
                            Box::new(ParseToken::Call(a, b)),
                            Some(Box::new(token)),
                        );
                    } else {
                        node = ParseToken::Call(a, Some(Box::new(token)))
                    },
                    ParseToken::CallParens(a, b) => if b.is_some() {
                        node = ParseToken::CallParens(
                            Box::new(ParseToken::CallParens(a, b)),
                            Some(Box::new(token)),
                        );
                    } else {
                        node = ParseToken::CallParens(a, Some(Box::new(token)))
                    },
                    ParseToken::Lambda(..) => {
                        node = ParseToken::CallParens(
                            Box::new(node),
                            Some(Box::new(token)),
                        );
                    }
                    ParseToken::Define(..) => return Err(ParseError::UnexpectedDefine),
                }
            },
            LexToken::Define => return Err(ParseError::UnexpectedDefine),
        }

        i += 1;
    }

    Ok(if let Some(ident) = define {
        ParseToken::Define(ident, Box::new(node))
    } else {
        node
    })
}

fn convert_expr(node: ParseToken) -> Option<LambdaItem> {
    match node {
        ParseToken::None => None,
        ParseToken::Define(..) => panic!("Define is not an expression"),
        ParseToken::Call(a, b) => if let Some(b) = b {
            Some(LambdaItem::Call(
                Box::new(a.into()),
                Box::new(convert_expr(*b).unwrap()),
            ))
        } else {
            Some(a.into())
        },
        ParseToken::CallParens(a, b) => if let Some(b) = b {
            Some(LambdaItem::Call(
                Box::new(convert_expr(*a).unwrap()),
                Box::new(convert_expr(*b).unwrap()),
            ))
        } else {
            Some(convert_expr(*a).unwrap())
        },
        ParseToken::Lambda(arg, body) => Some(LambdaItem::Lambda(Box::new(Lambda::new(
            arg,
            convert_expr(*body).expect("No lambda body"),
        )))),
    }
}

pub fn eval_expr(expr: &str, index: &mut LambdaIndex) {
    let node = match parse_lex(lex_expr(expr), ArgumentMap::new()) {
        Ok(node) => node,
        Err(err) => {
            eprintln!("{:?}", err);
            return;
        }
    };

    if let ParseToken::Define(name, node) = node {
        if let Some(node) = convert_expr(*node) {
            if let LambdaItem::Lambda(lambda) = node {
                index.lambdas.insert(name, *lambda);
            } else {
                eprintln!("Assignment only implemented for lambdas");
                /* if let Some(lambda) = index.get(&value).map(|x| x.clone()) {
                    index.lambdas.insert(name, lambda);
                } */
            }
        }
    } else {
        if let Some(node) = convert_expr(node) {
            println!("\x1b[36m{}\x1b[m", node.reduce(&HashMap::new(), index));
        }
    }
}
