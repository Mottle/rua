use float::Float;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    IntLit {
        value: i32,
        base: IntBase
    },
    FloatLit(Float),
    StringLit(String),
    Ident(String),
    BoolLit(bool),

    Keyword(Keyword),
    Sign(Punctuation),

    Unknown(UnknownCharInfo)
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum IntBase {
    Dec, Oct, Bin, Hex
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct UnknownCharInfo {
    unknown_char: char,
    row_number: usize,
    column_number: usize,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Keyword {
    Let, If, Else, Then, End, Lambda, Do, Struct, Enum,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Punctuation {
    /// ";"
    Semi,
    /// ","
    Comma,
    /// "."
    Dot,
    /// "("
    OpenParen,
    /// ")"
    CloseParen,
    /// "{"
    OpenBrace,
    /// "}"
    CloseBrace,
    /// "["
    OpenBracket,
    /// "]"
    CloseBracket,
    /// "@"
    At,
    /// "#"
    Pound,
    /// "~"
    Tilde,
    /// "?"
    Question,
    /// ":"
    Colon,
    /// "$"
    Dollar,
    /// "="
    Eq,
    /// "!"
    Bang,
    /// "<"
    Lt,
    /// ">"
    Gt,
    /// "-"
    Minus,
    /// "&"
    And,
    /// "|"
    Or,
    /// "+"
    Plus,
    /// "*"
    Star,
    /// "/"
    Slash,
    /// "^"
    Caret,
    /// "%"
    Percent,
}