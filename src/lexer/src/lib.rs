pub mod token;
pub mod char_sequence;
pub mod sequence;

use token::*;
use nom::IResult;
use nom::bytes::complete::{take_while, tag};
use nom::sequence::{preceded, pair, tuple, delimited};
use nom::branch::alt;
use nom::combinator::{recognize, map_res, map_opt, value, map, verify};
use nom::character::complete::{alpha1, alphanumeric1, digit1, char};
use std::str::FromStr;
use nom::multi::{many0, fold_many0};
use nom::bytes::complete::{take_while_m_n, is_not};
use nom::character::complete::multispace1;

#[macro_use]
extern crate nom;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn lexeme_int_lit_test() {
        let n1 = "12345";
        assert_eq!(lexeme_int_lit(n1).unwrap().1, Token::IntLit { value: 12345, base: IntBase::Dec });

        let n2 = "0x123";
        assert_eq!(lexeme_int_lit(n2).unwrap().1, Token::IntLit { value: 0x123, base: IntBase::Hex });

        let n3 = "0o123";
        assert_eq!(lexeme_int_lit(n3).unwrap().1, Token::IntLit { value: 0o123, base: IntBase::Oct });

        let n4 = "0b1011";
        assert_eq!(lexeme_int_lit(n4).unwrap().1, Token::IntLit { value: 0b1011, base: IntBase::Bin });
    }

    #[test]
    fn lexeme_bool_lit_test() {
        assert_eq!(lexeme_bool_lit("true").unwrap().1, Token::BoolLit(true));
        assert_eq!(lexeme_bool_lit("false").unwrap().1, Token::BoolLit(false));
    }

    #[test]
    fn lexeme_ident_test() {
        let id = "_fuck_123__SHIT";
        assert_eq!(lexeme_ident(id).unwrap().1, Token::Ident(id.into()));

    }

    #[test]
    fn lexeme_float_lit_test() {
        let f = "114.514";
        assert_eq!(lexeme_float_lit(f).unwrap().1, Token::FloatLit(114.514.into()));
    }

    #[test]
    fn lexeme_string_lit_test() {
        let str_lit = "\"abc\"";
        assert_eq!(lexeme_string_lit(str_lit).unwrap().1, Token::StringLit("abc".into()));

        let str_lit = "\"A\\nA\"";
        assert_eq!(lexeme_string_lit(str_lit).unwrap().1, Token::StringLit("A\nA".into()));
    }
}

named!(lexeme_let<&str, Token>, do_parse!(tag!("let") >> (Token::Keyword(Keyword::Let))));
named!(lexeme_if<&str, Token>, do_parse!(tag!("if") >> (Token::Keyword(Keyword::If))));
named!(lexeme_else<&str, Token>, do_parse!(tag!("else") >> (Token::Keyword(Keyword::Else))));
named!(lexeme_then<&str, Token>, do_parse!(tag!("then") >>  (Token::Keyword(Keyword::Then))));
named!(lexeme_end<&str, Token>, do_parse!(tag!("end") >>  (Token::Keyword(Keyword::End))));
named!(lexeme_lambda<&str, Token>, do_parse!(tag!("lambda") >>  (Token::Keyword(Keyword::Lambda))));
named!(lexeme_do<&str, Token>, do_parse!(tag!("do") >>  (Token::Keyword(Keyword::Do))));
named!(lexeme_struct<&str, Token>, do_parse!(tag!("struct") >>  (Token::Keyword(Keyword::Struct))));
named!(lexeme_enum<&str, Token>, do_parse!(tag!("enum") >>  (Token::Keyword(Keyword::Enum))));

/*
lexeme int
    dec: [0-9]+
    oct: [0o|0O][0-7]+
    bin: [0b|0B][0-1]+
    hex: [0x|0X][0-9|a-f|A-F]+
*/
named!(lexeme_int_lit<&str, Token>, alt!(lexeme_bin_int_lit | lexeme_oct_int_lit | lexeme_hex_int_lit | lexeme_dec_int_lit));

fn lexeme_dec_int_lit(s: &str) -> IResult<&str, Token> {
    let (rest, dec_int_str) = take_while(|c: char| c.is_digit(10))(s)?;
    let dec_int = dec_int_str.parse().unwrap();
    let token = Token::IntLit {
        value: dec_int,
        base: IntBase::Dec,
    };
    IResult::Ok((rest, token))
}

fn lexeme_oct_int_lit(s: &str) -> IResult<&str, Token> {
    let (rest, oct_int_str) = preceded(alt((tag("0o"), tag("0O"))), take_while(|c: char| c.is_digit(8)))(s)?;
    let oct_int = i32::from_str_radix(oct_int_str, 8).unwrap();
    let token = Token::IntLit {
        value: oct_int,
        base: IntBase::Oct,
    };
    IResult::Ok((rest, token))
}

fn lexeme_bin_int_lit(s: &str) -> IResult<&str, Token> {
    let (rest, bin_int_str) = preceded(alt((tag("0b"), tag("0B"))), take_while(|c: char| c.is_digit(2)))(s)?;
    let bin_int = i32::from_str_radix(bin_int_str, 2).unwrap();
    let token = Token::IntLit {
        value: bin_int,
        base: IntBase::Bin,
    };
    IResult::Ok((rest, token))
}

fn lexeme_hex_int_lit(s: &str) -> IResult<&str, Token> {
    let (rest, hex_int_str) = preceded(alt((tag("0x"), tag("0X"))), take_while(|c: char| c.is_digit(16)))(s)?;
    let hex_int = i32::from_str_radix(hex_int_str, 16).unwrap();
    let token = Token::IntLit {
        value: hex_int,
        base: IntBase::Hex,
    };
    IResult::Ok((rest, token))
}

/*
lexeme bool
    true, false
*/
named!(lexeme_bool_lit<&str, Token>, alt!(lexeme_true_lit | lexeme_false_lit));
named!(lexeme_true_lit<&str, Token>, value!(Token::BoolLit(true), tag!("true")));
named!(lexeme_false_lit<&str, Token>, value!(Token::BoolLit(false), tag!("false")));

/*
lexeme ident
    [a-z|A-Z|_][a-z|A-Z|0-9|_]*
*/
fn lexeme_ident(s: &str) -> IResult<&str, Token> {
    let (rest, ident_str) = recognize(
        pair(
            alt((alpha1, tag("_"))),
            many0(alt((alphanumeric1, tag("_"))))
        )
    )(s)?;
    let token = Token::Ident(ident_str.into());
    Ok((rest, token))
}

/*
lexeme float
    [0-9]+\.[0-9]+
*/
fn lexeme_float_lit(s: &str) -> IResult<&str, Token> {
    let (rest, tuple) = tuple((digit1, tag("."), digit1))(s)?;
    let (t1, _, t2) = tuple;
    let float_str = format!("{}.{}", t1, t2);
    let float = f32::from_str(&float_str).unwrap();
    let token = Token::FloatLit(float.into());
    Ok((rest, token))
}

/*
lexeme_string
    Can contain any raw unescaped code point besides \ and "
    Matches the following escape sequences: \b, \f, \n, \r, \t, \", \\, \/
    Matches code points like Rust: \u{XXXX}, where XXXX can be up to 6
    hex characters
    an escape followed by whitespace consumes all whitespace between the
    escape and the next non-whitespace character
*/
fn lexeme_unicode(input: & str) -> IResult<&str, char> {
    let parse_hex = take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit());

    //lexeme u{XXXX}.
    let parse_delimited_hex = preceded(
        char('u'),
        delimited(char('{'), parse_hex, char('}')),
    );

    // In this case we take the hex bytes from parse_hex and attempt to
    // convert them to a u32.
    let parse_u32 = map_res(parse_delimited_hex, move |hex| u32::from_str_radix(hex, 16));

    //because not all u32 values are valid unicode code points, we have to fallibly
    // convert to char with from_u32.
    map_opt(parse_u32, |value| std::char::from_u32(value))(input)
}

/// lexeme an escaped character: \n, \t, \r, \u{00AC}, etc.
fn lexeme_escaped_char(input: &str) -> IResult<&str, char> {
    preceded(
        char('\\'),
        alt((
            lexeme_unicode,
            value('\n', char('n')),
            value('\r', char('r')),
            value('\t', char('t')),
            value('\u{08}', char('b')),
            value('\u{0C}', char('f')),
            value('\\', char('\\')),
            value('/', char('/')),
            value('"', char('"')),
        )),
    )(input)
}

/// lexeme a backslash, followed by any amount of whitespace. This is used later
/// to discard any escaped whitespace.
fn lexeme_escaped_whitespace(
    input: &str,
) -> IResult<&str, &str> {
    preceded(char('\\'), multispace1)(input)
}

/// lexeme a non-empty block of text that doesn't include \ or "
fn lexeme_literal(input: &str) -> IResult<&str, &str> {
    let not_quote_slash = is_not("\"\\");
    verify(not_quote_slash, |s: &str| !s.is_empty())(input)
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, PartialEq, Eq)]
enum StringFragment {
    Literal(String),
    EscapedChar(char),
    EscapedWhitespace,
}

/// Combine lexeme_literal, lexeme_escaped_whitespace, and lexeme_escaped_char
/// into a StringFragment.
fn lexeme_fragment(input: &str) -> IResult<&str, StringFragment> {
    alt((
        map(lexeme_literal, |s| StringFragment::Literal(s.into())),
        map(lexeme_escaped_char, StringFragment::EscapedChar),
        value(StringFragment::EscapedWhitespace, lexeme_escaped_whitespace),
    ))(input)
}

/// lexeme a string. Use a loop of lexeme_fragment and push all of the fragments
/// into an output string.
fn lexeme_string_lit(input: &str) -> IResult<&str, Token> {
    let build_string = fold_many0(
        lexeme_fragment,
        String::new(),
        |mut string, fragment| {
            match fragment {
                StringFragment::Literal(s) => string.push_str(&s),
                StringFragment::EscapedChar(c) => string.push(c),
                StringFragment::EscapedWhitespace => {}
            }
            string
        },
    );
    let (rest, str) = delimited(char('"'), build_string, char('"'))(input)?;
    Ok((rest, Token::StringLit(str)))
}