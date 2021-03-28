pub mod token;
use token::*;
use nom::IResult;
use nom::bytes::complete::{take_while, tag};
use nom::sequence::{preceded, pair, tuple};
use nom::branch::alt;
use nom::combinator::recognize;
use nom::character::complete::{alpha1, alphanumeric1, digit1};
use std::str::FromStr;
use nom::multi::many0;

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
        let id1 = "_fuck_123__SHIT";
        assert_eq!(lexeme_ident(id1).unwrap().1, Token::Ident(id1.into()));

    }

    #[test]
    fn lexeme_float_lit_test() {
        let f = "114.514";
        assert_eq!(lexeme_float_lit(f).unwrap().1, Token::FloatLit(114.514.into()));
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