use nom::{AsBytes, Compare, CompareResult, ExtendInto, FindToken, FindSubstring, InputIter, Needed, InputLength, InputTake, InputTakeAtPosition, IResult, Offset, ParseTo, Slice};
use std::cmp::min;
use std::iter::{Enumerate, Copied};
use nom::error::{ParseError, ErrorKind};
use std::str::FromStr;
use std::ops::{Range, RangeFrom, RangeTo, RangeFull};
use std::str::{CharIndices, Chars};
// #[cfg(test)]
// mod test {
//     use super::*;
//     use nom::bytes::complete::{tag, take_while};
//     use nom::error::Error;
//
//     #[test]
//     fn tag_test() {
//         let cs = CharSequence::from("abc".as_bytes());
//         let f = tag::<&str, CharSequence<'_>, Error<CharSequence<'_>>>("a")(cs).unwrap();
//         assert_eq!(f.1.to_string(), "a")
//     }
//
//     #[test]
//     fn take_while_test() {
//         let cs = CharSequence::from("abc abc".as_bytes());
//         let f = take_while::<fn(u8) -> bool, CharSequence<'_>, Error<CharSequence<'_>>>(|c: u8| c.is_ascii_alphabetic())(cs).unwrap();
//         assert_eq!(f.1.to_string(), "abc")
//     }
// }

trait CalPosition {
    fn cal_pos(&self, now_pos: Position, count: usize) -> Position;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Sequence<T> {
    offset: usize,
    span: T,
    position: Position,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Position {
    row: usize,
    column: usize
}

impl Default for Position {
    fn default() -> Self {
        Position::from(0, 0)
    }
}

impl Position {
    fn from(row: usize, col: usize) -> Position {
        Position {
            row,
            column: col,
        }
    }
}

impl <T> Sequence<T> {
    fn from(t: T) -> Sequence<T> {
        Sequence::from_pos_offset(t, Position::default(), 0)
    }

    fn from_pos_offset(t: T, position: Position, offset: usize) -> Sequence<T> {
        Sequence {
            offset,
            span: t,
            position,
        }
    }
}

impl <T :  ToString> ToString for Sequence<T> {
    fn to_string(&self) -> String {
        self.span.to_string()
    }
}

impl <T :  AsBytes> AsBytes for Sequence<T> {
    fn as_bytes(&self) -> &[u8] {
        self.span.as_bytes()
    }
}

impl <'t, T :  AsBytes> Compare<&'t [u8]> for Sequence<T> {
    fn compare(&self, to: &[u8]) -> CompareResult {
        compare_u8_slice(self.as_bytes(), to)
    }

    fn compare_no_case(&self, to: &[u8]) -> CompareResult {
        let seq_with_no_case = self.as_bytes().to_ascii_lowercase();
        let to_with_no_case = to.to_ascii_lowercase();
        compare_u8_slice(seq_with_no_case.as_slice(), to_with_no_case.as_slice())
    }
}

impl <T :  AsBytes> Compare<&str> for Sequence<T> {
    fn compare(&self, t: &str) -> CompareResult {
        self.compare(t.as_bytes())
    }

    fn compare_no_case(&self, t: &str) -> CompareResult {
        self.compare_no_case(t.as_bytes())
    }
}

impl <T :  AsBytes> Compare<Sequence<T>> for Sequence<T> {
    fn compare(&self, t: Sequence<T>) -> CompareResult {
        self.compare(t.as_bytes())
    }

    fn compare_no_case(&self, t: Sequence<T>) -> CompareResult {
        self.compare_no_case(t.as_bytes())
    }
}

fn compare_u8_slice(base: &[u8], to: &[u8]) -> CompareResult {
    let base_len = base.len();
    let to_len = to.len();
    let length = min(base_len, to_len);
    let base_slice = &base[0..length];
    let to_slice = &to[0..length];
    if base_slice == to_slice {
        return if base_len >= to_len {
            CompareResult::Ok
        } else {
            CompareResult::Incomplete
        }
    }
    CompareResult::Error
}

impl <'t> ExtendInto for Sequence<&'t str> {
    type Item = char;
    type Extender = String;

    fn new_builder(&self) -> Self::Extender {
        String::new()
    }

    fn extend_into(&self, acc: &mut Self::Extender) {
        self.span.extend_into(acc)
    }
}

impl <'t> ExtendInto for Sequence<&'t [u8]> {
    type Item = u8;
    type Extender = Vec<u8>;

    fn new_builder(&self) -> Self::Extender {
        Vec::new()
    }

    fn extend_into(&self, acc: &mut Self::Extender) {
        self.span.extend_into(acc)
    }
}

impl <Span: FindToken<Token>, Token> FindToken<Token> for Sequence<Span> {
    fn find_token(&self, token: Token) -> bool {
        self.span.find_token(token)
    }
}

impl <'b, Span : FindSubstring<&'b str>> FindSubstring<&'b str> for Sequence<Span> {
    fn find_substring(&self, substr: &'b str) -> Option<usize> {
        self.span.find_substring(substr)
    }
}

impl <'t> InputIter for Sequence<&'t str> {
    type Item = char;
    type Iter = CharIndices<'t>;
    type IterElem = Chars<'t>;

    fn iter_indices(&self) -> Self::Iter {
        self.span.iter_indices()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.span.iter_elements()
    }

    fn position<P>(&self, predicate: P) -> Option<usize> where
        P: Fn(Self::Item) -> bool {
        self.span.position(predicate)
    }

    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        self.span.slice_index(count)
    }
}

impl <'t> InputIter for Sequence<&'t [u8]> {
    type Item = u8;
    type Iter = Enumerate<Self::IterElem>;
    type IterElem = Copied<std::slice::Iter<'t, u8>>;

    fn iter_indices(&self) -> Self::Iter {
        self.span.iter_indices()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.span.iter_elements()
    }

    fn position<P>(&self, predicate: P) -> Option<usize> where
        P: Fn(Self::Item) -> bool {
        self.span.position(predicate)
    }

    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        self.span.slice_index(count)
    }
}

impl <T : InputLength> InputLength for Sequence<T> {
    fn input_len(&self) -> usize {
        self.span.input_len()
    }
}

impl <T> InputTake for Sequence<T>
    where Self: Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>{
    fn take(&self, count: usize) -> Self {
        self.slice(..count)
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        (self.slice(count..), self.slice(..count))
    }
}

impl <T> InputTakeAtPosition for Sequence<T>
    where  T: InputTakeAtPosition + InputLength + InputIter,
           Self: Slice<RangeFrom<usize>> + Slice<RangeTo<usize>> + Clone {
    type Item = <T as InputIter>::Item;

    fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E> where
        P: Fn(Self::Item) -> bool {
        match self.span.position(predicate) {
            Some(n) => Ok(self.take_split(n)),
            None => Err(nom::Err::Incomplete(nom::Needed::new(1))),
        }
    }

    fn split_at_position1<P, E: ParseError<Self>>(&self, predicate: P, e: ErrorKind) -> IResult<Self, Self, E> where
        P: Fn(Self::Item) -> bool {
        match self.span.position(predicate) {
            Some(0) => Err(nom::Err::Error(E::from_error_kind(self.clone(), e))),
            Some(n) => Ok(self.take_split(n)),
            None => Err(nom::Err::Incomplete(nom::Needed::new(1))),
        }
    }

    fn split_at_position_complete<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E> where
        P: Fn(Self::Item) -> bool {
        match self.split_at_position(predicate) {
            Err(nom::Err::Incomplete(_)) => Ok(self.take_split(self.input_len())),
            res => res,
        }
    }

    fn split_at_position1_complete<P, E: ParseError<Self>>(&self, predicate: P, e: ErrorKind) -> IResult<Self, Self, E> where
        P: Fn(Self::Item) -> bool {
        match self.span.position(predicate) {
            Some(0) => Err(nom::Err::Error(E::from_error_kind(self.clone(), e))),
            Some(n) => Ok(self.take_split(n)),
            None => {
                if self.span.input_len() == 0 {
                    Err(nom::Err::Error(E::from_error_kind(self.clone(), e)))
                } else {
                    Ok(self.take_split(self.input_len()))
                }
            }
        }
    }
}

impl <T> Offset for Sequence<T> {
    fn offset(&self, second: &Self) -> usize {
        second.offset - self.offset
    }
}

impl <T : ParseTo<R>, R: FromStr> ParseTo<R> for Sequence<T> {
    fn parse_to(&self) -> Option<R> {
        self.span.parse_to()
    }
}

impl <T> Slice<Range<usize>> for Sequence<T>
    where T : Slice<Range<usize>> + CalPosition {
    fn slice(&self, range: Range<usize>) -> Self {
        let slice = self.span.slice(range.start..range.end);
        let pos = self.span.cal_pos(self.position, range.start);
        Sequence::from_pos_offset(slice, pos, self.offset + range.start)
    }
}

impl <T> Slice<RangeFrom<usize>> for Sequence<T>
    where T : Slice<Range<usize>> + CalPosition + InputLength {
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        self.slice(range.start..self.span.input_len())
    }
}

impl <T> Slice<RangeTo<usize>> for Sequence<T>
    where T : Slice<Range<usize>> + CalPosition + InputLength {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        self.slice(0..range.end)
    }
}

impl <T> Slice<RangeFull> for Sequence<T>
    where T : Slice<Range<usize>> + CalPosition + InputLength + Clone {
    fn slice(&self, _: RangeFull) -> Self {
        self.clone()
    }
}