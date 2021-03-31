use nom::{AsBytes, Compare, CompareResult, ExtendInto, FindToken, FindSubstring, InputIter, Needed, InputLength, InputTake, AsChar, InputTakeAtPosition, IResult, Offset, ParseTo, Slice};
use std::cmp::min;
use std::iter::Enumerate;
use nom::error::{ParseError, ErrorKind};
use std::str::FromStr;
use std::ops::{Range, RangeFrom, RangeTo, RangeFull};
use nom::regex::internal::Char;

#[cfg(test)]
mod test {
    use super::*;
    use nom::bytes::complete::tag;
    use nom::error::Error;

    #[test]
    fn tag_test() {
        let cs = CharSequence::from("abc".as_bytes());
        let needed = CharSequence::from("a".as_bytes());
        // println!("{:?}", cs.compare(needed));
        let f = tag::<CharSequence<'_>, CharSequence<'_>, Error<CharSequence<'_>>>(needed)(cs).unwrap();
        assert_eq!(f.1, CharSequence::from_str("a"))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CharSequence<'s> {
    sequence: &'s[u8],
    position: Position,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Position {
    row: usize,
    column: usize
}

impl Default for Position {
    fn default() -> Self {
        Position { row: 0, column: 0}
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

impl <'t> CharSequence<'t> {
    fn from_str(str: &str) -> CharSequence {
        CharSequence::from(str.as_bytes())
    }

    fn from_str_pos(str: &str, position: Position) -> CharSequence {
        CharSequence::from_pos(str.as_bytes(), position)
    }

    fn from(u: &[u8]) -> CharSequence {
        CharSequence {
            sequence: u,
            position: Position::default(),
        }
    }

    fn from_pos(u: &[u8], position: Position) -> CharSequence {
        CharSequence {
            sequence: u,
            position,
        }
    }

    fn split_at(&self, count: usize) -> (CharSequence<'t>, CharSequence<'t>) {
        let (suffix, prefix) = self.sequence.take_split(count);
        let mut col = self.position.column;
        let mut row = self.position.row;
        prefix.to_vec().iter().for_each(|u: &u8| {
            if u.as_char() == '\n' { row += 1; col = 0; }
            else { col += 1; }
        });
        (CharSequence::from_pos(suffix, Position::from(row, col)), CharSequence::from_pos(prefix, self.position))
    }
}

impl <'s> AsBytes for CharSequence<'s> {
    fn as_bytes(&self) -> &[u8] {
        self.sequence
    }
}

impl <'s, 't> Compare<&'s [u8]> for CharSequence<'t> {
    fn compare(&self, to: &[u8]) -> CompareResult {
        compare_u8_slice(self.sequence, to)
    }

    fn compare_no_case(&self, to: &[u8]) -> CompareResult {
        let seq_with_no_case = self.sequence.to_ascii_lowercase();
        let to_with_no_case = to.to_ascii_lowercase();
        compare_u8_slice(seq_with_no_case.as_slice(), to_with_no_case.as_slice())
    }
}

impl Compare<&str> for CharSequence<'_> {
    fn compare(&self, t: &str) -> CompareResult {
        self.compare(t.as_bytes())
    }

    fn compare_no_case(&self, t: &str) -> CompareResult {
        self.compare_no_case(t.as_bytes())
    }
}

impl Compare<CharSequence<'_>> for CharSequence<'_> {
    fn compare(&self, t: CharSequence<'_>) -> CompareResult {
        self.compare(t.sequence)
    }

    fn compare_no_case(&self, t: CharSequence<'_>) -> CompareResult {
        self.compare_no_case(t.sequence)
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

impl <'t> ExtendInto for CharSequence<'t> {
    type Item = u8;
    type Extender = Vec<u8>;

    fn new_builder(&self) -> Self::Extender {
        Vec::new()
    }

    fn extend_into(&self, acc: &mut Self::Extender) {
        acc.extend_from_slice(self.sequence)
    }
}

impl <'t> FindToken<u8> for CharSequence<'t> {
    fn find_token(&self, token: u8) -> bool {
        self.sequence.find_token(token)
    }
}

impl <'t, 'a> FindToken<&'a u8> for CharSequence<'t> {
    fn find_token(&self, token: &'a u8) -> bool {
        self.sequence.find_token(*token)
    }
}

impl <'t> FindToken<char> for CharSequence<'t> {
    fn find_token(&self, token: char) -> bool {
        self.sequence.find_token(token)
    }
}

impl <'t, 'b> FindSubstring<&'b str> for CharSequence<'t> {
    fn find_substring(&self, substr: &'b str) -> Option<usize> {
        self.sequence.find_substring(substr)
    }
}

impl <'t, 'b> FindSubstring<&'b [u8]> for CharSequence<'t> {
    fn find_substring(&self, substr: &'b [u8]) -> Option<usize> {
        self.sequence.find_substring(substr)
    }
}

impl <'t> InputIter for CharSequence<'t> {
    type Item = &'t u8;
    type Iter = Enumerate<std::slice::Iter<'t, u8>>;
    type IterElem = std::slice::Iter<'t, u8>;

    fn iter_indices(&self) -> Self::Iter {
        self.sequence.iter().enumerate()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.sequence.iter()
    }

    fn position<P>(&self, predicate: P) -> Option<usize> where
        P: Fn(Self::Item) -> bool {
        self.sequence.iter().position(|b| predicate(b))
    }

    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        if self.sequence.len() >= count {
            Ok(count)
        } else {
            Err(Needed::new(count - self.sequence.len()))
        }
    }
}

impl <'t> InputLength for CharSequence<'t> {
    fn input_len(&self) -> usize {
        self.sequence.len()
    }
}

impl <'t> InputTake for CharSequence<'t> {
    fn take(&self, count: usize) -> Self {
        let seq = self.sequence.take(count);
        CharSequence::from_pos(seq, self.position)
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        self.split_at(count)
    }
}

impl <'t> InputTakeAtPosition for CharSequence<'t> {
    type Item = u8;

    fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E> where
        P: Fn(Self::Item) -> bool {
        match (0..self.sequence.len()).find(|b| predicate(self.sequence[*b])) {
            Some(i) => Ok(self.split_at(i)),
            None => Err(nom::Err::Incomplete(Needed::new(1))),
        }
    }

    fn split_at_position1<P, E: ParseError<Self>>(&self, predicate: P, e: ErrorKind) -> IResult<Self, Self, E> where
        P: Fn(Self::Item) -> bool {
        match (0..self.sequence.len()).find(|b| predicate(self.sequence[*b])) {
            Some(0) =>  Err(nom::Err::Error(E::from_error_kind(*self, e))),
            Some(i) => Ok(self.split_at(i)),
            None => Err(nom::Err::Incomplete(Needed::new(1))),
        }
    }

    fn split_at_position_complete<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E> where
        P: Fn(Self::Item) -> bool {
        match (0..self.sequence.len()).find(|b| predicate(self.sequence[*b])) {
            Some(i) => Ok(self.split_at(i)),
            None => Ok(self.split_at(self.input_len())),
        }
    }

    fn split_at_position1_complete<P, E: ParseError<Self>>(&self, predicate: P, e: ErrorKind) -> IResult<Self, Self, E> where
        P: Fn(Self::Item) -> bool {
        match (0..self.sequence.len()).find(|b| predicate(self.sequence[*b])) {
            Some(0) => Err(nom::Err::Error(E::from_error_kind(*self, e))),
            Some(i) => Ok(self.split_at(i)),
            None => {
                if self.sequence.is_empty() {
                    Err(nom::Err::Error(E::from_error_kind(*self, e)))
                } else {
                    Ok(self.split_at(self.input_len()))
                }
            }
        }
    }
}

impl <'t> Offset for CharSequence<'t> {
    fn offset(&self, second: &Self) -> usize {
        second.sequence.as_ptr() as usize - self.sequence.as_ptr() as usize
    }
}

impl <'t, R: FromStr> ParseTo<R> for CharSequence<'t> {
    fn parse_to(&self) -> Option<R> {
        self.sequence.parse_to()
    }
}

impl <'t> Slice<Range<usize>> for CharSequence<'t> {
    fn slice(&self, range: Range<usize>) -> Self {
        let (start, _) = self.split_at(range.start);
        let (_, need) = start.split_at(range.end - range.start);
        need
    }
}

impl <'t> Slice<RangeFrom<usize>> for CharSequence<'t> {
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        self.slice(range.start..self.sequence.len())
    }
}

impl <'t> Slice<RangeTo<usize>> for CharSequence<'t> {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        self.slice(0..range.end)
    }
}

impl <'t> Slice<RangeFull> for CharSequence<'t> {
    fn slice(&self, range: RangeFull) -> Self {
        self.slice(0..self.sequence.len())
    }
}