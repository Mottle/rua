use nom::{AsBytes, Compare, CompareResult, ExtendInto, FindToken, FindSubstring, InputIter, Needed, InputLength, InputTake, AsChar, InputTakeAtPosition, IResult, Offset, ParseTo, Slice};
use std::cmp::min;
use std::iter::Enumerate;
use nom::error::{ParseError, ErrorKind};
use std::str::FromStr;
use std::ops::{Range, RangeFrom, RangeTo, RangeFull};

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
        let (prefix, suffix) = self.sequence.take_split(count);
        let mut col = self.position.column;
        let mut row = self.position.row;
        prefix.to_vec().iter().for_each(|u: &u8| {
            if u.as_char() == '\n' { row += 1; col = 0; }
            if u.as_char() == ' ' || u.as_char() == '\t' || u.as_char() == '\r' {
                col += 1;
            }
        });
        (CharSequence::from_pos(prefix, self.position), CharSequence::from_pos(suffix, Position::from(row, col)))
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

fn compare_u8_slice(a: &[u8], b: &[u8]) -> CompareResult {
    let a_len = a.len();
    let b_len = b.len();
    let length = min(a_len, b_len);
    let a_slice = &a[0..length];
    let b_slice = &b[0..length];
    if a_slice == b_slice {
        return if a_len == b_len {
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
        let (_, start) = self.split_at(range.start);
        let (need, _) = start.split_at(range.end - range.start);
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