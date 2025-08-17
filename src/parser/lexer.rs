use ariadne::Span;
use std::u32;

use crate::{File, arena::Id};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token {
    LParen,
    RParen,
    Atom,
}

#[derive(Clone, Copy, Debug)]
pub struct Loc {
    pub file: Id<File>,
    pub start: u32,
    pub end: u32,
}

impl Default for Loc {
    fn default() -> Self {
        Self::none()
    }
}

impl Loc {
    pub fn new(file: Id<File>, start: u32, end: u32) -> Self {
        Loc { file, start, end }
    }

    pub fn none() -> Self {
        Loc {
            file: Id::none(),
            start: u32::MAX,
            end: u32::MAX,
        }
    }

    pub fn join(&self, other: Self) -> Self {
        if !self.exists() {
            other
        } else if !other.exists() || self.file != other.file {
            self.clone()
        } else {
            Loc {
                file: self.file,
                start: self.start.min(other.start),
                end: self.end.max(other.end),
            }
        }
    }

    pub fn range(&self) -> std::ops::Range<usize> {
        self.start.try_into().unwrap()..self.end.try_into().unwrap()
    }

    pub fn exists(&self) -> bool {
        self.start != u32::MAX
    }

    pub fn end(file: Id<File>, text: &str) -> Self {
        let start = text.len().try_into().unwrap();
        Loc {
            file,
            start,
            end: start,
        }
    }

    /// Only meant to be used with the same source that the [`Loc`] was created from.
    pub fn text<'a>(&self, text: &'a str) -> &'a str {
        let start: usize = self.start.try_into().unwrap();
        let end: usize = self.end.try_into().unwrap();
        let bytes = &text.as_bytes()[start..end];
        unsafe { std::str::from_utf8_unchecked(bytes) }
    }
}

impl Span for Loc {
    type SourceId = Id<File>;

    fn source(&self) -> &Self::SourceId {
        &self.file
    }

    fn start(&self) -> usize {
        self.start.try_into().unwrap()
    }

    fn end(&self) -> usize {
        self.end.try_into().unwrap()
    }
}

#[derive(Clone, Debug)]
pub struct Lexeme {
    pub token: Token,
    pub loc: Loc,
}

impl Lexeme {
    fn new(token: Token, loc: Loc) -> Self {
        Self { token, loc }
    }
}

pub(crate) struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    file: Id<File>,
    text: &'a str,
}

impl<'a> Lexer<'a> {
    pub(crate) fn new(file: Id<File>, text: &'a str) -> Self {
        Self {
            chars: text.char_indices().peekable(),
            file,
            text,
        }
    }

    fn consume(&mut self) {
        self.chars.next();
    }

    fn position(&mut self) -> usize {
        if let Some((pos, _)) = self.chars.peek() {
            *pos
        } else {
            self.text.len()
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }

    fn emit(&mut self, token: Token, start: usize) -> Option<Lexeme> {
        let start: u32 = start.try_into().unwrap();
        let end: u32 = self.position().try_into().unwrap();
        Some(Lexeme::new(token, Loc::new(self.file, start, end)))
    }

    fn skip_space_and_comments(&mut self) {
        let mut comment = false;
        while let Some(next) = self.peek() {
            if comment {
                if next == '\n' {
                    comment = false;
                }
                self.chars.next();
                continue;
            }

            if next.is_whitespace() {
                self.chars.next();
                continue;
            }

            if next == ';' {
                comment = true;
                continue;
            }

            break;
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Lexeme;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            self.skip_space_and_comments();
            let (start, next) = self.chars.next()?;
            match next {
                '(' => {
                    return self.emit(Token::LParen, start);
                }

                ')' => {
                    return self.emit(Token::RParen, start);
                }

                _ => {
                    while let Some(next) = self.peek() {
                        if next.is_whitespace() || "();".contains(next) {
                            break;
                        }
                        self.consume();
                    }
                    return self.emit(Token::Atom, start);
                }
            }
        }
    }
}
