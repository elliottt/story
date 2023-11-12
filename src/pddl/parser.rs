use super::lexer::Lexer;
use super::types::Problem;

pub struct Parser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(text: &'a str) -> Self {
        Self {
            lexer: Lexer::new(text),
        }
    }

    pub fn problem(&mut self) -> super::Result<Problem> {
        todo!()
    }
}
