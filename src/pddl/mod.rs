
mod errors;
mod lexer;
mod parser;
mod types;

pub use types::*;

type Result<T> = std::result::Result<T, errors::Error>;

pub fn parse_problem(text: &'a) -> Result<Problem> {
    parser::Parser::new(text).problem()
}
