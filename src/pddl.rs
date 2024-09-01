mod errors;
mod lexer;
mod parser;
mod types;

pub use errors::{DisplayError, Error};
pub use lexer::{Lexeme, Lexer, Loc, Token};
pub use parser::Parser;
pub use types::*;

pub type Result<T> = std::result::Result<T, Error>;
