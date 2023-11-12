
mod errors;
mod lexer;
mod parser;
mod types;

pub use errors::Error;
pub use lexer::Lexer;
pub use types::*;

type Result<T> = std::result::Result<T, Error>;
