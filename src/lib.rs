mod arena;
mod context;
mod eval;
mod ground;
pub mod ir;
pub mod parser;
mod printing;

pub use context::{File, Files};
pub use ground::ground;
pub use printing::{Pretty, print_context};
