use ariadne::{Cache, Source};

use crate::arena::{Id, Named, NamedArena};

pub struct Context {
    pub files: NamedArena<File>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            files: NamedArena::new(),
        }
    }

    /// TODO: remove this by making the errors the parser returns into plain old values that can be
    /// used to re-create the report values later. This would mean that the files arena could be
    /// mutably borrowed instead, avoiding the copy here.
    pub fn file_cache(&self) -> NamedArena<File> {
        self.files.clone()
    }
}

impl Cache<Id<File>> for NamedArena<File> {
    type Storage = String;

    fn fetch(&mut self, id: &Id<File>) -> Result<&Source<Self::Storage>, impl std::fmt::Debug> {
        if !id.exists() {
            Result::Err("No such file")
        } else {
            Result::Ok(&self[*id].source)
        }
    }

    fn display<'a>(&self, id: &'a Id<File>) -> Option<impl std::fmt::Display + 'a> {
        if !id.exists() {
            return None;
        }

        Some(self[*id].path.clone())
    }
}

#[derive(Clone)]
pub struct File {
    pub path: String,
    pub source: Source,
}

impl Named for File {
    fn name(&self) -> &str {
        &self.path
    }
}

impl File {
    pub fn new(path: String) -> std::io::Result<File> {
        let text = std::fs::read_to_string(&path)?;
        let source = Source::from(text);
        std::io::Result::Ok(File { path, source })
    }
}
