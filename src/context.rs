use ariadne::{Cache, Source};

use crate::arena::{Id, Named, NamedArena};

pub type Files = NamedArena<File>;

impl Cache<Id<File>> for Files {
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
