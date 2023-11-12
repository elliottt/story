#[derive(Debug)]
pub enum Error {
    ExpectedToken {
        expected: super::Token,
        loc: super::Loc,
    },
    ExpectedAtom {
        expected: String,
        loc: super::Loc,
    },
    UnexpectedEof,
}

impl Error {
    pub fn display<'a>(self, source: &'a str) -> DisplayError<'a> {
        DisplayError { source, err: self }
    }
}

pub struct DisplayError<'a> {
    source: &'a str,
    err: Error,
}

impl<'a> std::fmt::Debug for DisplayError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl<'a> std::fmt::Display for DisplayError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.err {
            Error::ExpectedToken { expected, loc } => write!(f, "Expected {expected:?} at {loc:?}"),
            Error::ExpectedAtom { expected, loc } => {
                write!(f, "Expected atom `{expected}` at {loc:?}")
            }
            Error::UnexpectedEof => write!(f, "Unexpected end of file"),
        }
    }
}
