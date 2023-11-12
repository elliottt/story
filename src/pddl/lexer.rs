#[derive(Debug, Eq, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Atom,
}

#[derive(Debug)]
pub struct Loc {
    pub start: usize,
    pub end: usize,
}

impl Loc {
    pub fn text<'a>(&self, text: &'a str) -> &'a str {
        &text[self.start..self.end]
    }
}

#[derive(Debug)]
pub struct Lexeme {
    pub token: Token,
    pub loc: Loc,
}

impl Lexeme {
    pub fn text<'a>(&self, text: &'a str) -> &'a str {
        self.loc.text(text)
    }
}

pub struct Lexer<'a> {
    pub text: &'a str,
    chars: std::iter::Peekable<std::iter::Enumerate<std::str::Chars<'a>>>,
}

impl<'a> Lexer<'a> {
    pub fn new(text: &'a str) -> Self {
        Self {
            text,
            chars: text.chars().enumerate().peekable(),
        }
    }

    fn consume(&mut self) -> (usize, char) {
        self.chars.next().unwrap()
    }

    fn pos(&mut self) -> usize {
        self.chars.peek().map_or(self.text.len(), |(pos, _)| *pos)
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Lexeme;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(c) = self.peek() {
            if c == ';' {
                while let Some(c) = self.peek() {
                    if c == '\n' {
                        break;
                    }
                    self.consume();
                }
                continue;
            }

            if c.is_whitespace() {
                self.consume();
                continue;
            }

            break;
        }

        if self.peek().is_none() {
            return None;
        }

        let (start, c) = self.consume();
        match c {
            '(' => {
                let end = self.pos();
                Some(Lexeme {
                    token: Token::LParen,
                    loc: Loc { start, end },
                })
            }

            ')' => {
                let end = self.pos();
                Some(Lexeme {
                    token: Token::RParen,
                    loc: Loc { start, end },
                })
            }

            _ => {
                while let Some(c) = self.peek() {
                    const OTHERS: &str = "();";
                    if c.is_whitespace() || OTHERS.contains(c) {
                        break;
                    }
                    self.consume();
                }
                let end = self.pos();
                Some(Lexeme {
                    token: Token::Atom,
                    loc: Loc { start, end },
                })
            }
        }
    }
}

#[test]
fn test_comments() {
    let a = Vec::from_iter(Lexer::new("(hello)").map(|t| t.token));
    let b = Vec::from_iter(Lexer::new("(;hello\nhello;)\n)").map(|t| t.token));
    assert_eq!(a, b);
}

#[test]
fn test_nested() {
    let a = Vec::from_iter(Lexer::new("(a (b c) d)").map(|t| t.token));
    assert_eq!(
        a,
        [
            Token::LParen,
            Token::Atom,
            Token::LParen,
            Token::Atom,
            Token::Atom,
            Token::RParen,
            Token::Atom,
            Token::RParen,
        ]
    );
}

#[test]
fn test_text() {
    let text = "(a;foobarbaz\nb hello-world)";
    let a = Vec::from_iter(Lexer::new(text));
    assert_eq!(a.len(), 5);
    assert_eq!(a[1].text(text), "a");
    assert_eq!(a[3].text(text), "hello-world");
    assert_eq!(a[4].text(text), ")");
}
