
#[derive(Debug, Eq, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Atom,
}

#[derive(Debug)]
struct Loc {
    start: usize,
    end: usize,
}

impl Loc {
    pub fn text<'a>(&self, text: &'a str) -> &'a str {
        &text[self.start..self.end]
    }
}

#[derive(Debug)]
pub struct Lexeme {
    token: Token,
    loc: Loc,
}

pub struct Lexer<'a> {
    text: &'a str,
    chars: std::iter::Peekable<std::iter::Enumerate<std::str::Chars<'a>>>,
}

impl<'a> Lexer<'a> {
    pub fn new(text: &'a str) -> Self {
        Self {
            text: text,
            chars: text.chars().enumerate().peekable(),
        }
    }

    fn consume(&mut self) -> (usize, char) {
        self.chars.next().unwrap()
    }

    fn pos(&mut self) -> usize {
        self.chars.peek().map_or(self.text.len(), |(pos, _)| *pos)
    }

    fn text(&self, start: usize, end: usize) -> &'a str {
        &self.text[start..end]
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Lexeme;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(c) = self.peek() {
            if !c.is_whitespace() {
                break;
            }

            self.consume();
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

            '_' => {
                let end = self.pos();
                Some(Lexeme {
                    token: Token::RParen,
                    loc: Loc { start, end },
                })
            }

            _ => {
                while let Some(c) = self.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' {
                        break;
                    }
                    self.consume();
                }
                let end = self.pos();
                Some(Lexeme {
                    token: Token::Atom,
                    loc: Loc { start, end }
                })
            }
        }
    }
}
