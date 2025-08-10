mod lexer;
mod parser;

pub fn lexer<'a>(bytes: &'a str) -> impl Iterator<Item = lexer::Lexeme> + 'a {
    lexer::Lexer::new(bytes)
}

/// Parse a domain specification out of the bytes given.
pub fn parse_domain<'a>(bytes: &'a str) -> parser::Result<crate::ir::Domain> {
    let mut parser = parser::Parser::new(bytes);

    let mut domain = crate::ir::Domain {
        name: String::new(),
    };

    parser.list(|p| {
        p.keyword("define")?;

        p.list(|p| {
            p.keyword("domain")?;
            domain.name = String::from(p.atom()?);
            Result::Ok(())
        })?;

        Result::Ok(())
    })?;

    Result::Ok(domain)
}

#[test]
fn test_lexer_empty() {
    let ts = Vec::from_iter(lexer(""));
    assert!(ts.is_empty());
}

#[test]
fn test_lexer_parens() {
    let ts = Vec::from_iter(lexer("()())").map(|lexeme| lexeme.token));

    use lexer::Token::*;
    assert_eq!(ts, vec![LParen, RParen, LParen, RParen, RParen]);
}

#[test]
fn test_lexer_atoms() {
    let ts = Vec::from_iter(lexer("foo bar baz? :bonk").map(|lexeme| lexeme.token));

    use lexer::Token::*;
    assert_eq!(ts, vec![Atom, Atom, Atom, Atom]);
}

#[test]
fn test_source_extraction() {
    let text = "foo bar (baz?) :bonk";
    let ts = Vec::from_iter(lexer(text));

    assert_eq!("foo", ts[0].loc.text(text));
    assert_eq!("bar", ts[1].loc.text(text));
    assert_eq!("baz?", ts[3].loc.text(text));
    assert_eq!(":bonk", ts[5].loc.text(text));
}

#[test]
fn test_source_extraction_comments() {
    let text = "foo ;; foo bar ()\n  bar (baz?) :bonk";
    let ts = Vec::from_iter(lexer(text));

    assert_eq!("foo", ts[0].loc.text(text));
    assert_eq!("bar", ts[1].loc.text(text));
    assert_eq!("(", ts[2].loc.text(text));
    assert_eq!("baz?", ts[3].loc.text(text));
    assert_eq!(")", ts[4].loc.text(text));
    assert_eq!(":bonk", ts[5].loc.text(text));
}

#[test]
fn test_empty_domain() {
    let text = "(define (domain foo))";
    let result = parse_domain(text).expect("Failed to parse domain");
    assert_eq!("foo", result.name);
}
