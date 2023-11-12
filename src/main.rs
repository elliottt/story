mod pddl;

fn main() {
    let text = "(hello)";
    for token in pddl::Lexer::new(text) {
        println!("token: {:?}, text: '{}'", token, token.text(text));
    }

    let text = "( hello ;; foo bar baz \n  )";
    for token in pddl::Lexer::new(text) {
        println!("token: {:?}, text: '{}'", token, token.text(text));
    }

    let text = "(define (problem foo) (:domain foo))";
    let prob = pddl::Parser::new(text)
        .problem()
        .map_err(|e| e.display(text))
        .unwrap();
    println!("prob = {prob:#?}");
}
