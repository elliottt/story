
mod pddl;

fn main() {

    for token in pddl::lexer::Lexer::new("(hello)") {
        println!("token: {:?}", token);
    }

    for token in pddl::lexer::Lexer::new("( hello   )") {
        println!("token: {:?}", token);
    }

}
