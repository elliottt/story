use clap::Parser;

use story::{File, Files, ground, ir::Context, parser, print_context, planner::Graph};

#[derive(Parser, Debug)]
#[command()]
struct Args {
    #[arg(short = 'd', long = "domain")]
    domain: String,

    #[arg(short = 'p', long = "problem")]
    problem: String,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let mut files = Files::new();
    let mut context = Context::default();
    let domain_file = files.add(File::new(args.domain)?);
    let problem_file = files.add(File::new(args.problem)?);

    let mut errs = Vec::new();

    match parser::parse_domain(&files, domain_file, &mut context) {
        Result::Ok(_) => {}
        Result::Err(es) => errs.extend(es),
    }

    // No point in parsing the problem if the domain failed
    if errs.is_empty() {
        match parser::parse_problem(&files, problem_file, &mut context) {
            Result::Ok(_) => {}
            Result::Err(es) => errs.extend(es),
        }
    }

    if !errs.is_empty() {
        // If the errors produced by the parser weren't `Report<'a>`, it would be fine to re-borrow
        // the files here as the cache as well. Replacing the errors with structured ones that get
        // translated here would allow this.
        let mut cache = files.clone();
        for e in errs {
            e.print(&mut cache)?;
        }
    } else {
        ground(&mut context);
        println!("{}", print_context(&context));
        println!("{:#?}", Graph::build(&mut context));
    }

    Result::Ok(())
}
