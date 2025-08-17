use clap::Parser;
use std::collections::HashMap;

use story::parser;
use story::{Context, File};

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

    let mut context = Context::new();
    let domain_file = context.files.add(File::new(args.domain)?);
    let problem_file = context.files.add(File::new(args.problem)?);

    let mut domains = HashMap::new();
    let mut problem = None;
    let mut errs = Vec::new();

    match parser::parse_domain(&context, domain_file) {
        Result::Ok(d) => {
            domains.insert(d.name.clone(), d);
        }
        Result::Err(es) => errs.extend(es),
    }

    // No point in parsing the problem if the domain failed
    if errs.is_empty() {
        match parser::parse_problem(&context, problem_file, &mut domains) {
            Result::Ok(p) => {
                problem.replace(p);
            }
            Result::Err(es) => errs.extend(es),
        }
    }

    if !errs.is_empty() {
        let mut cache = context.file_cache();
        for e in errs {
            e.print(&mut cache)?;
        }
    } else {
        for domain in domains {
            println!("{:#?}", domain);
        }
        println!("{:#?}", problem.take());
    }

    Result::Ok(())
}
