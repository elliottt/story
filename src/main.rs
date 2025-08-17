use clap::Parser;
use std::collections::HashMap;

use story::parser;

#[derive(Parser, Debug)]
#[command()]
struct Args {
    #[arg(short = 'd', long = "domain")]
    domain: String,

    #[arg(short = 'p', long = "problem")]
    problem: String,
}

struct Sources<'a> {
    domain_path: &'a str,
    domain_source: ariadne::Source<&'a str>,

    problem_path: &'a str,
    problem_source: ariadne::Source<&'a str>,
}

impl<'a> Sources<'a> {
    fn new(
        domain_path: &'a str,
        domain_text: &'a str,
        problem_path: &'a str,
        problem_text: &'a str,
    ) -> Self {
        Sources {
            domain_path,
            domain_source: ariadne::Source::from(domain_text),
            problem_path,
            problem_source: ariadne::Source::from(problem_text),
        }
    }
}

impl<'a> ariadne::Cache<&'a str> for Sources<'a> {
    type Storage = &'a str;

    fn fetch(
        &mut self,
        id: &&'a str,
    ) -> Result<&ariadne::Source<Self::Storage>, impl std::fmt::Debug> {
        if *id == self.domain_path {
            Result::Ok(&self.domain_source)
        } else if *id == self.problem_path {
            Result::Ok(&self.problem_source)
        } else {
            anyhow::bail!("Unknown source `{}`", id)
        }
    }

    fn display<'b>(&self, id: &'b &'a str) -> Option<impl std::fmt::Display + 'b> {
        Some(*id)
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let mut domains = HashMap::new();
    let mut problem = None;

    let domain_path = args.domain.as_ref();
    let domain_text = std::fs::read_to_string(domain_path)?;

    let mut errs = Vec::new();

    match parser::parse_domain(domain_path, &domain_text) {
        Result::Ok(d) => {
            domains.insert(d.name.clone(), d);
        }
        Result::Err(es) => errs.extend(es),
    }

    let problem_path = args.problem.as_ref();
    let problem_text = std::fs::read_to_string(problem_path)?;

    // No point in parsing the problem if the domain failed
    if errs.is_empty() {
        match parser::parse_problem(problem_path, &problem_text, &mut domains) {
            Result::Ok(p) => {
                problem.replace(p);
            }
            Result::Err(es) => errs.extend(es),
        }
    }

    if !errs.is_empty() {
        let mut cache = Sources::new(
            domain_path,
            domain_text.as_ref(),
            problem_path,
            problem_text.as_ref(),
        );
        for e in errs {
            e.print(&mut cache)?;
        }
        anyhow::bail!("errors found");
    }

    for domain in domains {
        println!("{:#?}", domain);
    }
    println!("{:#?}", problem.take());

    Result::Ok(())
}
