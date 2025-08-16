use story::parser;

use clap::Parser;

#[derive(Parser, Debug)]
#[command()]
struct Args {
    #[arg(short = 'd', long = "domain")]
    domain: String,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    println!("Using domain: {}", args.domain);

    let path = args.domain.as_ref();
    let text = std::fs::read_to_string(path)?;
    let domain = match parser::parse_domain(path, &text) {
        Result::Ok(d) => d,
        Result::Err(es) => {
            let source = ariadne::Source::from(&text);
            for e in es {
                e.print((path, &source))?;
            }
            return Result::Ok(());
        }
    };

    println!("{:#?}", domain);

    Result::Ok(())
}
