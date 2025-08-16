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

    let text = std::fs::read_to_string(args.domain)?;
    let domain = parser::parse_domain(&text)?;

    println!("{:#?}", domain);

    Result::Ok(())
}
