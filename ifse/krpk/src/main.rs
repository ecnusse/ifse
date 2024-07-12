use std::fs;

use clap::Parser as CLIParser;
use krpk::FuzzSolver;

#[derive(Debug, CLIParser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long, default_value = None)]
    timeout: Option<usize>,
    input: String,
}

fn main() {
    let args = Args::parse();

    let mut solver = FuzzSolver::new();

    if let Some(timeout) = args.timeout {
        solver.set_fuzzer_option("max_time_in_milliseconds", timeout.to_string().as_str());
    }

    let input_text = fs::read_to_string(args.input).unwrap();
    let smt_script = krpk::smtparser::parse_str(input_text.as_str()).unwrap();
    let result = solver.solve(&smt_script).unwrap();
    println!("{:?}", result);
}
