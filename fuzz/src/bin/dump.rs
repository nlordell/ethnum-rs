//! Dump crash data.

use ethnum_fuzz::Target;
use std::{env, fs, process};

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        eprintln!("USAGE: dump PATH");
        process::exit(-1);
    }

    let bytes = fs::read(&args[1]).unwrap();
    let target = Target::load(&bytes).unwrap();
    println!("{:#?}", target);

    ethnum_fuzz::fuzz(&bytes).unwrap();
}
