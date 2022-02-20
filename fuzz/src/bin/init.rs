//! Initialize fuzz input in the target directory.

use ethnum_fuzz::Target;
use std::{
    env,
    fs::{self, File},
    io::Write as _,
    mem,
    path::Path,
    process,
};

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        eprintln!("USAGE: init DIRECTORY");
        process::exit(-1);
    }

    let dir = Path::new(&args[1]);
    println!("initializing directory {}/{{in,out}}", dir.display());
    fs::create_dir_all(dir.join("in")).unwrap();
    fs::create_dir_all(dir.join("out")).unwrap();

    let path = dir.join("in/seed");
    println!("writing seed {}", path.display());
    let mut seed = File::create(path).unwrap();
    let size = mem::size_of::<Target>();
    seed.write_all(&vec![0; size]).unwrap();
}
