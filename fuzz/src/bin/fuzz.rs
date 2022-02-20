//! AFL fuzzing target executable.

fn main() {
    afl::fuzz!(|data: &[u8]| {
        let _ = ethnum_fuzz::fuzz(data);
    });
}
