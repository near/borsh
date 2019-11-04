use std::fs::File;
use std::io::prelude::*;
use rand::SeedableRng;

use benchmarks::{Generate, Block};
use borsh::BorshSerialize;

/// Creates and saves bench input to a ./res directory
fn main() -> std::io::Result<()> {
    let path = format!("{}/res/block", env!("CARGO_MANIFEST_DIR"));
    let mut file = File::create(&path)?;
    let mut rng = rand_xorshift::XorShiftRng::from_seed([0u8; 16]);
    let block = Block::generate(&mut rng);
    file.write_all(&block.try_to_vec()?)?;
    Ok(())
}
