// Benchmarks using constant-size pre-generated input
// To run: cargo bench -- borsh_de_stable

use benchmarks::Block;
use borsh::BorshDeserialize;
use criterion::{criterion_group, criterion_main, Criterion};
use std::fs::File;
use std::io::prelude::*;

fn de_block(c: &mut Criterion) -> std::io::Result<()> {
    let path = format!("{}/res/block", env!("CARGO_MANIFEST_DIR"));
    let mut file = File::open(path)?;
    let mut buf = vec![];
    file.read_to_end(&mut buf)?;
    c.bench_function("borsh_de_stable", |b| {
        b.iter(|| Block::try_from_slice(&buf))
    });
    Ok(())
}

criterion_group!(de_benches, de_block);
criterion_main!(de_benches);
