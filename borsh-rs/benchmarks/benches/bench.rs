use benchmarks::{Account, Block, BlockHeader, Generate, SignedTransaction};
use borsh::{BorshDeserialize, BorshSerialize};
use rand::SeedableRng;
use serde::{Deserialize as SerdeDeserialize, Serialize as SerdeSerialize};
use speedy::Endianness;
use speedy::{Readable, Writable};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

fn ser_obj<T>(group_name: &str, num_samples: usize, c: &mut Criterion)
where
    for<'a> T: Generate
        + BorshSerialize
        + BorshDeserialize
        + SerdeSerialize
        + SerdeDeserialize<'a>
        + Readable<'a, speedy::Endianness>
        + Writable<speedy::Endianness>
        + 'static,
{
    let mut rng = rand_xorshift::XorShiftRng::from_seed([0u8; 16]);
    let mut group = c.benchmark_group(group_name);

    let objects: Vec<_> = (0..num_samples).map(|_| T::generate(&mut rng)).collect();
    let borsh_datas: Vec<Vec<u8>> = objects.iter().map(|t| t.try_to_vec().unwrap()).collect();
    let borsh_sizes: Vec<_> = borsh_datas.iter().map(|d| d.len()).collect();

    for i in 0..objects.len() {
        let size = borsh_sizes[i];
        let obj = &objects[i];

        let benchmark_param_display = format!("idx={}; size={}", i, size);

        group.throughput(Throughput::Bytes(size as u64));
        group.bench_with_input(
            BenchmarkId::new("cbor", benchmark_param_display.clone()),
            obj,
            |b, d| {
                b.iter(|| serde_cbor::to_vec(d).unwrap());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("bincode", benchmark_param_display.clone()),
            obj,
            |b, d| {
                b.iter(|| bincode::serialize(d).unwrap());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("borsh", benchmark_param_display.clone()),
            obj,
            |b, d| {
                b.iter(|| d.try_to_vec().unwrap());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("speedy", benchmark_param_display),
            obj,
            |b, d| {
                b.iter(|| d.write_to_vec(Endianness::LittleEndian).unwrap());
            },
        );
    }
    group.finish();
}

fn de_obj<T>(group_name: &str, num_samples: usize, c: &mut Criterion)
where
    for<'a> T: Generate
        + BorshSerialize
        + BorshDeserialize
        + SerdeSerialize
        + SerdeDeserialize<'a>
        + Readable<'a, speedy::Endianness>
        + Writable<speedy::Endianness>
        + 'static,
{
    let mut rng = rand_xorshift::XorShiftRng::from_seed([0u8; 16]);
    let mut group = c.benchmark_group(group_name);

    let objects: Vec<_> = (0..num_samples).map(|_| T::generate(&mut rng)).collect();
    let cbor_datas: Vec<Vec<u8>> = objects
        .iter()
        .map(|t| serde_cbor::to_vec(t).unwrap())
        .collect();
    let bincode_datas: Vec<Vec<u8>> = objects
        .iter()
        .map(|t| bincode::serialize(t).unwrap())
        .collect();
    let borsh_datas: Vec<Vec<u8>> = objects.iter().map(|t| t.try_to_vec().unwrap()).collect();
    let speedy_datas: Vec<Vec<u8>> = objects
        .iter()
        .map(|t| t.write_to_vec(Endianness::LittleEndian).unwrap())
        .collect();

    let borsh_sizes: Vec<_> = borsh_datas.iter().map(|d| d.len()).collect();

    for i in 0..objects.len() {
        let size = borsh_sizes[i];
        let cbor_data = &cbor_datas[i];
        let bincode_data = &bincode_datas[i];
        let borsh_data = &borsh_datas[i];
        let speedy_data = &speedy_datas[i];

        let benchmark_param_display = format!("idx={}; size={}", i, size);

        group.throughput(Throughput::Bytes(size as u64));
        group.bench_with_input(
            BenchmarkId::new("cbor", benchmark_param_display.clone()),
            cbor_data,
            |b, d| {
                b.iter(|| serde_cbor::from_slice::<T>(&d).unwrap());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("bincode", benchmark_param_display.clone()),
            bincode_data,
            |b, d| {
                b.iter(|| bincode::deserialize::<T>(&d).unwrap());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("borsh", benchmark_param_display.clone()),
            borsh_data,
            |b, d| {
                b.iter(|| T::try_from_slice(&d).unwrap());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("speedy", benchmark_param_display),
            speedy_data,
            |b, d| {
                b.iter(|| T::read_from_buffer(Endianness::LittleEndian, &d).unwrap());
            },
        );
    }
    group.finish();
}

fn ser_account(c: &mut Criterion) {
    ser_obj::<Account>("ser_account", 10, c);
}

fn ser_transaction(c: &mut Criterion) {
    ser_obj::<SignedTransaction>("ser_transaction", 10, c);
}

fn ser_header(c: &mut Criterion) {
    ser_obj::<BlockHeader>("ser_header", 10, c);
}

fn ser_block(c: &mut Criterion) {
    ser_obj::<Block>("ser_block", 10, c);
}

fn de_account(c: &mut Criterion) {
    de_obj::<Account>("de_account", 10, c);
}

fn de_transaction(c: &mut Criterion) {
    de_obj::<SignedTransaction>("de_transaction", 10, c);
}

fn de_header(c: &mut Criterion) {
    de_obj::<BlockHeader>("de_header", 10, c);
}

fn de_block(c: &mut Criterion) {
    de_obj::<Block>("de_block", 10, c);
}

criterion_group!(
    ser_benches,
    ser_account,
    ser_transaction,
    ser_header,
    ser_block
);
criterion_group!(de_benches, de_account, de_transaction, de_header, de_block);
criterion_main!(ser_benches, de_benches);
