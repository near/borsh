use bencher::{benchmark_group, benchmark_main, Bencher};
use benchmarks::{BlockHeader, Generate};
use borsh::{Deserializable, Serializable};
use lazy_static::lazy_static;
use speedy::Endianness;
use speedy::{Readable, Writable};

fn generator<T: Generate>(num: usize) -> Vec<T> {
    let mut res = vec![];
    for _ in 0..num {
        res.push(T::generate());
    }
    res
}

lazy_static! {
    static ref HEADERS: Vec<BlockHeader> = { generator::<BlockHeader>(1000) };
}

fn ser_block_header_borsh(bench: &mut Bencher) {
    let mut next = 0usize;
    bench.iter(move || {
        let value = &HEADERS[next];
        next += 1;
        next %= HEADERS.len();
        value.try_to_vec().unwrap();
    });
}

fn ser_block_header_bincode(bench: &mut Bencher) {
    let mut next = 0usize;
    bench.iter(move || {
        let value = &HEADERS[next];
        next += 1;
        next %= HEADERS.len();
        bincode::serialize(&value).unwrap();
    });
}

fn ser_block_header_cbor(bench: &mut Bencher) {
    let mut next = 0usize;
    bench.iter(move || {
        let value = &HEADERS[next];
        next += 1;
        next %= HEADERS.len();
        serde_cbor::to_vec(&value).unwrap();
    });
}

fn ser_block_header_speedy(bench: &mut Bencher) {
    let mut next = 0usize;
    bench.iter(move || {
        let value = &HEADERS[next];
        next += 1;
        next %= HEADERS.len();
        value.write_to_vec(Endianness::LittleEndian).unwrap();
    });
}

fn de_block_header_borsh(bench: &mut Bencher) {
    let headers: Vec<_> = HEADERS
        .iter()
        .map(|value| value.try_to_vec().unwrap())
        .collect();
    let mut next = 0usize;
    bench.iter(move || {
        let value = &headers[next];
        next += 1;
        next %= headers.len();
        BlockHeader::try_from_slice(&value).unwrap();
    });
}

fn de_block_header_bincode(bench: &mut Bencher) {
    let headers: Vec<_> = HEADERS
        .iter()
        .map(|value| bincode::serialize(&value).unwrap())
        .collect();
    let mut next = 0usize;
    bench.iter(move || {
        let value = &headers[next];
        next += 1;
        next %= headers.len();
        bincode::deserialize::<BlockHeader>(&value).unwrap();
    });
}

fn de_block_header_cbor(bench: &mut Bencher) {
    let headers: Vec<_> = HEADERS
        .iter()
        .map(|value| serde_cbor::to_vec(&value).unwrap())
        .collect();
    let mut next = 0usize;
    bench.iter(move || {
        let value = &headers[next];
        next += 1;
        next %= headers.len();
        serde_cbor::from_slice::<BlockHeader>(value).unwrap();
    });
}

fn de_block_header_speedy(bench: &mut Bencher) {
    let headers: Vec<_> = HEADERS
        .iter()
        .map(|value| value.write_to_vec(Endianness::LittleEndian).unwrap())
        .collect();
    let mut next = 0usize;
    bench.iter(move || {
        let value = &headers[next];
        next += 1;
        next %= headers.len();
        BlockHeader::read_from_buffer(Endianness::LittleEndian, value).unwrap();
    });
}

benchmark_group!(
    ser_block_header,
    ser_block_header_borsh,
    ser_block_header_bincode,
    ser_block_header_cbor,
    ser_block_header_speedy,
);

benchmark_group!(
    de_block_header,
    de_block_header_borsh,
    de_block_header_bincode,
    de_block_header_cbor,
    de_block_header_speedy,
);

benchmark_main!(ser_block_header, de_block_header);
