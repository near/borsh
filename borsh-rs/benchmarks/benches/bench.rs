use bencher::{benchmark_main, Bencher, TestDesc, TestDescAndFn, TestFn};
use benchmarks::{Account, Block, BlockHeader, Generate, SignedTransaction};
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

macro_rules! generic_bench {
    ( $SER_INPUT:ident, $DE_INPUT:ident, $type:tt, $group_name:ident) => {
        mod $group_name {
            use super::*;

            lazy_static! {
                static ref $SER_INPUT: Vec<$type> = { generator::<$type>(1000) };
            }

            pub fn ser_borsh(bench: &mut Bencher) {
                let mut next = 0usize;
                bench.iter(move || {
                    let value = &$SER_INPUT[next];
                    next += 1;
                    next %= $SER_INPUT.len();
                    value.try_to_vec().unwrap();
                });
            }

            pub fn ser_bincode(bench: &mut Bencher) {
                let mut next = 0usize;
                bench.iter(move || {
                    let value = &$SER_INPUT[next];
                    next += 1;
                    next %= $SER_INPUT.len();
                    bincode::serialize(&value).unwrap();
                });
            }

            pub fn ser_cbor(bench: &mut Bencher) {
                let mut next = 0usize;
                bench.iter(move || {
                    let value = &$SER_INPUT[next];
                    next += 1;
                    next %= $SER_INPUT.len();
                    serde_cbor::to_vec(&value).unwrap();
                });
            }

            pub fn ser_speedy(bench: &mut Bencher) {
                let mut next = 0usize;
                bench.iter(move || {
                    let value = &$SER_INPUT[next];
                    next += 1;
                    next %= $SER_INPUT.len();
                    value.write_to_vec(Endianness::LittleEndian).unwrap();
                });
            }

            pub fn de_borsh(bench: &mut Bencher) {
                let $DE_INPUT: Vec<_> = $SER_INPUT
                    .iter()
                    .map(|value| value.try_to_vec().unwrap())
                    .collect();
                let mut next = 0usize;
                bench.iter(move || {
                    let value = &$DE_INPUT[next];
                    next += 1;
                    next %= $DE_INPUT.len();
                    $type::try_from_slice(&value).unwrap();
                });
            }

            pub fn de_bincode(bench: &mut Bencher) {
                let $DE_INPUT: Vec<_> = $SER_INPUT
                    .iter()
                    .map(|value| bincode::serialize(&value).unwrap())
                    .collect();
                let mut next = 0usize;
                bench.iter(move || {
                    let value = &$DE_INPUT[next];
                    next += 1;
                    next %= $DE_INPUT.len();
                    bincode::deserialize::<$type>(&value).unwrap();
                });
            }

            pub fn de_cbor(bench: &mut Bencher) {
                let $DE_INPUT: Vec<_> = $SER_INPUT
                    .iter()
                    .map(|value| serde_cbor::to_vec(&value).unwrap())
                    .collect();
                let mut next = 0usize;
                bench.iter(move || {
                    let value = &$DE_INPUT[next];
                    next += 1;
                    next %= $DE_INPUT.len();
                    serde_cbor::from_slice::<$type>(value).unwrap();
                });
            }

            pub fn de_speedy(bench: &mut Bencher) {
                let $DE_INPUT: Vec<_> = $SER_INPUT
                    .iter()
                    .map(|value| value.write_to_vec(Endianness::LittleEndian).unwrap())
                    .collect();
                let mut next = 0usize;
                bench.iter(move || {
                    let value = &$DE_INPUT[next];
                    next += 1;
                    next %= $DE_INPUT.len();
                    $type::read_from_buffer(Endianness::LittleEndian, value).unwrap();
                });
            }
        }
        pub fn $group_name() -> ::std::vec::Vec<$crate::TestDescAndFn> {
            use std::borrow::Cow;
            let mut benches = ::std::vec::Vec::new();
            benches.push(TestDescAndFn {
                desc: TestDesc {
                    name: Cow::from(format!("ser_{}_borsh", stringify!($group_name))),
                    ignore: false,
                },
                testfn: TestFn::StaticBenchFn($group_name::ser_borsh),
            });

            benches.push(TestDescAndFn {
                desc: TestDesc {
                    name: Cow::from(format!("ser_{}_bincode", stringify!($group_name))),
                    ignore: false,
                },
                testfn: TestFn::StaticBenchFn($group_name::ser_bincode),
            });

            benches.push(TestDescAndFn {
                desc: TestDesc {
                    name: Cow::from(format!("ser_{}_cbor", stringify!($group_name))),
                    ignore: false,
                },
                testfn: TestFn::StaticBenchFn($group_name::ser_cbor),
            });

            benches.push(TestDescAndFn {
                desc: TestDesc {
                    name: Cow::from(format!("ser_{}_speedy", stringify!($group_name))),
                    ignore: false,
                },
                testfn: TestFn::StaticBenchFn($group_name::ser_speedy),
            });

            benches.push(TestDescAndFn {
                desc: TestDesc {
                    name: Cow::from(format!("de_{}_borsh", stringify!($group_name))),
                    ignore: false,
                },
                testfn: TestFn::StaticBenchFn($group_name::de_borsh),
            });

            benches.push(TestDescAndFn {
                desc: TestDesc {
                    name: Cow::from(format!("de_{}_bincode", stringify!($group_name))),
                    ignore: false,
                },
                testfn: TestFn::StaticBenchFn($group_name::de_bincode),
            });

            benches.push(TestDescAndFn {
                desc: TestDesc {
                    name: Cow::from(format!("de_{}_cbor", stringify!($group_name))),
                    ignore: false,
                },
                testfn: TestFn::StaticBenchFn($group_name::de_cbor),
            });

            benches.push(TestDescAndFn {
                desc: TestDesc {
                    name: Cow::from(format!("de_{}_speedy", stringify!($group_name))),
                    ignore: false,
                },
                testfn: TestFn::StaticBenchFn($group_name::de_speedy),
            });
            benches
        }
    };
}

generic_bench!(ACCOUNTS, accounts, Account, account);
generic_bench!(TRANSACTIONS, transactions, SignedTransaction, transaction);
generic_bench!(HEADERS, headers, BlockHeader, block_header);
generic_bench!(BLOCKS, blocks, Block, block);

benchmark_main!(account, transaction, block_header, block);
