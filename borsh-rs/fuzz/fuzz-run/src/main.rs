use borsh::BorshDeserialize;
use std::collections::{BTreeMap, HashMap, HashSet};

#[macro_use]
extern crate honggfuzz;

macro_rules! fuzz_types {
    (
        $data:ident;
        $( $type:ty, )*
    ) => {
        $(
            let _ = <$type>::deserialize(&mut &$data[..]);
        )*
    };

}

fn main() {
    loop {
        fuzz!(|data: &[u8]| {
            fuzz_types!(
                data;
                u32,
                u64,
                i32,
                i64,
                f32,
                f64,
                String,
                (u32,u64,i32,i64,f32,f64,String,),
                std::net::SocketAddrV4,
                std::net::SocketAddrV6,
                std::net::Ipv4Addr,
                std::net::Ipv6Addr,
                Box<[u8]>,
                Option<u64>,
                Option<String>,
                Option<Vec<u8>>,
                Option<Vec<u64>>,
                Option<Box<[u8]>>,
                Option<std::net::SocketAddrV4>,
                Vec<u64>,
                Vec<String>,
                Vec<Vec<u8>>,
                Vec<Vec<u64>>,
                Vec<Box<[u8]>>,
                Vec<std::net::SocketAddrV4>,
                HashSet<u64>,
                HashSet<String>,
                HashSet<Vec<u8>>,
                HashSet<Vec<u64>>,
                HashSet<Box<[u8]>>,
                HashSet<std::net::SocketAddrV4>,
                HashMap<u64, u64>,
                HashMap<String, String>,
                HashMap<std::net::SocketAddrV4, String>,
                HashMap<Vec<u8>, Vec<u8>>,
                HashMap<Box<[u8]>, HashMap<String, String>>,
                BTreeMap<u64, u64>,
                BTreeMap<String, String>,
                BTreeMap<Vec<u8>, Vec<u8>>,
                BTreeMap<Box<[u8]>, BTreeMap<String, String>>,
            );
        });
    }
}
