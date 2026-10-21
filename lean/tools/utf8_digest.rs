//! The enumeration of `borsh-spec selftest-utf8`, run against Rust's `core::str::from_utf8`.
//!
//! It prints, per length, how many byte strings `from_utf8` accepts and an FNV-1a digest
//! of the accept/reject bits in enumeration order (first byte slowest), in the same format as
//! the `length N: accepted A digest D` lines of `borsh-spec selftest-utf8`.  The enumeration is
//! every byte string of length 1 to 3 and the length-4 strings whose last two bytes come from a
//! fixed 15-value sample.  Identical output means identical accept sets on that enumeration.
//!
//! Build and run:  rustc -O -o utf8_digest tools/utf8_digest.rs && ./utf8_digest
fn main() {
    let sample: [u8; 15] = [
        0x00, 0x41, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc2, 0xe0, 0xf0, 0xf4, 0xff,
    ];
    let mut counts = [0u64; 4];
    let mut hashes = [0xcbf2_9ce4_8422_2325u64; 4];
    let mut step = |len: usize, bs: &[u8]| {
        let ok = std::str::from_utf8(bs).is_ok();
        if ok {
            counts[len - 1] += 1;
        }
        hashes[len - 1] = (hashes[len - 1] ^ (ok as u64)).wrapping_mul(0x100_0000_01b3);
    };
    for b0 in 0..=255u8 {
        step(1, &[b0]);
        for b1 in 0..=255u8 {
            step(2, &[b0, b1]);
            for b2 in 0..=255u8 {
                step(3, &[b0, b1, b2]);
            }
            for &b2 in &sample {
                for &b3 in &sample {
                    step(4, &[b0, b1, b2, b3]);
                }
            }
        }
    }
    for l in 0..4 {
        println!("length {}: accepted {} digest {}", l + 1, counts[l], hashes[l]);
    }
}
