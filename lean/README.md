# Borsh in Lean

[`Spec.lean`](Spec.lean) defines the Borsh format: types, values, `encode` and
`decode`, in about 200 lines. Read that file first.

[`Theorems.lean`](Theorems.lean) proves, for every schema:

- `decode_encode`: decoding an encoding returns the value, whatever bytes follow it.
- `encode_decode`: the decoder only accepts encodings, so each valid value has
  exactly one byte form.
- `encode_injective`: different values have different encodings.

These are statements about the Lean definitions. That they match borsh-rs is checked
by the vectors below and by differential testing, not by the proofs.

## Command-line tool

```sh
lake build                       # spec, proofs and the borsh-spec tool
lake test                        # runs vectors.tsv
printf 'u32\t2a000000\n' | lake exe borsh-spec decode
# ok	4	2a000000
```

Each input line is `SCHEMA<TAB>HEX`. The answer is `ok<TAB>BYTES_READ<TAB>REENCODED_HEX`,
`err<TAB>reason` (the bytes are rejected) or `bad<TAB>reason` (the line or schema is).
Bytes after the value are allowed and not read. Schemas are S-expressions:

```
u8 … u128  i8 … i128  f32  f64  bool  unit  string
(option T)  (vec T)  (array N T)  (set T)  (map K V)  (tuple T…)
(enum (TAG T) …)    ; TAG is the byte written; list variants in Rust's Ord order
```

`Result<T, E>` is `(enum (1 T) (0 E))`: `Ok` is written as 1 but sorts first.
Schemas Rust cannot have are `bad`: zero-sized `Vec` elements or map keys, float keys,
enums with no variants or a repeated tag.

[`vectors.tsv`](vectors.tsv) holds the conformance vectors: `SCHEMA<TAB>HEX<TAB>EXPECTED`,
where a bare `err` or `bad` matches on the first field only.

## Where borsh-rs differs

- Without the `de_strict_order` feature, borsh-rs accepts unsorted or repeated map keys
  and sorts them. This spec, like `de_strict_order`, rejects them.
- borsh-rs rejects collections of a fieldless single-variant enum (a Rust zero-sized
  type) although each element writes a tag byte. This spec accepts them; see the end of
  `vectors.tsv`.
