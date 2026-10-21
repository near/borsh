# Schema syntax, line protocol and decoding semantics

This file fixes the interfaces of the Lean specification: the text syntax of
schemas, the line protocol of `borsh-spec decode`, and the decoding rules that
the Lean code implements.  Where the prose specification in the repository
`README.md` is ambiguous or silent, [`DECISIONS.md`](DECISIONS.md) says how it
was resolved and why.

## Schema text syntax

One schema per line, no tabs.  Tokens are words (runs of `a-z0-9`) and parentheses;
runs of spaces separate tokens and may be omitted next to a parenthesis.  Any other
character is an error.

```
schema  := prim | "(" form ")"
prim    := u8 | u16 | u32 | u64 | u128 | i8 | i16 | i32 | i64 | i128
         | f32 | f64 | bool | unit | string
form    := option schema
         | vec schema
         | array N schema             -- N decimal, no length prefix on the wire
         | tuple schema*              -- structs and tuples; (tuple) == unit
         | enum variant*              -- see below
         | map schema schema          -- key schema, value schema
         | set schema
variant := "(" TAG schema ")"         -- TAG decimal 0..255, written as one byte
```

`unit` and `(tuple)` are the same schema.  A unit variant is `(TAG (tuple))`.  The
parser accepts `(enum)` with no variants; the schema is then rejected as not
well-formed.

### Enums

Each variant has an explicit wire tag.  **The order of the variants in the list is
their order as map keys and set elements** (the rank): a variant earlier in the list
compares smaller than a later one, whatever the tags, and values of one variant
compare by payload.  The tag is what is written to and read from the wire.

- A default derived Rust enum is `(enum (0 S0) (1 S1) ...)`: tags are the declaration
  indices, which is also the derived `Ord`.
- An enum with `#[borsh(use_discriminant = true)]` uses its discriminants as tags
  and derived `Ord` follows the discriminants: list the variants in ascending order
  of discriminant.
- Rust's `Result<T, E>` has `Err = 0`, `Ok = 1` on the wire and `Ok < Err` in `Ord`:
  `(enum (1 T) (0 E))`.
- An enum with explicit discriminants and `use_discriminant = false` has tags equal to
  declaration indices and derived `Ord` by discriminant: list the variants in
  ascending order of discriminant, each with its declaration index as tag.

The order of the list has no effect on the wire format, only on which key sequences
are accepted for maps and sets (see "Key order").

### Well-formedness

A schema that fails these conditions is answered with `bad`:

- `vec`, `set`, and the key of `map` must not have encoded size 0 (borsh's
  zero-sized-type ban, applied statically at every depth; see decisions 3 and 15).
  A schema has encoded size 0 when it is `unit`, `(tuple)` of such schemas, or an
  `array` of length 0 or of a schema of size 0.
- Map and set key schemas must not contain `f32` or `f64` anywhere (not `Ord` in Rust).
- Enums have at least one variant, and their tags are pairwise distinct.
- The schema's **factor** (below) must not exceed the tool's cap.

## Line protocol: `borsh-spec decode`

```
borsh-spec decode [--lenient] [--line-buffered] [--max-factor N] [--max-steps N]
```

Line-batched over stdin/stdout; one output line per input line, in order.  Large
batches are handled without per-line process startup.

Input line: `SCHEMA<TAB>HEX` where HEX is lowercase hexadecimal of even length,
possibly empty.

Output line, exactly one of:

- `ok<TAB>CONSUMED<TAB>REENCODED_HEX`: decoding a prefix of the input succeeded,
  consumed `CONSUMED` bytes (decimal), and `encode(value)` is `REENCODED_HEX`.
  Trailing input bytes are allowed (prefix decode).
- `err<TAB>REASON`: the input is rejected.  REASON is short and tab-free.
- `bad<TAB>REASON`: the line, the schema or the hex did not parse, the schema is
  not well-formed, its factor exceeds the schema cap, or the request exceeds the
  step cap (see "Resource guard").

REASON is informative only; compare the first field.  A line that is not
`SCHEMA<TAB>HEX` and hex that is not lowercase `0-9a-f` of even length are `bad`.  A
trailing carriage return is ignored.

Comparing re-encodings instead of values is sound because encoding is injective
(theorem `encode_injective`), so no shared value format is needed.  To test another
implementation against this one, call its counterpart of `T::deserialize(&mut slice)`
(not a `from_slice` that demands full consumption); consumed = original length minus
remaining length; re-encoding = its serialiser applied to the decoded value.

### Lenient mode

With `--lenient` the decoder is the one of borsh-rs without its `de_strict_order`
feature.  The line format is unchanged.  `CONSUMED` is the number of bytes read (it does
not depend on the order of the keys), and `REENCODED_HEX` is
the **canonical encoding of the decoded value**, which differs from the consumed bytes
when the input had unsorted or repeated keys.  See "Lenient decoding" below.

### Resource guard

Every schema has a factor `factor(s)` (`BorshSpec/Cost.lean`) such that decoding any
input of length `n` takes at most `(n + 1) * factor(s)` steps of the instrumented
decoder.  The tool applies two limits, both answered `bad`:

- a schema with `factor(s) > 2^20` (override with `--max-factor N`).  This bounds the
  constant: it does not bound the work on a long input, and the factor multiplies at
  every level of nested collections (21 levels of `vec`, or 8 of `set` or `map`,
  reach the cap);
- a request with `(n + 1) * factor(s) > 2^26` (override with `--max-steps N`), which
  by the bound above takes at most `2^26` steps whenever it is answered.

`bad` therefore has two kinds of cause that the first field does not tell apart: the
request is not valid, or it is valid and too large for the guard.  For example, a
well-formed `(vec u8)` of about 34 MB is answered `bad` although borsh-rs decodes it.
Compare the REASON text (it begins `resource limit` for the guard) or raise the caps
(`--max-steps`, `--max-factor`) when testing large inputs; a client must not treat
`bad` as a statement about the format when the reason is a resource limit.

The limits are not part of the format; they exist because a schema such as
`(array 4294967295 unit)` makes every decoder produce four billion elements from no
input.  Decision 18 explains the factor and the limits.

### Vector files: `borsh-spec check`

```
borsh-spec check [--lenient] FILE...
```

Each line of a vector file is `SCHEMA<TAB>HEX<TAB>EXPECTED`, where EXPECTED is the full
answer (`ok<TAB>CONSUMED<TAB>HEX`) or the bare word `err` or `bad` (which match on the
category only).  Blank lines and lines starting with `#` are skipped.  A line
`@mode strict` or `@mode lenient` selects the decoder for the lines after it; the
default is strict, or lenient with `--lenient`.  In strict mode every expected `ok`
must also be the answer of the lenient decoder.  The exit status is non-zero if any
line fails.

### `borsh-spec selftest-utf8`

Compares the UTF-8 validator with Lean's own on a bounded set of strings and prints
per-length accept counts with a digest, for comparison with `core::str::from_utf8`.

## Decoding semantics (strict)

- Integers little-endian, fixed width; signed integers two's complement.  `bool` byte
  must be 0 or 1.
- `option`: tag 0 = None, 1 = Some; other tags rejected.
- Floats: IEEE-754 bits, little-endian.  NaN (any payload, either sign) rejected on
  decode and on encode.  `-0.0` and `0.0` are distinct values with distinct encodings.
- `string`: u32 LE byte length, then bytes that must be valid UTF-8 as Rust's
  `core::str::from_utf8` accepts them (RFC 3629: no overlongs, no surrogates, nothing
  above U+10FFFF).
- `vec` / `set` / `map`: u32 LE count, then elements / keys / key-value pairs (key
  then value).  A count larger than the input could hold fails when the input runs
  out.
- `array N S`: N elements, no prefix.
- `tuple`: fields in order.  `enum`: u8 tag, then the payload of the variant with
  that tag; unknown tags rejected.
- `set` elements and `map` keys must be **strictly ascending** in the key order below:
  unsorted and repeated keys are rejected.  This is the canonical form and matches
  borsh-rs with the `de_strict_order` feature.
- Encoding fails on NaN, on values that are not of the schema's type, on unsorted or
  repeated keys, on invalid UTF-8, and on any collection or string of length at least
  2^32.

### Key order

The order is Rust's `Ord` for the corresponding std type, applied to the key type.  It
does not look at the encoded bytes.

- Integers: numeric (signed for `i*`).  `bool`: false < true.  `unit`: equal.
- `string`: byte-lexicographic (equal to code point order).
- `option`: None < Some, then payload.
- `vec`, `array`, `set`: lexicographic over elements, a proper prefix first.
- `tuple`: lexicographic over fields.  `map`: lexicographic over (key, value) pairs.
- `enum`: by the position of the variant in the schema's variant list, then payload.

Floats have no key order; a schema using one in a key is not well-formed.

## Lenient decoding

Without `de_strict_order`, borsh-rs reads the whole `Vec<(K, V)>` or `Vec<T>` first
(so the bytes consumed do not depend on the order) and then collects it into the
container.  The result, which the lenient decoder reproduces, is:

- `BTreeMap`, `HashMap`: entries are inserted in input order, so of several entries
  with the same key **the last one wins** (its value replaces the earlier ones).
- `BTreeSet`, `HashSet`: repeated elements collapse to one.
- The container is then ordered by key; its serialisation is the strict encoding.

Everything else (integer, bool, option and enum tags, NaN, UTF-8, the zero-size ban,
lengths) is identical to strict decoding, and on every input that strict decoding
accepts the lenient decoder returns the same value.  The normalisation applies inside
every map and set of the value, at every depth.

Strict decoding is the specification; lenient decoding documents what existing
borsh-rs deployments accept, so that differences from the canonical format can be
tested rather than assumed.
