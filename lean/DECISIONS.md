# Decisions

Where the prose specification (the "Specification" section of the repository
`README.md`) is ambiguous, wrong or silent, this specification decides as below.
"Rust" means borsh-rs at commit `c4749d6a` (a local checkout, not vendored here),
whose behaviour is what existing data was written with.  The schema syntax and the
line protocol are in [`PROTOCOL.md`](PROTOCOL.md).

### 1. Unordered containers are ordered by the key type's `Ord`, strictly

*Prose*: "all unordered containers (hashmap/hashset) are ordered in lexicographic
order by key (in tie breaker case on value)."

*Decision*: map keys and set elements are written in strictly ascending order of the
key's `Ord` (`Value.cmp`, `BorshSpec/Spec.lean`).

*Why*: keys are unique, so the value tie-breaker is unreachable.  borsh-rs sorts by
the key type's `Ord`, not by the encoded bytes, and the two differ for signed
integers (`-1` encodes as `ff..ff`, which sorts after `0` byte-wise) and for
little-endian integers generally (`1` is `01 00 00 00`, `256` is `00 01 00 00`).
`vectors/ordering.tsv` has the discriminating cases.  A user key type with a custom
`Ord` is out of scope.

### 2. Enum variants: the list order is the key order, the tag is explicit

*Prose*: "enums are serialized with using `u8` for the enum ordinal"; the table says
"the number of the variant".

*Decision*: an enum schema lists `(wire tag, payload)` pairs and **the list order is the
key order of the variants** (`PROTOCOL.md`, "Enums").  A value carries the variant's
index in the list, not its tag; `encode` maps index to tag and `decode` maps tag to
index.

*Why*: the wire tag and Rust's derived `Ord` disagree for two kinds of enums.
`Result<T, E>` is written `Err = 0`, `Ok = 1` but `Ok < Err`, so
`BTreeSet<Result<u8, u8>> {Ok(5), Err(1)}` is serialised by borsh-rs as
`02000000 0105 0001`.  An enum with explicit discriminants (`A = 5, B = 2`) and
`use_discriminant = false` writes declaration indices as tags but orders by
discriminant.  Making the variant index part of the schema lets one definition cover all
cases, including default enums (`(enum (0 S0) (1 S1) ...)`), while `Value.cmp` stays
structural and schema-independent (decision 19).  Ordering by wire tag, the obvious
alternative, is wrong for the first two kinds.

### 3. Zero-sized types: encoded size, not `size_of`

*Decision*: `vec`, `set` and the key of a `map` must not have encoded size 0
(`Schema.zeroSized`).

*Why*: borsh-rs checks `size_of::<T>() == 0`, which is not "encoded size 0": an enum
with a single fieldless variant is a Rust ZST (unless it has `#[repr(u8)]`, which gives
it size 1) but its encoding is a tag byte, so `(vec (enum (0 unit)))` is `ok` here and
an error in borsh-rs for `enum One { A }`.  The specification states the ban in terms
of the wire format.  The opposite mismatch (Rust size above 0, encoded size 0) is
decision 27.  `vectors/divergences.tsv` pins both.

### 4. Strict decoding is the specification; default borsh-rs is not canonical

*Decision*: decoding rejects unsorted and repeated map and set keys.

*Why*: that is the canonical form (one encoding per value, the "bijection" the prose
asks for).  borsh-rs matches it only with the `de_strict_order` feature; by default it
accepts both and the last repeated entry wins.  The default behaviour is specified
separately as the lenient decoder (decision 8) and is a documented non-canonical
deviation of the Rust crate, not part of the format.

### 5. Recursive types and depth limits are out of scope

The schema syntax cannot express recursion, so every schema is a finite tree.  No depth
limit is specified; the executable's stack use is bounded by schema depth, and the
input-sized loops (`vec`, `array`, `set`, `map`, `string`) do not recurse per element.
borsh-rs has no depth limit either: a recursive type such as
`struct L { next: Option<Box<L>> }` decoded from a million bytes of `01` overflows the
stack and aborts the process.  That is outside this model, which has no recursive
schemas.

### 6. Integers are `Nat` and `Int`; the schema has two integer constructors

`Schema.uint w` and `Schema.sint w` take an `IntWidth` (8, 16, 32, 64, 128 bits) instead
of ten constructors.  Values are `Value.uint (n : Nat)` and `Value.sint (i : Int)`,
range-checked by `hasType`.  Encoding is then `toLE`/`fromLE` arithmetic, and the signed
case is `i mod 2^(8w)`.

### 7. Bytes are `List UInt8`; `ByteArray` appears only in the UTF-8 self-test

Proof-friendliness.  Hex is converted on `List Char`.

### 8. Lenient decoding

*Decision*: `Lenient.decode` reads entries in input order, stably sorts them by key,
and collapses each run of equal keys to its last entry; sets collapse repeated
elements.  Everything else is as in strict mode, and the bytes consumed are the same.

*Why*: this is what borsh-rs does without `de_strict_order`.  It decodes the whole
`Vec<(K, V)>` or `Vec<T>` first and then collects.  Checked with a small test program
(not part of this repository) against borsh-rs, for `BTreeMap<u8, u8>` and
`HashMap<u8, u8>`, with and without the feature:

- `{1: 7}` then `{1: 9}` decodes to `{1: 9}`, and `{1: 9}` then `{1: 7}` to `{1: 7}`
  (last wins, whichever order the input has), for both map types;
- entries `2→1, 1→2, 2→3` decode to `{1: 2, 2: 3}` for both;
- `BTreeSet<u8>` and `HashSet<u8>` collapse `5, 5, 5` to `{5}` and sort `3, 1, 2`;
- `BTreeSet<Result<u8, u8>>` read from `Err(1), Ok(5)` is written back `Ok(5), Err(1)`;
- with `de_strict_order` all of the unsorted or repeated inputs above are rejected.

Re-serialising a `HashMap`/`HashSet` sorts by key, so the re-encoding is the strict
encoding for the hashed containers too.  For sets, which of several equal elements
survives is irrelevant because `Value.cmp a b = .eq` only for equal values.  The
normalisation applies inside every map and set at every depth.

The behaviour is pinned by theorems, not only by examples.  `Value.normalize` is the
structural normalisation (children first, then each map and set), `KeyPolicy.raw` is
the policy that keeps keys as read, and `lenient_eq_normalize_raw` says that
`Lenient.decode` is the raw decoder followed by `Value.normalize`.  `normalizeMap_mem_iff`
says an entry survives exactly when no later entry has its key (last wins),
`normalizeSet_mem_iff` that a set neither gains nor loses elements, and the two
`strictAsc` theorems that the result is sorted.  A decoder that kept the *first* entry
of a repeated key would satisfy `lenient_eq_strict_of_strict`, `lenient_canonical` and
`lenient_progress` but not `normalizeMap_mem_iff`.

### 9. Floats are raw bit patterns; they may not be keys

`Value.f32 (bits : UInt32)`, `Value.f64 (bits : UInt64)`.  NaN is the bit predicate
"exponent all ones and mantissa non-zero" (`isNaN32`, `isNaN64`), any payload and either
sign, and is rejected on decode and on encode.  `-0.0` and `0.0` are different values
with different encodings.  No `Float` arithmetic is involved.  The prose says
`little_endian(x as integer_type)`, which in Rust is a numeric cast; the encoding is
the IEEE-754 bit pattern (`to_bits`).

Floats may not occur in map or set keys: they are not `Ord` in Rust.  This is a
protocol choice, not a Rust limitation (a wrapper such as `OrderedFloat` could be a key
in Rust); such wrappers are not modelled.

### 10. Enum values carry an index; repeated tags use the first variant

`Schema.enum (vs : List (UInt8 × Schema))`, `Value.enum (idx : Nat) (v : Value)`.  Tags
are `UInt8`, so the range `0..255` is the type; well-formedness requires at least one
variant and pairwise distinct tags.  A schema with a repeated tag is not well-formed,
but the codec is still unambiguous: `decode` returns the index of the *first* variant
with the tag, and `hasType`/`encode` accept an index only if no earlier variant has the
same tag.  This is what lets the round-trip theorem hold without a well-formedness
hypothesis.  `unit` is `tuple []` (there is no separate unit schema or value).

### 11. Own UTF-8 validator

`validUtf8` (`Utf8.lean`) implements the well-formed byte sequence table of the Unicode
standard (RFC 3629) directly, not via `String.validateUTF8`, so the specification does
not depend on a library's behaviour.  It is intended to equal Rust's
`core::str::from_utf8`.  That is tested, and its agreement with an independent UTF-8
grammar is the statement `validUtf8_iff`.  `selftest-utf8` compares it with Lean's
validator on all strings of length 1 to 3 and on length-4 strings whose first two
bytes are arbitrary and whose last two come from a 15-value sample (nothing of length
5 or more); `tools/utf8_digest.rs`, a Rust program over `core::str::from_utf8`,
reproduces the same per-length accept counts and digests, and CI compares the two
outputs.

### 12. `encode` is strict; validity is its success set

`encode s v` returns `none` unless `v` is valid for `s`: well-typed, no NaN, strings
valid UTF-8, all collection lengths below `2^32`, set elements and map keys strictly
ascending, and no zero-sized `vec`/`set`/key.  In particular it does not sort: an
unsorted `Value.map` is not encodable.  (Rust sorts when it serialises a `HashMap`; in
this model the list order *is* the wire order.)  `encode` re-checks inline rather than
calling `hasType`/`canonical`, so "`encode` succeeds iff `Valid`" is a theorem
(`encode_isSome_iff_valid`) and not a definition.

### 13. Typing and canonicity are separate Boolean checks with Prop wrappers

`hasType` (shape and ranges) and `canonical` (NaN, UTF-8, lengths, order),
`Valid = HasType ∧ Canonical`.  The Booleans are structurally recursive and
`rfl`/`decide`-friendly; the Prop wrappers have `Decidable` instances.

### 14. `encode` and `decode` are total on every schema, with no fuel

Both are structurally recursive on `Schema`, with mutual helpers for tuple fields and
enum variants.  They do not require `wellFormed`: `vec`, `set` and map keys that are
zero-sized fail in both directions, which makes every loop consume input, and repeated
enum tags are resolved the same way on both sides (decision 10).  So the round-trip,
canonical-decoding and progress theorems carry no well-formedness hypothesis;
`wellFormed` matters for `minSize_attained`, for the float-key ban (which the codec does
not itself enforce) and for which schemas the executable accepts.

### 15. The zero-size ban is static, at every depth

`wellFormed` rejects `(option (vec unit))` even though borsh-rs only raises its error
when a `Vec<()>` is actually deserialised (so `Option::<Vec<()>>::None` decodes there).
A depth-independent rule is simpler to state and to prove, and describes "the type is
not usable", which is what a schema is.  The codec itself also checks the ban where it
matters (decision 14).  `vectors/divergences.tsv` pins the difference; a differential
harness skips schemas the specification calls `bad`.

### 16. Fail-fast decoding with accumulating loops

* `takeExact n bs` inspects at most `min n bs.length` bytes.
* `decodeMany d n acc bs` is structural on `n`, accumulates results reversed and stops at
  the first failure; with a non-zero-sized element it runs at most `bs.length + 1`
  iterations whatever `n` is, so `0xffffffff` with a short body fails quickly and
  allocates only what the input holds.  The cost theorem makes this precise
  (decision 18).
* The accumulator-and-reverse form, and `List.mapM` plus `List.flatten` in `encode`,
  are tail recursive, so a two-million element vector does not overflow the stack.
* Tuple fields and enum variants recurse per schema node, not per input element.

### 17. One decoder, two key policies; order is checked after reading all keys

`decodeWith P` takes a `KeyPolicy`, the only point where strict and lenient decoding
differ: what happens to the list of decoded set elements or map entries.  Strict:
accept if strictly ascending, else fail.  Lenient: sort and collapse (decision 8).
`decode` is `decodeWith KeyPolicy.strict` and `Lenient.decode` is
`decodeWith Lenient.policy`.  The theorem `lenient_eq_strict_of_strict` is then a
statement about two policies, not about two copies of a decoder.  The strict check runs
on the decoded key list after the loop, not incrementally; it accepts exactly the inputs
borsh-rs accepts with `de_strict_order` (which also reads the whole `Vec` first); only
the point of failure differs.

### 18. Cost model, schema factor and the resource guard

`Tooling/Cost.lean` has `decodeC`, the strict decoder instrumented with a step counter, and
`Schema.factor`.  A step is a visit of a schema node, a byte validated as UTF-8, or the
work of comparing two keys during the order check (charged `1 + min` of their sizes).
The theorem `decode_steps_le` says `steps ≤ (input length + 1) * factor s`, for every
schema.  The factor is `1` for leaves, `1 +` the contents for `option`/`tuple`, `1 +` the
number of variants `+` the largest payload factor for `enum` (the variant search costs
one step per variant examined), `2 *` the element factor for `vec`, `6 *` for `set` and `map` (the order check costs at
most twice the decoding of the keys), and for `array n s`: `1 + n * factor s` if `s` is
zero-sized, `1 + 2 * factor s` otherwise.  The constants are not tight; they are what
the proof goes through with.

`array n s` with a zero-sized `s` is the one place where the decoder produces more than
one element per input byte: it makes `n` elements from no input, by definition
(Rust's `[(); N]` is also fine).  The effect composes: an array whose element is not
zero-sized but contains such an array makes each of its elements materialise its own.
So the claim "work is proportional to the input" is false without a schema-dependent
factor, and the element bound likewise (`decode_elems_le`).

The executable has two guards.

* **Schema guard**: a schema with `factor > 2^20` is `bad` (`--max-factor` overrides).
  This bounds the *constant* only: the work for an empty input is at most about a
  million steps, but an input of `n` bytes may still cost `(n + 1) * 2^20`.  A schema
  over the cap contains a zero-sized array of about a million elements, or nests
  collections deeply.  The factor is exponential in nesting depth, since it multiplies
  at every level: `vec` doubles it and `set` and `map` multiply it by six, so the cap
  is reached at 21 levels of `vec` and at 8 levels of `set` or `map`.
* **Request guard**: a request with `(input length + 1) * factor > 2^26` is `bad`
  (`--max-steps` overrides).  By `decode_steps_le` (`decode_steps_le_of_withinSteps`) a
  request that passes takes at most `2^26` steps, whatever the input and the schema,
  about a second on the machine of the throughput figures.  Without it,
  the schema `(vec (tuple u8 (array 500000 unit)))`, which passes the schema guard,
  took 2 s on 104 bytes of input and was out of memory on 100 kB: each input byte
  starts an array of half a million slots.  The guard is deliberately the theorem's
  bound and not a measurement, so it also refuses some requests that would have been
  cheap; the factor is loose for ordinary schemas.  The value `2^26` is a choice, not
  a theorem: with `(map string (map string u8))`, whose factor is
  `6 * (1 + 6 * (1 + 1)) = 78`, requests over `2^26 / 78 = 860386` bytes are refused,
  and `(map string (map string (vec u8)))` (factor 114) is limited to about 590 kB.
  For the pathological schema above the same cap allows 66 input bytes.  A harness
  that really sends larger payloads raises `--max-steps`; the price is the time and
  memory of the worst case, both proportional to the cap.

Memory is bounded by the same product, because `elems v ≤ steps`
(`decode_elems_le_steps`): at most `2^26` collection elements are ever built.  Both
guards are properties of the tool, not of the format.  An adversarial *schema* is
outside the protocol's threat model (schemas come from the test harness).  The model
covers the strict decoder only; the lenient decoder does the same decoding and then
sorts, which costs `O(k log k)` key comparisons for `k` keys and is not covered by a
theorem (the request guard applies to it unchanged, and `k` is at most the number of
steps).  The bound is on the step-counting model `decodeC`, tied to `decode` by
`decodeC_result`; it is not a statement about compiled running time.

### 19. Key order is schema-independent

`Value.cmp` inspects only the value's constructors; values of different constructors are
ordered by `shapeIndex` (this never happens for well-typed values of one schema).
Enum values compare by variant index, then payload.  Floats compare by raw bits to keep
`cmp` total, though well-formed schemas never use them as keys.  Encode and decode use
the same test (`strictAsc`), so their mutual consistency needs no order laws; the laws
(`Value.cmp_self`, `cmp_eq_iff`, `cmp_swap`, `cmp_trans`) are needed for decoded sets
and maps to be duplicate-free and for the lenient decoder.

### 20. Schema text parser and printer

Words are `[a-z0-9]+`; parentheses are tokens by themselves; runs of spaces separate
tokens (so `( vec u8 )` is accepted); tabs and any other character are rejected.  Array
lengths are decimal digit strings (leading zeros accepted, no upper bound: `[T; N]` in
Rust has `N <= usize::MAX`, the specification does not model that); enum tags must be
below 256.  `(enum)` with no variants parses and is rejected by `wellFormed`, so that
parsing and well-formedness stay separate and `parse (print s) = s` holds for every
schema (`parse_print`).  The printer writes `unit` for the empty tuple.  The parser
(tokenise, build an S-expression with an explicit stack, convert) is structural and
needs no fuel.

### 21. Executable behaviour outside the protocol

* HEX must be lowercase `0-9a-f` of even length; anything else is `bad<TAB>invalid hex`.
  A line that is not `SCHEMA<TAB>HEX` is `bad<TAB>line must be SCHEMA<TAB>HEX`.
* `err`/`bad` reasons are informative; `check` compares only the category when an
  expectation is a bare `err` or `bad`.
* Output is flushed every 8192 lines and at EOF, or per line with `--line-buffered`.
* For each successful decode the executable asserts, on the compiled code, `hasType`,
  `canonical` and, in strict mode, that the re-encoding equals the consumed bytes; in
  lenient mode that the re-encoding decodes strictly back to the same value.  A
  violation is printed as `err<TAB>internal: ...`, and `check` never lets such an
  answer satisfy a bare `err`.
* `check` also requires that every expected `ok` of a strict vector is the lenient
  decoder's answer too.
* Parsed schemas are cached (bounded at 4096 entries).

### 22. No `DecidableEq` on `Schema` and `Value`; `BEq Value` comes from the key order

Lean's `deriving DecidableEq` does not support these nested inductives (`List Schema`,
`List (UInt8 × Schema)`), and `deriving BEq` on them produces a `partial` function,
which is opaque to the kernel: not even `Value.uint 1 == Value.uint 1` can be proved
by `rfl` or `decide`, and `Value.beq_iff` could never be proved.  So `Schema` and
`Value` derive only `Repr`, and `BEq Value` is defined in `Spec.lean` as
`cmp a b == .eq`; `Value.beq_iff` then reduces to `Value.cmp_eq_iff`.  Theorem
statements use propositional equality.  `Schema` has no `BEq` (nothing uses one).
`#guard` checks that compare values with `==` evaluate the compiled `cmp`; the
kernel-checked pins are the `example` lines in `Tooling/Examples.lean`.

### 23. Build policy

Lean `v4.35.0` and Batteries `v4.35.0`, both pinned; no Mathlib.  `warningAsError = true`
and `autoImplicit = false` in `lakefile.toml`.  The definitions (`BorshSpec`), the
theorems and the executable build and lint warning-free (`lake lint` covers all three).  The theorems are a separate library
(`BorshSpecTheorems`, root `BorshSpec/Theorems.lean`) so that the executable does not
depend on the proofs.  No `sorry` is allowed anywhere: `lake build --wfail` fails on
one.  `BorshSpec/Theorems/Axioms.lean` pins the axioms of the 53 headline theorems (the 51 of the three statement files and the two equivalence theorems of `SpecEquiv.lean`) with
`#guard_msgs`, so a new dependency on `sorryAx` or `Lean.ofReduceBool` fails the build; the
helper lemmas are covered transitively.  CI also checks that every theorem of the four
statement files has a pin, and rejects `partial`, `unsafe`, `opaque`, `implemented_by`,
`extern` and `csimp` in the sources, since each of them lets the compiled executable
differ from the definitions the theorems are about.

### 24. Differential testing method

The Rust side is a harness that is not part of this repository.  It maps Rust types to
schema text (a "zoo" of std types and derived structs and enums, including enums with
explicit discriminants and `use_discriminant`, and every map and set in `BTreeMap`,
`HashMap`, `BTreeSet` and `HashSet` variants), and builds against `borsh-rs/borsh` twice,
with and without `de_strict_order`.  For each type it generates inputs, decodes each
with `T::deserialize(&mut slice)`, re-encodes with `borsh::to_vec`, and compares accept or
reject, bytes consumed and the re-encoding with the answer of `borsh-spec`.  The pairing is
exact: the default build against `borsh-spec decode --lenient`, the `de_strict_order` build
against `borsh-spec decode`.  Inputs are valid values from a generator, mutations of them,
random bytes, and exhaustive enumerations under stated bounds (short inputs, every
sequence of up to six entries over a fixed key set for each map and set type, integer
extremes, large counts).  A second command of the harness runs the vector files through
borsh-rs: each line is mapped to a Rust type with the same schema, the `de_strict_order`
build checks the strict-mode lines and the default build the lenient-mode lines and the
expected `ok` answers of strict-mode lines; `lake test` checks the same files against the
Lean code.  The only expected non-matches are the zero-size classes of decisions 3, 15 and 27.  The harness
fails when its Lean binary is replaced by deliberately broken variants, which is the
evidence that it can see a disagreement; the figures are in the "Evidence" section of the
README.

### 25. What the theorems do and do not establish

Round trip, canonical decoding, injectivity, progress and the order laws would hold for
any self-consistent codec, including one that agreed on a wrong wire format (for example
`true` written as `2`, or an always-true UTF-8 check): they fix no byte.  The format is
fixed by the definitions, by the vectors, by the `#guard`/`rfl` examples in
`Tooling/Examples.lean` and by differential testing.  The relational grammar
(`decode_iff_encodes`) and `validUtf8_iff` tie the codec to a second statement of the
format, written from the prose and `PROTOCOL.md` without a decoder in it.  That second
statement is *not* independent in every respect: the grammar uses the same key order
`Value.cmp`, the same integer widths (`IntWidth.bytes`) and the same value
representation as the codec, so a consistently wrong key order (say, reversed) would
satisfy it.  The key order is protected by the `cmp` pins in `Tooling/Examples.lean`, the
ordering vectors and the differential test; the NaN test is written differently
(mask form in the grammar, field extraction in the codec) and the UTF-8 rules are
stated twice, with `validUtf8_iff_validateUTF8` as a third statement through the
standard library's validator.  Nothing proves agreement with Rust.

### 26. What the prose README does not say

The "Specification" section contains no decoding rules at all (bool and option tag
validity, UTF-8, NaN, zero-sized types, `Result`, `BTreeMap`/`BTreeSet`, `isize` and
`usize`, `NonZero*`); decode-side behaviour here comes from borsh-rs and `PROTOCOL.md`.
Its remark that objects and binary representations are in bijection holds, in borsh-rs,
only with `de_strict_order` and only for full consumption (prefix decoding, which is
what `deserialize(&mut slice)` does, accepts trailing bytes; `try_from_slice` does not);
this specification states the corresponding facts as theorems (`encode_injective`,
`encode_decode`, `encode_prefix_free`).  Even then the claim is about the encoding, not
about every Rust type: `IndexMap` and `IndexSet` are written in insertion order, so two
values that compare equal can encode differently; `0.0` and `-0.0` compare equal under
`PartialEq` but encode differently (decision 9); and `SocketAddrV6` drops its flow
information and scope id, so distinct values encode identically.  None of these types
is modelled here.  The enum row does not say
that the variant number is the declaration index unless `use_discriminant` is set, nor
that `Result` is `Err = 0, Ok = 1`.  The HashMap/HashSet rows say "sorted by key" without
saying that the order is the key type's `Ord` (decision 1), and the rule applies to
`BTreeMap` and `BTreeSet` as well.  The float row says `x as integer_type`, which in
Rust is a numeric cast; the bytes are `to_bits()` (decision 9).  `repr(len() as u32)`
should read: serialisation fails if the length exceeds `u32::MAX`.

### 27. Rust's zero-size test can be bypassed: `Vec<Box<()>>`

borsh-rs tests `size_of::<T>() == 0`.  `Box<()>` has size 8 but encodes to zero bytes,
so `Vec<Box<()>>` is *not* rejected: any `u32` count decodes from no input and allocates
8 bytes per element (about 2 GB for count `0x10000000`).  The specification answers
`bad` for `(vec unit)`.  This is a borsh-rs issue rather than a specification question;
the rule "encoded size 0" is the intended one.
