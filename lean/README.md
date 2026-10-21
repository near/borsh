# Borsh, executable and machine-checked specification (Lean 4)

This directory contains a formal specification of the [Borsh](https://borsh.io)
binary format written in Lean 4, in the Lake package `BorshSpec`, with an executable
front end `borsh-spec`.

**Start with [`BorshSpec/Spec.lean`](BorshSpec/Spec.lean).**  It is the whole format
in one file of about 540 lines, prose and the UTF-8 table included: the `Schema` and
`Value` types, little-endian integers, the key order of maps and sets, the UTF-8 rule,
and `Spec.encode` and `Spec.decode`, written in the order of the table in this
README, one rule per match arm, with the list of everything that is rejected.  Everything else in this directory is checking
or tooling around that file.

`Spec.lean` is the normative definition of the format.  `Spec.encode` and `Spec.decode`
are **theorem-proven equal** to the internal codec (`encode` and `decode` in
`Encode.lean` and `Decode.lean`) that the theorems below are stated about:

* `spec_encode_eq (s : Schema) (v : Value) : Spec.encode s v = encode s v`
* `spec_decode_eq (s : Schema) (bs : List UInt8) : Spec.decode s bs = decode s bs`

Both hold for every schema, value and input (`Theorems/SpecEquiv.lean`, proofs in
`Theorems/specequiv/`), so every theorem below holds for the readable codec as well.
Both proofs are by structural induction on the schema.  `Tooling/Examples.lean` also
checks `Spec.*` against the internal codec on concrete inputs; those checks are now
redundant with the theorems.

To read the specification as a web page, see "Reading the specification in a browser".

* The **spec** (`BorshSpec/`) is plain, total, structurally recursive Lean code:
  `Spec.lean` (readable codec, types, key order), the internal codec the theorems are
  about (`Encode`, `Decode`, `Typing`, `Schema`), the UTF-8 validator and the relational
  grammars the codec is checked against.  Bytes are `List UInt8`.  `BorshSpec/Tooling/`
  holds what is not the format: the lenient decoder that models borsh-rs without
  `de_strict_order`, the step-counting decoder and schema cost factor (a resource model
  for the executable's request guard), the schema parser and printer, hex, and build-time
  examples.
* The **theorems** (`BorshSpec/Theorems/`) are statements about those definitions.
  They are a separate library, so the spec and the tool build whatever state the
  proofs are in.  See "What is proven".
* The **executable** `borsh-spec` runs the spec on `SCHEMA<TAB>HEX` lines, so other
  implementations (the Rust crate, in particular) can be tested against it.
* The **vectors** in `vectors/` are a curated conformance corpus.

Normative references: the "Specification" section of the repository `README.md`,
resolved where it is ambiguous by [`DECISIONS.md`](DECISIONS.md).  The schema text
syntax, the line protocol and the decoding rules are in [`PROTOCOL.md`](PROTOCOL.md).

## Claim terminology

* **theorem-proven**: a Lean theorem checked by the kernel, with `#print axioms`
  limited to `propext`, `Classical.choice`, `Quot.sound`.  Only the section "What is
  proven" lists such claims.
* **differentially tested**: a harness compared two implementations on concrete
  inputs and found no disagreement.  Evidence, not proof.
* **exhaustively enumerated under stated bounds**: every input within a stated bound
  was checked (for example every byte string of length 1 to 3 by `selftest-utf8`).
  Evidence for the bound only.
* **tested**: `#guard` checks, vector files, property runs.  Also evidence only.

A passing test is never described as a proof.

## What is proven

The 51 theorems stated in `Theorems/RoundTrip.lean`, `Theorems/Grammar.lean` and
`Theorems/Resources.lean`, and the two equivalence theorems of `Theorems/SpecEquiv.lean`
(53 in all), are theorem-proven: checked by the Lean kernel, with no
`sorry` and no `native_decide`.  These are the headline results; the lemmas they are
proved from are in the lowercase directories `Theorems/roundtrip/`, `Theorems/grammar/`
and `Theorems/resources/` and are covered transitively.  `Theorems/Axioms.lean` pins
`#print axioms` for each of the 53, so the build fails if a footprint changes, and CI
checks that every theorem of the four statement files has a pin.  The tables below
list the 51, and "Readable codec" lists the other two.

Axioms: every theorem depends on at most `propext`, `Classical.choice` and
`Quot.sound`.  Exceptions, which need fewer: `toLE_length`, `toLE_eq_leBytes` and
`sintToNat_eq_twosComplement` use `propext` only; `natToSint_sintToNat` and
`factor_pos` use `propext` and `Quot.sound`.  Unless a row says otherwise, a
theorem has no hypothesis on the schema (it need not be well-formed) and "decoder"
means the strict decoder `decode`.

What these theorems are: properties of the Lean definitions.  They show the
definitions are self-consistent and agree with a separately written relational
grammar.  They do not show that the format matches the prose specification or
borsh-rs; that is what the vectors, `Tooling/Examples.lean` and the differential tests under
"Evidence" are for (decision 25).

### Codec (`Theorems/RoundTrip.lean`)

| Theorem | Plain-English statement | Hypotheses |
|---------|-------------------------|------------|
| `decode_encode` | If `encode s v` gives `bs`, decoding `bs ++ rest` returns `v` and exactly `rest` (round trip and prefix-freeness) | `encode s v = some bs` |
| `encode_decode` | If `decode` succeeds on `bs` with `(v, rest)`, then `v` is encodable and `bs` is its encoding followed by `rest`: only canonical encodings are accepted | none |
| `decode_eq_some_iff` | Both directions of the two above in one statement | none |
| `decode_append` | Bytes after a decoded value do not change the result; they are returned unread | decode succeeded |
| `encode_injective`, `encode_prefix_free` | Equal encodings under one schema come from equal values; if one encoding is a prefix of another they are equal | both encodings exist |
| `encode_isSome_iff_valid` | `encode` succeeds exactly on valid values (right shape and canonical) | none |
| `decode_valid` | Whatever `decode` returns is valid | decode succeeded |
| `progress`, `minSize_pos_iff`, `encode_eq_nil_of_zeroSized` | A successful decode consumes at least `minSize s` bytes; `minSize` is positive exactly when the schema is not zero-sized; a zero-sized schema encodes to no bytes | as stated |
| `minSize_attained` | `minSize` is the size of some encoding | `s.WellFormed` (false without it, for example `(enum (0 u8) (0 unit))`) |
| `decode_set_sorted`, `decode_map_sorted` | A decoded set or map has strictly ascending keys at every pair of positions, so no duplicate keys | decode succeeded |
| `Value.cmp_self`, `cmp_eq_iff`, `cmp_swap`, `cmp_trans`, `Value.beq_iff` | The key order is a strict total order that says `eq` only for equal values; `==` on values is equality | none |
| `toLE_length`, `fromLE_toLE`, `natToSint_sintToNat` | Little-endian encoding has the requested length and reads back modulo `256^w`; two's complement conversion is inverse on in-range integers | in-range integer for the last |

### Lenient decoder (`Theorems/RoundTrip.lean`)

| Theorem | Plain-English statement |
|---------|-------------------------|
| `lenient_eq_strict_of_strict` | Whenever the strict decoder accepts, the lenient decoder returns the same result |
| `lenient_canonical` | Whatever the lenient decoder returns is valid, encodes to canonical bytes, and those bytes decode strictly back to the same value with nothing left |
| `lenient_eq_normalize_raw` | The lenient decoder is the decoder that keeps every set element and map entry as read, followed by `Value.normalize` (sort, collapse repeats, last entry of a repeated map key wins) |
| `lenient_rest_eq_raw_rest` | The bytes consumed do not depend on key order or repetition |
| `normalizeMap_mem_iff`, `normalizeMap_strictAsc` | An entry survives exactly when no later entry has its key; the keys are strictly ascending |
| `normalizeSet_mem_iff`, `normalizeSet_strictAsc` | Normalising a set keeps exactly the elements it had; they are strictly ascending |
| `lenient_progress` | The lenient decoder consumes at least `minSize s` bytes |

### Grammar and UTF-8 (`Theorems/Grammar.lean`)

| Theorem | Plain-English statement |
|---------|-------------------------|
| `decode_iff_encodes`, `encode_iff_encodes` | `decode` and `encode` agree with the relational grammar `Encodes` of `BorshSpec/Grammar.lean`, which was written from the prose without a decoder |
| `validUtf8_iff` | `validUtf8` accepts exactly the byte strings of the RFC 3629 grammar (Unicode Table 3-7), `WellFormedUtf8` |
| `validUtf8_iff_validateUTF8` | `validUtf8` agrees with Lean's `ByteArray.validateUTF8` on every byte string (the bounded `selftest-utf8` becomes a theorem) |
| `toLE_eq_leBytes`, `sintToNat_eq_twosComplement`, `isNaN32_iff`, `isNaN64_iff` | The codec's little-endian, two's complement and NaN tests equal the grammar's separately written ones |

The grammar shares with the codec the key order `Value.cmp`, the integer widths and
the representation of values, so agreement says nothing about those three.

### Resources, text forms (`Theorems/Resources.lean`)

| Theorem | Plain-English statement |
|---------|-------------------------|
| `decodeC_result` | The step-counting decoder returns what `decode` returns |
| `factor_pos` | Every schema has a positive cost factor |
| `decode_steps_le`, `decode_steps_le_consumed`, `decode_steps_le_empty` | Decoding takes at most `(input length + 1) * factor s` steps, successful or not; the same bound in consumed bytes; at most `factor s` steps on empty input |
| `decode_steps_le_of_withinSteps` | If a request passes the executable's request guard (`(length + 1) * factor <= cap`), decoding takes at most `cap` steps |
| `decode_steps_le_of_withinBudget` | If the factor is within the schema cap, `n` input bytes take at most `(n + 1) * cap` steps (the schema cap alone does not bound long inputs) |
| `decode_elems_le_steps`, `decode_elems_le` | A decoded value has at most as many collection elements as steps, and at most `(consumed + 1) * factor s` |
| `parse_print` | Parsing the printed form of any schema gives the schema back |
| `hex_decode_encode`, `hex_encode_decode` | Hex decoding inverts hex encoding; text accepted by `Hex.decode` is exactly what `Hex.encode` writes |

### Readable codec (`Theorems/SpecEquiv.lean`)

| Theorem | Plain-English statement |
|---------|-------------------------|
| `spec_encode_eq` | `Spec.encode` of `BorshSpec/Spec.lean` returns exactly what the internal `encode` returns, for every schema and value (failures included) |
| `spec_decode_eq` | `Spec.decode` returns exactly what the internal `decode` returns, for every schema and input (failures and the unread rest included) |

Both depend on `propext`, `Classical.choice` and `Quot.sound`.  A change to
`Spec.encode` or `Spec.decode` means these proofs must be updated.

### Not covered by the theorems

* That the definitions match borsh-rs: see "Evidence".  No theorem mentions Rust.
* The wall-clock time or memory of the compiled executable.  The cost theorems count
  steps of the model in `Tooling/Cost.lean`; the lenient decoder's sort is outside that model.
* The CLI front end (`Main.lean`: argument parsing, line protocol, buffering).  It is
  tested by `lake test`, not proved.
* The statement of `decode_iff_encodes` is only as good as the grammar `Encodes`,
  which is read against the prose by hand.
* Divergences from borsh-rs listed in `DECISIONS.md` and `vectors/divergences.tsv`.

CI runs `lake build --wfail`, so a `sorry` anywhere fails the build; no file sets
`warn.sorry false`.  Separate steps
of `.github/workflows/lean.yml` also reject `sorry`, `native_decide`, `axiom`,
`partial`, `unsafe`, `opaque`, `implemented_by`, `extern` and `csimp` in the sources
(the compiled executable then runs the definitions the theorems are about), and check
that every theorem has an axiom pin.

## Layout

| Path | Contents |
|------|----------|
| `BorshSpec/Spec.lean` | **the format, readable**: `Schema`, `Value`, little-endian integers and NaN tests, `takeExact`, the key order `Value.cmp` and `strictAsc`, and `Spec.encode` / `Spec.decode` |
| `BorshSpec/Utf8.lean` | `validUtf8`, intended to equal Rust `core::str::from_utf8` (RFC 3629 table) |
| `BorshSpec/Utf8Grammar.lean`, `BorshSpec/Grammar.lean` | the UTF-8 grammar `WellFormedUtf8` and the relational grammar `Encodes`, written from the prose without a decoder |
| `BorshSpec/Schema.lean` | float predicate, decidable `wellFormed`, `minSize` (the type and `zeroSized` are in `Spec.lean`) |
| `BorshSpec/Typing.lean` | `hasType`, `canonical`, and the `HasType`/`Canonical`/`Valid` Props |
| `BorshSpec/Encode.lean` | the internal `encode : Schema → Value → Option (List UInt8)` that the theorems are about |
| `BorshSpec/Decode.lean` | the internal `decode : Schema → List UInt8 → Option (Value × List UInt8)`, via `decodeWith` and `KeyPolicy` |
| `BorshSpec/Tooling/Lenient.lean` | `Lenient.decode`: borsh-rs without `de_strict_order` |
| `BorshSpec/Tooling/Cost.lean` | a resource model, not part of the format definition: `decodeC` (decode with a step counter), `Schema.factor`, `Value.elems`, the schema cap `maxFactor` and the request cap `maxSteps` |
| `BorshSpec/Tooling/Hex.lean` | `Hex.encode`, `Hex.decode` |
| `BorshSpec/Tooling/Parse.lean` | `parseSchema : String → Except String Schema` and `Schema.print` |
| `BorshSpec/Tooling/Examples.lean` | `#guard` and `rfl` checks run at build time, including `Spec.*` against the internal codec |
| `BorshSpec/Theorems.lean`, `BorshSpec/Theorems/` | theorems (second library, `BorshSpecTheorems`): the statements in `RoundTrip.lean`, `Grammar.lean`, `Resources.lean`, `SpecEquiv.lean`; their proofs in the lowercase directories `roundtrip/`, `grammar/`, `resources/`, `specequiv/`; the axiom pins in `Axioms.lean`; `SpecEquiv.lean` proves that the readable codec equals the internal one |
| `doc/` | a separate Lake package (Verso) that renders `BorshSpec/Spec.lean` as one HTML page; not part of the main package |
| `Main.lean` | the `borsh-spec` executable; imports the definitions only |
| `vectors/core.tsv` | conformance corpus for the strict decoder |
| `vectors/ordering.tsv` | key order: `Result`, explicit discriminants, signed integers, strings, nesting |
| `vectors/lenient.tsv` | lenient mode (`@mode lenient`): sorting, last-write-wins, collapsing sets |
| `vectors/cli.tsv` | protocol and resource-guard edge cases |
| `vectors/divergences.tsv` | known divergences from borsh-rs, with the spec's answers |
| `tools/utf8_digest.rs` | the `selftest-utf8` enumeration run through Rust's `core::str::from_utf8` (CI compares its output with the Lean validator's) |
| `PROTOCOL.md` | schema text syntax, line protocol, decoding and lenient semantics |
| `DECISIONS.md` | numbered decisions, with the places where the prose README is ambiguous |

## Build, lint, test

Install [elan](https://github.com/leanprover/elan); the toolchain
(`leanprover/lean4:v4.35.0`, pinned in `lean-toolchain`) is fetched on demand.
Dependency: [Batteries](https://github.com/leanprover-community/batteries) at tag
`v4.35.0` (used only for its linter).  No Mathlib.

```sh
cd lean
lake build --wfail          # definitions, executable and theorems; warnings are errors
lake build borsh-spec       # just the executable and what it imports
lake test                   # borsh-spec check on the vector files
lake lint                   # Batteries runLinter on the definitions, the theorems and Main
lake env leanchecker BorshSpec.Theorems   # replay the compiled theorem modules through the standalone kernel checker
lake exe borsh-spec selftest-utf8
```

CI (`.github/workflows/lean.yml`) runs the same on `lean/**` changes and also checks
that every module, helpers included, is imported by its library root, scans the
sources as described under "What is proven", and compares the UTF-8 enumeration with
`tools/utf8_digest.rs` (needs `rustc`).

## Reading the specification in a browser

`BorshSpec/Spec.lean` can be rendered as a single literate HTML page: the module
documentation becomes prose, each docstring sits next to the definition it
documents, and the code shown is the real code, highlighted, with hover types.
The page is generated from `Spec.lean` itself, never from a copy.

```sh
./doc/render.sh        # writes out/spec.html, one self-contained file
```

`doc/` is a separate Lake package that depends on [Verso](https://github.com/leanprover/verso)
(pinned to the release matching this Lean toolchain).  The main package has no
dependency on it, and `lake build`, `lake test` and `lake lint` never touch it.  The
first run builds Verso, which takes about a minute; it needs network access to
github.com, elan and python3 (standard library only).  To get the full multi-page Verso
site instead, run `lake query :literateHtml` in `doc/`.  The output directory `out/` is
git-ignored.  CI renders the page in a separate job and keeps it as the
`borsh-spec-html` build artifact, so a Verso or toolchain bump that breaks rendering
fails there.

The page has no external assets and opens from disk.  A few hover tooltips link to
lean-lang.org, which needs the network when followed.

## The `borsh-spec` executable

```
borsh-spec decode [--lenient] [--line-buffered] [--max-factor N] [--max-steps N]
borsh-spec check [--lenient] FILE...
borsh-spec selftest-utf8
```

`decode` reads `SCHEMA<TAB>HEX` lines from stdin and writes one of
`ok<TAB>CONSUMED<TAB>REENCODED_HEX`, `err<TAB>REASON` or `bad<TAB>REASON` per line;
`--lenient` selects the decoder of borsh-rs without `de_strict_order`.  Output is
block-buffered (flushed every 8192 lines and at EOF); a client that writes one
request and waits for the reply must pass `--line-buffered`.  Beyond the protocol the
binary checks, for every `ok`, that the decoded value is valid and that re-encoding is
consistent with the input (strict: equal to the consumed bytes; lenient: decodes
strictly back to the same value); a violation prints `err<TAB>internal: ...`.  See
`PROTOCOL.md` for the full protocol, the vector file format, and the resource guard
(schemas whose `factor` exceeds 2^20 are `bad`, and so are requests for which
`(input length + 1) * factor` exceeds 2^26).

Example (a default Rust `Result<u8, u8>` set, written in key order, and its
out-of-order input in lenient mode):

```sh
printf '(set (enum (1 u8) (0 u8)))\t0200000001050001\n' | lake exe borsh-spec decode
# ok	8	0200000001050001
printf '(set (enum (1 u8) (0 u8)))\t0200000000010105\n' | lake exe borsh-spec decode --lenient
# ok	8	0200000001050001
```

## Scope

Covered: all integer widths (little endian, two's complement), `f32`/`f64` (raw bits,
NaN rejected, `-0.0` distinct), `bool`, `unit`/tuples, `option`, `string` (exact
`from_utf8` validity), fixed arrays, `vec`, enums with explicit tags and an explicit
key order (default enums, `use_discriminant`, `Result`, explicit discriminants), strict
`map`/`set` (strictly ascending keys in the Rust `Ord` order), the lenient decoder of
borsh-rs, the zero-sized-type and float-key bans (schema well-formedness).

Not covered (see `DECISIONS.md`): recursive types and depth limits; user types with
custom `Ord`, `Serialize` or `Deserialize`; wrapper types whose Rust size is non-zero
but whose encoding is empty, such as `Box<()>` (decision 27); types such as
`SocketAddr`, `Box`, `Rc`, `Cow` and `PhantomData`, which are Rust types over the same
primitives; `NonZero*` integers (decode rejects 0; the schema syntax has no form for
them); insertion-ordered containers (`IndexMap`, `IndexSet`), which borsh-rs writes in
insertion order and does not order-check, so they are not the format described here;
the byte order of `HashMap` iteration (serialisation always sorts); the cost of
lenient sorting.  `usize` and `isize` are `u64` and `i64` here; borsh-rs fails to
decode a `usize` above `u32::MAX` on a 32-bit target, which is not modelled.

## Evidence

All of this is testing, not proof.  The Rust side of the differential evidence is a
harness that is not part of this repository (it needs a borsh-rs checkout as a path
dependency); its method is decision 24 and its figures below are those of one run, on
one host (Darwin arm64, rustc 1.98.0), against borsh-rs at commit `c4749d6a`, with fixed
seeds.

* **Vectors**: `lake test` runs 513 cases (`core` 359, `ordering` 71, `lenient` 54,
  `cli` 23, `divergences` 6) against the Lean code.  Expected `ok` lines were written by
  hand (or from small generators that are not part of this repository), not produced by
  the Lean code under test.  They cover every schema form, truncated input,
  `0xffffffff` length prefixes, NaN payloads, `-0.0`, invalid UTF-8, keys in numeric
  versus byte order, `Result` and discriminant orders, duplicate and unsorted keys in
  strict and lenient mode, sparse enum tags, trailing bytes and ill-formed schemas.
* **The vectors against borsh-rs** (differentially tested): the same files were run
  through borsh-rs by the harness, each line mapped to a Rust type with the same schema.
  The `de_strict_order` build checks the strict-mode lines and the default build checks
  the lenient-mode lines and the expected `ok` answers of strict-mode lines.  Result: 299 comparisons in the default build and 460 in the
  `de_strict_order` build, no disagreement.
  The lines that are not compared are those with no Rust counterpart: ill-formed or
  oversized schemas and invalid hex (expected `bad`), and a few schemas that cannot be
  instantiated as Rust types (an array of a million unit slots nested in arrays, a
  20-fold nested `Vec`, `[u8; 4294967295]`).  The `divergences.tsv` lines are the ones where the answer of the
  specification differs from borsh-rs (decisions 3, 15 and 27); the harness classifies
  them as the documented divergences.
* **Generated inputs against borsh-rs** (differentially tested; exhaustively enumerated
  under stated bounds where noted): for 178 Rust types (std containers, derived
  structs and enums, every map and set as `BTreeMap`/`HashMap`/`BTreeSet`/`HashSet`),
  127,529,490 inputs per build, each compared for accept or reject, bytes consumed and
  re-encoding.  The default build of borsh-rs is compared with `borsh-spec decode
  --lenient` and the `de_strict_order` build with `borsh-spec decode`; there is no
  allowance for key order.  Result: no disagreement in either build; a second run with
  another seed (393,129,490 inputs per build) also none.  The inputs are valid values
  from a generator, their mutations, random bytes, and enumerations under stated bounds:
  all byte strings of length 0 to 2, every length prefix of a fixed set followed by every
  body of length 0 to 4 over an 8-byte alphabet, every sequence of up to six entries (up
  to three for 25-entry sets) over a fixed key set for each key-sensitive map and set
  type, all 3-byte UTF-8 bodies, all `f32` NaN and infinity patterns, integer extremes.
  The only non-matches are the documented zero-size classes (decisions 3, 15 and 27):
  `rust_zst_bypass` is borsh-rs accepting a `Vec<Box<()>>`-like collection of any count
  from no input where the specification rejects the schema, and is capped at 100,000
  elements (larger counts are not run).
* **Sensitivity of the harness**: it was also run against 19 deliberately broken Lean
  builds (a wrong NaN test, a wrong enum order, a first-wins lenient decoder, unchecked
  key order, ...): each is detected, and a strict-only or lenient-only break is seen in
  the matching build only.  The list is hand-picked, so this shows the harness can see
  these faults, not that it sees all faults.
* **Not compared**: encoding failures in Rust (NaN, collections of 2^32 elements or
  more); types without a counterpart in the schema syntax (`NonZero*`, `char`, `IpAddr`
  and other `core::net` types, recursive types); other hosts, pointer widths and
  borsh-rs commits.  The Lean request guard (`2^26` steps) did not fire in these runs; it
  answers `bad` for a well-formed request that is merely large, such as a `(vec u8)` of
  34 MB (see `PROTOCOL.md`).
* **UTF-8**: `selftest-utf8` compares `validUtf8` with Lean's `ByteArray.validateUTF8`
  on every byte string of length 1 to 3 and on length-4 strings whose first two bytes
  are arbitrary and whose last two come from a 15-value sample (exhaustively enumerated
  under those bounds; nothing of length 5 or more).  It prints per-length accept
  counts and FNV-1a digests (lengths 1 to 4: 128, 18304, 2650112, 439296 accepted;
  digests 15916373298706122661, 220262124203203237, 16099763588572943141,
  6323684113820245157).  `tools/utf8_digest.rs` runs the same enumeration through Rust's
  `core::str::from_utf8` and prints the same figures; CI compares the two outputs.
  Separately, `validUtf8_iff_validateUTF8` is a theorem.
* **Throughput**: `borsh-spec decode` on one million lines (eight short schemas cycled:
  a tuple, a string, a vector, a map, a set, an enum, nested vectors, an option; all
  `ok`) takes about 1.7 s in strict mode and 1.9 s with `--lenient`, single-threaded,
  on an Apple M5 Pro.  A single line with a two-million-element `(vec u8)` (4 MB of hex)
  is decoded in about 0.5 s without stack problems.
