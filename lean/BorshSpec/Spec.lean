import BorshSpec.Utf8

/-!
# The Borsh format, in one file

This is the file to read.  It defines what a schema and a value are, how integers
and keys are ordered on the wire, and two functions, `Spec.encode` and
`Spec.decode`.  Everything is total and structurally recursive: no `partial`, no fuel.

*Short on time?*  Read **Types**, then jump to **The codec**.  Integers, key order and
UTF-8 are helpers that the codec calls; the codec's arms follow the order of the
specification table in `lean/README.md` (with `Unit`, `Struct`, `Fields`, `Named fields`
and `Unnamed fields` all in the one `tuple` arm).

* **Types** (`Schema`, `Value`): a schema is a Rust type, a value is data of that type.
* **Integers**: little endian; floats are raw bits and NaN is an error.
* **Key order**: map keys and set elements are written in strictly ascending order.
* **UTF-8**: strings must be valid UTF-8 (Unicode Table 3-7, below).
* **`Spec.encode`**, **`Spec.decode`**: the codec.  Decoding is strict: it accepts
  only what encoding produces.

Bytes are `List UInt8`.  Failure is `none` (Rust: `Err`, `None`).  The theorems
are in `BorshSpec/Theorems/`; the internal codec they are stated about is
`BorshSpec/Encode.lean` and `Decode.lean` (see `lean/README.md`).
-/

namespace BorshSpec

/-! ## Types -/

/-- The five integer widths of Borsh. -/
inductive IntWidth where
  /-- One byte. -/ | w8
  /-- Two bytes. -/ | w16
  /-- Four bytes. -/ | w32
  /-- Eight bytes. -/ | w64
  /-- Sixteen bytes. -/ | w128
  deriving DecidableEq, Repr, Inhabited

/-- The number of bytes occupied by an integer of the given width. -/
def IntWidth.bytes : IntWidth → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8
  | .w128 => 16

/-- A Borsh schema: the shape of a Rust type.  Structs, tuples and `()` are all
`tuple`; `()` is `tuple []`.  Recursive types are not expressible.

An enum is a list of variants, each a `(wire tag, payload schema)` pair; a unit
variant has payload `tuple []`.  A variant has two numbers, and they are different:

* its **wire tag**, the byte written before the payload (Rust: the declaration
  position, or the discriminant under `#[borsh(use_discriminant = true)]`);
* its **variant index**, its position in this list, which decides how it sorts as a
  map key or set element (Rust: `#[derive(Ord)]` orders variants by discriminant).

A value records the variant index (`Value.enum i payload`) and `encode` looks up the
tag.  For a plain derived enum the two agree: `[(0, A), (1, B), …]`.  They differ for
`Result<T, E>`, which is `enum [(1, T), (0, E)]`: `Ok v` is `Value.enum 0 v`, sorts
before every `Err`, and is written as the byte `01` followed by `v`. -/
inductive Schema where
  /-- `u8` to `u128`. -/ | uint (w : IntWidth)
  /-- `i8` to `i128`, two's complement. -/ | sint (w : IntWidth)
  /-- `f32`; NaN is an error. -/ | f32
  /-- `f64`; NaN is an error. -/ | f64
  /-- `bool`. -/ | bool
  /-- `String`. -/ | string
  /-- `Option<T>`. -/ | option (s : Schema)
  /-- `Vec<T>`. -/ | vec (s : Schema)
  /-- `[T; n]`: `n` elements, no length prefix. -/ | array (n : Nat) (s : Schema)
  /-- A struct or tuple: fields in order. -/ | tuple (fs : List Schema)
  /-- An enum: `(wire tag, payload)` per variant, in variant-index order. -/
  | enum (vs : List (UInt8 × Schema))
  /-- `HashMap<K, V>` / `BTreeMap<K, V>`.  A well-formed schema has no float inside
  the key (Rust floats have no `Ord`); `encode` and `decode` do not check this
  (`Schema.wellFormed` in `Schema.lean` does). -/ | map (k v : Schema)
  /-- `HashSet<T>` / `BTreeSet<T>`.  The same no-float rule applies to `s`. -/ | set (s : Schema)
  deriving Repr

/-- A Borsh value, untyped on its own (`HasType` in `Typing.lean` says which schema
it fits).  Integers are `Nat`/`Int`, floats are raw bits (so `-0.0 ≠ 0.0`), strings
are bytes, collections are lists in wire order, and an enum value holds the *index*
of its variant in the schema's list, not its wire tag. -/
inductive Value where
  /-- An unsigned integer. -/ | uint (n : Nat)
  /-- A signed integer. -/ | sint (i : Int)
  /-- An `f32`, as bits. -/ | f32 (bits : UInt32)
  /-- An `f64`, as bits. -/ | f64 (bits : UInt64)
  /-- A `bool`. -/ | bool (b : Bool)
  /-- A string, as UTF-8 bytes. -/ | string (bytes : List UInt8)
  /-- `None`. -/ | optNone
  /-- `Some v`. -/ | optSome (v : Value)
  /-- A `Vec`. -/ | vec (xs : List Value)
  /-- A fixed-length array. -/ | array (xs : List Value)
  /-- A struct or tuple; `tuple []` is `()`. -/ | tuple (xs : List Value)
  /-- An enum value: variant index (not wire tag), payload. -/ | enum (idx : Nat) (v : Value)
  /-- A map, as its entries in wire order. -/ | map (kvs : List (Value × Value))
  /-- A set, as its elements in wire order. -/ | set (xs : List Value)
  deriving Repr

/-- The schema `()`. -/
def Schema.unit : Schema := .tuple []

/-- The value `()`. -/
def Value.unit : Value := .tuple []

namespace Schema

mutual

/-- Whether every value of the schema encodes to zero bytes (Rust: `size_of == 0`):
`()`, a struct or tuple of zero-sized fields, and `[T; 0]` or `[T; n]` with `T`
zero-sized.  Borsh rejects zero-sized element types in `Vec`, sets and map keys,
since a count could then be huge for free. -/
def zeroSized : Schema → Bool
  | .array n s => n == 0 || zeroSized s
  | .tuple fs => zeroSizedAll fs
  | _ => false

/-- `zeroSized` holds for every schema of a list (vacuously for `[]`). -/
def zeroSizedAll : List Schema → Bool
  | [] => true
  | s :: fs => zeroSized s && zeroSizedAll fs

end

end Schema

/-! ## Integers and floats -/

/-- `toLE w n` is the `w`-byte little-endian encoding of `n`; higher bits are dropped. -/
def toLE : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => (n % 256).toUInt8 :: toLE w (n / 256)

/-- The number denoted by a little-endian byte list. -/
def fromLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * fromLE bs

/-- Split off exactly `n` leading bytes, or fail if fewer are available (Rust:
`bytes.split_at(n)` after a length check).  It never allocates `n` bytes, only looks at
the input, so a hostile `n` costs no more than the input does. -/
def takeExact (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if (bs.take n).length = n then some (bs.take n, bs.drop n) else none

/-- Read a `w`-byte little-endian unsigned integer, returning the rest. -/
def readLE (w : Nat) (bs : List UInt8) : Option (Nat × List UInt8) :=
  (takeExact w bs).map fun (a, r) => (fromLE a, r)

/-- Whether a 32-bit pattern is a NaN: exponent all ones, mantissa non-zero.  As bit
masks: `bits & 0x7F80_0000 == 0x7F80_0000 && bits & 0x007F_FFFF != 0`, which is
`f32::is_nan` on `f32::from_bits(bits)`. -/
def isNaN32 (bits : UInt32) : Bool :=
  (bits.toNat / 2 ^ 23) % 2 ^ 8 == 2 ^ 8 - 1 && bits.toNat % 2 ^ 23 != 0

/-- Whether a 64-bit pattern is a NaN: `bits & 0x7FF0_0000_0000_0000 ==
0x7FF0_0000_0000_0000 && bits & 0x000F_FFFF_FFFF_FFFF != 0`, as `f64::is_nan`.  Only
NaN fails: infinities, subnormals and `-0.0` (bits `0x8000_0000_0000_0000`) are fine. -/
def isNaN64 (bits : UInt64) : Bool :=
  (bits.toNat / 2 ^ 52) % 2 ^ 11 == 2 ^ 11 - 1 && bits.toNat % 2 ^ 52 != 0

namespace Schema

/-- The width-`w` signed range test: `iN::MIN <= i && i <= iN::MAX`. -/
def sintInRange (w : IntWidth) (i : Int) : Bool :=
  decide (-(2 ^ (8 * w.bytes - 1) : Int) ≤ i ∧ i < 2 ^ (8 * w.bytes - 1))

/-- The two's-complement unsigned residue of a signed integer on `w` bytes: Rust's
`i as uN`, which wraps (`-2i32 as u32 = 0xFFFF_FFFE`). -/
def sintToNat (w : IntWidth) (i : Int) : Nat := (i % 2 ^ (8 * w.bytes)).toNat

/-- The signed integer denoted by an unsigned residue on `w` bytes: Rust's `n as iN`. -/
def natToSint (w : IntWidth) (n : Nat) : Int :=
  if n < 2 ^ (8 * w.bytes - 1) then (n : Int) else (n : Int) - 2 ^ (8 * w.bytes)

/-- Read a `u32` length or count (the partner of `Spec.u32Prefix`). -/
def readU32 (bs : List UInt8) : Option (Nat × List UInt8) := readLE 4 bs

end Schema

/-! ## Key order -/

namespace Value

/-- Which constructor built a value (`uint` is 0, …, `set` is 13).  `cmp` uses it only
to stay total when values of different shape meet, which never happens in well-typed
data. -/
def shapeIndex : Value → Nat
  | .uint _ => 0
  | .sint _ => 1
  | .f32 _ => 2
  | .f64 _ => 3
  | .bool _ => 4
  | .string _ => 5
  | .optNone => 6
  | .optSome _ => 7
  | .vec _ => 8
  | .array _ => 9
  | .tuple _ => 10
  | .enum _ _ => 11
  | .map _ => 12
  | .set _ => 13

/-- Byte-lexicographic order, a proper prefix being smaller (Rust: `<[u8]>::cmp`). -/
def cmpBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match compare a b with
    | .eq => cmpBytes as bs
    | o => o

mutual

/-- The order of Rust's `Ord` on the matching std types.  Map keys and set elements
are written in this order:

* integers numerically, signed ones included: `-1 < 0`, although the bytes
  `ff ff ff ff` are larger than `00 00 00 00`;
* `false < true`; `None < Some _`, then by payload;
* strings by their UTF-8 bytes;
* `Vec`, arrays, structs, tuples, sets and maps lexicographically, element by
  element, a proper prefix being smaller;
* enums by variant index (not wire tag), then by payload.

Floats are banned from keys; they are ordered by bits only to keep `cmp` total.  The
last arm, by `shapeIndex`, is there for totality too; a Rust implementation can ignore
both.  There are three copies of the lexicographic loop (`cmpBytes`, `cmpList`,
`cmpPairs`) because a nested inductive needs one mutual definition per list shape. -/
def cmp : Value → Value → Ordering
  | .uint a, .uint b => compare a b
  | .sint a, .sint b => compare a b
  | .f32 a, .f32 b => compare a b
  | .f64 a, .f64 b => compare a b
  | .bool a, .bool b => compare a b
  | .string a, .string b => cmpBytes a b
  | .optNone, .optNone => .eq
  | .optNone, .optSome _ => .lt
  | .optSome _, .optNone => .gt
  | .optSome a, .optSome b => cmp a b
  | .vec a, .vec b => cmpList a b
  | .array a, .array b => cmpList a b
  | .tuple a, .tuple b => cmpList a b
  | .set a, .set b => cmpList a b
  | .enum i a, .enum j b =>
    match compare i j with
    | .eq => cmp a b
    | o => o
  | .map a, .map b => cmpPairs a b
  | a, b => compare a.shapeIndex b.shapeIndex

/-- Lexicographic extension of `cmp` to lists of values. -/
def cmpList : List Value → List Value → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmp a b with
    | .eq => cmpList as bs
    | o => o

/-- Lexicographic extension of `cmp` to lists of `(key, value)` pairs. -/
def cmpPairs : List (Value × Value) → List (Value × Value) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (ka, va) :: as, (kb, vb) :: bs =>
    match cmp ka kb with
    | .eq =>
      match cmp va vb with
      | .eq => cmpPairs as bs
      | o => o
    | o => o

end

/-- `==` on values: the key order says `eq`.  (The derived `BEq` of a nested
inductive is opaque, so nothing could be proved about it.) -/
instance : BEq Value := ⟨fun a b => cmp a b == .eq⟩

/-- The list is strictly ascending: this rules out duplicates and unsorted input at
once. -/
def strictAsc : List Value → Bool
  | a :: b :: rest => cmp a b == .lt && strictAsc (b :: rest)
  | _ => true

end Value

/-! ## UTF-8

A `String` is a `u32` byte length followed by that many bytes, which must be
well-formed UTF-8: exactly the byte strings Rust's `std::str::from_utf8` accepts.
That is no overlong forms, no surrogates, nothing above `U+10FFFF`.  The rule is
Table 3-7 of the Unicode Standard; a byte string is well-formed when it is a
concatenation of these nine shapes (`..` is an inclusive byte range, all in hex):

| Code points          | 1st byte | 2nd byte | 3rd byte | 4th byte |
|----------------------|----------|----------|----------|----------|
| U+0000..U+007F       | 00..7F   |          |          |          |
| U+0080..U+07FF       | C2..DF   | 80..BF   |          |          |
| U+0800..U+0FFF       | E0       | A0..BF   | 80..BF   |          |
| U+1000..U+CFFF       | E1..EC   | 80..BF   | 80..BF   |          |
| U+D000..U+D7FF       | ED       | 80..9F   | 80..BF   |          |
| U+E000..U+FFFF       | EE..EF   | 80..BF   | 80..BF   |          |
| U+10000..U+3FFFF     | F0       | 90..BF   | 80..BF   | 80..BF   |
| U+40000..U+FFFFF     | F1..F3   | 80..BF   | 80..BF   | 80..BF   |
| U+100000..U+10FFFF   | F4       | 80..8F   | 80..BF   | 80..BF   |

Everything else is ill-formed: a lone continuation byte, `C0`, `C1`, `F5..FF`, a
surrogate (`ED A0..BF`), or a truncated sequence.  `validUtf8` (`Utf8.lean`) is the
validator the codec calls; `Utf8Grammar.lean` states this table as a relation, one
constructor per row, and `validUtf8_iff` proves the two agree. -/

/-! ## The codec

`Spec.encode s v` is the canonical encoding of `v` under `s`, or `none` if `v` is
not a valid value of `s`.  `Spec.decode s bs` reads one value from the front of `bs`
and returns it with the unread bytes, or `none` if the input is rejected.  The
encoder takes collections *in wire order* and never sorts or repairs anything.

**What is rejected** (every one of these is `none`):

* *Decode*: truncated input; a `bool` byte other than 0 or 1; an `Option` tag other
  than 0 or 1; an enum tag no variant carries; a NaN float; a string that is not valid
  UTF-8; a zero-sized element type in a `Vec`, set or map key; map keys or set
  elements that are not strictly ascending (so a duplicate is rejected too).
* *Encode* rejects the matching cases, and also: an integer outside the range of its
  width; an array whose length is not `n`; a count or byte length of `2^32` or more;
  a variant index out of range; a wire tag already used by an earlier variant; a value
  whose shape does not fit the schema.

**Trailing bytes.**  `decode` returns the unread bytes and does not look at them.  A
caller that wants Rust's `try_from_slice` behaviour rejects unless the returned rest is
empty; that check is the caller's, not part of `decode`. -/

namespace Spec

/-- `repr(len() as u32)`: a count or byte length, as four bytes. -/
def u32Prefix (n : Nat) : List UInt8 := toLE 4 n

/-- Write every element with `enc` and concatenate; fail if any element fails. -/
def encodeAll {α : Type} (enc : α → Option (List UInt8)) : List α → Option (List UInt8)
  | [] => some []
  | x :: rest => do
    let bytes ← enc x
    let more ← encodeAll enc rest
    pure (bytes ++ more)

/-- Reject unless the keys are strictly ascending (no duplicates, no disorder). -/
def requireAscending (keys : List Value) : Option Unit :=
  if Value.strictAsc keys then some () else none

mutual

/-- The canonical encoding; `none` means the value is invalid for the schema. -/
def encode : Schema → Value → Option (List UInt8)
  -- Integers: little_endian(x); the value must fit the width.
  | .uint w, .uint n =>
    if n < 2 ^ (8 * w.bytes) then some (toLE w.bytes n) else none
  | .sint w, .sint i =>
    if Schema.sintInRange w i then some (toLE w.bytes (Schema.sintToNat w i)) else none
  -- Floats: err_if_nan(x), then little_endian(bits).
  | .f32, .f32 bits => if isNaN32 bits then none else some (toLE 4 bits.toNat)
  | .f64, .f64 bits => if isNaN64 bits then none else some (toLE 8 bits.toNat)
  -- Unit, struct, tuple, named or unnamed fields: every field in order; `()` writes
  -- nothing.  (README rows Unit, Struct, Fields, Named fields, Unnamed fields.)
  | .tuple fs, .tuple xs => encodeFields fs xs
  -- Bool: 1 for true, 0 for false.
  | .bool, .bool b => some [if b then 1 else 0]
  -- Fixed-size array: every element, no length prefix.
  | .array n s, .array xs =>
    if xs.length == n then encodeAll (encode s) xs else none
  -- Vec: repr(len as u32), then every element.  Zero-sized elements are rejected.
  | .vec s, .vec xs =>
    if s.zeroSized || 2 ^ 32 ≤ xs.length then none
    else do
      let body ← encodeAll (encode s) xs
      pure (u32Prefix xs.length ++ body)
  -- Enum: the wire tag of the variant at index `i`, then its payload.  `none` for an
  -- index out of range or a tag already used by an earlier variant.
  | .enum vs, .enum i payload => encodeVariant vs [] i payload
  -- HashMap: repr(len as u32), then key and value of each entry.  `encode` does NOT
  -- sort: the entries must already be in strictly ascending key order (so no duplicate
  -- keys), else `none`.  Also `none` for a zero-sized key or 2^32 or more entries.
  | .map k v, .map entries =>
    if k.zeroSized || 2 ^ 32 ≤ entries.length then none
    else do
      requireAscending (entries.map fun entry => entry.1)
      let encodeEntry (entry : Value × Value) : Option (List UInt8) := do
        let keyBytes ← encode k entry.1
        let valueBytes ← encode v entry.2
        pure (keyBytes ++ valueBytes)
      let body ← encodeAll encodeEntry entries
      pure (u32Prefix entries.length ++ body)
  -- HashSet: repr(len as u32), then the elements.  As for maps, no sorting: the
  -- elements must already be strictly ascending.  Also `none` for a zero-sized
  -- element or 2^32 or more elements.
  | .set s, .set xs =>
    if s.zeroSized || 2 ^ 32 ≤ xs.length then none
    else do
      requireAscending xs
      let body ← encodeAll (encode s) xs
      pure (u32Prefix xs.length ++ body)
  -- Option: 0 for None; 1 and then the payload for Some.
  | .option _, .optNone => some [0]
  | .option s, .optSome v => do
    let payload ← encode s v
    pure (1 :: payload)
  -- String: repr(byte length as u32), then the bytes, which must be valid UTF-8.
  -- The length is the number of bytes, not characters.  `none` for 2^32 or more bytes.
  | .string, .string bytes =>
    if bytes.length < 2 ^ 32 && validUtf8 bytes then some (u32Prefix bytes.length ++ bytes)
    else none
  -- Any other pairing is not a value of that schema.
  | _, _ => none

/-- Struct fields in order; the schema and value must have the same number of fields. -/
def encodeFields : List Schema → List Value → Option (List UInt8)
  | [], [] => some []
  | s :: fs, v :: vs => do
    let first ← encode s v
    let others ← encodeFields fs vs
    pure (first ++ others)
  | _, _ => none

/-- Encode `payload` as the variant at index `i` of `vs`: that variant's wire tag, then
the payload.  `earlier` collects the tags of the variants before it.  If one of them
has the same tag, a decoder would read the bytes back as that earlier variant, so the
value has no encoding: reject.  (Walking down the list instead of indexing keeps the
payload schema a structural subterm of `vs`.) -/
def encodeVariant : List (UInt8 × Schema) → List UInt8 → Nat → Value → Option (List UInt8)
  | [], _, _, _ => none
  | (tag, s) :: _, earlier, 0, payload =>
    if earlier.contains tag then none
    else do
      let body ← encode s payload
      pure (tag :: body)
  | (tag, _) :: rest, earlier, i + 1, payload => encodeVariant rest (tag :: earlier) i payload

end

/-- Run `decodeOne` `n` times in a row and collect the results.  It stops at the
first failure; `n` is never used to allocate, so a hostile count only costs as many
steps as the input has bytes (a zero-sized element is rejected before the loop).  For
`array`, `n` comes from the schema, not from the input, so it is never hostile.
It builds the list front to back; the internal `decodeMany` accumulates in reverse. -/
def decodeN {α : Type} (decodeOne : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (x, rest) ← decodeOne bs
    let (xs, rest') ← decodeN decodeOne n rest
    pure (x :: xs, rest')

mutual

/-- Strict decoding of one value from the front of the input; see the section header. -/
def decode : Schema → List UInt8 → Option (Value × List UInt8)
  -- Integers: little_endian(x), as many bytes as the width.  Too few bytes: reject.
  | .uint w, bs => do
    let (n, rest) ← readLE w.bytes bs
    pure (.uint n, rest)
  | .sint w, bs => do
    let (n, rest) ← readLE w.bytes bs
    pure (.sint (Schema.natToSint w n), rest)
  -- Floats: four or eight bytes of bits.  Reject NaN.
  | .f32, bs => do
    let (n, rest) ← readLE 4 bs
    let bits := UInt32.ofNat n
    if isNaN32 bits then none else pure (.f32 bits, rest)
  | .f64, bs => do
    let (n, rest) ← readLE 8 bs
    let bits := UInt64.ofNat n
    if isNaN64 bits then none else pure (.f64 bits, rest)
  -- Unit, struct, tuple, named or unnamed fields: the fields in order; `()` reads
  -- nothing.
  | .tuple fs, bs => do
    let (xs, rest) ← decodeFields fs bs
    pure (.tuple xs, rest)
  -- Bool: one byte, 0 or 1.  Reject any other byte, and empty input.
  | .bool, 0 :: rest => some (.bool false, rest)
  | .bool, 1 :: rest => some (.bool true, rest)
  | .bool, _ => none
  -- Fixed-size array: `n` elements, no length prefix.
  | .array n s, bs => do
    let (xs, rest) ← decodeN (decode s) n bs
    pure (.array xs, rest)
  -- Vec: a u32 count, then that many elements.  Reject a zero-sized element type.
  | .vec s, bs =>
    if s.zeroSized then none
    else do
      let (count, rest) ← Schema.readU32 bs
      let (xs, rest') ← decodeN (decode s) count rest
      pure (.vec xs, rest')
  -- Enum: a tag byte names the variant, then its payload.  Reject an unknown tag.
  | .enum _, [] => none
  | .enum vs, tag :: rest => decodeVariant vs 0 tag rest
  -- HashMap: a u32 count, then entries.  Reject keys that are not strictly ascending.
  | .map k v, bs =>
    if k.zeroSized then none
    else do
      let (count, rest) ← Schema.readU32 bs
      let decodeEntry (input : List UInt8) : Option ((Value × Value) × List UInt8) := do
        let (key, afterKey) ← decode k input
        let (value, afterValue) ← decode v afterKey
        pure ((key, value), afterValue)
      let (entries, rest') ← decodeN decodeEntry count rest
      requireAscending (entries.map fun entry => entry.1)
      pure (.map entries, rest')
  -- HashSet: a u32 count, then elements.  Reject elements not strictly ascending.
  | .set s, bs =>
    if s.zeroSized then none
    else do
      let (count, rest) ← Schema.readU32 bs
      let (xs, rest') ← decodeN (decode s) count rest
      requireAscending xs
      pure (.set xs, rest')
  -- Option: tag 0 is None, tag 1 is Some and a payload.  Reject any other tag.
  | .option _, 0 :: rest => some (.optNone, rest)
  | .option s, 1 :: rest => do
    let (v, rest') ← decode s rest
    pure (.optSome v, rest')
  | .option _, _ => none
  -- String: a u32 byte length, then that many bytes.  Reject truncated input
  -- and bytes that are not valid UTF-8.
  | .string, bs => do
    let (len, rest) ← Schema.readU32 bs
    let (bytes, rest') ← takeExact len rest
    if validUtf8 bytes then pure (.string bytes, rest') else none

/-- Struct fields in order. -/
def decodeFields : List Schema → List UInt8 → Option (List Value × List UInt8)
  | [], bs => some ([], bs)
  | s :: fs, bs => do
    let (first, rest) ← decode s bs
    let (others, rest') ← decodeFields fs rest
    pure (first :: others, rest')

/-- Find the first variant whose wire tag is `tag` and decode its payload; `i` counts
the variant index while walking the list, and the result is `.enum i payload`.  No
variant has that tag: reject. -/
def decodeVariant : List (UInt8 × Schema) → Nat → UInt8 → List UInt8 →
    Option (Value × List UInt8)
  | [], _, _, _ => none
  | (tag', s) :: rest, i, tag, bs =>
    if tag' == tag then do
      let (payload, rest') ← decode s bs
      pure (.enum i payload, rest')
    else decodeVariant rest (i + 1) tag bs

end

end Spec

end BorshSpec
