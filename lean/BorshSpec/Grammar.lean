import BorshSpec.Schema
import BorshSpec.Utf8Grammar

/-!
# The Borsh wire format as a grammar

`Encodes s v bs` says that the byte string `bs` is the Borsh encoding of the value
`v` under the schema `s`.  It is written as a relation, one constructor (or a few) for
each row of the table in the "Specification" section of the repository `README.md`
and for each rule of `PROTOCOL.md`, and it contains no function that decodes.  It is a
second statement of the format, independent of the executable codec; the theorem that
the two agree is in `BorshSpec.Theorems`.

Every constructor quotes the prose rule it transcribes.  The helper relations are

* `leBytes n x`: the `n` little-endian bytes of the number `x`;
* `SizeZero s`: the schema `s` has encoded size zero (every encoding is empty);
* `EncodesAll`, `EncodesFields`, `EncodesPairs`: a list of values (or fields, or
  key/value pairs) whose encodings are concatenated;
* `Ascending`: a list of values is strictly ascending for `Value.cmp`;
* `VariantAt`: the enum variant at a given index is the first one with a given tag.
-/

namespace BorshSpec

/-- The `n` bytes of the number `x`, least significant byte first.  The bytes of
`x mod 256^n` are written; callers state `x < 256^n` where truncation must not
occur. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => UInt8.ofNat (x % 256) :: leBytes n (x / 256)

/-- The unsigned number `i mod 256^n`, which is the two's complement bit pattern of
the integer `i` in `n` bytes. -/
def twosComplement (n : Nat) (i : Int) : Nat := (i % ((256 ^ n : Nat) : Int)).toNat

/-- A `binary32` bit pattern is a NaN: with the sign bit cleared, the pattern lies
above the pattern of infinity, `0x7F800000` (exponent field all ones, mantissa field
non-zero), whatever the payload.  Written with a mask, unlike `isNaN32`, which
extracts the fields by division. -/
def IsNaN32 (bits : UInt32) : Prop :=
  0x7F800000 < (bits &&& 0x7FFFFFFF).toNat

/-- A `binary64` bit pattern is a NaN: with the sign bit cleared, the pattern lies
above the pattern of infinity, `0x7FF0000000000000`, whatever the payload. -/
def IsNaN64 (bits : UInt64) : Prop :=
  0x7FF0000000000000 < (bits &&& 0x7FFFFFFFFFFFFFFF).toNat

mutual

/-- The schema has encoded size zero: every value of it is written as no bytes.
PROTOCOL.md, "Well-formedness": "A schema has encoded size 0 when it is `unit`,
`(tuple)` of such schemas, or an `array` of length 0 or of a schema of size 0." -/
inductive SizeZero : Schema → Prop where
  /-- A tuple (struct, unit) all of whose fields have encoded size zero. -/
  | tuple (fs : List Schema) : SizeZeroAll fs → SizeZero (.tuple fs)
  /-- An array of length zero. -/
  | arrayEmpty (s : Schema) : SizeZero (.array 0 s)
  /-- An array of a schema of encoded size zero. -/
  | arrayElem (n : Nat) (s : Schema) : SizeZero s → SizeZero (.array n s)

/-- Every schema of the list has encoded size zero. -/
inductive SizeZeroAll : List Schema → Prop where
  /-- The empty list. -/
  | nil : SizeZeroAll []
  /-- A schema of size zero followed by schemas of size zero. -/
  | cons (s : Schema) (fs : List Schema) :
      SizeZero s → SizeZeroAll fs → SizeZeroAll (s :: fs)

end

/-- The list of values is strictly ascending for `Value.cmp`: each element is
smaller than the next.  Repeated elements and unsorted elements are both excluded. -/
inductive Ascending : List Value → Prop where
  /-- The empty list. -/
  | nil : Ascending []
  /-- A single element. -/
  | single (a : Value) : Ascending [a]
  /-- An element smaller than the head of an ascending list. -/
  | cons (a b : Value) (rest : List Value) :
      Value.cmp a b = .lt → Ascending (b :: rest) → Ascending (a :: b :: rest)

/-- `VariantAt vs i tag s`: in the variant list `vs`, the first variant carrying the
wire tag `tag` is at position `i` and has payload schema `s`.  Positions are the variant
indices of `Schema.enum`, the ones carried by `Value.enum`. -/
inductive VariantAt : List (UInt8 × Schema) → Nat → UInt8 → Schema → Prop where
  /-- The head of the list is the variant. -/
  | here (tag : UInt8) (s : Schema) (rest : List (UInt8 × Schema)) :
      VariantAt ((tag, s) :: rest) 0 tag s
  /-- The variant is further down the list, and the head carries another tag. -/
  | there (tag' : UInt8) (s' : Schema) (rest : List (UInt8 × Schema))
      (i : Nat) (tag : UInt8) (s : Schema) :
      tag' ≠ tag → VariantAt rest i tag s →
      VariantAt ((tag', s') :: rest) (i + 1) tag s

mutual

/-- `Encodes s v bs`: `bs` is the Borsh encoding of the value `v` of schema `s`. -/
inductive Encodes : Schema → Value → List UInt8 → Prop where
  /-- Integers (`u8` to `u128`): "integers are little endian" and
  `little_endian(x)`.  The value must fit the width. -/
  | uint (w : IntWidth) (n : Nat) :
      n < 256 ^ w.bytes →
      Encodes (.uint w) (.uint n) (leBytes w.bytes n)
  /-- Integers (`i8` to `i128`): `little_endian(x)` of the two's complement
  representation.  The value must fit the width. -/
  | sint (w : IntWidth) (i : Int) :
      -((256 ^ w.bytes / 2 : Nat) : Int) ≤ i → i < ((256 ^ w.bytes / 2 : Nat) : Int) →
      Encodes (.sint w) (.sint i) (leBytes w.bytes (twosComplement w.bytes i))
  /-- Floats, `f32`: `err_if_nan(x)`, then `little_endian(x as integer_type)`; the
  integer is the IEEE-754 bit pattern (DECISIONS.md, 9). -/
  | f32 (bits : UInt32) :
      ¬ IsNaN32 bits →
      Encodes .f32 (.f32 bits) (leBytes 4 bits.toNat)
  /-- Floats, `f64`: as `f32`, with eight bytes. -/
  | f64 (bits : UInt64) :
      ¬ IsNaN64 bits →
      Encodes .f64 (.f64 bits) (leBytes 8 bits.toNat)
  /-- Bool, `false`: "if x { repr(1 as u8) } else { repr(0 as u8) }". -/
  | boolFalse : Encodes .bool (.bool false) [0]
  /-- Bool, `true`: "if x { repr(1 as u8) } else { repr(0 as u8) }". -/
  | boolTrue : Encodes .bool (.bool true) [1]
  /-- String: "encoded = utf8_encoding(x) as Vec<u8>; repr(encoded.len() as u32);
  repr(encoded as Vec<u8>)".  The bytes are well-formed UTF-8 and their number fits
  a `u32`. -/
  | string (bytes : List UInt8) :
      WellFormedUtf8 bytes → bytes.length < 2 ^ 32 →
      Encodes .string (.string bytes) (leBytes 4 bytes.length ++ bytes)
  /-- Option, `None`: "if x.is_some() { repr(1 as u8) ... } else { repr(0 as u8) }". -/
  | optNone (s : Schema) : Encodes (.option s) .optNone [0]
  /-- Option, `Some`: "repr(1 as u8); repr(x.unwrap() as ident)". -/
  | optSome (s : Schema) (v : Value) (bs : List UInt8) :
      Encodes s v bs → Encodes (.option s) (.optSome v) (1 :: bs)
  /-- Dynamic sized array: "repr(len() as u32); for el in x { repr(el as ident) }".
  The element schema must not have encoded size zero (PROTOCOL.md, "Well-formedness"),
  and the count fits a `u32`. -/
  | vec (s : Schema) (xs : List Value) (bs : List UInt8) :
      ¬ SizeZero s → xs.length < 2 ^ 32 → EncodesAll s xs bs →
      Encodes (.vec s) (.vec xs) (leBytes 4 xs.length ++ bs)
  /-- Fixed sized arrays: "for el in x { repr(el as ident) }", with no length
  prefix; the array has exactly `n` elements. -/
  | array (n : Nat) (s : Schema) (xs : List Value) (bs : List UInt8) :
      xs.length = n → EncodesAll s xs bs →
      Encodes (.array n s) (.array xs) bs
  /-- Struct, unnamed fields and unit: "repr(x.0 as type0) repr(x.1 as type1) ...",
  "structs are serialized in the order of fields in the struct"; "Unit: We do not
  write anything" (the empty tuple). -/
  | tuple (fs : List Schema) (vs : List Value) (bs : List UInt8) :
      EncodesFields fs vs bs → Encodes (.tuple fs) (.tuple vs) bs
  /-- Enum: "repr(X as u8); repr(x.X as fieldsX)".  The value names the variant by its
  position `i` in the schema's list, the first byte is the wire tag of that variant,
  and the rest is the encoding of the payload under the variant's schema.  If several
  variants carry the same tag (such a schema is not well-formed) the first one is the
  variant of the tag. -/
  | enum (vs : List (UInt8 × Schema)) (i : Nat) (tag : UInt8) (s : Schema)
      (v : Value) (bs : List UInt8) :
      VariantAt vs i tag s → Encodes s v bs →
      Encodes (.enum vs) (.enum i v) (tag :: bs)
  /-- HashMap: "repr(x.len() as u32); for (k, v) in x.sorted_by_key() { repr(k as
  ident0); repr(v as ident1) }".  The keys are strictly ascending in the key order
  (`Value.cmp`; PROTOCOL.md, "Key order" and "Decoding semantics"), the key schema
  does not have encoded size zero, and the count fits a `u32`. -/
  | map (k v : Schema) (kvs : List (Value × Value)) (bs : List UInt8) :
      ¬ SizeZero k → kvs.length < 2 ^ 32 → Ascending (kvs.map Prod.fst) →
      EncodesPairs k v kvs bs →
      Encodes (.map k v) (.map kvs) (leBytes 4 kvs.length ++ bs)
  /-- HashSet: "repr(x.len() as u32); for el in x.sorted() { repr(el as ident) }".
  The elements are strictly ascending in the key order, the element schema does not
  have encoded size zero, and the count fits a `u32`. -/
  | set (s : Schema) (xs : List Value) (bs : List UInt8) :
      ¬ SizeZero s → xs.length < 2 ^ 32 → Ascending xs → EncodesAll s xs bs →
      Encodes (.set s) (.set xs) (leBytes 4 xs.length ++ bs)

/-- `EncodesAll s xs bs`: `bs` is the concatenation of the encodings of the values
`xs`, each under the schema `s`. -/
inductive EncodesAll : Schema → List Value → List UInt8 → Prop where
  /-- No values, no bytes. -/
  | nil (s : Schema) : EncodesAll s [] []
  /-- The encoding of the first value followed by the encodings of the others. -/
  | cons (s : Schema) (x : Value) (xs : List Value) (b bs : List UInt8) :
      Encodes s x b → EncodesAll s xs bs → EncodesAll s (x :: xs) (b ++ bs)

/-- `EncodesFields fs vs bs`: `bs` is the concatenation of the encodings of the values
`vs`, the `i`-th under the `i`-th schema of `fs`, in order. -/
inductive EncodesFields : List Schema → List Value → List UInt8 → Prop where
  /-- No fields, no bytes. -/
  | nil : EncodesFields [] [] []
  /-- The encoding of the first field followed by the encodings of the others. -/
  | cons (s : Schema) (fs : List Schema) (x : Value) (vs : List Value)
      (b bs : List UInt8) :
      Encodes s x b → EncodesFields fs vs bs →
      EncodesFields (s :: fs) (x :: vs) (b ++ bs)

/-- `EncodesPairs k v kvs bs`: `bs` is the concatenation, for each entry in order, of the
encoding of the key under `k` and then the encoding of the value under `v`. -/
inductive EncodesPairs : Schema → Schema → List (Value × Value) → List UInt8 → Prop where
  /-- No entries, no bytes. -/
  | nil (k v : Schema) : EncodesPairs k v [] []
  /-- The key and the value of the first entry, then the other entries. -/
  | cons (k v : Schema) (a b : Value) (kvs : List (Value × Value))
      (bk bv bs : List UInt8) :
      Encodes k a bk → Encodes v b bv → EncodesPairs k v kvs bs →
      EncodesPairs k v ((a, b) :: kvs) (bk ++ bv ++ bs)

end

end BorshSpec
