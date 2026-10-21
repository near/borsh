/-!
# Borsh schemas

A `Schema` describes the shape of a Borsh-serialisable type, in the form that the
schema text syntax of `PROTOCOL.md` denotes it.  Rust structs, tuples and the unit
type all become `Schema.tuple`; Rust enums become `Schema.enum`.

An enum lists its variants as `(wire tag, payload schema)` pairs, and **the order
of the list is the key order of the variants**: the variant at position `i` has
rank `i`, and values of the enum compare by rank before payload (`Value.cmp`).
The wire tag is independent of the rank.  A default derived enum is
`(enum (0 S0) (1 S1) ...)`; Rust's `Result<T, E>` is `(enum (1 T) (0 E))`, since
`Ok < Err` in Rust's `Ord` but `Ok` is written with tag `1`.

This module also contains the decidable well-formedness check that the protocol
imposes on schemas (`Schema.wellFormed`) and the least encoded size of a schema
(`Schema.minSize`).

Recursive types are not expressible (decision 5 in `DECISIONS.md`).  All mutual
definitions below are structurally recursive on `Schema`.
-/

namespace BorshSpec

/-- The five integer widths of Borsh. -/
inductive IntWidth where
  /-- One byte. -/
  | w8
  /-- Two bytes. -/
  | w16
  /-- Four bytes. -/
  | w32
  /-- Eight bytes. -/
  | w64
  /-- Sixteen bytes. -/
  | w128
  deriving DecidableEq, Repr, Inhabited

/-- The number of bytes occupied by an integer of the given width. -/
def IntWidth.bytes : IntWidth → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8
  | .w128 => 16

/-- A Borsh schema.

`uint w` is `u8`..`u128`, `sint w` is `i8`..`i128`.  `unit` is `tuple []`.
`enum` carries `(wire tag, payload schema)` pairs in key-order rank order; a unit
variant has payload `tuple []`.  `map k v` has key schema `k` and value schema `v`.
`array n s` has no length prefix on the wire. -/
inductive Schema where
  /-- Unsigned integer `u8` to `u128`. -/
  | uint (w : IntWidth)
  /-- Signed (two's complement) integer `i8` to `i128`. -/
  | sint (w : IntWidth)
  /-- IEEE-754 binary32; NaN is rejected. -/
  | f32
  /-- IEEE-754 binary64; NaN is rejected. -/
  | f64
  /-- One byte, `0` or `1`. -/
  | bool
  /-- A `u32` byte length followed by valid UTF-8. -/
  | string
  /-- A one-byte tag (`0` None, `1` Some), then the payload if Some. -/
  | option (s : Schema)
  /-- A `u32` element count, then the elements. -/
  | vec (s : Schema)
  /-- `n` elements, no length prefix. -/
  | array (n : Nat) (s : Schema)
  /-- Fields in order; `tuple []` is the unit type. -/
  | tuple (fs : List Schema)
  /-- A one-byte wire tag, then the payload of the variant carrying that tag.
  The list order is the key order (rank) of the variants. -/
  | enum (vs : List (UInt8 × Schema))
  /-- A `u32` entry count, then key/value pairs with strictly ascending keys. -/
  | map (k v : Schema)
  /-- A `u32` element count, then strictly ascending elements. -/
  | set (s : Schema)
  deriving Repr

namespace Schema

/-- The `unit` schema: a tuple with no fields. -/
def unit : Schema := .tuple []

mutual

/-- Whether every value of the schema encodes to the empty byte string.

This is the spec's notion of Borsh's zero-sized-type ban (decision 3): borsh-rs
tests `size_of::<T>() == 0`, the spec tests *encoded* size 0. -/
def zeroSized : Schema → Bool
  | .uint _ => false
  | .sint _ => false
  | .f32 => false
  | .f64 => false
  | .bool => false
  | .string => false
  | .option _ => false
  | .vec _ => false
  | .array n s => n == 0 || zeroSized s
  | .tuple fs => zeroSizedAll fs
  | .enum _ => false
  | .map _ _ => false
  | .set _ => false

/-- `zeroSized` holds for every schema of a list (vacuously for `[]`). -/
def zeroSizedAll : List Schema → Bool
  | [] => true
  | s :: fs => zeroSized s && zeroSizedAll fs

end

mutual

/-- Whether `f32` or `f64` occurs anywhere inside the schema.  Floats are not
`Ord` in Rust, so they may not occur in map or set keys. -/
def hasFloat : Schema → Bool
  | .uint _ => false
  | .sint _ => false
  | .f32 => true
  | .f64 => true
  | .bool => false
  | .string => false
  | .option s => hasFloat s
  | .vec s => hasFloat s
  | .array _ s => hasFloat s
  | .tuple fs => hasFloatAny fs
  | .enum vs => hasFloatVariants vs
  | .map k v => hasFloat k || hasFloat v
  | .set s => hasFloat s

/-- `hasFloat` holds for some schema of a list. -/
def hasFloatAny : List Schema → Bool
  | [] => false
  | s :: fs => hasFloat s || hasFloatAny fs

/-- `hasFloat` holds for some payload of an enum's variant list. -/
def hasFloatVariants : List (UInt8 × Schema) → Bool
  | [] => false
  | (_, s) :: vs => hasFloat s || hasFloatVariants vs

end

mutual

/-- The decidable well-formedness check.

* `vec`, `set` and the key of `map` must not be zero-sized;
* map and set keys must not contain floats;
* enums have at least one variant and pairwise distinct tags
  (tags are `UInt8`, so the range `0..255` is automatic).

The conditions apply at every depth of the schema. -/
def wellFormed : Schema → Bool
  | .uint _ => true
  | .sint _ => true
  | .f32 => true
  | .f64 => true
  | .bool => true
  | .string => true
  | .option s => wellFormed s
  | .vec s => wellFormed s && !zeroSized s
  | .array _ s => wellFormed s
  | .tuple fs => wellFormedAll fs
  | .enum vs => !vs.isEmpty && decide ((vs.map Prod.fst).Nodup) && wellFormedVariants vs
  | .map k v => wellFormed k && wellFormed v && !zeroSized k && !hasFloat k
  | .set s => wellFormed s && !zeroSized s && !hasFloat s

/-- `wellFormed` holds for every schema of a list. -/
def wellFormedAll : List Schema → Bool
  | [] => true
  | s :: fs => wellFormed s && wellFormedAll fs

/-- `wellFormed` holds for every payload of an enum's variant list. -/
def wellFormedVariants : List (UInt8 × Schema) → Bool
  | [] => true
  | (_, s) :: vs => wellFormed s && wellFormedVariants vs

end

/-- Propositional form of `wellFormed`. -/
def WellFormed (s : Schema) : Prop := s.wellFormed = true

instance (s : Schema) : Decidable (WellFormed s) :=
  inferInstanceAs (Decidable (s.wellFormed = true))

mutual

/-- The least number of bytes any encoding of the schema occupies.

Every successful decode consumes at least this many bytes (theorem `progress`),
and for well-formed schemas the bound is attained (theorem `minSize_attained`).
In particular `minSize s > 0` exactly when `s` is not `zeroSized`, which is why
every iteration of a `vec`/`set`/`map` loop consumes input. -/
def minSize : Schema → Nat
  | .uint w => w.bytes
  | .sint w => w.bytes
  | .f32 => 4
  | .f64 => 8
  | .bool => 1
  | .string => 4
  | .option _ => 1
  | .vec _ => 4
  | .array n s => n * minSize s
  | .tuple fs => minSizeAll fs
  | .enum vs => 1 + (minSizeVariants vs).getD 0
  | .map _ _ => 4
  | .set _ => 4

/-- Sum of `minSize` over a list of schemas. -/
def minSizeAll : List Schema → Nat
  | [] => 0
  | s :: fs => minSize s + minSizeAll fs

/-- The least `minSize` among the payloads of an enum's variants, or `none` when
there are no variants. -/
def minSizeVariants : List (UInt8 × Schema) → Option Nat
  | [] => none
  | (_, s) :: vs =>
    some (match minSizeVariants vs with
      | none => minSize s
      | some m => min (minSize s) m)

end

end Schema

end BorshSpec
