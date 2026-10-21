/-!
# Borsh values

`Value` is the abstract data a schema describes.  A value is *untyped* on its
own: the constructors are shared between schemas (every unsigned integer is a
`uint`, whatever its width), and `HasType` (in `BorshSpec.Typing`) says which
schema a value inhabits.

* integers are `Nat` / `Int` (range-checked by typing), so little-endian
  encoding is plain arithmetic;
* floats are raw IEEE-754 bit patterns, so `-0.0` and `0.0` are different
  values and NaN is detected on bits;
* strings are byte lists (validated as UTF-8 by canonicity);
* `unit` is `tuple []`;
* an enum value carries the *index* (rank) of its variant in the schema's variant
  list, not its wire tag.  The wire tag is looked up by `encode` and `decode`.
  This keeps the key order `Value.cmp` independent of the schema;
* collections are lists.  `set` and `map` hold their elements in the order
  they appear on the wire, which canonicity requires to be strictly ascending.

`Value` has no derived `BEq`: for a nested inductive type the derived instance is a
`partial` (hence opaque) function that the kernel cannot unfold, so no theorem could
be proved about it.  The Boolean equality `==` on values is defined in
`BorshSpec.Order`, from the key order.
-/

namespace BorshSpec

/-- A Borsh value; see the module docstring. -/
inductive Value where
  /-- An unsigned integer, as a natural number. -/
  | uint (n : Nat)
  /-- A signed integer. -/
  | sint (i : Int)
  /-- A binary32 float, as its raw bit pattern. -/
  | f32 (bits : UInt32)
  /-- A binary64 float, as its raw bit pattern. -/
  | f64 (bits : UInt64)
  /-- A boolean. -/
  | bool (b : Bool)
  /-- A string, as its UTF-8 bytes. -/
  | string (bytes : List UInt8)
  /-- `None`. -/
  | optNone
  /-- `Some v`. -/
  | optSome (v : Value)
  /-- A vector. -/
  | vec (xs : List Value)
  /-- A fixed-length array. -/
  | array (xs : List Value)
  /-- A tuple or struct; `tuple []` is the unit value. -/
  | tuple (xs : List Value)
  /-- An enum value: the index of the variant in the schema's variant list, and
  its payload. -/
  | enum (idx : Nat) (v : Value)
  /-- A map, as its entries in wire order. -/
  | map (kvs : List (Value × Value))
  /-- A set, as its elements in wire order. -/
  | set (xs : List Value)
  deriving Repr

namespace Value

/-- The unit value, `tuple []`. -/
def unit : Value := .tuple []

end Value

end BorshSpec
