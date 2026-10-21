import BorshSpec.Value

/-!
# Key order

`Value.cmp` is the order that map and set keys must be strictly ascending in.
It is a structural, schema-independent comparison that agrees, on values of one
schema, with Rust's `Ord` for the corresponding std type (`PROTOCOL.md`, "Key order"):

* integers numerically (`sint` signed), `bool` with `false < true`, unit equal;
* strings byte-lexicographically (this is also what `Vec<u8>` does);
* `option`: `None < Some`, then payload;
* `vec`, `array`, `set`, `tuple`: lexicographic over elements, a proper
  prefix first;
* `map`: lexicographic over `(key, value)` pairs;
* `enum`: by variant index (the position in the schema's variant list), then payload.

Floats are banned from keys by well-formedness; `cmp` still orders them (by raw
bits) only to stay total.  Values built from different constructors are
ordered by constructor rank; this case never arises on well-typed values of one
schema.

Encoding and decoding use the same strictness test `strictAsc`, so their mutual
consistency does not depend on `cmp` being an order; `cmp` being a strict total
order compatible with equality is a separate theorem (`Theorems/RoundTrip.lean`)
needed for decoded sets and maps to be duplicate-free and for the lenient decoder.
-/

namespace BorshSpec

namespace Value

/-- The constructor index of a value, used to order values of different shape. -/
def rank : Value → Nat
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

/-- Lexicographic order on byte lists, a proper prefix being smaller. -/
def cmpBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match compare a b with
    | .eq => cmpBytes as bs
    | o => o

mutual

/-- The key order on values; see the module docstring. -/
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
  | a, b => compare a.rank b.rank

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

/-- Boolean equality of values, defined as the key order answering `.eq`.  (The
`BEq` that `deriving` produces for a nested inductive type is `partial`, hence
opaque, and nothing could be proved about it.)  That this agrees with `=` is the
theorem `Value.beq_iff`, which rests on `Value.cmp_eq_iff`. -/
instance : BEq Value := ⟨fun a b => cmp a b == .eq⟩

/-- The list is strictly ascending for `cmp`: this rules out duplicates and
unsorted elements at once. -/
def strictAsc : List Value → Bool
  | a :: b :: rest => cmp a b == .lt && strictAsc (b :: rest)
  | _ => true

end Value

end BorshSpec
