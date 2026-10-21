import BorshSpec.Spec

/-!
# Schema predicates

The `Schema` type is defined in `Spec.lean`, together with `zeroSized`.  This module
has the decidable well-formedness check that the protocol imposes on schemas
(`Schema.wellFormed`), the float test it uses (`hasFloat`), and the least encoded
size of a schema (`Schema.minSize`).

Recursive types are not expressible (decision 5 in `DECISIONS.md`).  All mutual
definitions below are structurally recursive on `Schema`.
-/

namespace BorshSpec

namespace Schema

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
