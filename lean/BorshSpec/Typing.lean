import BorshSpec.Schema

/-!
# Typing and canonicity

Two independent conditions on a value `v` against a schema `s`:

* `HasType s v`: `v` has the shape `s` describes.  Integers are in range for
  their width, `array n` holds exactly `n` elements, an enum value's index names a
  variant and its payload has that variant's schema, and no `vec`/`set`/map-key
  position is zero-sized (Borsh's ZST ban, decision 3).  An enum index must also be
  the *first* variant carrying its wire tag, so that a schema with a repeated tag
  (not well-formed) still has an unambiguous codec (decision 10).
* `Canonical s v`: `v` is something Borsh can write and read back.  Floats are
  not NaN, strings are valid UTF-8, collection lengths (strings included) are
  below `2^32`, and `set` elements and `map` keys are strictly ascending in the
  key order `Value.cmp`.

`Valid s v` is both.  The encoder `encode` succeeds exactly on valid values
(theorem `encode_isSome_iff_valid`, not an assumption here).

Both checks are Boolean functions, structurally recursive on the schema, with
Prop-valued wrappers.
-/

namespace BorshSpec

namespace Schema

mutual

/-- Shape check: does the value have the schema's shape? -/
def hasType : Schema → Value → Bool
  | .uint w, .uint n => decide (n < 2 ^ (8 * w.bytes))
  | .sint w, .sint i => sintInRange w i
  | .f32, .f32 _ => true
  | .f64, .f64 _ => true
  | .bool, .bool _ => true
  | .string, .string _ => true
  | .option _, .optNone => true
  | .option s, .optSome v => hasType s v
  | .vec s, .vec xs => !s.zeroSized && xs.all (hasType s)
  | .array n s, .array xs => xs.length == n && xs.all (hasType s)
  | .tuple fs, .tuple xs => hasTypeFields fs xs
  | .enum vs, .enum i v => hasTypeVariant vs [] i v
  | .map k v, .map kvs => !k.zeroSized && kvs.all fun (a, b) => hasType k a && hasType v b
  | .set s, .set xs => !s.zeroSized && xs.all (hasType s)
  | _, _ => false

/-- Field-wise shape check for a tuple: same length, each field has its type. -/
def hasTypeFields : List Schema → List Value → Bool
  | [], [] => true
  | s :: fs, v :: vs => hasType s v && hasTypeFields fs vs
  | _, _ => false

/-- Shape check for an enum value `enum i v`: the `i`-th variant exists, its tag is
not carried by an earlier variant (`earlier` holds the tags of the variants passed
so far), and `v` has its payload schema. -/
def hasTypeVariant : List (UInt8 × Schema) → List UInt8 → Nat → Value → Bool
  | [], _, _, _ => false
  | (t, s) :: _, earlier, 0, v => !earlier.contains t && hasType s v
  | (t, _) :: vs, earlier, i + 1, v => hasTypeVariant vs (t :: earlier) i v

end

mutual

/-- Canonicity check; see the module docstring.  It presupposes `hasType` for
the cases where shapes matter, and answers `true` for ill-shaped values it has
no opinion on. -/
def canonical : Schema → Value → Bool
  | .f32, .f32 b => !isNaN32 b
  | .f64, .f64 b => !isNaN64 b
  | .string, .string bs => decide (bs.length < 2 ^ 32) && validUtf8 bs
  | .option s, .optSome v => canonical s v
  | .vec s, .vec xs => decide (xs.length < 2 ^ 32) && xs.all (canonical s)
  | .array _ s, .array xs => xs.all (canonical s)
  | .tuple fs, .tuple xs => canonicalFields fs xs
  | .enum vs, .enum i v => canonicalVariant vs i v
  | .map k v, .map kvs =>
    decide (kvs.length < 2 ^ 32) && Value.strictAsc (kvs.map Prod.fst) &&
      kvs.all fun (a, b) => canonical k a && canonical v b
  | .set s, .set xs =>
    decide (xs.length < 2 ^ 32) && Value.strictAsc xs && xs.all (canonical s)
  | _, _ => true

/-- Field-wise canonicity for a tuple. -/
def canonicalFields : List Schema → List Value → Bool
  | s :: fs, v :: vs => canonical s v && canonicalFields fs vs
  | _, _ => true

/-- Canonicity of the payload of the `i`-th variant. -/
def canonicalVariant : List (UInt8 × Schema) → Nat → Value → Bool
  | [], _, _ => true
  | (_, s) :: _, 0, v => canonical s v
  | _ :: vs, i + 1, v => canonicalVariant vs i v

end

end Schema

/-- `v` has the shape of `s` (propositional form of `Schema.hasType`). -/
def HasType (s : Schema) (v : Value) : Prop := s.hasType v = true

/-- `v` is canonical for `s` (propositional form of `Schema.canonical`). -/
def Canonical (s : Schema) (v : Value) : Prop := s.canonical v = true

/-- A valid value: well-shaped and canonical. -/
def Valid (s : Schema) (v : Value) : Prop := HasType s v ∧ Canonical s v

instance (s : Schema) (v : Value) : Decidable (HasType s v) :=
  inferInstanceAs (Decidable (s.hasType v = true))

instance (s : Schema) (v : Value) : Decidable (Canonical s v) :=
  inferInstanceAs (Decidable (s.canonical v = true))

instance (s : Schema) (v : Value) : Decidable (Valid s v) :=
  inferInstanceAs (Decidable (HasType s v ∧ Canonical s v))

end BorshSpec
