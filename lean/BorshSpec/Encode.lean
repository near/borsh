import BorshSpec.Typing

/-!
# Encoding

`encode s v` is the canonical Borsh encoding of `v` under `s`, or `none` when
`v` is not a valid value of `s` (ill-typed, NaN, a collection of `2^32`
elements or more, invalid UTF-8, unsorted or duplicate set/map keys, or a
zero-sized `vec`/`set`/map key).

An enum value carries the index of its variant; `encode` writes that variant's
wire tag.  It does not consult `hasType`/`canonical`; it re-checks everything
inline, so that "`encode` succeeds iff the value is valid" is a theorem
(`encode_isSome_iff_valid`) rather than a definition.

The only loops over input-sized data are `List.mapM` and `List.flatten`, which
are tail recursive in compiled code.
-/

namespace BorshSpec

namespace Schema

/-- The two's-complement unsigned residue of a signed integer on `w` bytes. -/
def sintToNat (w : IntWidth) (i : Int) : Nat := (i % 2 ^ (8 * w.bytes)).toNat

mutual

/-- The canonical encoding; see the module docstring. -/
def encode : Schema → Value → Option (List UInt8)
  | .uint w, .uint n =>
    if n < 2 ^ (8 * w.bytes) then some (toLE w.bytes n) else none
  | .sint w, .sint i =>
    if sintInRange w i then some (toLE w.bytes (sintToNat w i)) else none
  | .f32, .f32 b => if isNaN32 b then none else some (toLE 4 b.toNat)
  | .f64, .f64 b => if isNaN64 b then none else some (toLE 8 b.toNat)
  | .bool, .bool b => some [if b then 1 else 0]
  | .string, .string bs =>
    if bs.length < 2 ^ 32 && validUtf8 bs then some (toLE 4 bs.length ++ bs) else none
  | .option _, .optNone => some [0]
  | .option s, .optSome v => (encode s v).map (1 :: ·)
  | .vec s, .vec xs =>
    if s.zeroSized || 2 ^ 32 ≤ xs.length then none
    else ((xs.mapM (encode s)).map List.flatten).map (toLE 4 xs.length ++ ·)
  | .array n s, .array xs =>
    if xs.length == n then (xs.mapM (encode s)).map List.flatten else none
  | .tuple fs, .tuple xs => encodeFields fs xs
  | .enum vs, .enum i v => encodeVariant vs [] i v
  | .map k v, .map kvs =>
    if k.zeroSized || 2 ^ 32 ≤ kvs.length || !Value.strictAsc (kvs.map Prod.fst) then none
    else
      ((kvs.mapM fun (a, b) => do
          let ea ← encode k a
          let eb ← encode v b
          pure (ea ++ eb)).map List.flatten).map (toLE 4 kvs.length ++ ·)
  | .set s, .set xs =>
    if s.zeroSized || 2 ^ 32 ≤ xs.length || !Value.strictAsc xs then none
    else ((xs.mapM (encode s)).map List.flatten).map (toLE 4 xs.length ++ ·)
  | _, _ => none

/-- Concatenated encodings of tuple fields; the lengths must agree. -/
def encodeFields : List Schema → List Value → Option (List UInt8)
  | [], [] => some []
  | s :: fs, v :: vs => do
    let e ← encode s v
    let es ← encodeFields fs vs
    pure (e ++ es)
  | _, _ => none

/-- Encode the payload `v` of the `i`-th variant: its wire tag, then `v` under that
variant's schema.  `earlier` holds the tags of the variants passed so far; a
variant whose tag an earlier variant already carries cannot be encoded, because
`decode` would read that tag back as the earlier variant. -/
def encodeVariant : List (UInt8 × Schema) → List UInt8 → Nat → Value → Option (List UInt8)
  | [], _, _, _ => none
  | (t, s) :: _, earlier, 0, v =>
    if earlier.contains t then none else (encode s v).map (t :: ·)
  | (t, _) :: vs, earlier, i + 1, v => encodeVariant vs (t :: earlier) i v

end

end Schema

export Schema (encode)

end BorshSpec
