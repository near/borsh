import BorshSpec.Decode

/-!
# Lenient decoding: the default behaviour of borsh-rs

borsh-rs without its `de_strict_order` feature (the default) does not check the
order of map and set entries.  It reads the whole `Vec<(K, V)>` or `Vec<T>` first
(so the bytes consumed are the same as in strict mode) and then collects it into
the container:

* `BTreeMap` and `HashMap`: entries are inserted in input order, so on a repeated
  key **the last entry wins** (its value replaces the earlier one).  The result
  does not depend on whether the input was sorted.
* `BTreeSet` and `HashSet`: repeated elements collapse to one.

Both were confirmed against borsh-rs with a small test program (DECISIONS.md,
decision 8).  Re-serialising the container always writes strictly ascending keys,
so the *re-encoding* of a lenient decode is the canonical encoding of the
normalised value.

`Lenient.decode` models exactly that: it is the strict decoder with a different
`KeyPolicy`.  The entries are read in input order, stably sorted by key
(`Value.cmp`), and each run of equal keys is collapsed to its last member.  For
sets, equal elements are indistinguishable (`cmp a b = .eq` only for `a = b`), so
which of them survives is irrelevant.

Everything else (integers, bool and option tags, enum tags, NaN, UTF-8, the
zero-sized-type ban, array lengths) is identical to strict decoding.  Lenient
decoding accepts a superset of what strict decoding accepts, and returns the same
result on every input that strict decoding accepts (theorem
`lenient_eq_strict_of_strict`).

What lenient decoding does is pinned by `lenient_eq_normalize_raw`: it equals the
decoder that keeps every key as read (`KeyPolicy.raw`) followed by `Value.normalize`,
which sorts each set and map and collapses repeated keys, the last entry winning
(`normalizeMap_mem_iff`, `normalizeSet_mem_iff`).
-/

namespace BorshSpec

namespace Lenient

/-- `a ≤ b` in the key order, as a Boolean. -/
def keyLe (a b : Value) : Bool := Value.cmp a b != .gt

/-- Collapse each run of consecutive elements that `same` identifies into its
last member.  The result is built in reverse and flipped at the end, so the
function is tail recursive. -/
def dedupLast {α : Type} (same : α → α → Bool) : List α → List α → List α
  | [], acc => acc.reverse
  | x :: rest, acc =>
    match acc with
    | y :: acc' => if same y x then dedupLast same rest (x :: acc') else dedupLast same rest (x :: acc)
    | [] => dedupLast same rest [x]

/-- Normalise decoded set elements: stable sort by `Value.cmp`, drop repeats. -/
def normalizeSet (xs : List Value) : List Value :=
  dedupLast (fun a b => Value.cmp a b == .eq) (xs.mergeSort keyLe) []

/-- Normalise decoded map entries: stable sort by key, and of each run of equal
keys keep the last entry, which is the last one in input order because the sort
is stable. -/
def normalizeMap (kvs : List (Value × Value)) : List (Value × Value) :=
  dedupLast (fun a b => Value.cmp a.1 b.1 == .eq)
    (kvs.mergeSort fun a b => keyLe a.1 b.1) []

/-- The lenient policy: never rejects, always normalises. -/
def policy : KeyPolicy where
  set xs := some (normalizeSet xs)
  map kvs := some (normalizeMap kvs)

/-- The lenient decoder: prefix decoding as in borsh-rs without `de_strict_order`. -/
def decode (s : Schema) (bs : List UInt8) : Option (Value × List UInt8) :=
  Schema.decodeWith policy s bs

end Lenient

namespace Value

mutual

/-- Normalise a value as the lenient decoder does: normalise every child, then
apply `Lenient.normalizeSet` or `Lenient.normalizeMap` at each set and map (the
children first, because the lenient decoder normalises an inner container before the
outer one sees it).  Everything else is left alone. -/
def normalize : Value → Value
  | .optSome v => .optSome v.normalize
  | .vec xs => .vec (normalizeList xs)
  | .array xs => .array (normalizeList xs)
  | .tuple xs => .tuple (normalizeList xs)
  | .enum i v => .enum i v.normalize
  | .map kvs => .map (Lenient.normalizeMap (normalizePairs kvs))
  | .set xs => .set (Lenient.normalizeSet (normalizeList xs))
  | .uint n => .uint n
  | .sint i => .sint i
  | .f32 b => .f32 b
  | .f64 b => .f64 b
  | .bool b => .bool b
  | .string bs => .string bs
  | .optNone => .optNone

/-- `normalize` on every value of a list. -/
def normalizeList : List Value → List Value
  | [] => []
  | x :: xs => x.normalize :: normalizeList xs

/-- `normalize` on the key and the value of every entry of a list. -/
def normalizePairs : List (Value × Value) → List (Value × Value)
  | [] => []
  | (k, v) :: kvs => (k.normalize, v.normalize) :: normalizePairs kvs

end

end Value

end BorshSpec
