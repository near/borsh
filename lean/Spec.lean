/-!
# The Borsh format

Borsh turns a value into bytes, guided by the value's type. This file is the whole
format: what a type (`Schema`) and a value (`Value`) are, and `encode` / `decode`.
`Theorems.lean` proves the two are inverse, so each valid value has exactly one
encoding and the decoder accepts nothing else.

Everything is little-endian. Lengths and counts are `u32`. Nothing is sorted for you:
map keys must already be in ascending order, or the value is rejected.
-/

namespace Borsh

abbrev Bytes := List UInt8

/-- A Borsh type. The Rust types not listed here are shorthands, defined below. -/
inductive Schema where
  | uint (bytes : Nat)                      -- `u8` is `uint 1`, … `u128` is `uint 16`
  | int (bytes : Nat)                       -- `i8` … `i128`, two's complement
  | f32
  | f64
  | string
  | vec (elem : Schema)
  | tuple (fields : List Schema)            -- tuples, structs, `()`
  | enum (variants : List (UInt8 × Schema)) -- `(tag byte, payload)`, in `Ord` order
  | map (key value : Schema)                -- `BTreeMap`, `HashMap`

/-- A value, untyped: the schema says how to read it. -/
inductive Value where
  | int (i : Int)                  -- any integer; a float as its raw bits
  | str (bytes : Bytes)            -- a string, as UTF-8 bytes
  | list (xs : List Value)         -- a `Vec` or tuple; a map is a list of `[key, value]`
  | variant (i : Nat) (v : Value)  -- an enum: its variant's *position* in the schema, payload

namespace Schema

def unit : Schema := tuple []
def bool : Schema := enum [(0, unit), (1, unit)]
def option (t : Schema) : Schema := enum [(0, unit), (1, t)]
/-- `Ok` is written with tag 1 but sorts before `Err`, so it comes first. -/
def result (t e : Schema) : Schema := enum [(1, t), (0, e)]
def array (n : Nat) (t : Schema) : Schema := tuple (List.replicate n t)
def set (t : Schema) : Schema := map t unit

/-- Encodes to zero bytes whatever the value. Borsh rejects these as `Vec` elements and
map keys: otherwise four bytes of count could claim four billion elements for free. -/
def zeroSized : Schema → Bool
  | tuple fs => (fs.map zeroSized).all id
  | _ => false

end Schema

/-! ## Helpers -/

/-- `n` as `w` little-endian bytes (high bits dropped). -/
def toLE : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, n => (n % 256).toUInt8 :: toLE w (n / 256)

/-- The number `bs` denotes, little-endian. -/
def fromLE : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * fromLE bs

/-- An integer as `w` bytes, two's complement (`-1` is `ff ff …`). -/
def intLE (w : Nat) (x : Int) : Bytes := toLE w (x % 2 ^ (8 * w)).toNat

/-- Split off the first `n` bytes, if there are that many. -/
def take (n : Nat) (bs : Bytes) : Option (Bytes × Bytes) :=
  if (bs.take n).length = n then some (bs.take n, bs.drop n) else none

/-- Read a `w`-byte unsigned integer. -/
def readLE (w : Nat) (bs : Bytes) : Option (Nat × Bytes) := do
  let (b, rest) ← take w bs
  pure (fromLE b, rest)

/-- IEEE 754 NaN: exponent all ones, mantissa not zero. -/
def isNaN (expBits mantBits bits : Nat) : Bool :=
  bits / 2 ^ mantBits % 2 ^ expBits == 2 ^ expBits - 1 && bits % 2 ^ mantBits != 0

/-- Well-formed UTF-8, as Rust's `str::from_utf8` checks it. -/
def utf8 (bs : Bytes) : Bool := ByteArray.validateUTF8 ⟨bs.toArray⟩

/-- Run `f` `n` times, threading the input. -/
def repeatN {α : Type} (f : Bytes → Option (α × Bytes)) : Nat → Bytes → Option (List α × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (x, bs) ← f bs
    let (xs, bs) ← repeatN f n bs
    pure (x :: xs, bs)

/-! ## Key order

Map keys are in Rust's `Ord` order, not byte order: `-1 < 0` although `ff ff ff ff`
is larger than `00 00 00 00`. Lists compare element by element (a prefix first), so
strings compare bytewise. Enums compare by position in the schema, then by payload. -/

mutual
def cmp : Value → Value → Ordering
  | .int a, .int b => compare a b
  | .str a, .str b => compare a b
  | .list a, .list b => cmpList a b
  | .variant i a, .variant j b => (compare i j).then (cmp a b)
  | _, _ => .eq  -- different shapes: never two keys of one map

def cmpList : List Value → List Value → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs => (cmp a b).then (cmpList as bs)
end

/-- Strictly ascending, so also no duplicates. -/
def ascending : List Value → Bool
  | a :: b :: rest => cmp a b == .lt && ascending (b :: rest)
  | _ => true

/-- The key of a map entry `[key, value]`. -/
def key : Value → Value
  | .list (k :: _) => k
  | v => v

/-! ## Encode and decode

`encode s v` is `none` when `v` is not a valid value of `s`. `decode s bs` reads one
value from the front of `bs` and returns it with the bytes left over; `none` means the
input is rejected. -/

mutual
def encode : Schema → Value → Option Bytes
  | .uint w, .int x => if 0 ≤ x ∧ x < 2 ^ (8 * w) then some (intLE w x) else none
  | .int w, .int x => if -2 ^ (8 * w) / 2 ≤ x ∧ x < 2 ^ (8 * w) / 2 then some (intLE w x) else none
  | .f32, .int x => if 0 ≤ x ∧ x < 2 ^ 32 ∧ !isNaN 8 23 x.toNat then some (intLE 4 x) else none
  | .f64, .int x => if 0 ≤ x ∧ x < 2 ^ 64 ∧ !isNaN 11 52 x.toNat then some (intLE 8 x) else none
  | .string, .str s => if s.length < 2 ^ 32 ∧ utf8 s then some (toLE 4 s.length ++ s) else none
  | .vec t, .list xs =>
    if t.zeroSized ∨ 2 ^ 32 ≤ xs.length then none
    else (toLE 4 xs.length ++ ·.flatten) <$> xs.mapM (encode t)
  | .tuple ts, .list xs => encodeFields ts xs
  | .enum vs, .variant i x => encodeVariant vs [] i x
  | .map k v, .list es =>
    if k.zeroSized ∨ 2 ^ 32 ≤ es.length ∨ !ascending (es.map key) then none
    else (toLE 4 es.length ++ ·.flatten) <$> es.mapM fun
      | .list [a, b] => do pure ((← encode k a) ++ (← encode v b))
      | _ => none
  | _, _ => none

def encodeFields : List Schema → List Value → Option Bytes
  | [], [] => some []
  | t :: ts, x :: xs => do pure ((← encode t x) ++ (← encodeFields ts xs))
  | _, _ => none

/-- Variant number `i`: its tag, then its payload. `seen` holds the tags before it; if
one of them is the same tag, decoding would pick that variant instead, so reject. -/
def encodeVariant : List (UInt8 × Schema) → List UInt8 → Nat → Value → Option Bytes
  | [], _, _, _ => none
  | (tag, t) :: _, seen, 0, x => if seen.contains tag then none else (tag :: ·) <$> encode t x
  | (tag, _) :: vs, seen, i + 1, x => encodeVariant vs (tag :: seen) i x
end

mutual
def decode : Schema → Bytes → Option (Value × Bytes)
  | .uint w, bs => do
    let (n, bs) ← readLE w bs
    pure (.int n, bs)
  | .int w, bs => do
    let (n, bs) ← readLE w bs
    pure (.int (if n < 2 ^ (8 * w) / 2 then n else n - 2 ^ (8 * w)), bs)
  | .f32, bs => do
    let (n, bs) ← readLE 4 bs
    if isNaN 8 23 n then none else pure (.int n, bs)
  | .f64, bs => do
    let (n, bs) ← readLE 8 bs
    if isNaN 11 52 n then none else pure (.int n, bs)
  | .string, bs => do
    let (n, bs) ← readLE 4 bs
    let (s, bs) ← take n bs
    if utf8 s then pure (.str s, bs) else none
  | .vec t, bs => do
    if t.zeroSized then none
    let (n, bs) ← readLE 4 bs
    let (xs, bs) ← repeatN (decode t) n bs
    pure (.list xs, bs)
  | .tuple ts, bs => do
    let (xs, bs) ← decodeFields ts bs
    pure (.list xs, bs)
  | .enum vs, tag :: bs => decodeVariant vs 0 tag bs
  | .enum _, [] => none
  | .map k v, bs => do
    if k.zeroSized then none
    let (n, bs) ← readLE 4 bs
    let (es, bs) ← repeatN (fun bs => do
      let (a, bs) ← decode k bs
      let (b, bs) ← decode v bs
      pure (.list [a, b], bs)) n bs
    if ascending (es.map key) then pure (.list es, bs) else none

def decodeFields : List Schema → Bytes → Option (List Value × Bytes)
  | [], bs => some ([], bs)
  | t :: ts, bs => do
    let (x, bs) ← decode t bs
    let (xs, bs) ← decodeFields ts bs
    pure (x :: xs, bs)

/-- The first variant whose tag is `tag`; `i` counts positions. Unknown tag: reject. -/
def decodeVariant : List (UInt8 × Schema) → Nat → UInt8 → Bytes → Option (Value × Bytes)
  | [], _, _, _ => none
  | (tag', t) :: vs, i, tag, bs =>
    if tag' == tag then (fun (x, bs) => (.variant i x, bs)) <$> decode t bs
    else decodeVariant vs (i + 1) tag bs
end

end Borsh
