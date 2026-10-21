import BorshSpec
import BorshSpec.Theorems.roundtrip.Lenient

/-!
# Round trip, canonical decoding, key order, lenient decoding

Statements about the codec (`encode`, `decode`), the key order `Value.cmp` and the
lenient decoder.  None of them needs `WellFormed`: `encode` and `decode` re-check the
zero-size rule and the enum-tag rule themselves, with the same tests, so they agree
on every schema (DECISIONS.md, decisions 10 and 14).

These theorems are internal-consistency properties of the definitions.  They would
hold for a codec that agreed with itself on a wrong wire format (DECISIONS.md,
decision 25); the format is fixed by the definitions, the vectors, `Tooling/Examples.lean`
and differential testing, not by anything here.
-/

namespace BorshSpec

/-! ## Byte-level helpers -/

/-- A little-endian encoding on `w` bytes has exactly `w` bytes. -/
theorem toLE_length (w n : Nat) : (toLE w n).length = w := by
  exact RT.toLE_length w n

/-- Reading back a little-endian encoding gives the number modulo `256^w`: the bits
above `8 * w` are dropped. -/
theorem fromLE_toLE (w n : Nat) : fromLE (toLE w n) = n % 256 ^ w := by
  exact RT.fromLE_toLE w n

/-- The two's complement conversion is inverse on the integers that are in range for
the width. -/
theorem natToSint_sintToNat (w : IntWidth) (i : Int) (h : Schema.sintInRange w i = true) :
    Schema.natToSint w (Schema.sintToNat w i) = i := by
  exact RT.natToSint_sintToNat w i h

/-! ## The codec -/

/-- **Round trip with prefix-freeness.**  If `encode s v` succeeds with bytes `bs`, then
decoding `bs` followed by any further bytes `rest` returns `v` and leaves exactly
`rest`.  No hypothesis beyond the success of `encode`: the schema need not be
well-formed. -/
theorem decode_encode (s : Schema) (v : Value) (bs rest : List UInt8)
    (h : encode s v = some bs) : decode s (bs ++ rest) = some (v, rest) := by
  exact RT.decode_encode' s v bs rest h

/-- **Canonical decoding.**  If `decode` succeeds on `bs` with value `v` and leftover
`rest`, then `v` is encodable and `bs` is its encoding followed by `rest`: the strict
decoder accepts only canonical encodings.  No hypothesis on the schema. -/
theorem encode_decode (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8)
    (h : decode s bs = some (v, rest)) :
    ∃ enc, encode s v = some enc ∧ bs = enc ++ rest := by
  obtain ⟨pre, he, hb⟩ := RT.sound KeyPolicy.strict RT.sound_strict s bs v rest h
  exact ⟨pre, he, hb RT.exact_strict⟩

/-- `decode` succeeds with `(v, rest)` exactly when `bs` is the encoding of `v`
followed by `rest`.  (Both directions of the two theorems above.) -/
theorem decode_eq_some_iff (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8) :
    decode s bs = some (v, rest) ↔ ∃ enc, encode s v = some enc ∧ bs = enc ++ rest := by
  constructor
  · exact encode_decode s bs v rest
  · rintro ⟨enc, he, rfl⟩
    exact decode_encode s v enc rest he

/-- **Trailing bytes.**  Bytes after a decoded value do not change the result: they
are returned unread. -/
theorem decode_append (s : Schema) (bs t : List UInt8) (v : Value) (rest : List UInt8)
    (h : decode s bs = some (v, rest)) : decode s (bs ++ t) = some (v, rest ++ t) := by
  obtain ⟨enc, he, rfl⟩ := encode_decode s bs v rest h
  rw [List.append_assoc]
  exact decode_encode s v enc (rest ++ t) he

/-- **Injectivity.**  Two values of the same schema with the same encoding are equal. -/
theorem encode_injective (s : Schema) (v w : Value) (bs : List UInt8)
    (hv : encode s v = some bs) (hw : encode s w = some bs) : v = w := by
  have h1 := decode_encode s v bs [] hv
  have h2 := decode_encode s w bs [] hw
  rw [h1] at h2
  exact (Prod.mk.inj (Option.some.inj h2)).1

/-- **Prefix-freeness.**  If the encoding of one value is a prefix of the encoding of
another under the same schema, the two encodings are equal (and so are the values, by
`encode_injective`). -/
theorem encode_prefix_free (s : Schema) (v w : Value) (a b : List UInt8)
    (hv : encode s v = some a) (hw : encode s w = some b) (hp : a <+: b) : a = b := by
  obtain ⟨c, rfl⟩ := hp
  have h1 := decode_encode s v a c hv
  have h2 := decode_encode s w (a ++ c) [] hw
  rw [List.append_nil] at h2
  rw [h1] at h2
  have hc : c = [] := (Prod.mk.inj (Option.some.inj h2)).2
  subst hc
  simp

/-- **`encode` succeeds exactly on valid values.**  `Valid` is the conjunction of the
Boolean shape check `hasType` and the canonicity check `canonical` (`Typing.lean`). -/
theorem encode_isSome_iff_valid (s : Schema) (v : Value) :
    (encode s v).isSome = true ↔ Valid s v := by
  exact RT.encode_isSome_iff_valid' s v

/-- Whatever the strict decoder returns is a valid value.  (Follows from
`encode_decode` and `encode_isSome_iff_valid`.) -/
theorem decode_valid (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8)
    (h : decode s bs = some (v, rest)) : Valid s v := by
  obtain ⟨enc, he, -⟩ := encode_decode s bs v rest h
  exact (encode_isSome_iff_valid s v).1 (by simp [he])

/-- **Progress.**  A successful decode consumes at least `minSize s` bytes. -/
theorem progress (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8)
    (h : decode s bs = some (v, rest)) : s.minSize + rest.length ≤ bs.length := by
  exact RT.progress_with KeyPolicy.strict s bs v rest h

/-- A schema has encoded size zero for every value exactly when its least size is
zero.  This is why every iteration of a `vec`/`set`/`map` loop (whose element schema
is not zero-sized) consumes input. -/
theorem minSize_pos_iff (s : Schema) : 0 < s.minSize ↔ s.zeroSized = false := by
  exact RT.minSize_pos_iff' s

/-- A zero-sized schema encodes every value it accepts to the empty byte string.  (This
is what `zeroSized` means; `progress` and `minSize_pos_iff` only give a lower bound.) -/
theorem encode_eq_nil_of_zeroSized (s : Schema) (v : Value) (bs : List UInt8)
    (hz : s.zeroSized = true) (h : encode s v = some bs) : bs = [] := by
  exact RT.encode_nil_of_zeroSized s hz v bs h

/-- For a well-formed schema the bound `minSize` is attained by some encoding.  The
hypothesis is needed: for `(enum (0 u8) (0 unit))`, which repeats a tag, `minSize` is
`1`, yet the second variant cannot be encoded (the tag `0` is read back as the first
variant) and the first variant takes two bytes, so no one-byte encoding exists. -/
theorem minSize_attained (s : Schema) (h : s.WellFormed) :
    ∃ v bs, encode s v = some bs ∧ bs.length = s.minSize := by
  exact RT.minSize_witness s h

/-! ## Decoded sets and maps -/

/-- A decoded set is strictly ascending in the key order at every pair of positions,
not only adjacent ones, and in particular has no duplicates. -/
theorem decode_set_sorted (s : Schema) (bs : List UInt8) (xs : List Value) (rest : List UInt8)
    (h : decode (.set s) bs = some (.set xs, rest)) :
    xs.Pairwise (fun a b => Value.cmp a b = .lt) ∧ xs.Nodup := by
  obtain ⟨-, hc⟩ := decode_valid _ bs _ rest h
  simp only [Canonical, Schema.canonical, Bool.and_eq_true] at hc
  exact ⟨RT.strictAsc_pairwise xs hc.1.2, RT.strictAsc_nodup hc.1.2⟩

/-- A decoded map has strictly ascending keys at every pair of positions, and in
particular no duplicate keys. -/
theorem decode_map_sorted (k v : Schema) (bs : List UInt8) (kvs : List (Value × Value))
    (rest : List UInt8) (h : decode (.map k v) bs = some (.map kvs, rest)) :
    (kvs.map Prod.fst).Pairwise (fun a b => Value.cmp a b = .lt) ∧ (kvs.map Prod.fst).Nodup := by
  obtain ⟨-, hc⟩ := decode_valid _ bs _ rest h
  simp only [Canonical, Schema.canonical, Bool.and_eq_true] at hc
  exact ⟨RT.strictAsc_pairwise _ hc.1.2, RT.strictAsc_nodup hc.1.2⟩

/-! ## The key order

`Value.cmp` is a strict total order compatible with equality: reflexive (`.eq` on
equal values), `.eq` only on equal values, antisymmetric (swapping the arguments swaps
the result) and transitive.  Totality is the fact that `Ordering` has three values. -/

/-- Every value is equal to itself in the key order. -/
theorem Value.cmp_self (a : Value) : Value.cmp a a = .eq := by
  exact RT.cmp_self a

/-- The key order says `.eq` exactly for equal values. -/
theorem Value.cmp_eq_iff (a b : Value) : Value.cmp a b = .eq ↔ a = b := by
  exact RT.cmp_eq_iff'

/-- Swapping the arguments swaps the result. -/
theorem Value.cmp_swap (a b : Value) : Value.cmp b a = (Value.cmp a b).swap := by
  exact RT.cmp_swap a b

/-- Strict less-than is transitive. -/
theorem Value.cmp_trans (a b c : Value) :
    Value.cmp a b = .lt → Value.cmp b c = .lt → Value.cmp a c = .lt := by
  exact RT.cmp_trans a b c

/-- The Boolean equality on values (`BEq Value`, defined from `Value.cmp` in
`Spec.lean`) agrees with propositional equality.  The executable compares values
with `==` in its self-checks. -/
theorem Value.beq_iff (a b : Value) : (a == b) = true ↔ a = b := by
  show (Value.cmp a b == .eq) = true ↔ a = b
  rw [beq_iff_eq]
  exact RT.cmp_eq_iff'

/-! ## Lenient decoding -/

/-- **Lenient decoding extends strict decoding.**  On every input the strict decoder
accepts, the lenient decoder returns the same value and the same leftover. -/
theorem lenient_eq_strict_of_strict (s : Schema) (bs : List UInt8) (r : Value × List UInt8)
    (h : decode s bs = some r) : Lenient.decode s bs = some r := by
  obtain ⟨enc, he, rfl⟩ := encode_decode s bs r.1 r.2 (by simpa using h)
  have := RT.complete Lenient.policy RT.accepts_lenient s r.1 enc he r.2
  simpa [Lenient.decode] using this

/-- **Lenient decoding returns canonical values.**  Whatever the lenient decoder
returns is valid, it encodes to canonical bytes, and the strict decoder reads those
bytes back to the same value with nothing left over.  (The executable asserts the last
part on every lenient answer.) -/
theorem lenient_canonical (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8)
    (h : Lenient.decode s bs = some (v, rest)) :
    Valid s v ∧ ∃ enc, encode s v = some enc ∧ decode s enc = some (v, []) := by
  obtain ⟨pre, he, -⟩ := RT.sound Lenient.policy RT.sound_lenient s bs v rest h
  refine ⟨RT.valid_of_encode s v pre he, pre, he, ?_⟩
  simpa using decode_encode s v pre [] he

/-- **What lenient decoding does.**  The lenient decoder reads the input exactly as a
decoder that keeps every set element and map entry as read (`KeyPolicy.raw`) and then
normalises the result (`Value.normalize`): inner containers first, each set and map
sorted by `Value.cmp` with repeated keys collapsed, the last entry of a repeated map
key winning.  This is the behaviour of borsh-rs without `de_strict_order`. -/
theorem lenient_eq_normalize_raw (s : Schema) (bs : List UInt8) :
    Lenient.decode s bs =
      (Schema.decodeWith KeyPolicy.raw s bs).map fun (v, r) => (v.normalize, r) := by
  exact RT.lenient_eq_raw s bs

/-- The bytes the lenient decoder consumes do not depend on the order or repetition of
the keys: it leaves exactly the rest that the raw decoder leaves (and fails exactly
when the raw decoder fails). -/
theorem lenient_rest_eq_raw_rest (s : Schema) (bs : List UInt8) :
    (Lenient.decode s bs).map (·.2) = (Schema.decodeWith KeyPolicy.raw s bs).map (·.2) := by
  have h := lenient_eq_normalize_raw s bs
  simp only [Lenient.decode] at h ⊢
  rw [h]
  cases Schema.decodeWith KeyPolicy.raw s bs <;> simp

/-- **Last entry wins.**  An entry survives `normalizeMap` exactly when no later entry
has the same key.  (So a repeated key keeps the value of its last occurrence, whatever
the input order.) -/
theorem normalizeMap_mem_iff (kvs : List (Value × Value)) (e : Value × Value) :
    e ∈ Lenient.normalizeMap kvs ↔
      ∃ pre post, kvs = pre ++ e :: post ∧ ∀ e' ∈ post, e'.1 ≠ e.1 := by
  exact RT.normalizeMap_mem_iff' kvs e

/-- The keys of a normalised map are strictly ascending. -/
theorem normalizeMap_strictAsc (kvs : List (Value × Value)) :
    Value.strictAsc ((Lenient.normalizeMap kvs).map Prod.fst) = true := by
  exact RT.normalizeMap_strictAsc' kvs

/-- **Sets collapse.**  Normalising a set neither adds nor drops an element: repeats
become one. -/
theorem normalizeSet_mem_iff (xs : List Value) (x : Value) :
    x ∈ Lenient.normalizeSet xs ↔ x ∈ xs := by
  exact RT.normalizeSet_mem_iff' xs x

/-- The elements of a normalised set are strictly ascending. -/
theorem normalizeSet_strictAsc (xs : List Value) :
    Value.strictAsc (Lenient.normalizeSet xs) = true := by
  exact RT.normalizeSet_strictAsc' xs

/-- The lenient decoder consumes at least `minSize s` bytes, as the strict one does. -/
theorem lenient_progress (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8)
    (h : Lenient.decode s bs = some (v, rest)) : s.minSize + rest.length ≤ bs.length := by
  exact RT.progress_with Lenient.policy s bs v rest h

end BorshSpec
