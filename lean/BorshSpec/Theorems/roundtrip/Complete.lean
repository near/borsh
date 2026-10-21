import BorshSpec.Theorems.roundtrip.Order

/-!
# Decoding what `encode` wrote

The decoder is `Schema.decodeWith P` for a key policy `P`.  Reading back an encoding
needs only that the policy leaves strictly ascending keys alone (`Accepts`); this
holds for the strict policy (by definition), for the raw policy, and for the
lenient policy (`Normalize.lean`).
-/

namespace BorshSpec

namespace RT

open Schema

/-- The policy returns strictly ascending set elements and map entries unchanged. -/
def Accepts (P : KeyPolicy) : Prop :=
  (∀ xs, Value.strictAsc xs = true → P.set xs = some xs) ∧
    (∀ kvs, Value.strictAsc (kvs.map Prod.fst) = true → P.map kvs = some kvs)

/-- The strict policy accepts strictly ascending keys unchanged. -/
theorem accepts_strict : Accepts KeyPolicy.strict := by
  refine ⟨fun xs h => ?_, fun kvs h => ?_⟩ <;> simp [KeyPolicy.strict, h]

/-- The strict decoder is `decodeWith` for the strict policy. -/
theorem decode_def (s : Schema) (bs : List UInt8) :
    decode s bs = decodeWith KeyPolicy.strict s bs := rfl

/-- `UInt32` bit patterns survive the round trip through `Nat`. -/
theorem uint32_toNat_lt (b : UInt32) : b.toNat < 2 ^ (8 * 4) := by
  have := b.toNat_lt
  simpa using this

/-- `UInt64` bit patterns survive the round trip through `Nat`. -/
theorem uint64_toNat_lt (b : UInt64) : b.toNat < 2 ^ (8 * 8) := by
  have := b.toNat_lt
  simpa using this

/-- Round trip for the leaf forms: integers, floats, `bool` and `string`. -/
theorem complete_leaf (P : KeyPolicy) (s : Schema) (v : Value) (bs : List UInt8)
    (hs : (∃ w, s = .uint w) ∨ (∃ w, s = .sint w) ∨ s = .f32 ∨ s = .f64 ∨ s = .bool ∨
      s = .string)
    (h : encode s v = some bs) (rest : List UInt8) :
    decodeWith P s (bs ++ rest) = some (v, rest) := by
  rcases hs with ⟨w, rfl⟩ | ⟨w, rfl⟩ | rfl | rfl | rfl | rfl
  · cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      simp [decodeWith, readLE_toLE hn]
    · simp at h
  · cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      simp [decodeWith, readLE_toLE (sintToNat_lt _ _), natToSint_sintToNat _ _ hn]
    · simp at h
  · cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · simp at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      rename_i bits
      have hn' : isNaN32 bits = false := by simpa using hn
      simp [decodeWith, readLE_toLE (uint32_toNat_lt bits), hn']
  · cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · simp at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      rename_i bits
      have hn' : isNaN64 bits = false := by simpa using hn
      simp [decodeWith, readLE_toLE (uint64_toNat_lt bits), hn']
  · cases v <;> simp only [encode, reduceCtorEq] at h
    rename_i b
    simp only [Option.some.injEq] at h
    subst h
    cases b <;> simp [decodeWith]
  · cases v <;> simp only [encode, reduceCtorEq] at h
    rename_i body
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      simp [decodeWith, Schema.readU32, List.append_assoc,
        readLE_toLE (by simpa using hv.1 : body.length < 2 ^ (8 * 4)),
        takeExact_append rfl, hv.2]
    · simp at h

mutual

/-- **Round trip.**  If `encode s v` succeeds with bytes `bs`, then the decoder
applied to `bs` followed by any further bytes `rest` returns `v` and leaves exactly
`rest` unread, for every policy that accepts strictly ascending keys. -/
theorem complete (P : KeyPolicy) (hP : Accepts P) :
    ∀ (s : Schema) (v : Value) (bs : List UInt8), encode s v = some bs →
      ∀ rest, decodeWith P s (bs ++ rest) = some (v, rest)
  | .uint w, v, bs, h, rest => complete_leaf P _ v bs (.inl ⟨w, rfl⟩) h rest
  | .sint w, v, bs, h, rest => complete_leaf P _ v bs (.inr (.inl ⟨w, rfl⟩)) h rest
  | .f32, v, bs, h, rest => complete_leaf P _ v bs (.inr (.inr (.inl rfl))) h rest
  | .f64, v, bs, h, rest => complete_leaf P _ v bs (.inr (.inr (.inr (.inl rfl)))) h rest
  | .bool, v, bs, h, rest =>
    complete_leaf P _ v bs (.inr (.inr (.inr (.inr (.inl rfl))))) h rest
  | .string, v, bs, h, rest =>
    complete_leaf P _ v bs (.inr (.inr (.inr (.inr (.inr rfl))))) h rest
  | .option s, v, bs, h, rest => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [decodeWith]
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      simp [decodeWith, complete P hP s _ e he rest]
  | .vec s, v, bs, h, rest => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    rename_i xs
    split at h
    · simp at h
    · rename_i hc
      rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      rw [Option.map_eq_some_iff] at he
      obtain ⟨es, hes, rfl⟩ := he
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hc
      have key := decodeMany_complete (fun b => decodeWith P s b) (encode s)
        (fun x p hx r => complete P hP s x p hx r) xs es hes rest
      have hlen : xs.length < 2 ^ (8 * 4) := by simpa using hc.2
      simp [decodeWith, hc.1, Schema.readU32, List.append_assoc, readLE_toLE hlen, key]
  | .array n s, v, bs, h, rest => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    rename_i xs
    split at h
    · rename_i hn
      rw [Option.map_eq_some_iff] at h
      obtain ⟨es, hes, rfl⟩ := h
      have key := decodeMany_complete (fun b => decodeWith P s b) (encode s)
        (fun x p hx r => complete P hP s x p hx r) xs es hes rest
      simp only [beq_iff_eq] at hn
      subst hn
      simp [decodeWith, key]
    · simp at h
  | .tuple fs, v, bs, h, rest => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    simp [decodeWith, completeFields P hP fs _ bs h rest]
  | .enum vs, v, bs, h, rest => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    obtain ⟨t, e, rfl, -, hd⟩ := completeVariant P hP vs _ _ _ bs h
    simp [decodeWith, hd 0 rest]
  | .map k s, v, bs, h, rest => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    rename_i kvs
    split at h
    · simp at h
    · rename_i hc
      rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      rw [Option.map_eq_some_iff] at he
      obtain ⟨es, hes, rfl⟩ := he
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or,
        Bool.not_eq_true] at hc
      have hlen : kvs.length < 2 ^ (8 * 4) := by simpa using hc.1.2
      have hsorted : Value.strictAsc (kvs.map Prod.fst) = true := by simpa using hc.2
      simp only [decodeWith, hc.1.1, Schema.readU32, List.append_assoc, readLE_toLE hlen]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [decodeMany_complete _
        (fun (p : Value × Value) => do
          let ea ← encode k p.1
          let eb ← encode s p.2
          pure (ea ++ eb)) ?hd kvs es (by simpa using hes) rest]
      · simp [hP.2 kvs hsorted]
      · rintro ⟨a, c⟩ p hp r
        simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hp
        obtain ⟨ea, hea, eb, heb, rfl⟩ := hp
        simp [complete P hP k a ea hea (eb ++ r), complete P hP s c eb heb r]
  | .set s, v, bs, h, rest => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    rename_i xs
    split at h
    · simp at h
    · rename_i hc
      rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      rw [Option.map_eq_some_iff] at he
      obtain ⟨es, hes, rfl⟩ := he
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or,
        Bool.not_eq_true] at hc
      have hlen : xs.length < 2 ^ (8 * 4) := by simpa using hc.1.2
      have hsorted : Value.strictAsc xs = true := by simpa using hc.2
      simp only [decodeWith, hc.1.1, Schema.readU32, List.append_assoc, readLE_toLE hlen]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [decodeMany_complete _ (encode s) (fun x p hx r => complete P hP s x p hx r) xs es hes
        rest]
      simp [hP.1 xs hsorted]

/-- Round trip for the fields of a tuple. -/
theorem completeFields (P : KeyPolicy) (hP : Accepts P) :
    ∀ (fs : List Schema) (vs : List Value) (bs : List UInt8), encodeFields fs vs = some bs →
      ∀ rest, decodeFieldsWith P fs (bs ++ rest) = some (vs, rest)
  | [], [], bs, h, rest => by
    simp only [encodeFields, Option.some.injEq] at h
    subst h
    simp [decodeFieldsWith]
  | [], _ :: _, bs, h, rest => by simp [encodeFields] at h
  | _ :: _, [], bs, h, rest => by simp [encodeFields] at h
  | s :: fs, v :: vs, bs, h, rest => by
    simp only [encodeFields, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨e, he, es, hes, rfl⟩ := h
    simp [decodeFieldsWith, List.append_assoc, complete P hP s v e he (es ++ rest),
      completeFields P hP fs vs es hes rest]

/-- Round trip for the payload of an enum variant.  The variant list `vs` is the tail of
the schema's list after `earlier.length` variants whose tags are `earlier`; the
decoder, started at index `j` on `vs`, finds variant `j + i`. -/
theorem completeVariant (P : KeyPolicy) (hP : Accepts P) :
    ∀ (vs : List (UInt8 × Schema)) (earlier : List UInt8) (i : Nat) (v : Value)
      (bs : List UInt8), encodeVariant vs earlier i v = some bs →
      ∃ (t : UInt8) (e : List UInt8), bs = t :: e ∧ earlier.contains t = false ∧
        ∀ (j : Nat) (rest : List UInt8),
          decodeVariantWith P vs j t (e ++ rest) = some (.enum (j + i) v, rest)
  | [], _, _, _, bs, h => by simp [encodeVariant] at h
  | (t, s) :: vs, earlier, 0, v, bs, h => by
    simp only [encodeVariant] at h
    split at h
    · simp at h
    · rename_i hc
      rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      refine ⟨t, e, rfl, by simpa using hc, fun j rest => ?_⟩
      simp [decodeVariantWith, complete P hP s v e he rest]
  | (t, s) :: vs, earlier, i + 1, v, bs, h => by
    simp only [encodeVariant] at h
    obtain ⟨t', e, rfl, hc, hd⟩ := completeVariant P hP vs (t :: earlier) i v bs h
    have hne : (t == t') = false := by
      cases hh : (t == t')
      · rfl
      · have := eq_of_beq hh
        subst this
        simp at hc
    refine ⟨t', e, rfl, by simp at hc; simpa using hc.2, fun j rest => ?_⟩
    simp only [decodeVariantWith, hne, Bool.false_eq_true, ↓reduceIte]
    rw [hd (j + 1) rest]
    congr 3
    omega

end

/-- **Round trip for the strict decoder.** -/
theorem decode_encode' (s : Schema) (v : Value) (bs rest : List UInt8)
    (h : encode s v = some bs) : decode s (bs ++ rest) = some (v, rest) :=
  complete KeyPolicy.strict accepts_strict s v bs h rest

end RT

end BorshSpec
