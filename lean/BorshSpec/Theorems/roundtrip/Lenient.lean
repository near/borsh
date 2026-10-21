import BorshSpec.Theorems.roundtrip.Size
import BorshSpec.Theorems.roundtrip.Normalize

/-!
# The lenient decoder

* the lenient policy is sound (`PolicySound`) and accepts strictly ascending keys
  unchanged (`Accepts`);
* the lenient decoder is the raw decoder followed by `Value.normalize`.
-/

namespace BorshSpec

namespace RT

open Schema

/-- `normalizeList` is `List.map normalize`. -/
theorem normalizeList_eq : ∀ xs : List Value, Value.normalizeList xs = xs.map Value.normalize
  | [] => by simp [Value.normalizeList]
  | x :: xs => by simp [Value.normalizeList, normalizeList_eq xs]

/-- `normalizePairs` maps `normalize` over keys and values. -/
theorem normalizePairs_eq :
    ∀ kvs : List (Value × Value),
      Value.normalizePairs kvs = kvs.map fun p => (p.1.normalize, p.2.normalize)
  | [] => by simp [Value.normalizePairs]
  | (k, v) :: kvs => by simp [Value.normalizePairs, normalizePairs_eq kvs]

/-- The lenient policy accepts strictly ascending keys unchanged. -/
theorem accepts_lenient : Accepts Lenient.policy := by
  refine ⟨fun xs h => ?_, fun kvs h => ?_⟩
  · simp [Lenient.policy, normalizeSet_of_strictAsc xs h]
  · simp [Lenient.policy, normalizeMap_of_strictAsc kvs h]

/-- The lenient policy is sound. -/
theorem sound_lenient : PolicySound Lenient.policy := by
  refine ⟨fun xs ys h => ?_, fun kvs kvs' h => ?_⟩
  · simp only [Lenient.policy, Option.some.injEq] at h
    subst h
    exact ⟨normalizeSet_strictAsc' xs, normalizeSet_subset xs, normalizeSet_length xs⟩
  · simp only [Lenient.policy, Option.some.injEq] at h
    subst h
    exact ⟨normalizeMap_strictAsc' kvs, normalizeMap_subset kvs, normalizeMap_length kvs⟩

/-- The raw policy accepts everything unchanged. -/
theorem accepts_raw : Accepts KeyPolicy.raw := by
  refine ⟨fun xs _ => ?_, fun kvs _ => ?_⟩ <;> simp [KeyPolicy.raw]

/-- A leaf schema decodes the same under every policy. -/
theorem decodeWith_leaf (P Q : KeyPolicy) (s : Schema) (bs : List UInt8)
    (hs : (∃ w, s = .uint w) ∨ (∃ w, s = .sint w) ∨ s = .f32 ∨ s = .f64 ∨ s = .bool ∨
      s = .string) :
    decodeWith P s bs = decodeWith Q s bs := by
  rcases hs with ⟨w, rfl⟩ | ⟨w, rfl⟩ | rfl | rfl | rfl | rfl <;> simp only [decodeWith]

/-- The values a leaf schema decodes to are fixed by `normalize`. -/
theorem normalize_of_leaf (P : KeyPolicy) (s : Schema) (bs : List UInt8) (v : Value)
    (rest : List UInt8)
    (hs : (∃ w, s = .uint w) ∨ (∃ w, s = .sint w) ∨ s = .f32 ∨ s = .f64 ∨ s = .bool ∨
      s = .string)
    (h : decodeWith P s bs = some (v, rest)) : v.normalize = v := by
  obtain ⟨pre, -, he⟩ := sound_leaf P s bs v rest hs h
  obtain ⟨ht, -⟩ := valid_of_encode s v pre he
  rcases hs with ⟨w, rfl⟩ | ⟨w, rfl⟩ | rfl | rfl | rfl | rfl <;>
    cases v <;> simp_all [Schema.hasType, Value.normalize]

/-- The decoder of one map entry, as inlined in `decodeWith`. -/
def pairDec (P : KeyPolicy) (k v : Schema) (b : List UInt8) :
    Option ((Value × Value) × List UInt8) :=
  match decodeWith P k b with
  | none => none
  | some (a, r₁) =>
    match decodeWith P v r₁ with
    | none => none
    | some (c, r₂) => some ((a, c), r₂)

/-- The `map` clause of `decodeWith`, with the entry decoder named. -/
theorem decodeWith_map_eq (P : KeyPolicy) (k v : Schema) (bs : List UInt8) :
    decodeWith P (.map k v) bs =
      (if k.zeroSized then none
      else
        match readU32 bs with
        | none => none
        | some (n, r) =>
          match decodeMany (pairDec P k v) n [] r with
          | none => none
          | some (kvs, r') => (P.map kvs).map fun kvs' => (.map kvs', r')) := by
  simp only [decodeWith]
  rfl

mutual

/-- **The lenient decoder is the raw decoder followed by `normalize`.** -/
theorem lenient_eq_raw :
    ∀ (s : Schema) (bs : List UInt8),
      decodeWith Lenient.policy s bs =
        (decodeWith KeyPolicy.raw s bs).map fun (v, r) => (v.normalize, r)
  | .uint w, bs => leaf_case (.inl ⟨w, rfl⟩) bs
  | .sint w, bs => leaf_case (.inr (.inl ⟨w, rfl⟩)) bs
  | .f32, bs => leaf_case (.inr (.inr (.inl rfl))) bs
  | .f64, bs => leaf_case (.inr (.inr (.inr (.inl rfl)))) bs
  | .bool, bs => leaf_case (.inr (.inr (.inr (.inr (.inl rfl))))) bs
  | .string, bs => leaf_case (.inr (.inr (.inr (.inr (.inr rfl))))) bs
  | .option s, bs => by
    cases bs with
    | nil => simp [decodeWith]
    | cons b r =>
      by_cases h0 : b = 0
      · simp [decodeWith, h0, Value.normalize]
      · by_cases h1 : b = 1
        · simp only [decodeWith, h1, ↓reduceIte]
          rw [lenient_eq_raw s r]
          cases decodeWith KeyPolicy.raw s r <;> simp [Value.normalize]
        · simp [decodeWith, h0, h1]
  | .vec s, bs => by
    by_cases hz : s.zeroSized = true
    · simp [decodeWith, hz]
    · simp only [decodeWith, hz, Bool.false_eq_true, ↓reduceIte]
      cases hr : readU32 bs with
      | none => simp
      | some p =>
        obtain ⟨n, r⟩ := p
        have key := decodeMany_map (fun b => decodeWith KeyPolicy.raw s b)
          (fun b => decodeWith Lenient.policy s b) Value.normalize
          (fun b => lenient_eq_raw s b) n [] r
        simp only [List.map_nil] at key
        simp only [key]
        cases decodeMany (fun b => decodeWith KeyPolicy.raw s b) n [] r <;>
          simp [Value.normalize, normalizeList_eq]
  | .array n s, bs => by
    have key := decodeMany_map (fun b => decodeWith KeyPolicy.raw s b)
      (fun b => decodeWith Lenient.policy s b) Value.normalize
      (fun b => lenient_eq_raw s b) n [] bs
    simp only [List.map_nil] at key
    simp only [decodeWith, key]
    cases decodeMany (fun b => decodeWith KeyPolicy.raw s b) n [] bs <;>
      simp [Value.normalize, normalizeList_eq]
  | .tuple fs, bs => by
    simp only [decodeWith, lenient_eq_raw_fields fs bs]
    cases decodeFieldsWith KeyPolicy.raw fs bs <;>
      simp [Value.normalize, normalizeList_eq]
  | .enum vs, bs => by
    cases bs with
    | nil => simp [decodeWith]
    | cons t r =>
      simp only [decodeWith]
      exact lenient_eq_raw_variant vs 0 t r
  | .map k v, bs => by
    rw [decodeWith_map_eq, decodeWith_map_eq]
    by_cases hz : k.zeroSized = true
    · simp [hz]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      cases hr : readU32 bs with
      | none => simp
      | some p =>
        obtain ⟨n, r⟩ := p
        have hpair : ∀ b : List UInt8,
            pairDec Lenient.policy k v b = (pairDec KeyPolicy.raw k v b).map
              fun (q : (Value × Value) × List UInt8) =>
                ((q.1.1.normalize, q.1.2.normalize), q.2) := by
          intro b
          simp only [pairDec]
          rw [lenient_eq_raw k b]
          cases hk : decodeWith KeyPolicy.raw k b with
          | none => simp
          | some q =>
            obtain ⟨a, r₁⟩ := q
            simp only [Option.map_some]
            rw [lenient_eq_raw v r₁]
            cases decodeWith KeyPolicy.raw v r₁ <;> simp
        have key := decodeMany_map (pairDec KeyPolicy.raw k v) (pairDec Lenient.policy k v)
          (fun p => (p.1.normalize, p.2.normalize)) hpair n [] r
        simp only [List.map_nil] at key
        dsimp only
        rw [key]
        cases hm : decodeMany (pairDec KeyPolicy.raw k v) n [] r with
        | none => simp
        | some q =>
          obtain ⟨kvs, r'⟩ := q
          simp [Lenient.policy, KeyPolicy.raw, Value.normalize, normalizePairs_eq]
  | .set s, bs => by
    by_cases hz : s.zeroSized = true
    · simp [decodeWith, hz]
    · simp only [decodeWith, hz, Bool.false_eq_true, ↓reduceIte]
      cases hr : readU32 bs with
      | none => simp
      | some p =>
        obtain ⟨n, r⟩ := p
        have key := decodeMany_map (fun b => decodeWith KeyPolicy.raw s b)
          (fun b => decodeWith Lenient.policy s b) Value.normalize
          (fun b => lenient_eq_raw s b) n [] r
        simp only [List.map_nil] at key
        simp only [key]
        cases decodeMany (fun b => decodeWith KeyPolicy.raw s b) n [] r with
        | none => simp
        | some q =>
          obtain ⟨xs, r'⟩ := q
          simp [Lenient.policy, KeyPolicy.raw, Value.normalize, normalizeList_eq]
where
  /-- The leaf case. -/
  leaf_case {s : Schema}
      (hs : (∃ w, s = .uint w) ∨ (∃ w, s = .sint w) ∨ s = .f32 ∨ s = .f64 ∨ s = .bool ∨
        s = .string) (bs : List UInt8) :
      decodeWith Lenient.policy s bs =
        (decodeWith KeyPolicy.raw s bs).map fun (v, r) => (v.normalize, r) := by
    rw [decodeWith_leaf Lenient.policy KeyPolicy.raw s bs hs]
    cases h : decodeWith KeyPolicy.raw s bs with
    | none => rfl
    | some p =>
      obtain ⟨v, r⟩ := p
      simp [normalize_of_leaf KeyPolicy.raw s bs v r hs h]

/-- The tuple-field version of `lenient_eq_raw`. -/
theorem lenient_eq_raw_fields :
    ∀ (fs : List Schema) (bs : List UInt8),
      decodeFieldsWith Lenient.policy fs bs =
        (decodeFieldsWith KeyPolicy.raw fs bs).map fun (vs, r) => (vs.map Value.normalize, r)
  | [], bs => by simp [decodeFieldsWith]
  | s :: fs, bs => by
    simp only [decodeFieldsWith]
    rw [lenient_eq_raw s bs]
    cases hv : decodeWith KeyPolicy.raw s bs with
    | none => simp
    | some p =>
      obtain ⟨v, r⟩ := p
      simp only [Option.map_some]
      rw [lenient_eq_raw_fields fs r]
      cases decodeFieldsWith KeyPolicy.raw fs r <;> simp

/-- The enum-variant version of `lenient_eq_raw`. -/
theorem lenient_eq_raw_variant :
    ∀ (vs : List (UInt8 × Schema)) (j : Nat) (t : UInt8) (bs : List UInt8),
      decodeVariantWith Lenient.policy vs j t bs =
        (decodeVariantWith KeyPolicy.raw vs j t bs).map fun (v, r) => (v.normalize, r)
  | [], _, _, _ => by simp [decodeVariantWith]
  | (t', s) :: vs, j, t, bs => by
    by_cases ht : t' == t
    · simp only [decodeVariantWith, ht, ↓reduceIte]
      rw [lenient_eq_raw s bs]
      cases decodeWith KeyPolicy.raw s bs <;> simp [Value.normalize]
    · simp only [decodeVariantWith, ht, Bool.false_eq_true, ↓reduceIte]
      exact lenient_eq_raw_variant vs (j + 1) t bs

end

end RT

end BorshSpec
