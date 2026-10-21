import BorshSpec.Theorems.roundtrip.Sound

/-!
# `encode` succeeds exactly on valid values

`valid_of_encode` and `encode_of_valid` are the two directions of
`encode_isSome_iff_valid`, proved by induction on the schema, with companion lemmas for
the fields of a tuple and the variants of an enum.
-/

namespace BorshSpec

namespace RT

open Schema

mutual

/-- **Totality of encoding on valid values.**  A value that has the shape of `s` and is
canonical has an encoding. -/
theorem encode_of_valid :
    ∀ (s : Schema) (v : Value), hasType s v = true → canonical s v = true →
      ∃ bs, encode s v = some bs
  | .uint w, v, ht, hc => by
    cases v <;> simp only [hasType, reduceCtorEq] at ht
    simp only [decide_eq_true_eq] at ht
    simp [encode, ht]
  | .sint w, v, ht, hc => by
    cases v <;> simp only [hasType, reduceCtorEq] at ht
    simp [encode, ht]
  | .f32, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    rename_i bits
    have hc' : isNaN32 bits = false := by simpa using hc
    simp [encode, hc']
  | .f64, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    rename_i bits
    have hc' : isNaN64 bits = false := by simpa using hc
    simp [encode, hc']
  | .bool, v, ht, hc => by
    cases v <;> simp only [hasType, reduceCtorEq] at ht
    simp [encode]
  | .string, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp [encode, hc.1, hc.2]
  | .option s, v, ht, hc => by
    cases v <;> simp only [hasType, reduceCtorEq] at ht
    · simp [encode]
    · simp only [canonical] at hc
      obtain ⟨e, he⟩ := encode_of_valid s _ ht hc
      simp [encode, he]
  | .vec s, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    rename_i xs
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq] at ht hc
    obtain ⟨es, hes⟩ := mapM_isSome (encode s) xs
      fun x hx => encode_of_valid s x (ht.2 x hx) (hc.2 x hx)
    exact ⟨toLE 4 xs.length ++ es.flatten, by simp [encode, ht.1, hc.1, hes]⟩
  | .array n s, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    rename_i xs
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ht hc
    obtain ⟨es, hes⟩ := mapM_isSome (encode s) xs
      fun x hx => encode_of_valid s x (ht.2 x hx) (hc x hx)
    exact ⟨es.flatten, by simp [encode, ht.1, hes]⟩
  | .tuple fs, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    obtain ⟨bs, hbs⟩ := encodeFields_of_valid fs _ ht hc
    exact ⟨bs, by simpa [encode] using hbs⟩
  | .enum vs, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    obtain ⟨bs, hbs⟩ := encodeVariant_of_valid vs [] _ _ ht hc
    exact ⟨bs, by simpa [encode] using hbs⟩
  | .map k s, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    rename_i kvs
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq] at ht hc
    obtain ⟨es, hes⟩ := mapM_isSome
      (fun (p : Value × Value) => do
        let ea ← encode k p.1
        let eb ← encode s p.2
        pure (ea ++ eb)) kvs
      (by
        rintro ⟨a, c⟩ hx
        obtain ⟨ea, hea⟩ := encode_of_valid k a (by simpa using (ht.2 _ hx).1)
          (by simpa using (hc.2 _ hx).1)
        obtain ⟨eb, heb⟩ := encode_of_valid s c (by simpa using (ht.2 _ hx).2)
          (by simpa using (hc.2 _ hx).2)
        exact ⟨ea ++ eb, by simp [hea, heb, bind, pure]⟩)
    refine ⟨toLE 4 kvs.length ++ es.flatten, ?_⟩
    simp [encode, ht.1, hc.1.1, hc.1.2]
    exact ⟨es, hes, rfl⟩
  | .set s, v, ht, hc => by
    cases v <;> simp only [hasType, canonical, reduceCtorEq] at ht hc
    rename_i xs
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq] at ht hc
    obtain ⟨es, hes⟩ := mapM_isSome (encode s) xs
      fun x hx => encode_of_valid s x (ht.2 x hx) (hc.2 x hx)
    exact ⟨toLE 4 xs.length ++ es.flatten, by simp [encode, ht.1, hc.1.1, hc.1.2, hes]⟩

/-- Totality of encoding for tuple fields. -/
theorem encodeFields_of_valid :
    ∀ (fs : List Schema) (vs : List Value), hasTypeFields fs vs = true →
      canonicalFields fs vs = true → ∃ bs, encodeFields fs vs = some bs
  | [], [], _, _ => ⟨[], rfl⟩
  | [], _ :: _, ht, _ => by simp [hasTypeFields] at ht
  | _ :: _, [], ht, _ => by simp [hasTypeFields] at ht
  | s :: fs, v :: vs, ht, hc => by
    simp only [hasTypeFields, canonicalFields, Bool.and_eq_true] at ht hc
    obtain ⟨e, he⟩ := encode_of_valid s v ht.1 hc.1
    obtain ⟨es, hes⟩ := encodeFields_of_valid fs vs ht.2 hc.2
    exact ⟨e ++ es, by simp [encodeFields, he, hes, bind, pure]⟩

/-- Totality of encoding for the payload of an enum variant. -/
theorem encodeVariant_of_valid :
    ∀ (vs : List (UInt8 × Schema)) (earlier : List UInt8) (i : Nat) (v : Value),
      hasTypeVariant vs earlier i v = true → canonicalVariant vs i v = true →
        ∃ bs, encodeVariant vs earlier i v = some bs
  | [], _, _, _, ht, _ => by simp [hasTypeVariant] at ht
  | (t, s) :: vs, earlier, 0, v, ht, hc => by
    simp only [hasTypeVariant, canonicalVariant, Bool.and_eq_true, Bool.not_eq_true'] at ht hc
    obtain ⟨e, he⟩ := encode_of_valid s v ht.2 hc
    have hn : ¬ t ∈ earlier := by simpa using ht.1
    exact ⟨t :: e, by simp [encodeVariant, hn, he]⟩
  | (t, s) :: vs, earlier, i + 1, v, ht, hc => by
    simp only [hasTypeVariant, canonicalVariant] at ht hc
    obtain ⟨e, he⟩ := encodeVariant_of_valid vs (t :: earlier) i v ht hc
    exact ⟨e, by simp [encodeVariant, he]⟩

end

mutual

/-- **Encoding implies validity.**  Whatever `encode` produces comes from a value that
has the shape of `s` and is canonical. -/
theorem valid_of_encode :
    ∀ (s : Schema) (v : Value) (bs : List UInt8), encode s v = some bs →
      hasType s v = true ∧ canonical s v = true
  | .uint w, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · rename_i hn
      simp [hasType, canonical, hn]
    · simp at h
  | .sint w, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · rename_i hn
      simp [hasType, canonical, hn]
    · simp at h
  | .f32, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · simp at h
    · rename_i hn
      simpa [hasType, canonical] using hn
  | .f64, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · simp at h
    · rename_i hn
      simpa [hasType, canonical] using hn
  | .bool, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    simp [hasType, canonical]
  | .string, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    split at h
    · rename_i hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      simp [hasType, canonical, hv.1, hv.2]
    · simp at h
  | .option s, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    · simp [hasType, canonical]
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      obtain ⟨ht, hc⟩ := valid_of_encode s _ e he
      simp [hasType, canonical, ht, hc]
  | .vec s, v, bs, h => by
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
      have hall := mapM_forall (encode s) xs es hes
      have hlen : xs.length < 2 ^ 32 := by simpa using hc.2
      refine ⟨?_, ?_⟩
      · simp only [hasType, hc.1, Bool.not_false, Bool.true_and, List.all_eq_true]
        intro x hx
        obtain ⟨p, hp⟩ := hall x hx
        exact (valid_of_encode s x p hp).1
      · simp only [canonical, hlen, decide_true, Bool.true_and, List.all_eq_true]
        intro x hx
        obtain ⟨p, hp⟩ := hall x hx
        exact (valid_of_encode s x p hp).2
  | .array n s, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    rename_i xs
    split at h
    · rename_i hn
      rw [Option.map_eq_some_iff] at h
      obtain ⟨es, hes, rfl⟩ := h
      have hall := mapM_forall (encode s) xs es hes
      refine ⟨?_, ?_⟩
      · simp only [hasType, hn, Bool.true_and, List.all_eq_true]
        intro x hx
        obtain ⟨p, hp⟩ := hall x hx
        exact (valid_of_encode s x p hp).1
      · simp only [canonical, List.all_eq_true]
        intro x hx
        obtain ⟨p, hp⟩ := hall x hx
        exact (valid_of_encode s x p hp).2
    · simp at h
  | .tuple fs, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    obtain ⟨ht, hc⟩ := valid_of_encodeFields fs _ bs h
    exact ⟨by simpa [hasType] using ht, by simpa [canonical] using hc⟩
  | .enum vs, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    obtain ⟨ht, hc⟩ := valid_of_encodeVariant vs [] _ _ bs h
    exact ⟨by simpa [hasType] using ht, by simpa [canonical] using hc⟩
  | .map k s, v, bs, h => by
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
      have hlen : kvs.length < 2 ^ 32 := by simpa using hc.1.2
      have hsorted : Value.strictAsc (kvs.map Prod.fst) = true := by simpa using hc.2
      have hall := mapM_forall (fun (p : Value × Value) => do
          let ea ← encode k p.1
          let eb ← encode s p.2
          pure (ea ++ eb)) kvs es hes
      have hpair : ∀ a c, (a, c) ∈ kvs →
          hasType k a = true ∧ canonical k a = true ∧ hasType s c = true ∧
            canonical s c = true := by
        intro a c hx
        obtain ⟨p, hp⟩ := hall _ hx
        simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hp
        obtain ⟨ea, hea, eb, heb, -⟩ := hp
        obtain ⟨h1, h2⟩ := valid_of_encode k a ea hea
        obtain ⟨h3, h4⟩ := valid_of_encode s c eb heb
        exact ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ?_⟩
      · simp only [hasType, hc.1.1, Bool.not_false, Bool.true_and, List.all_eq_true,
          Bool.and_eq_true]
        rintro ⟨a, c⟩ hx
        exact ⟨(hpair a c hx).1, (hpair a c hx).2.2.1⟩
      · simp only [canonical, hlen, decide_true, Bool.true_and, hsorted, List.all_eq_true,
          Bool.and_eq_true]
        rintro ⟨a, c⟩ hx
        exact ⟨(hpair a c hx).2.1, (hpair a c hx).2.2.2⟩
  | .set s, v, bs, h => by
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
      have hlen : xs.length < 2 ^ 32 := by simpa using hc.1.2
      have hsorted : Value.strictAsc xs = true := by simpa using hc.2
      have hall := mapM_forall (encode s) xs es hes
      refine ⟨?_, ?_⟩
      · simp only [hasType, hc.1.1, Bool.not_false, Bool.true_and, List.all_eq_true]
        intro x hx
        obtain ⟨p, hp⟩ := hall x hx
        exact (valid_of_encode s x p hp).1
      · simp only [canonical, hlen, decide_true, Bool.true_and, hsorted, List.all_eq_true]
        intro x hx
        obtain ⟨p, hp⟩ := hall x hx
        exact (valid_of_encode s x p hp).2

/-- Encoding the fields of a tuple implies validity of the fields. -/
theorem valid_of_encodeFields :
    ∀ (fs : List Schema) (vs : List Value) (bs : List UInt8), encodeFields fs vs = some bs →
      hasTypeFields fs vs = true ∧ canonicalFields fs vs = true
  | [], [], _, _ => by simp [hasTypeFields, canonicalFields]
  | [], _ :: _, bs, h => by simp [encodeFields] at h
  | _ :: _, [], bs, h => by simp [encodeFields] at h
  | s :: fs, v :: vs, bs, h => by
    simp only [encodeFields, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨e, he, es, hes, rfl⟩ := h
    obtain ⟨h1, h2⟩ := valid_of_encode s v e he
    obtain ⟨h3, h4⟩ := valid_of_encodeFields fs vs es hes
    exact ⟨by simp [hasTypeFields, h1, h3], by simp [canonicalFields, h2, h4]⟩

/-- Encoding the payload of an enum variant implies validity. -/
theorem valid_of_encodeVariant :
    ∀ (vs : List (UInt8 × Schema)) (earlier : List UInt8) (i : Nat) (v : Value)
      (bs : List UInt8), encodeVariant vs earlier i v = some bs →
        hasTypeVariant vs earlier i v = true ∧ canonicalVariant vs i v = true
  | [], _, _, _, bs, h => by simp [encodeVariant] at h
  | (t, s) :: vs, earlier, 0, v, bs, h => by
    simp only [encodeVariant] at h
    split at h
    · simp at h
    · rename_i hc
      rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      obtain ⟨h1, h2⟩ := valid_of_encode s v e he
      have hn : ¬ t ∈ earlier := by simpa using hc
      simp [hasTypeVariant, canonicalVariant, hn, h1, h2]
  | (t, _) :: vs, earlier, i + 1, v, bs, h => by
    simp only [encodeVariant] at h
    exact valid_of_encodeVariant vs (t :: earlier) i v bs h

end

/-- `encode` succeeds exactly on valid values. -/
theorem encode_isSome_iff_valid' (s : Schema) (v : Value) :
    (encode s v).isSome = true ↔ Valid s v := by
  constructor
  · intro h
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 h
    exact valid_of_encode s v bs hbs
  · rintro ⟨ht, hc⟩
    obtain ⟨bs, hbs⟩ := encode_of_valid s v ht hc
    simp [hbs]

end RT

end BorshSpec
