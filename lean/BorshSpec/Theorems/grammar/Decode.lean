import BorshSpec.Theorems.grammar.Encode

/-!
# Helper lemmas: `decode` against the grammar

`decodeWith strict s B = some (v, r)` exactly when `B = b ++ r` for some `b` with
`Encodes s v b`.  The statement about a prefix `bs ++ rest` follows by cancelling `rest`.
-/

namespace BorshSpec

namespace GrammarProof

/-- `decodeMany` against a relation on lists: it succeeds with `xs` and leaves `r` exactly
when the list read is the accumulator reversed followed by `ys`, and the bytes read are
the ones related to `ys`. -/
theorem decodeMany_iff {α : Type} (d : List UInt8 → Option (α × List UInt8))
    (E : α → List UInt8 → Prop) (R : List α → List UInt8 → Prop)
    (Hd : ∀ x B r, d B = some (x, r) ↔ ∃ b, B = b ++ r ∧ E x b)
    (Rnil : ∀ bs, R [] bs ↔ bs = [])
    (Rcons : ∀ y ys bs, R (y :: ys) bs ↔ ∃ b bs', bs = b ++ bs' ∧ E y b ∧ R ys bs') :
    ∀ (n : Nat) (acc : List α) (B : List UInt8) (xs : List α) (r : List UInt8),
      Schema.decodeMany d n acc B = some (xs, r) ↔
        ∃ ys b, xs = acc.reverse ++ ys ∧ ys.length = n ∧ B = b ++ r ∧ R ys b
  | 0 => by
    intro acc B xs r
    simp only [Schema.decodeMany, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨[], [], by simp, rfl, by simp, (Rnil _).2 rfl⟩
    · rintro ⟨ys, b, rfl, h1, rfl, h2⟩
      have := List.length_eq_zero_iff.1 h1
      subst this
      have := (Rnil _).1 h2
      subst this
      simp
  | n + 1 => by
    intro acc B xs r
    simp only [Schema.decodeMany]
    have ih := decodeMany_iff d E R Hd Rnil Rcons n
    cases hd : d B with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨ys, b, _, h1, h2, h3⟩
      obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := by
        cases ys with
        | nil => simp at h1
        | cons y ys' => exact ⟨y, ys', rfl⟩
      obtain ⟨b1, b2, rfl, h4, _⟩ := (Rcons _ _ _).1 h3
      have := (Hd y B (b2 ++ r)).2 ⟨b1, by rw [h2]; simp, h4⟩
      rw [hd] at this
      exact absurd this (by simp)
    | some p =>
      obtain ⟨x, r'⟩ := p
      simp only [ih (x :: acc) r' xs r]
      constructor
      · rintro ⟨ys, b', rfl, h1, h2, h3⟩
        obtain ⟨b0, h5, h6⟩ := (Hd x B r').1 hd
        refine ⟨x :: ys, b0 ++ b', by simp, by simp [h1], by rw [h5, h2]; simp, ?_⟩
        exact (Rcons _ _ _).2 ⟨b0, b', rfl, h6, h3⟩
      · rintro ⟨ys, b, rfl, h1, h2, h3⟩
        obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := by
          cases ys with
          | nil => simp at h1
          | cons y ys' => exact ⟨y, ys', rfl⟩
        obtain ⟨b1, b2, rfl, h4, h5⟩ := (Rcons _ _ _).1 h3
        have h6 := (Hd y B (b2 ++ r)).2 ⟨b1, by rw [h2]; simp, h4⟩
        rw [hd] at h6
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h6)
        exact ⟨ys', b2, by simp, by simpa using h1, rfl, h5⟩


theorem readU32_iff (B : List UInt8) (n : Nat) (r : List UInt8) :
    Schema.readU32 B = some (n, r) ↔ n < 2 ^ 32 ∧ B = leBytes 4 n ++ r := by
  unfold Schema.readU32
  rw [readLE_leBytes_iff]

theorem leBytes_append_inj {k n m : Nat} {a b : List UInt8} (hn : n < 256 ^ k) (hm : m < 256 ^ k)
    (h : leBytes k n ++ a = leBytes k m ++ b) : n = m ∧ a = b := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_leBytes, length_leBytes])
  have := congrArg fromLE h1
  rw [fromLE_leBytes, fromLE_leBytes, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
  exact ⟨this, h2⟩

theorem prefix_unique {len n : Nat} {body r r0 : List UInt8} (h1 : len < 2 ^ 32)
    (h2 : n < 2 ^ 32) (h : leBytes 4 len ++ body ++ r = leBytes 4 n ++ r0) :
    len = n ∧ r0 = body ++ r := by
  rw [List.append_assoc] at h
  obtain ⟨h3, h4⟩ := leBytes_append_inj (k := 4) (by simpa using h1) (by simpa using h2) h
  exact ⟨h3, h4.symm⟩

/-- `decodeMany` from an empty accumulator. -/
theorem decodeMany_iff0 {α : Type} (d : List UInt8 → Option (α × List UInt8))
    (E : α → List UInt8 → Prop) (R : List α → List UInt8 → Prop)
    (Hd : ∀ x B r, d B = some (x, r) ↔ ∃ b, B = b ++ r ∧ E x b)
    (Rnil : ∀ bs, R [] bs ↔ bs = [])
    (Rcons : ∀ y ys bs, R (y :: ys) bs ↔ ∃ b bs', bs = b ++ bs' ∧ E y b ∧ R ys bs')
    (n : Nat) (B : List UInt8) (xs : List α) (r : List UInt8) :
    Schema.decodeMany d n [] B = some (xs, r) ↔ ∃ b, B = b ++ r ∧ xs.length = n ∧ R xs b := by
  rw [decodeMany_iff d E R Hd Rnil Rcons]
  constructor
  · rintro ⟨ys, b, rfl, h1, h2, h3⟩
    exact ⟨b, h2, by simpa using h1, by simpa using h3⟩
  · rintro ⟨b, h1, h2, h3⟩
    exact ⟨xs, b, by simp, h2, h1, h3⟩

theorem map_pair_iff {α : Type} (o : Option (α × List UInt8)) (g : α → Value)
    (v : Value) (r : List UInt8) :
    (o.map fun (xs, r) => (g xs, r)) = some (v, r) ↔ ∃ xs, o = some (xs, r) ∧ g xs = v := by
  cases o with
  | none => simp
  | some p =>
    obtain ⟨xs, r'⟩ := p
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨xs, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨ys, ⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, rfl⟩

theorem pairs_cons' (k w : Schema) (y : Value × Value) (kvs : List (Value × Value))
    (bs : List UInt8) :
    EncodesPairs k w (y :: kvs) bs ↔ ∃ b bs', bs = b ++ bs' ∧
      (∃ bk bv, b = bk ++ bv ∧ Encodes k y.1 bk ∧ Encodes w y.2 bv) ∧ EncodesPairs k w kvs bs' := by
  obtain ⟨a, c⟩ := y
  rw [pairs_cons]
  constructor
  · rintro ⟨bk, bv, bs', rfl, h1, h2, h3⟩
    exact ⟨bk ++ bv, bs', rfl, ⟨bk, bv, rfl, h1, h2⟩, h3⟩
  · rintro ⟨b, bs', rfl, ⟨bk, bv, rfl, h1, h2⟩, h3⟩
    exact ⟨bk, bv, bs', rfl, h1, h2, h3⟩

theorem pair_iff (k w : Schema)
    (ihk : ∀ (v : Value) (B r : List UInt8),
      Schema.decodeWith KeyPolicy.strict k B = some (v, r) ↔ ∃ b, B = b ++ r ∧ Encodes k v b)
    (ihw : ∀ (v : Value) (B r : List UInt8),
      Schema.decodeWith KeyPolicy.strict w B = some (v, r) ↔ ∃ b, B = b ++ r ∧ Encodes w v b)
    (p : Value × Value) (B r : List UInt8) :
    (match Schema.decodeWith KeyPolicy.strict k B with
      | none => none
      | some (a, r₁) =>
        match Schema.decodeWith KeyPolicy.strict w r₁ with
        | none => none
        | some (c, r₂) => some ((a, c), r₂)) = some (p, r) ↔
      ∃ b, B = b ++ r ∧ ∃ bk bv, b = bk ++ bv ∧ Encodes k p.1 bk ∧ Encodes w p.2 bv := by
  obtain ⟨a, c⟩ := p
  cases h1 : Schema.decodeWith KeyPolicy.strict k B with
  | none =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨b, rfl, bk, bv, rfl, h2, _⟩
    have := (ihk a (bk ++ bv ++ r) (bv ++ r)).2 ⟨bk, by simp, h2⟩
    rw [h1] at this
    exact absurd this (by simp)
  | some q =>
    obtain ⟨a', r1⟩ := q
    cases h2 : Schema.decodeWith KeyPolicy.strict w r1 with
    | none =>
      simp only [h2, reduceCtorEq, false_iff]
      rintro ⟨b, rfl, bk, bv, rfl, h3, h4⟩
      have e1 := (ihk a (bk ++ bv ++ r) (bv ++ r)).2 ⟨bk, by simp, h3⟩
      rw [h1] at e1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
      have e2 := (ihw c (bv ++ r) r).2 ⟨bv, rfl, h4⟩
      rw [h2] at e2
      exact absurd e2 (by simp)
    | some q' =>
      obtain ⟨c', r2⟩ := q'
      simp only [h2, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨rfl, rfl⟩, rfl⟩
        obtain ⟨bk, hb1, hb2⟩ := (ihk a' B r1).1 h1
        obtain ⟨bv, hb3, hb4⟩ := (ihw c' r1 r2).1 h2
        exact ⟨bk ++ bv, by rw [hb1, hb3]; simp, bk, bv, rfl, hb2, hb4⟩
      · rintro ⟨b, rfl, bk, bv, rfl, h3, h4⟩
        have e1 := (ihk a (bk ++ bv ++ r) (bv ++ r)).2 ⟨bk, by simp, h3⟩
        rw [h1] at e1
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
        have e2 := (ihw c (bv ++ r) r).2 ⟨bv, rfl, h4⟩
        rw [h2] at e2
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e2)
        exact ⟨⟨rfl, rfl⟩, rfl⟩

mutual

theorem decode_iff : (s : Schema) → ∀ (v : Value) (B r : List UInt8),
    (Schema.decodeWith KeyPolicy.strict s B = some (v, r) ↔ ∃ b, B = b ++ r ∧ Encodes s v b)
  | .uint w => by
    intro v B r
    simp only [Schema.decodeWith, enc_uint]
    cases hr : readLE w.bytes B with
    | none =>
      simp only [Option.map_none, reduceCtorEq, false_iff]
      rintro ⟨b, rfl, n, rfl, h1, rfl⟩
      rw [readLE_leBytes h1] at hr
      exact absurd hr (by simp)
    | some p =>
      obtain ⟨n, r'⟩ := p
      obtain ⟨h1, h2⟩ := (readLE_leBytes_iff _ _ _ _).1 hr
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨leBytes w.bytes n, h2, n, rfl, h1, rfl⟩
      · rintro ⟨b, rfl, m, rfl, h3, rfl⟩
        obtain ⟨rfl, rfl⟩ := leBytes_append_inj h3 h1 h2
        exact ⟨rfl, rfl⟩
  | .sint w => by
    intro v B r
    simp only [Schema.decodeWith, enc_sint]
    cases hr : readLE w.bytes B with
    | none =>
      simp only [Option.map_none, reduceCtorEq, false_iff]
      rintro ⟨b, rfl, i, rfl, _, _, rfl⟩
      rw [readLE_leBytes (twos_lt w i)] at hr
      exact absurd hr (by simp)
    | some p =>
      obtain ⟨n, r'⟩ := p
      obtain ⟨h1, h2⟩ := (readLE_leBytes_iff _ _ _ _).1 hr
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        have hin := (sintInRange_iff w _).1 (sintInRange_natToSint w n h1)
        refine ⟨leBytes w.bytes n, h2, Schema.natToSint w n, rfl, hin.1, hin.2, ?_⟩
        rw [twos_natToSint w n h1]
      · rintro ⟨b, rfl, i, rfl, h3, h4, rfl⟩
        obtain ⟨h5, rfl⟩ := leBytes_append_inj (twos_lt w i) h1 h2
        rw [← h5, natToSint_twos w i ((sintInRange_iff w i).2 ⟨h3, h4⟩)]
        exact ⟨rfl, rfl⟩
  | .f32 => by
    intro v B r
    simp only [Schema.decodeWith, enc_f32]
    cases hr : readLE 4 B with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨b, rfl, bits, rfl, _, rfl⟩
      rw [readLE_leBytes (toNat_lt32 bits)] at hr
      exact absurd hr (by simp)
    | some p =>
      obtain ⟨n, r'⟩ := p
      obtain ⟨h1, h2⟩ := (readLE_leBytes_iff _ _ _ _).1 hr
      by_cases hn : isNaN32 (UInt32.ofNat n) = true
      · simp only [hn, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨b, rfl, bits, rfl, h3, rfl⟩
        obtain ⟨h5, rfl⟩ := leBytes_append_inj (toNat_lt32 bits) h1 h2
        apply h3
        rw [← isNaN32_iff]
        have : UInt32.ofNat n = bits := by rw [← h5, UInt32.ofNat_toNat]
        rw [this] at hn
        exact hn
      · simp only [hn, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          refine ⟨leBytes 4 n, h2, UInt32.ofNat n, rfl, ?_, ?_⟩
          · rw [← isNaN32_iff]; exact hn
          · rw [toNat_ofNat32 h1]
        · rintro ⟨b, rfl, bits, rfl, _, rfl⟩
          obtain ⟨h5, rfl⟩ := leBytes_append_inj (toNat_lt32 bits) h1 h2
          rw [← h5, UInt32.ofNat_toNat]
          exact ⟨rfl, rfl⟩
  | .f64 => by
    intro v B r
    simp only [Schema.decodeWith, enc_f64]
    cases hr : readLE 8 B with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨b, rfl, bits, rfl, _, rfl⟩
      rw [readLE_leBytes (toNat_lt64 bits)] at hr
      exact absurd hr (by simp)
    | some p =>
      obtain ⟨n, r'⟩ := p
      obtain ⟨h1, h2⟩ := (readLE_leBytes_iff _ _ _ _).1 hr
      by_cases hn : isNaN64 (UInt64.ofNat n) = true
      · simp only [hn, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨b, rfl, bits, rfl, h3, rfl⟩
        obtain ⟨h5, rfl⟩ := leBytes_append_inj (toNat_lt64 bits) h1 h2
        apply h3
        rw [← isNaN64_iff]
        have : UInt64.ofNat n = bits := by rw [← h5, UInt64.ofNat_toNat]
        rw [this] at hn
        exact hn
      · simp only [hn, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          refine ⟨leBytes 8 n, h2, UInt64.ofNat n, rfl, ?_, ?_⟩
          · rw [← isNaN64_iff]; exact hn
          · rw [toNat_ofNat64 h1]
        · rintro ⟨b, rfl, bits, rfl, _, rfl⟩
          obtain ⟨h5, rfl⟩ := leBytes_append_inj (toNat_lt64 bits) h1 h2
          rw [← h5, UInt64.ofNat_toNat]
          exact ⟨rfl, rfl⟩
  | .bool => by
    intro v B r
    simp only [Schema.decodeWith, enc_bool]
    cases B with
    | nil =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨b, h, x, _, rfl⟩
      simp at h
    | cons b0 r0 =>
      by_cases h0 : b0 = 0
      · subst h0
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨[0], rfl, false, rfl, rfl⟩
        · rintro ⟨b, h, x, rfl, rfl⟩
          cases x
          · simp at h
            exact ⟨rfl, h⟩
          · simp at h
      · by_cases h1 : b0 = 1
        · subst h1
          simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩
            exact ⟨[1], rfl, true, rfl, rfl⟩
          · rintro ⟨b, h, x, rfl, rfl⟩
            cases x
            · simp at h
            · simp at h
              exact ⟨rfl, h⟩
        · simp only [h0, h1, ↓reduceIte, reduceCtorEq, false_iff]
          rintro ⟨b, h, x, rfl, rfl⟩
          cases x
          · simp at h
            exact h0 h.1
          · simp at h
            exact h1 h.1
  | .string => by
    intro v B r
    simp only [Schema.decodeWith, enc_string]
    cases hr : Schema.readU32 B with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨b, rfl, body, rfl, _, h2, rfl⟩
      have := (readU32_iff (leBytes 4 body.length ++ body ++ r) body.length (body ++ r)).2
        ⟨h2, by simp⟩
      rw [hr] at this
      exact absurd this (by simp)
    | some p =>
      obtain ⟨n, r0⟩ := p
      obtain ⟨h1, h2⟩ := (readU32_iff _ _ _).1 hr
      cases ht : takeExact n r0 with
      | none =>
        simp only [ht, reduceCtorEq, false_iff]
        rintro ⟨b, rfl, body, rfl, _, h4, rfl⟩
        obtain ⟨rfl, h6⟩ := prefix_unique h4 h1 h2
        have := (takeExact_iff body.length r0 body r).2 ⟨h6, rfl⟩
        rw [ht] at this
        exact absurd this (by simp)
      | some q =>
        obtain ⟨body, r'⟩ := q
        obtain ⟨ht1, ht2⟩ := (takeExact_iff _ _ _ _).1 ht
        by_cases hv : validUtf8 body = true
        · simp only [ht, hv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩
            refine ⟨leBytes 4 body.length ++ body, ?_, body, rfl, (validUtf8_iff_wf body).1 hv, ?_, rfl⟩
            · rw [h2, ht1, ht2]; simp
            · rw [ht2]; exact h1
          · rintro ⟨b, rfl, body2, rfl, h3, h4, rfl⟩
            obtain ⟨h5, h6⟩ := prefix_unique h4 h1 h2
            subst h5
            rw [ht1] at h6
            obtain ⟨rfl, rfl⟩ := List.append_inj h6 ht2
            exact ⟨rfl, rfl⟩
        · simp only [ht, hv, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
          rintro ⟨b, rfl, body2, rfl, h3, h4, rfl⟩
          obtain ⟨h5, h6⟩ := prefix_unique h4 h1 h2
          subst h5
          rw [ht1] at h6
          obtain ⟨rfl, rfl⟩ := List.append_inj h6 ht2
          exact hv ((validUtf8_iff_wf _).2 h3)
  | .option s => by
    intro v B r
    have ih := decode_iff s
    simp only [Schema.decodeWith, enc_option]
    cases B with
    | nil =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨b, h, (⟨_, rfl⟩ | ⟨x, b', _, rfl, _⟩)⟩ <;> simp at h
    | cons b0 r0 =>
      by_cases h0 : b0 = 0
      · subst h0
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨[0], rfl, Or.inl ⟨rfl, rfl⟩⟩
        · rintro ⟨b, h, (⟨rfl, rfl⟩ | ⟨x, b', rfl, rfl, _⟩)⟩
          · simp at h
            exact ⟨rfl, h⟩
          · simp at h
      · by_cases h1 : b0 = 1
        · subst h1
          simp only [h0, ↓reduceIte]
          rw [map_pair_iff]
          constructor
          · rintro ⟨x, h, rfl⟩
            obtain ⟨b', h3, h4⟩ := (ih x r0 r).1 h
            exact ⟨1 :: b', by simp [h3], Or.inr ⟨x, b', rfl, rfl, h4⟩⟩
          · rintro ⟨b, h, (⟨rfl, rfl⟩ | ⟨x, b', rfl, rfl, h4⟩)⟩
            · simp at h
            · simp at h
              exact ⟨x, (ih x r0 r).2 ⟨b', h, h4⟩, rfl⟩
        · simp only [h0, h1, ↓reduceIte, reduceCtorEq, false_iff]
          rintro ⟨b, h, (⟨rfl, rfl⟩ | ⟨x, b', rfl, rfl, _⟩)⟩
          · simp at h
            exact h0 h.1
          · simp at h
            exact h1 h.1
  | .vec s => by
    intro v B r
    have ih := decode_iff s
    simp only [Schema.decodeWith, enc_vec]
    by_cases hz : s.zeroSized = true
    · simp only [hz, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨b, _, xs, b', _, _, h, _⟩
      exact h ((zeroSized_iff s).1 hz)
    · have hz' : ¬ SizeZero s := fun h => hz ((zeroSized_iff s).2 h)
      simp only [hz, Bool.false_eq_true, ↓reduceIte]
      cases hr : Schema.readU32 B with
      | none =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨b, rfl, xs, b', rfl, rfl, _, h1, _⟩
        have := (readU32_iff (leBytes 4 xs.length ++ b' ++ r) xs.length (b' ++ r)).2
          ⟨h1, by simp⟩
        rw [hr] at this
        exact absurd this (by simp)
      | some p =>
        obtain ⟨n, r0⟩ := p
        obtain ⟨h1, h2⟩ := (readU32_iff _ _ _).1 hr
        have dm := decodeMany_iff0 (fun b => Schema.decodeWith KeyPolicy.strict s b) (Encodes s)
          (EncodesAll s) ih (all_nil s) (all_cons s) n r0
        simp only []
        rw [map_pair_iff]
        constructor
        · rintro ⟨xs, h, rfl⟩
          obtain ⟨b, hb1, hb2, hb3⟩ := (dm xs r).1 h
          subst hb2
          exact ⟨leBytes 4 xs.length ++ b, by rw [h2, hb1]; simp, xs, b, rfl, rfl, hz', h1, hb3⟩
        · rintro ⟨b, rfl, xs, b', rfl, rfl, _, h3, h4⟩
          obtain ⟨h5, h6⟩ := prefix_unique h3 h1 h2
          subst h5
          exact ⟨xs, (dm xs r).2 ⟨b', h6, rfl, h4⟩, rfl⟩
  | .array n s => by
    intro v B r
    have ih := decode_iff s
    have dm := decodeMany_iff0 (fun b => Schema.decodeWith KeyPolicy.strict s b) (Encodes s)
      (EncodesAll s) ih (all_nil s) (all_cons s) n B
    simp only [Schema.decodeWith, enc_array]
    rw [map_pair_iff]
    constructor
    · rintro ⟨xs, h, rfl⟩
      obtain ⟨b, h1, h2, h3⟩ := (dm xs r).1 h
      exact ⟨b, h1, xs, rfl, h2, h3⟩
    · rintro ⟨b, h1, xs, rfl, h2, h3⟩
      exact ⟨xs, (dm xs r).2 ⟨b, h1, h2, h3⟩, rfl⟩
  | .tuple fs => by
    intro v B r
    have ih := fields_dec_iff fs
    simp only [Schema.decodeWith, enc_tuple]
    rw [map_pair_iff]
    constructor
    · rintro ⟨xs, h, rfl⟩
      obtain ⟨b, h1, h2⟩ := (ih xs B r).1 h
      exact ⟨b, h1, xs, rfl, h2⟩
    · rintro ⟨b, h1, xs, rfl, h2⟩
      exact ⟨xs, (ih xs B r).2 ⟨b, h1, h2⟩, rfl⟩
  | .enum vs => by
    intro v B r
    have ih := variant_dec_iff vs
    simp only [Schema.decodeWith, enc_enum]
    cases B with
    | nil =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨b, h, i, tag, s', x, b', _, rfl, _⟩
      simp at h
    | cons t r0 =>
      simp only []
      rw [ih]
      constructor
      · rintro ⟨j, s', x, b, rfl, hv, h1, h2⟩
        exact ⟨t :: b, by simp [h1], j, t, s', x, b, by simp, rfl, hv, h2⟩
      · rintro ⟨b, h, i, tag, s', x, b', rfl, rfl, hv, h2⟩
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        exact ⟨i, s', x, b', by simp, hv, h, h2⟩
  | .map k w => by
    intro v B r
    have ihk := decode_iff k
    have ihw := decode_iff w
    simp only [Schema.decodeWith, enc_map]
    by_cases hz : k.zeroSized = true
    · simp only [hz, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨b, _, xs, b', _, _, h, _⟩
      exact h ((zeroSized_iff k).1 hz)
    · have hz' : ¬ SizeZero k := fun h => hz ((zeroSized_iff k).2 h)
      simp only [hz, Bool.false_eq_true, ↓reduceIte]
      cases hr : Schema.readU32 B with
      | none =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨b, rfl, xs, b', rfl, rfl, _, h1, _⟩
        have := (readU32_iff (leBytes 4 xs.length ++ b' ++ r) xs.length (b' ++ r)).2
          ⟨h1, by simp⟩
        rw [hr] at this
        exact absurd this (by simp)
      | some p =>
        obtain ⟨n, r0⟩ := p
        obtain ⟨h1, h2⟩ := (readU32_iff _ _ _).1 hr
        simp only []
        have dm := decodeMany_iff0 (fun b =>
            match Schema.decodeWith KeyPolicy.strict k b with
            | none => none
            | some (a, r₁) =>
              match Schema.decodeWith KeyPolicy.strict w r₁ with
              | none => none
              | some (c, r₂) => some ((a, c), r₂))
          (fun p b => ∃ bk bv, b = bk ++ bv ∧ Encodes k p.1 bk ∧ Encodes w p.2 bv)
          (EncodesPairs k w) (fun x B r => pair_iff k w ihk ihw x B r) (pairs_nil k w)
          (fun y ys bs => pairs_cons' k w y ys bs) n r0
        cases hd : Schema.decodeMany (fun b =>
            match Schema.decodeWith KeyPolicy.strict k b with
            | none => none
            | some (a, r₁) =>
              match Schema.decodeWith KeyPolicy.strict w r₁ with
              | none => none
              | some (c, r₂) => some ((a, c), r₂)) n [] r0 with
        | none =>
          simp only [reduceCtorEq, false_iff]
          rintro ⟨b, rfl, kvs, b', rfl, rfl, _, h3, _, h4⟩
          obtain ⟨h5, h6⟩ := prefix_unique h3 h1 h2
          subst h5
          have := (dm kvs r).2 ⟨b', h6, rfl, h4⟩
          rw [hd] at this
          exact absurd this (by simp)
        | some q =>
          obtain ⟨kvs, r'⟩ := q
          obtain ⟨b', hb1, hb2, hb3⟩ := (dm kvs r').1 hd
          by_cases hsa : Value.strictAsc (kvs.map Prod.fst) = true
          · simp only [KeyPolicy.strict, hsa, ↓reduceIte, Option.map_some, Option.some.injEq,
              Prod.mk.injEq]
            constructor
            · rintro ⟨rfl, rfl⟩
              subst hb2
              exact ⟨leBytes 4 kvs.length ++ b', by rw [h2, hb1]; simp, kvs, b', rfl, rfl, hz', h1,
                (strictAsc_iff _).1 hsa, hb3⟩
            · rintro ⟨b, rfl, kvs2, b2, rfl, rfl, _, h3, _, h4⟩
              obtain ⟨h5, h6⟩ := prefix_unique h3 h1 h2
              subst h5
              have := (dm kvs2 r).2 ⟨b2, h6, rfl, h4⟩
              rw [hd] at this
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj this)
              exact ⟨rfl, rfl⟩
          · simp only [KeyPolicy.strict, hsa, Bool.false_eq_true, ↓reduceIte, Option.map_none,
              reduceCtorEq, false_iff]
            rintro ⟨b, rfl, kvs2, b2, rfl, rfl, _, h3, h5, h4⟩
            obtain ⟨h6, h7⟩ := prefix_unique h3 h1 h2
            subst h6
            have := (dm kvs2 r).2 ⟨b2, h7, rfl, h4⟩
            rw [hd] at this
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj this)
            exact hsa ((strictAsc_iff _).2 h5)
  | .set s => by
    intro v B r
    have ih := decode_iff s
    simp only [Schema.decodeWith, enc_set]
    by_cases hz : s.zeroSized = true
    · simp only [hz, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨b, _, xs, b', _, _, h, _⟩
      exact h ((zeroSized_iff s).1 hz)
    · have hz' : ¬ SizeZero s := fun h => hz ((zeroSized_iff s).2 h)
      simp only [hz, Bool.false_eq_true, ↓reduceIte]
      cases hr : Schema.readU32 B with
      | none =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨b, rfl, xs, b', rfl, rfl, _, h1, _⟩
        have := (readU32_iff (leBytes 4 xs.length ++ b' ++ r) xs.length (b' ++ r)).2
          ⟨h1, by simp⟩
        rw [hr] at this
        exact absurd this (by simp)
      | some p =>
        obtain ⟨n, r0⟩ := p
        obtain ⟨h1, h2⟩ := (readU32_iff _ _ _).1 hr
        have dm := decodeMany_iff0 (fun b => Schema.decodeWith KeyPolicy.strict s b) (Encodes s)
          (EncodesAll s) ih (all_nil s) (all_cons s) n r0
        simp only []
        cases hd : Schema.decodeMany (fun b => Schema.decodeWith KeyPolicy.strict s b) n [] r0 with
        | none =>
          simp only [reduceCtorEq, false_iff]
          rintro ⟨b, rfl, xs, b', rfl, rfl, _, h3, _, h4⟩
          obtain ⟨h5, h6⟩ := prefix_unique h3 h1 h2
          subst h5
          have := (dm xs r).2 ⟨b', h6, rfl, h4⟩
          rw [hd] at this
          exact absurd this (by simp)
        | some q =>
          obtain ⟨xs, r'⟩ := q
          obtain ⟨b', hb1, hb2, hb3⟩ := (dm xs r').1 hd
          by_cases hsa : Value.strictAsc xs = true
          · simp only [KeyPolicy.strict, hsa, ↓reduceIte, Option.map_some, Option.some.injEq,
              Prod.mk.injEq]
            constructor
            · rintro ⟨rfl, rfl⟩
              subst hb2
              exact ⟨leBytes 4 xs.length ++ b', by rw [h2, hb1]; simp, xs, b', rfl, rfl, hz', h1,
                (strictAsc_iff xs).1 hsa, hb3⟩
            · rintro ⟨b, rfl, xs2, b2, rfl, rfl, _, h3, _, h4⟩
              obtain ⟨h5, h6⟩ := prefix_unique h3 h1 h2
              subst h5
              have := (dm xs2 r).2 ⟨b2, h6, rfl, h4⟩
              rw [hd] at this
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj this)
              exact ⟨rfl, rfl⟩
          · simp only [KeyPolicy.strict, hsa, Bool.false_eq_true, ↓reduceIte, Option.map_none,
              reduceCtorEq, false_iff]
            rintro ⟨b, rfl, xs2, b2, rfl, rfl, _, h3, h5, h4⟩
            obtain ⟨h6, h7⟩ := prefix_unique h3 h1 h2
            subst h6
            have := (dm xs2 r).2 ⟨b2, h7, rfl, h4⟩
            rw [hd] at this
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj this)
            exact hsa ((strictAsc_iff xs).2 h5)

theorem fields_dec_iff : (fs : List Schema) → ∀ (vs : List Value) (B r : List UInt8),
    (Schema.decodeFieldsWith KeyPolicy.strict fs B = some (vs, r) ↔
      ∃ b, B = b ++ r ∧ EncodesFields fs vs b)
  | [] => by
    intro vs B r
    simp only [Schema.decodeFieldsWith, fields_nil, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨[], by simp, rfl, rfl⟩
    · rintro ⟨b, h, rfl, rfl⟩
      exact ⟨rfl, by simpa using h⟩
  | s :: fs => by
    intro vs B r
    have ih := decode_iff s
    have ih' := fields_dec_iff fs
    simp only [Schema.decodeFieldsWith, fields_cons]
    cases h1 : Schema.decodeWith KeyPolicy.strict s B with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨b, rfl, x, xs, b1, bs', rfl, rfl, h2, _⟩
      have := (ih x (b1 ++ bs' ++ r) (bs' ++ r)).2 ⟨b1, by simp, h2⟩
      rw [h1] at this
      exact absurd this (by simp)
    | some q =>
      obtain ⟨x, r1⟩ := q
      cases h2 : Schema.decodeFieldsWith KeyPolicy.strict fs r1 with
      | none =>
        simp only [h2, reduceCtorEq, false_iff]
        rintro ⟨b, rfl, x', xs, b1, bs', rfl, rfl, h3, h4⟩
        have e1 := (ih x' (b1 ++ bs' ++ r) (bs' ++ r)).2 ⟨b1, by simp, h3⟩
        rw [h1] at e1
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
        have e2 := (ih' xs (bs' ++ r) r).2 ⟨bs', rfl, h4⟩
        rw [h2] at e2
        exact absurd e2 (by simp)
      | some q' =>
        obtain ⟨xs, r2⟩ := q'
        simp only [h2, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          obtain ⟨b1, hb1, hb2⟩ := (ih x B r1).1 h1
          obtain ⟨bs', hb3, hb4⟩ := (ih' xs r1 r2).1 h2
          exact ⟨b1 ++ bs', by rw [hb1, hb3]; simp, x, xs, b1, bs', rfl, rfl, hb2, hb4⟩
        · rintro ⟨b, rfl, x', xs', b1, bs', ⟨rfl, rfl⟩, rfl, h3, h4⟩
          have e1 := (ih x' (b1 ++ bs' ++ r) (bs' ++ r)).2 ⟨b1, by simp, h3⟩
          rw [h1] at e1
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
          have e2 := (ih' xs' (bs' ++ r) r).2 ⟨bs', rfl, h4⟩
          rw [h2] at e2
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e2)
          exact ⟨rfl, rfl⟩

theorem variant_dec_iff : (vs : List (UInt8 × Schema)) → ∀ (i : Nat) (t : UInt8)
    (B : List UInt8) (v : Value) (r : List UInt8),
    (Schema.decodeVariantWith KeyPolicy.strict vs i t B = some (v, r) ↔
      ∃ j s x b, v = .enum (i + j) x ∧ VariantAt vs j t s ∧ B = b ++ r ∧ Encodes s x b)
  | [] => by
    intro i t B v r
    simp only [Schema.decodeVariantWith, reduceCtorEq, false_iff]
    rintro ⟨j, s, x, b, _, h, _⟩
    exact variantAt_nil _ _ _ h
  | (t', s) :: vs => by
    intro i t B v r
    have ih := decode_iff s
    have ih' := variant_dec_iff vs
    simp only [Schema.decodeVariantWith]
    by_cases ht : t' = t
    · subst ht
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [map_pair_iff]
      constructor
      · rintro ⟨x, h, rfl⟩
        obtain ⟨b, h1, h2⟩ := (ih x B r).1 h
        exact ⟨0, s, x, b, rfl, (variantAt_zero _ _ _ _ _).2 ⟨rfl, rfl⟩, h1, h2⟩
      · rintro ⟨j, s', x, b, rfl, hv, h1, h2⟩
        cases j with
        | zero =>
          obtain ⟨_, rfl⟩ := (variantAt_zero _ _ _ _ _).1 hv
          exact ⟨x, (ih x B r).2 ⟨b, h1, h2⟩, rfl⟩
        | succ j =>
          exact absurd rfl ((variantAt_succ _ _ _ _ _ _).1 hv).1
    · have hb : (t' == t) = false := by simpa using ht
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rw [ih']
      constructor
      · rintro ⟨j, s', x, b, rfl, hv, h1, h2⟩
        exact ⟨j + 1, s', x, b, by congr 1; omega, (variantAt_succ _ _ _ _ _ _).2 ⟨ht, hv⟩, h1, h2⟩
      · rintro ⟨j, s', x, b, rfl, hv, h1, h2⟩
        cases j with
        | zero =>
          exact absurd (((variantAt_zero _ _ _ _ _).1 hv).1.symm) ht
        | succ j =>
          obtain ⟨_, hv'⟩ := (variantAt_succ _ _ _ _ _ _).1 hv
          exact ⟨j, s', x, b, by congr 1; omega, hv', h1, h2⟩

end

end GrammarProof

end BorshSpec
