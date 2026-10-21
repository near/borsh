import BorshSpec

/-!
# The instrumented decoder agrees with the decoder

Helper lemmas for `Theorems/Resources.lean`: the first component of `decodeC` is
`decode`.  The loops (`decodeManyC`), the tuple fields and the enum variants are
related one by one.
-/

namespace BorshSpec

namespace Schema

/-- The counted loop computes the same result as `decodeMany`. -/
theorem decodeManyC_fst {α : Type} (d' : List UInt8 → Counted (α × List UInt8))
    (d : List UInt8 → Option (α × List UInt8)) (h : ∀ b, (d' b).1 = d b) :
    ∀ (m : Nat) (acc : List α) (bs : List UInt8) (steps : Nat),
      (decodeManyC d' m acc bs steps).1 = decodeMany d m acc bs
  | 0, _, _, _ => by simp [decodeManyC, decodeMany]
  | m + 1, acc, bs, steps => by
    simp only [decodeManyC, decodeMany]
    rcases hd : d' bs with ⟨res, k⟩
    have h1 : res = d bs := by simpa [hd] using h bs
    cases res with
    | none => simp [← h1]
    | some p =>
      obtain ⟨x, r⟩ := p
      rw [← h1]
      exact decodeManyC_fst d' d h m (x :: acc) r (steps + k)

/-- The counted order check computes the same result as `Value.strictAsc`. -/
theorem strictAscC_fst : ∀ xs : List Value, (Value.strictAscC xs).1 = Value.strictAsc xs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp only [Value.strictAscC, Value.strictAsc]
    by_cases h : Value.cmp a b == .lt
    · simp [h, strictAscC_fst (b :: rest)]
    · simp [h]

mutual

/-- The first component of `decodeC` is `decode`. -/
theorem decodeC_fst : ∀ (s : Schema) (bs : List UInt8), (s.decodeC bs).1 = decode s bs
  | .uint w, bs => by simp [decodeC, decode, decodeWith]
  | .sint w, bs => by simp [decodeC, decode, decodeWith]
  | .f32, bs => by
    simp only [decodeC, decode, decodeWith]
    cases readLE 4 bs with
    | none => rfl
    | some p => obtain ⟨n, r⟩ := p; simp only
  | .f64, bs => by
    simp only [decodeC, decode, decodeWith]
    cases readLE 8 bs with
    | none => rfl
    | some p => obtain ⟨n, r⟩ := p; simp only
  | .bool, bs => by
    simp only [decodeC, decode, decodeWith]
    cases bs with
    | nil => rfl
    | cons b r => simp only
  | .string, bs => by
    simp only [decodeC, decode, decodeWith]
    cases readU32 bs with
    | none => rfl
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only
      cases takeExact n r with
      | none => rfl
      | some q => obtain ⟨body, r'⟩ := q; simp only
  | .option s, bs => by
    simp only [decodeC, decode, decodeWith]
    cases bs with
    | nil => rfl
    | cons b r =>
      simp only
      split
      · rfl
      · split
        · have := decodeC_fst s r
          rcases hd : decodeC s r with ⟨res, k⟩
          rw [hd] at this
          simp only at this
          simp only [this, decode]
        · rfl
  | .vec s, bs => by
    simp only [decodeC, decode, decodeWith]
    split
    · rfl
    · cases readU32 bs with
      | none => rfl
      | some p =>
        obtain ⟨n, r⟩ := p
        simp only
        have := decodeManyC_fst (fun b => decodeC s b) (fun b => decodeWith KeyPolicy.strict s b)
          (fun b => decodeC_fst s b) n [] r 0
        rcases hd : decodeManyC (fun b => decodeC s b) n [] r 0 with ⟨res, k⟩
        rw [hd] at this
        simp only at this
        simp only [this]
  | .array n s, bs => by
    simp only [decodeC, decode, decodeWith]
    have := decodeManyC_fst (fun b => decodeC s b) (fun b => decodeWith KeyPolicy.strict s b)
      (fun b => decodeC_fst s b) n [] bs 0
    rcases hd : decodeManyC (fun b => decodeC s b) n [] bs 0 with ⟨res, k⟩
    rw [hd] at this
    simp only at this
    simp only [this]
  | .tuple fs, bs => by
    simp only [decodeC, decode, decodeWith]
    have := decodeFieldsC_fst fs bs
    rcases hd : decodeFieldsC fs bs with ⟨res, k⟩
    rw [hd] at this
    simp only at this
    simp only [this]
  | .enum vs, bs => by
    simp only [decodeC, decode, decodeWith]
    cases bs with
    | nil => rfl
    | cons t r =>
      simp only
      have := decodeVariantC_fst vs 0 t r
      rcases hd : decodeVariantC vs 0 t r with ⟨res, k⟩
      rw [hd] at this
      simp only at this
      exact this
  | .map k v, bs => by
    simp only [decodeC, decode, decodeWith]
    split
    · rfl
    · cases readU32 bs with
      | none => rfl
      | some p =>
        obtain ⟨n, r⟩ := p
        simp only
        have hpair := decodeManyC_fst
          (fun b => match decodeC k b with
            | (none, c₁) => (none, c₁)
            | (some (a, r₁), c₁) =>
              match decodeC v r₁ with
              | (none, c₂) => (none, c₁ + c₂)
              | (some (c, r₂), c₂) => (some ((a, c), r₂), c₁ + c₂))
          (fun b => match decodeWith KeyPolicy.strict k b with
            | none => none
            | some (a, r₁) =>
              match decodeWith KeyPolicy.strict v r₁ with
              | none => none
              | some (c, r₂) => some ((a, c), r₂))
          (fun b => by
            have h1 := decodeC_fst k b
            rcases hd : decodeC k b with ⟨res, c₁⟩
            rw [hd] at h1
            replace h1 : res = decodeWith KeyPolicy.strict k b := h1
            cases res with
            | none => simp [← h1]
            | some q =>
              obtain ⟨a, r₁⟩ := q
              have h2 := decodeC_fst v r₁
              rcases hd2 : decodeC v r₁ with ⟨res2, c₂⟩
              rw [hd2] at h2
              replace h2 : res2 = decodeWith KeyPolicy.strict v r₁ := h2
              cases res2 with
              | none => simp [← h1, ← h2, hd2]
              | some q2 => obtain ⟨c, r₂⟩ := q2; simp [← h1, ← h2, hd2])
          n [] r 0
        rcases hd : decodeManyC
          (fun b => match decodeC k b with
            | (none, c₁) => (none, c₁)
            | (some (a, r₁), c₁) =>
              match decodeC v r₁ with
              | (none, c₂) => (none, c₁ + c₂)
              | (some (c, r₂), c₂) => (some ((a, c), r₂), c₁ + c₂)) n [] r 0 with ⟨res, c⟩
        rw [hd] at hpair
        replace hpair : res = _ := hpair
        cases res with
        | none => erw [← hpair]
        | some q =>
          obtain ⟨kvs, r'⟩ := q
          have := strictAscC_fst (kvs.map Prod.fst)
          rcases ha : Value.strictAscC (kvs.map Prod.fst) with ⟨ok, c'⟩
          rw [ha] at this
          replace this : ok = Value.strictAsc (kvs.map Prod.fst) := this
          erw [← hpair]
          simp [KeyPolicy.strict, ← this, ha]
  | .set s, bs => by
    simp only [decodeC, decode, decodeWith]
    split
    · rfl
    · cases readU32 bs with
      | none => rfl
      | some p =>
        obtain ⟨n, r⟩ := p
        simp only
        have hmany := decodeManyC_fst (fun b => decodeC s b)
          (fun b => decodeWith KeyPolicy.strict s b) (fun b => decodeC_fst s b) n [] r 0
        rcases hd : decodeManyC (fun b => decodeC s b) n [] r 0 with ⟨res, c⟩
        rw [hd] at hmany
        replace hmany : res = _ := hmany
        cases res with
        | none => erw [← hmany]
        | some q =>
          obtain ⟨xs, r'⟩ := q
          have := strictAscC_fst xs
          rcases ha : Value.strictAscC xs with ⟨ok, c'⟩
          rw [ha] at this
          replace this : ok = Value.strictAsc xs := this
          erw [← hmany]
          simp [KeyPolicy.strict, ← this, ha]

/-- The first component of `decodeFieldsC` is `decodeFieldsWith`. -/
theorem decodeFieldsC_fst : ∀ (fs : List Schema) (bs : List UInt8),
    (decodeFieldsC fs bs).1 = decodeFieldsWith KeyPolicy.strict fs bs
  | [], bs => by simp [decodeFieldsC, decodeFieldsWith]
  | s :: fs, bs => by
    simp only [decodeFieldsC, decodeFieldsWith]
    have h1 := decodeC_fst s bs
    rcases hd : decodeC s bs with ⟨res, k⟩
    rw [hd] at h1
    replace h1 : res = decodeWith KeyPolicy.strict s bs := h1
    cases res with
    | none => simp [← h1]
    | some p =>
      obtain ⟨v, r⟩ := p
      rw [← h1]
      have h2 := decodeFieldsC_fst fs r
      rcases hd2 : decodeFieldsC fs r with ⟨res2, k2⟩
      rw [hd2] at h2
      replace h2 : res2 = decodeFieldsWith KeyPolicy.strict fs r := h2
      cases res2 with
      | none => simp [← h2, hd2]
      | some q => obtain ⟨vs, r'⟩ := q; simp [← h2, hd2]

/-- The first component of `decodeVariantC` is `decodeVariantWith`. -/
theorem decodeVariantC_fst : ∀ (vs : List (UInt8 × Schema)) (i : Nat) (t : UInt8)
    (bs : List UInt8), (decodeVariantC vs i t bs).1 = decodeVariantWith KeyPolicy.strict vs i t bs
  | [], _, _, _ => by simp [decodeVariantC, decodeVariantWith]
  | (t', s) :: vs, i, t, bs => by
    simp only [decodeVariantC, decodeVariantWith]
    by_cases h : t' == t
    · simp only [h, ite_true]
      have h1 := decodeC_fst s bs
      rcases hd : decodeC s bs with ⟨res, k⟩
      rw [hd] at h1
      simp only at h1
      simp [h1, decode]
    · simp only [h]
      have := decodeVariantC_fst vs (i + 1) t bs
      rcases hd : decodeVariantC vs (i + 1) t bs with ⟨res, k⟩
      rw [hd] at this
      simpa using this

end

end Schema

end BorshSpec
