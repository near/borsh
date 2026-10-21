import BorshSpec

/-!
# Decoding never reads past the input, and reads a byte unless the schema is zero-sized

Helper lemmas for `Theorems/Resources.lean`.  The statements are about the
unread rest `r` of a successful decode:

* `r` is no longer than the input;
* if the schema is not zero-sized, `r` is strictly shorter.

They are stated for every key policy, since the policy only rearranges the keys it
is given and never touches the unread input.
-/

namespace BorshSpec

/-- `takeExact` removes exactly `n` bytes. -/
theorem ResLemmas.takeExact_length {n : Nat} {bs a r : List UInt8} (h : takeExact n bs = some (a, r)) :
    r.length + n = bs.length := by
  unfold takeExact at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rename_i hl
    simp only [List.length_take] at hl
    simp only [List.length_drop]
    omega
  · simp at h

/-- `takeExact` returns exactly `n` bytes. -/
theorem ResLemmas.takeExact_fst_length {n : Nat} {bs a r : List UInt8} (h : takeExact n bs = some (a, r)) :
    a.length = n := by
  unfold takeExact at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    assumption
  · simp at h

/-- `readLE w` removes exactly `w` bytes. -/
theorem ResLemmas.readLE_length {w : Nat} {bs r : List UInt8} {n : Nat} (h : readLE w bs = some (n, r)) :
    r.length + w = bs.length := by
  unfold readLE at h
  cases ht : takeExact w bs with
  | none => simp [ht] at h
  | some p =>
    obtain ⟨a, r'⟩ := p
    simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ResLemmas.takeExact_length ht

/-- Every integer width occupies at least one byte. -/
theorem ResLemmas.bytes_pos (w : IntWidth) : 0 < w.bytes := by cases w <;> decide

namespace Schema

/-- A loop whose body never reads past its input never reads past its input. -/
theorem ResLemmas.decodeMany_le {α : Type} (d : List UInt8 → Option (α × List UInt8))
    (hd : ∀ b x r, d b = some (x, r) → r.length ≤ b.length) :
    ∀ (m : Nat) (acc : List α) (bs : List UInt8) (xs : List α) (r : List UInt8),
      decodeMany d m acc bs = some (xs, r) → r.length ≤ bs.length
  | 0, acc, bs, xs, r, h => by
    simp only [decodeMany, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  | m + 1, acc, bs, xs, r, h => by
    simp only [decodeMany] at h
    cases hb : d bs with
    | none => simp [hb] at h
    | some p =>
      obtain ⟨x, r₁⟩ := p
      simp only [hb] at h
      have := ResLemmas.decodeMany_le d hd m (x :: acc) r₁ xs r h
      have := hd bs x r₁ hb
      omega

/-- A loop of at least one iteration whose body always reads a byte, reads a byte. -/
theorem ResLemmas.decodeMany_lt {α : Type} (d : List UInt8 → Option (α × List UInt8))
    (hd : ∀ b x r, d b = some (x, r) → r.length < b.length) :
    ∀ (m : Nat) (acc : List α) (bs : List UInt8) (xs : List α) (r : List UInt8),
      0 < m → decodeMany d m acc bs = some (xs, r) → r.length < bs.length
  | 0, _, _, _, _, hm, _ => by omega
  | m + 1, acc, bs, xs, r, _, h => by
    simp only [decodeMany] at h
    cases hb : d bs with
    | none => simp [hb] at h
    | some p =>
      obtain ⟨x, r₁⟩ := p
      simp only [hb] at h
      have := ResLemmas.decodeMany_le d (fun b x r h => Nat.le_of_lt (hd b x r h)) m (x :: acc) r₁ xs r h
      have := hd bs x r₁ hb
      omega

mutual

/-- A successful decode leaves no more than it was given, and strictly less when the
schema is not zero-sized. -/
theorem ResLemmas.decodeWith_length (P : KeyPolicy) :
    ∀ (s : Schema) (bs : List UInt8) (v : Value) (r : List UInt8),
      decodeWith P s bs = some (v, r) →
        r.length ≤ bs.length ∧ (s.zeroSized = false → r.length < bs.length)
  | .uint w, bs, v, r, h => by
    simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨n, r'⟩, hr, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨-, rfl⟩ := hv
    have := ResLemmas.readLE_length hr
    have := ResLemmas.bytes_pos w
    simp only [zeroSized]
    omega
  | .sint w, bs, v, r, h => by
    simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨n, r'⟩, hr, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨-, rfl⟩ := hv
    have := ResLemmas.readLE_length hr
    have := ResLemmas.bytes_pos w
    simp only [zeroSized]
    omega
  | .f32, bs, v, r, h => by
    simp only [decodeWith] at h
    cases hr : readLE 4 bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨n, r'⟩ := p
      simp only [hr] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := ResLemmas.readLE_length hr
        simp only [zeroSized]
        omega
  | .f64, bs, v, r, h => by
    simp only [decodeWith] at h
    cases hr : readLE 8 bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨n, r'⟩ := p
      simp only [hr] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := ResLemmas.readLE_length hr
        simp only [zeroSized]
        omega
  | .bool, bs, v, r, h => by
    simp only [decodeWith] at h
    cases bs with
    | nil => simp at h
    | cons b r' =>
      simp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp [zeroSized]
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          simp [zeroSized]
        · simp at h
  | .string, bs, v, r, h => by
    simp only [decodeWith] at h
    cases hr : readU32 bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨n, r₁⟩ := p
      simp only [hr] at h
      cases hk : takeExact n r₁ with
      | none => simp [hk] at h
      | some q =>
        obtain ⟨body, r₂⟩ := q
        simp only [hk] at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have h1 : r₁.length + 4 = bs.length := ResLemmas.readLE_length hr
          have h2 := ResLemmas.takeExact_length hk
          simp only [zeroSized]
          omega
        · simp at h
  | .option s, bs, v, r, h => by
    simp only [decodeWith] at h
    cases bs with
    | nil => simp at h
    | cons b r' =>
      simp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp [zeroSized]
      · split at h
        · rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨v', r''⟩, hd, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨-, rfl⟩ := hv
          have := (ResLemmas.decodeWith_length P s r' v' r'' hd).1
          simp only [zeroSized, List.length_cons]
          omega
        · simp at h
  | .vec s, bs, v, r, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · cases hr : readU32 bs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨n, r₁⟩ := p
        simp only [hr] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨xs, r₂⟩, hm, hv⟩ := h
        simp only [Prod.mk.injEq] at hv
        obtain ⟨-, rfl⟩ := hv
        have h1 : r₁.length + 4 = bs.length := ResLemmas.readLE_length hr
        have h2 := ResLemmas.decodeMany_le (fun b => decodeWith P s b)
          (fun b x r h => (ResLemmas.decodeWith_length P s b x r h).1) n [] r₁ xs r₂ hm
        simp only [zeroSized]
        omega
  | .array n s, bs, v, r, h => by
    simp only [decodeWith] at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨xs, r₂⟩, hm, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨-, rfl⟩ := hv
    have h2 := ResLemmas.decodeMany_le (fun b => decodeWith P s b)
      (fun b x r h => (ResLemmas.decodeWith_length P s b x r h).1) n [] bs xs r₂ hm
    refine ⟨h2, fun hz => ?_⟩
    simp only [zeroSized, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hz
    exact ResLemmas.decodeMany_lt (fun b => decodeWith P s b)
      (fun b x r h => (ResLemmas.decodeWith_length P s b x r h).2 hz.2) n [] bs xs r₂ (by omega) hm
  | .tuple fs, bs, v, r, h => by
    simp only [decodeWith] at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨xs, r₂⟩, hm, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨-, rfl⟩ := hv
    simpa only [zeroSized] using ResLemmas.decodeFieldsWith_length P fs bs xs r₂ hm
  | .enum vs, bs, v, r, h => by
    simp only [decodeWith] at h
    cases bs with
    | nil => simp at h
    | cons t r' =>
      simp only at h
      have := ResLemmas.decodeVariantWith_length P vs 0 t r' v r h
      simp only [zeroSized, List.length_cons]
      omega
  | .map k w, bs, v, r, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · cases hr : readU32 bs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨n, r₁⟩ := p
        simp only [hr] at h
        cases hm : decodeMany
            (fun b => match decodeWith P k b with
              | none => none
              | some (a, r₁) =>
                match decodeWith P w r₁ with
                | none => none
                | some (c, r₂) => some ((a, c), r₂)) n [] r₁ with
        | none => erw [hm] at h; simp at h
        | some q =>
          obtain ⟨kvs, r₂⟩ := q
          erw [hm] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨kvs', -, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨-, rfl⟩ := hv
          have h1 : r₁.length + 4 = bs.length := ResLemmas.readLE_length hr
          have h2 := ResLemmas.decodeMany_le
            (fun b => match decodeWith P k b with
              | none => none
              | some (a, r₁) =>
                match decodeWith P w r₁ with
                | none => none
                | some (c, r₂) => some ((a, c), r₂))
            (fun b x r h => by
              cases ha : decodeWith P k b with
              | none => simp [ha] at h
              | some q =>
                obtain ⟨a, r'⟩ := q
                simp only [ha] at h
                cases hb : decodeWith P w r' with
                | none => simp [hb] at h
                | some q2 =>
                  obtain ⟨c, r''⟩ := q2
                  simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  have := (ResLemmas.decodeWith_length P k b a r' ha).1
                  have := (ResLemmas.decodeWith_length P w r' c r'' hb).1
                  omega)
            n [] r₁ kvs r₂ hm
          simp only [zeroSized]
          omega
  | .set s, bs, v, r, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · cases hr : readU32 bs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨n, r₁⟩ := p
        simp only [hr] at h
        cases hm : decodeMany (fun b => decodeWith P s b) n [] r₁ with
        | none => erw [hm] at h; simp at h
        | some q =>
          obtain ⟨xs, r₂⟩ := q
          erw [hm] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨xs', -, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨-, rfl⟩ := hv
          have h1 : r₁.length + 4 = bs.length := ResLemmas.readLE_length hr
          have h2 := ResLemmas.decodeMany_le (fun b => decodeWith P s b)
            (fun b x r h => (ResLemmas.decodeWith_length P s b x r h).1) n [] r₁ xs r₂ hm
          simp only [zeroSized]
          omega

/-- The tuple-field version of `ResLemmas.decodeWith_length`. -/
theorem ResLemmas.decodeFieldsWith_length (P : KeyPolicy) :
    ∀ (fs : List Schema) (bs : List UInt8) (vs : List Value) (r : List UInt8),
      decodeFieldsWith P fs bs = some (vs, r) →
        r.length ≤ bs.length ∧ (zeroSizedAll fs = false → r.length < bs.length)
  | [], bs, vs, r, h => by
    simp only [decodeFieldsWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [zeroSizedAll]
  | s :: fs, bs, vs, r, h => by
    simp only [decodeFieldsWith] at h
    cases h1 : decodeWith P s bs with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨v, r₁⟩ := p
      simp only [h1] at h
      cases h2 : decodeFieldsWith P fs r₁ with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨vs', r₂⟩ := q
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have a1 := ResLemmas.decodeWith_length P s bs v r₁ h1
        have a2 := ResLemmas.decodeFieldsWith_length P fs r₁ vs' r₂ h2
        refine ⟨by omega, fun hz => ?_⟩
        simp only [zeroSizedAll, Bool.and_eq_false_iff] at hz
        rcases hz with hz | hz
        · have := a1.2 hz
          omega
        · have := a2.2 hz
          omega

/-- The enum-variant version of `ResLemmas.decodeWith_length`: the payload decode never
reads past its input (the tag byte is accounted for by the caller). -/
theorem ResLemmas.decodeVariantWith_length (P : KeyPolicy) :
    ∀ (vs : List (UInt8 × Schema)) (i : Nat) (t : UInt8) (bs : List UInt8) (v : Value)
      (r : List UInt8), decodeVariantWith P vs i t bs = some (v, r) → r.length ≤ bs.length
  | [], i, t, bs, v, r, h => by simp [decodeVariantWith] at h
  | (t', s) :: vs, i, t, bs, v, r, h => by
    simp only [decodeVariantWith] at h
    split at h
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨v', r'⟩, hd, hv⟩ := h
      simp only [Prod.mk.injEq] at hv
      obtain ⟨-, rfl⟩ := hv
      exact (ResLemmas.decodeWith_length P s bs v' r' hd).1
    · exact ResLemmas.decodeVariantWith_length P vs (i + 1) t bs v r h

end

end Schema

end BorshSpec
