import BorshSpec

/-!
# Helper lemmas: the UTF-8 validator against the Table 3-7 grammar

Both directions of `validUtf8_iff`, proved here so that `Theorems/Grammar.lean` states
the result without the case analysis.
-/

namespace BorshSpec

namespace GrammarProof

theorem inRange_iff (lo hi b : UInt8) : inRange lo hi b = true ↔ InRange lo hi b := by
  simp [inRange, InRange]

theorem isCont_iff (b : UInt8) : isCont b = true ↔ InRange 0x80 0xBF b := by
  simp [isCont, inRange_iff]

theorem inRange_toNat (lo hi b : UInt8) :
    InRange lo hi b ↔ lo.toNat ≤ b.toNat ∧ b.toNat ≤ hi.toNat := by
  simp [InRange, UInt8.le_iff_toNat_le]

theorem inRange_mono {lo hi lo' hi' b : UInt8} (h1 : lo' ≤ lo) (h2 : hi ≤ hi')
    (h : InRange lo hi b) : InRange lo' hi' b :=
  ⟨UInt8.le_trans h1 h.1, UInt8.le_trans h.2 h2⟩

theorem inRange_of_beq {c b : UInt8} (h : (b == c) = true) : InRange c c b := by
  have := eq_of_beq h
  subst this
  exact ⟨UInt8.le_refl _, UInt8.le_refl _⟩

/-- One unfolding step of the validator. -/
theorem validUtf8_cons (b0 : UInt8) (rest : List UInt8) : validUtf8 (b0 :: rest) =
    (if b0 ≤ 0x7F then validUtf8 rest
    else if inRange 0xC2 0xDF b0 then
      match rest with
      | b1 :: r => isCont b1 && validUtf8 r
      | _ => false
    else if b0 == 0xE0 then
      match rest with
      | b1 :: b2 :: r => inRange 0xA0 0xBF b1 && isCont b2 && validUtf8 r
      | _ => false
    else if inRange 0xE1 0xEC b0 || b0 == 0xEE || b0 == 0xEF then
      match rest with
      | b1 :: b2 :: r => isCont b1 && isCont b2 && validUtf8 r
      | _ => false
    else if b0 == 0xED then
      match rest with
      | b1 :: b2 :: r => inRange 0x80 0x9F b1 && isCont b2 && validUtf8 r
      | _ => false
    else if b0 == 0xF0 then
      match rest with
      | b1 :: b2 :: b3 :: r => inRange 0x90 0xBF b1 && isCont b2 && isCont b3 && validUtf8 r
      | _ => false
    else if inRange 0xF1 0xF3 b0 then
      match rest with
      | b1 :: b2 :: b3 :: r => isCont b1 && isCont b2 && isCont b3 && validUtf8 r
      | _ => false
    else if b0 == 0xF4 then
      match rest with
      | b1 :: b2 :: b3 :: r => inRange 0x80 0x8F b1 && isCont b2 && isCont b3 && validUtf8 r
      | _ => false
    else false) := by
  conv => lhs; rw [validUtf8.eq_def]
  rfl

theorem wf_of_validUtf8 : ∀ (n : Nat) (bs : List UInt8), bs.length ≤ n →
    validUtf8 bs = true → WellFormedUtf8 bs
  | _, [], _, _ => .nil
  | 0, _ :: _, hl, _ => by simp at hl
  | n + 1, b0 :: rest, hl, h => by
    have hl' : rest.length ≤ n := by simp at hl; omega
    rw [validUtf8_cons] at h
    by_cases c1 : b0 ≤ 0x7F
    · simp only [c1, ↓reduceIte] at h
      exact .row1 b0 rest ⟨by simp [UInt8.le_iff_toNat_le], c1⟩ (wf_of_validUtf8 n rest hl' h)
    simp only [c1, ↓reduceIte] at h
    by_cases c2 : inRange 0xC2 0xDF b0 = true
    · simp only [c2, ↓reduceIte] at h
      rcases rest with _ | ⟨b1, r⟩
      · simp at h
      · simp only [Bool.and_eq_true] at h
        exact .row2 b0 b1 r ((inRange_iff ..).1 c2) ((isCont_iff _).1 h.1)
          (wf_of_validUtf8 n r (by simp at hl'; omega) h.2)
    simp only [c2, Bool.false_eq_true, ↓reduceIte] at h
    by_cases c3 : (b0 == 0xE0) = true
    · simp only [c3, ↓reduceIte] at h
      rcases rest with _ | ⟨b1, _ | ⟨b2, r⟩⟩
      · simp at h
      · simp at h
      · simp only [Bool.and_eq_true] at h
        exact .row3 b0 b1 b2 r (inRange_of_beq c3) ((inRange_iff ..).1 h.1.1)
          ((isCont_iff _).1 h.1.2) (wf_of_validUtf8 n r (by simp at hl'; omega) h.2)
    simp only [c3, Bool.false_eq_true, ↓reduceIte] at h
    by_cases c4 : (inRange 0xE1 0xEC b0 || b0 == 0xEE || b0 == 0xEF) = true
    · simp only [c4, ↓reduceIte] at h
      rcases rest with _ | ⟨b1, _ | ⟨b2, r⟩⟩
      · simp at h
      · simp at h
      · simp only [Bool.and_eq_true] at h
        have hr := wf_of_validUtf8 n r (by simp at hl'; omega) h.2
        simp only [Bool.or_eq_true] at c4
        rcases c4 with (hb | hb) | hb
        · exact .row4 b0 b1 b2 r ((inRange_iff ..).1 hb) ((isCont_iff _).1 h.1.1)
            ((isCont_iff _).1 h.1.2) hr
        · have := inRange_of_beq hb
          exact .row6 b0 b1 b2 r (inRange_mono (by decide) (by decide) this)
            ((isCont_iff _).1 h.1.1) ((isCont_iff _).1 h.1.2) hr
        · have := inRange_of_beq hb
          exact .row6 b0 b1 b2 r (inRange_mono (by decide) (by decide) this)
            ((isCont_iff _).1 h.1.1) ((isCont_iff _).1 h.1.2) hr
    simp only [c4, Bool.false_eq_true, ↓reduceIte] at h
    by_cases c5 : (b0 == 0xED) = true
    · simp only [c5, ↓reduceIte] at h
      rcases rest with _ | ⟨b1, _ | ⟨b2, r⟩⟩
      · simp at h
      · simp at h
      · simp only [Bool.and_eq_true] at h
        exact .row5 b0 b1 b2 r (inRange_of_beq c5) ((inRange_iff ..).1 h.1.1)
          ((isCont_iff _).1 h.1.2) (wf_of_validUtf8 n r (by simp at hl'; omega) h.2)
    simp only [c5, Bool.false_eq_true, ↓reduceIte] at h
    by_cases c6 : (b0 == 0xF0) = true
    · simp only [c6, ↓reduceIte] at h
      rcases rest with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩
      · simp at h
      · simp at h
      · simp at h
      · simp only [Bool.and_eq_true] at h
        exact .row7 b0 b1 b2 b3 r (inRange_of_beq c6) ((inRange_iff ..).1 h.1.1.1)
          ((isCont_iff _).1 h.1.1.2) ((isCont_iff _).1 h.1.2)
          (wf_of_validUtf8 n r (by simp at hl'; omega) h.2)
    simp only [c6, Bool.false_eq_true, ↓reduceIte] at h
    by_cases c7 : inRange 0xF1 0xF3 b0 = true
    · simp only [c7, ↓reduceIte] at h
      rcases rest with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩
      · simp at h
      · simp at h
      · simp at h
      · simp only [Bool.and_eq_true] at h
        exact .row8 b0 b1 b2 b3 r ((inRange_iff ..).1 c7) ((isCont_iff _).1 h.1.1.1)
          ((isCont_iff _).1 h.1.1.2) ((isCont_iff _).1 h.1.2)
          (wf_of_validUtf8 n r (by simp at hl'; omega) h.2)
    simp only [c7, Bool.false_eq_true, ↓reduceIte] at h
    by_cases c8 : (b0 == 0xF4) = true
    · simp only [c8, ↓reduceIte] at h
      rcases rest with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩
      · simp at h
      · simp at h
      · simp at h
      · simp only [Bool.and_eq_true] at h
        exact .row9 b0 b1 b2 b3 r (inRange_of_beq c8) ((inRange_iff ..).1 h.1.1.1)
          ((isCont_iff _).1 h.1.1.2) ((isCont_iff _).1 h.1.2)
          (wf_of_validUtf8 n r (by simp at hl'; omega) h.2)
    simp only [c8, Bool.false_eq_true, ↓reduceIte] at h

/-- The well-formed byte strings are accepted by the validator. -/
theorem validUtf8_of_wf {bs : List UInt8} (h : WellFormedUtf8 bs) : validUtf8 bs = true := by
  induction h with
  | nil => rfl
  | row1 b1 rest h1 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega
  | row2 b1 b2 rest h1 h2 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1 h2
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega
  | row3 b1 b2 b3 rest h1 h2 h3 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1 h2 h3
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega
  | row4 b1 b2 b3 rest h1 h2 h3 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1 h2 h3
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega
  | row5 b1 b2 b3 rest h1 h2 h3 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1 h2 h3
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega
  | row6 b1 b2 b3 rest h1 h2 h3 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1 h2 h3
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega
  | row7 b1 b2 b3 b4 rest h1 h2 h3 h4 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1 h2 h3 h4
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega
  | row8 b1 b2 b3 b4 rest h1 h2 h3 h4 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1 h2 h3 h4
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega
  | row9 b1 b2 b3 b4 rest h1 h2 h3 h4 _ ih =>
    rw [validUtf8_cons]
    simp [InRange, UInt8.le_iff_toNat_le] at h1 h2 h3 h4
    simp [inRange, isCont, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, ih]
    repeat' split
    all_goals omega

/-- The executable validator accepts exactly the grammar of Table 3-7. -/
theorem validUtf8_iff_wf (bs : List UInt8) : validUtf8 bs = true ↔ WellFormedUtf8 bs :=
  ⟨wf_of_validUtf8 bs.length bs (Nat.le_refl _), validUtf8_of_wf⟩

end GrammarProof

end BorshSpec
