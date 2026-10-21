import BorshSpec.Theorems.grammar.Utf8

/-!
# Helper lemmas: the UTF-8 validator against Lean's own

Lean's `ByteArray.validateUTF8` accepts exactly the byte arrays of the form
`List.utf8Encode m` for a list of characters `m`.  This module shows that the byte lists
of that form are exactly the ones that the Table 3-7 grammar accepts, which with
`validUtf8_iff_wf` gives `validUtf8_iff_validateUTF8`.
-/

namespace BorshSpec

namespace GrammarProof

theorem inRange_ofNat {lo hi : UInt8} {n : Nat} (h1 : lo.toNat ≤ n % 256)
    (h2 : n % 256 ≤ hi.toNat) : InRange lo hi (UInt8.ofNat n) := by
  rw [inRange_toNat]
  simpa using ⟨h1, h2⟩

/-- Every character encodes to a well-formed prefix. -/
theorem wf_encodeChar (c : Char) (rest : List UInt8) (h : WellFormedUtf8 rest) :
    WellFormedUtf8 (String.utf8EncodeChar c ++ rest) := by
  have hv := c.valid
  have hc : c.toNat = c.val.toNat := rfl
  simp only [UInt32.isValidChar, Nat.isValidChar] at hv
  unfold String.utf8EncodeChar
  by_cases h1 : c.val.toNat ≤ 0x7f
  · simp only [h1, ↓reduceIte, List.cons_append, List.nil_append]
    exact .row1 _ rest (inRange_ofNat (by simp) (by simp; omega)) h
  by_cases h2 : c.val.toNat ≤ 0x7ff
  · simp only [h1, h2, ↓reduceIte, List.cons_append, List.nil_append]
    exact .row2 _ _ rest (inRange_ofNat (by simp; omega) (by simp; omega))
      (inRange_ofNat (by simp; omega) (by simp; omega)) h
  by_cases h3 : c.val.toNat ≤ 0xffff
  · simp only [h1, h2, h3, ↓reduceIte, List.cons_append, List.nil_append]
    by_cases h4 : c.val.toNat < 0x1000
    · exact .row3 _ _ _ rest (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega)) h
    by_cases h5 : c.val.toNat < 0xD000
    · exact .row4 _ _ _ rest (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega)) h
    by_cases h6 : c.val.toNat < 0xD800
    · exact .row5 _ _ _ rest (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega)) h
    · exact .row6 _ _ _ rest (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega)) h
  · simp only [h1, h2, h3, ↓reduceIte, List.cons_append, List.nil_append]
    by_cases h4 : c.val.toNat < 0x40000
    · exact .row7 _ _ _ _ rest (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega)) h
    by_cases h5 : c.val.toNat < 0x100000
    · exact .row8 _ _ _ _ rest (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega)) h
    · exact .row9 _ _ _ _ rest (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega))
        (inRange_ofNat (by simp; omega) (by simp; omega)) h

theorem byte_eq {b : UInt8} {n : Nat} (h : n % 256 = b.toNat) : UInt8.ofNat n = b := by
  apply UInt8.toNat_inj.1
  simpa using h

/-- The character with scalar value `v`. -/
def mkChar (v : Nat) (hv : v.isValidChar) : Char :=
  ⟨UInt32.ofNat v, by
    have : v < 2 ^ 32 := by
      simp only [Nat.isValidChar] at hv
      omega
    show (UInt32.ofNat v).toNat.isValidChar
    rw [show (UInt32.ofNat v).toNat = v by simp [Nat.mod_eq_of_lt this]]
    exact hv⟩

theorem mkChar_toNat (v : Nat) (hv : v.isValidChar) : (mkChar v hv).val.toNat = v := by
  have : v < 2 ^ 32 := by
    simp only [Nat.isValidChar] at hv
    omega
  simp [mkChar, Nat.mod_eq_of_lt this]

theorem encode_mkChar (v : Nat) (hv : v.isValidChar) :
    String.utf8EncodeChar (mkChar v hv) =
      if v ≤ 0x7f then [UInt8.ofNat v]
      else if v ≤ 0x7ff then [UInt8.ofNat (v / 64 % 0x20 + 0xc0), UInt8.ofNat (v % 0x40 + 0x80)]
      else if v ≤ 0xffff then
        [UInt8.ofNat (v / 4096 % 0x10 + 0xe0), UInt8.ofNat (v / 64 % 0x40 + 0x80),
          UInt8.ofNat (v % 0x40 + 0x80)]
      else
        [UInt8.ofNat (v / 262144 % 0x08 + 0xf0), UInt8.ofNat (v / 4096 % 0x40 + 0x80),
          UInt8.ofNat (v / 64 % 0x40 + 0x80), UInt8.ofNat (v % 0x40 + 0x80)] := by
  unfold String.utf8EncodeChar
  simp only [mkChar_toNat]

/-- Every well-formed byte string is the encoding of a list of characters. -/
theorem exists_chars {bs : List UInt8} (h : WellFormedUtf8 bs) :
    ∃ m : List Char, bs = m.flatMap String.utf8EncodeChar := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | row1 b1 rest h1 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1
    simp at h1
    obtain ⟨v, hvd⟩ : ∃ v, v = b1.toNat := ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show v ≤ 0x7f by omega, ↓reduceIte, List.cons_append, List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩
  | row2 b1 b2 rest h1 h2 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1 h2
    simp at h1 h2
    obtain ⟨v, hvd⟩ : ∃ v, v = (b1.toNat - 192) * 64 + (b2.toNat - 128) := ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show ¬ v ≤ 0x7f by omega, show v ≤ 0x7ff by omega, ↓reduceIte, List.cons_append,
      List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩⟩
  | row3 b1 b2 b3 rest h1 h2 h3 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1 h2 h3
    simp at h1 h2 h3
    obtain ⟨v, hvd⟩ : ∃ v, v = (b1.toNat - 224) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128) :=
      ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show ¬ v ≤ 0x7f by omega, show ¬ v ≤ 0x7ff by omega, show v ≤ 0xffff by omega,
      ↓reduceIte, List.cons_append, List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩⟩⟩
  | row4 b1 b2 b3 rest h1 h2 h3 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1 h2 h3
    simp at h1 h2 h3
    obtain ⟨v, hvd⟩ : ∃ v, v = (b1.toNat - 224) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128) :=
      ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show ¬ v ≤ 0x7f by omega, show ¬ v ≤ 0x7ff by omega, show v ≤ 0xffff by omega,
      ↓reduceIte, List.cons_append, List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩⟩⟩
  | row5 b1 b2 b3 rest h1 h2 h3 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1 h2 h3
    simp at h1 h2 h3
    obtain ⟨v, hvd⟩ : ∃ v, v = (b1.toNat - 224) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128) :=
      ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show ¬ v ≤ 0x7f by omega, show ¬ v ≤ 0x7ff by omega, show v ≤ 0xffff by omega,
      ↓reduceIte, List.cons_append, List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩⟩⟩
  | row6 b1 b2 b3 rest h1 h2 h3 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1 h2 h3
    simp at h1 h2 h3
    obtain ⟨v, hvd⟩ : ∃ v, v = (b1.toNat - 224) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128) :=
      ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show ¬ v ≤ 0x7f by omega, show ¬ v ≤ 0x7ff by omega, show v ≤ 0xffff by omega,
      ↓reduceIte, List.cons_append, List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩⟩⟩
  | row7 b1 b2 b3 b4 rest h1 h2 h3 h4 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1 h2 h3 h4
    simp at h1 h2 h3 h4
    obtain ⟨v, hvd⟩ : ∃ v, v = (b1.toNat - 240) * 262144 + (b2.toNat - 128) * 4096 +
        (b3.toNat - 128) * 64 + (b4.toNat - 128) := ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show ¬ v ≤ 0x7f by omega, show ¬ v ≤ 0x7ff by omega, show ¬ v ≤ 0xffff by omega,
      ↓reduceIte, List.cons_append, List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩⟩⟩⟩
  | row8 b1 b2 b3 b4 rest h1 h2 h3 h4 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1 h2 h3 h4
    simp at h1 h2 h3 h4
    obtain ⟨v, hvd⟩ : ∃ v, v = (b1.toNat - 240) * 262144 + (b2.toNat - 128) * 4096 +
        (b3.toNat - 128) * 64 + (b4.toNat - 128) := ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show ¬ v ≤ 0x7f by omega, show ¬ v ≤ 0x7ff by omega, show ¬ v ≤ 0xffff by omega,
      ↓reduceIte, List.cons_append, List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩⟩⟩⟩
  | row9 b1 b2 b3 b4 rest h1 h2 h3 h4 _ ih =>
    obtain ⟨m, rfl⟩ := ih
    rw [inRange_toNat] at h1 h2 h3 h4
    simp at h1 h2 h3 h4
    obtain ⟨v, hvd⟩ : ∃ v, v = (b1.toNat - 240) * 262144 + (b2.toNat - 128) * 4096 +
        (b3.toNat - 128) * 64 + (b4.toNat - 128) := ⟨_, rfl⟩
    have hv : v.isValidChar := by simp only [Nat.isValidChar]; omega
    refine ⟨mkChar v hv :: m, ?_⟩
    rw [List.flatMap_cons, encode_mkChar]
    simp only [show ¬ v ≤ 0x7f by omega, show ¬ v ≤ 0x7ff by omega, show ¬ v ≤ 0xffff by omega,
      ↓reduceIte, List.cons_append, List.nil_append]
    exact List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, List.cons_eq_cons.2 ⟨(byte_eq (by omega)).symm, rfl⟩⟩⟩⟩

/-- Every encoding of a list of characters is well-formed. -/
theorem wf_flatMap (m : List Char) : WellFormedUtf8 (m.flatMap String.utf8EncodeChar) := by
  induction m with
  | nil => exact .nil
  | cons c m ih =>
    rw [List.flatMap_cons]
    exact wf_encodeChar c _ ih

theorem mk_toArray (l : List UInt8) : ByteArray.mk l.toArray = l.toByteArray :=
  ByteArray.ext (by rw [List.data_toByteArray])

theorem validUtf8_iff_validateUTF8 (bs : List UInt8) :
    validUtf8 bs = true ↔ ByteArray.validateUTF8 (ByteArray.mk bs.toArray) = true := by
  rw [validUtf8_iff_wf, ByteArray.validateUTF8_eq_true_iff]
  constructor
  · intro h
    obtain ⟨m, rfl⟩ := exists_chars h
    exact ⟨m, mk_toArray _⟩
  · rintro ⟨m, hm⟩
    have : bs = m.flatMap String.utf8EncodeChar := by
      have h1 := congrArg ByteArray.data hm
      have h2 : (m.flatMap String.utf8EncodeChar).toByteArray.data =
          (m.flatMap String.utf8EncodeChar).toArray := List.data_toByteArray
      have h3 : bs.toArray = (m.flatMap String.utf8EncodeChar).toArray := by
        rw [← h2]
        exact h1
      exact List.toArray_inj h3
    rw [this]
    exact wf_flatMap m

end GrammarProof

end BorshSpec
