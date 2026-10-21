import BorshSpec

/-!
# Hexadecimal text: helper lemmas

Digit-level facts behind `hex_decode_encode` and `hex_encode_decode` in
`Theorems/Resources.lean`.
-/

namespace BorshSpec

namespace Hex

/-- The order on characters is the order on their code points. -/
theorem char_le_iff (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

/-- The digit of a value below 16 reads back as that value. -/
theorem digitVal_digit : ∀ n, n < 16 → digitVal (digit n) = some n := by decide

/-- A character that `digitVal` accepts is the digit of the value it reads. -/
theorem digit_digitVal (c : Char) (n : Nat) (h : digitVal c = some n) :
    n < 16 ∧ digit n = c := by
  unfold digitVal at h
  split at h
  · rename_i h1
    obtain ⟨h1a, h1b⟩ := h1
    simp only [Option.some.injEq] at h
    rw [char_le_iff] at h1a h1b
    have e0 : ('0' : Char).toNat = 48 := by decide
    have e9 : ('9' : Char).toNat = 57 := by decide
    rw [e0] at h1a
    rw [e9] at h1b
    subst h
    refine ⟨by omega, ?_⟩
    unfold digit
    have hlt : c.toNat - 48 < 10 := by omega
    simp only [hlt, ite_true]
    have : 48 + (c.toNat - 48) = c.toNat := by omega
    rw [this, Char.ofNat_toNat]
  · split at h
    · rename_i h1
      obtain ⟨h1a, h1b⟩ := h1
      simp only [Option.some.injEq] at h
      rw [char_le_iff] at h1a h1b
      have e0 : ('a' : Char).toNat = 97 := by decide
      have e9 : ('f' : Char).toNat = 102 := by decide
      rw [e0] at h1a
      rw [e9] at h1b
      subst h
      refine ⟨by omega, ?_⟩
      unfold digit
      have hlt : ¬ (c.toNat - 87 < 10) := by omega
      simp only [hlt, ite_false]
      have : 87 + (c.toNat - 87) = c.toNat := by omega
      rw [this, Char.ofNat_toNat]
    · simp at h

/-- The two digits of a byte read back as the byte. -/
theorem decodeChars_byteChars (b : UInt8) (rest : List Char) (acc : List UInt8) :
    decodeChars (byteChars b ++ rest) acc = decodeChars rest (b :: acc) := by
  have hb := UInt8.toNat_lt b
  have h1 : b.toNat / 16 < 16 := by omega
  have h2 : b.toNat % 16 < 16 := by omega
  have h3 : (b.toNat / 16 * 16 + b.toNat % 16).toUInt8 = b := by
    have : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
    rw [this]
    exact UInt8.ofNat_toNat
  simp only [byteChars, List.cons_append, List.nil_append, decodeChars,
    digitVal_digit _ h1, digitVal_digit _ h2, h3]

/-- Decoding the digits of a byte string gives the byte string (after the accumulator). -/
theorem decodeChars_flatMap : ∀ (bs acc : List UInt8),
    decodeChars (bs.flatMap byteChars) acc = some (acc.reverse ++ bs)
  | [], acc => by simp [decodeChars]
  | b :: bs, acc => by
    rw [List.flatMap_cons, decodeChars_byteChars, decodeChars_flatMap bs (b :: acc)]
    simp

/-- The digits of a byte are the digits of its two nibbles. -/
theorem byteChars_of_digits (a c : Char) (hi lo : Nat) (ha : digitVal a = some hi)
    (hc : digitVal c = some lo) : byteChars (hi * 16 + lo).toUInt8 = [a, c] := by
  obtain ⟨h1, rfl⟩ := digit_digitVal a hi ha
  obtain ⟨h2, rfl⟩ := digit_digitVal c lo hc
  have e : (hi * 16 + lo).toUInt8.toNat = hi * 16 + lo := by
    rw [Nat.toUInt8_eq]
    exact UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  simp only [byteChars, e]
  have e1 : (hi * 16 + lo) / 16 = hi := by omega
  have e2 : (hi * 16 + lo) % 16 = lo := by omega
  rw [e1, e2]

/-- Whatever `decodeChars` accepts is the digit text of the bytes it returns. -/
theorem decodeChars_inv : ∀ (cs : List Char) (acc out : List UInt8),
    decodeChars cs acc = some out →
      ∃ bs, cs = bs.flatMap byteChars ∧ out = acc.reverse ++ bs
  | [], acc, out, h => by
    simp only [decodeChars, Option.some.injEq] at h
    exact ⟨[], rfl, by simp [h]⟩
  | [_], acc, out, h => by simp [decodeChars] at h
  | a :: c :: rest, acc, out, h => by
    simp only [decodeChars] at h
    cases ha : digitVal a with
    | none => simp [ha] at h
    | some hi =>
      cases hc : digitVal c with
      | none => simp [ha, hc] at h
      | some lo =>
        simp only [ha, hc] at h
        obtain ⟨bs, hbs, hout⟩ := decodeChars_inv rest _ out h
        refine ⟨(hi * 16 + lo).toUInt8 :: bs, ?_, ?_⟩
        · rw [List.flatMap_cons, byteChars_of_digits a c hi lo ha hc, hbs]
          rfl
        · rw [hout]
          simp

end Hex

end BorshSpec
