import BorshSpec

/-!
# Byte-level lemmas for the round-trip proofs

Facts about `toLE`, `fromLE`, `takeExact`, `readLE` and the signed-integer conversions.
Everything is in the namespace `BorshSpec.RT`, so that the helper lemmas cannot clash
with names in the other theorem modules.
-/

namespace BorshSpec

namespace RT

/-- A little-endian encoding on `w` bytes has exactly `w` bytes. -/
theorem toLE_length : ∀ (w n : Nat), (toLE w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [toLE, toLE_length w]

/-- Reading back a little-endian encoding gives the number modulo `256^w`. -/
theorem fromLE_toLE : ∀ (w n : Nat), fromLE (toLE w n) = n % 256 ^ w
  | 0, n => by simp [toLE, fromLE, Nat.mod_one]
  | w + 1, n => by
    have ih := fromLE_toLE w (n / 256)
    have h1 : ((n % 256).toUInt8).toNat = n % 256 := by simp
    have h2 : n % 256 ^ (w + 1) = n % 256 + 256 * (n / 256 % 256 ^ w) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    simp only [toLE, fromLE, ih, h1, h2]

/-- Every little-endian byte string of length `w` denotes a number below `256 ^ w`. -/
theorem fromLE_lt : ∀ (bs : List UInt8), fromLE bs < 2 ^ (8 * bs.length)
  | [] => by simp [fromLE]
  | b :: bs => by
    have h := fromLE_lt bs
    have hb := b.toNat_lt
    have hp : 2 ^ (8 * (b :: bs).length) = 2 ^ (8 * bs.length) * 256 := by
      rw [List.length_cons, Nat.mul_succ, Nat.pow_add]
    rw [hp]
    simp only [fromLE]
    omega

/-- Decoding the little-endian encoding of `n` gives `n` back, provided `n` fits. -/
theorem fromLE_toLE_of_lt (w n : Nat) (h : n < 2 ^ (8 * w)) : fromLE (toLE w n) = n := by
  rw [fromLE_toLE]
  have : (256 : Nat) ^ w = 2 ^ (8 * w) := by
    rw [Nat.pow_mul]
  rw [this]
  exact Nat.mod_eq_of_lt h

/-- Encoding the number denoted by a `w`-byte string gives the string back. -/
theorem toLE_fromLE : ∀ (bs : List UInt8), toLE bs.length (fromLE bs) = bs
  | [] => rfl
  | b :: bs => by
    have hb := b.toNat_lt
    have h1 : (b.toNat + 256 * fromLE bs) % 256 = b.toNat := by omega
    have h2 : (b.toNat + 256 * fromLE bs) / 256 = fromLE bs := by omega
    simp only [fromLE, List.length_cons, toLE, h1, h2, toLE_fromLE bs]
    simp

/-- `takeExact` succeeds on any input that starts with `n` bytes. -/
theorem takeExact_append {n : Nat} {a : List UInt8} (h : a.length = n) (r : List UInt8) :
    takeExact n (a ++ r) = some (a, r) := by
  subst h
  simp [takeExact]

/-- A successful `takeExact` splits the input in two. -/
theorem takeExact_eq_some {n : Nat} {bs a r : List UInt8}
    (h : takeExact n bs = some (a, r)) : a.length = n ∧ bs = a ++ r := by
  unfold takeExact at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hl, (List.take_append_drop n bs).symm⟩
  · simp at h

/-- Reading back a written fixed-width integer. -/
theorem readLE_toLE {w n : Nat} (h : n < 2 ^ (8 * w)) (r : List UInt8) :
    readLE w (toLE w n ++ r) = some (n, r) := by
  simp [readLE, takeExact_append (toLE_length w n), fromLE_toLE_of_lt w n h]

/-- A successful fixed-width read consumes the little-endian encoding of its result. -/
theorem readLE_eq_some {w : Nat} {bs : List UInt8} {n : Nat} {r : List UInt8}
    (h : readLE w bs = some (n, r)) : n < 2 ^ (8 * w) ∧ bs = toLE w n ++ r := by
  unfold readLE at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨a, r'⟩, h1, h2⟩ := h
  obtain ⟨hl, hbs⟩ := takeExact_eq_some h1
  simp only [Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  subst hl
  exact ⟨fromLE_lt a, by rw [toLE_fromLE]; exact hbs⟩

/-- A successful fixed-width read consumes at least `w` bytes. -/
theorem readLE_length {w : Nat} {bs : List UInt8} {n : Nat} {r : List UInt8}
    (h : readLE w bs = some (n, r)) : w + r.length ≤ bs.length := by
  obtain ⟨_, rfl⟩ := readLE_eq_some h
  simp [toLE_length]

/-- The unsigned residue of a signed integer fits its width. -/
theorem sintToNat_lt (w : IntWidth) (i : Int) : Schema.sintToNat w i < 2 ^ (8 * w.bytes) := by
  cases w <;> simp only [Schema.sintToNat, IntWidth.bytes] <;> omega

/-- The signed reading of a residue is in range. -/
theorem sintInRange_natToSint (w : IntWidth) (n : Nat) (h : n < 2 ^ (8 * w.bytes)) :
    Schema.sintInRange w (Schema.natToSint w n) = true := by
  by_cases hc : n < 2 ^ (8 * w.bytes - 1)
  · simp only [Schema.natToSint, hc, ↓reduceIte, Schema.sintInRange]
    apply decide_eq_true
    cases w <;> simp only [IntWidth.bytes] at hc ⊢ <;> omega
  · simp only [Schema.natToSint, hc, ↓reduceIte, Schema.sintInRange]
    apply decide_eq_true
    cases w <;> simp only [IntWidth.bytes] at hc h ⊢ <;> omega

/-- Writing a signed integer and reading it back is the identity on the range. -/
theorem natToSint_sintToNat (w : IntWidth) (i : Int) (h : Schema.sintInRange w i = true) :
    Schema.natToSint w (Schema.sintToNat w i) = i := by
  unfold Schema.sintInRange at h
  replace h := of_decide_eq_true h
  by_cases hc : Schema.sintToNat w i < 2 ^ (8 * w.bytes - 1)
  · simp only [Schema.natToSint, hc, ↓reduceIte]
    cases w <;> simp only [IntWidth.bytes, Schema.sintToNat] at h hc ⊢ <;> omega
  · simp only [Schema.natToSint, hc, ↓reduceIte]
    cases w <;> simp only [IntWidth.bytes, Schema.sintToNat] at h hc ⊢ <;> omega

/-- Reading a residue as a signed integer and writing it back is the identity. -/
theorem sintToNat_natToSint (w : IntWidth) (n : Nat) (h : n < 2 ^ (8 * w.bytes)) :
    Schema.sintToNat w (Schema.natToSint w n) = n := by
  by_cases hc : n < 2 ^ (8 * w.bytes - 1)
  · simp only [Schema.natToSint, hc, ↓reduceIte]
    cases w <;> simp only [IntWidth.bytes, Schema.sintToNat] at hc h ⊢ <;> omega
  · simp only [Schema.natToSint, hc, ↓reduceIte]
    cases w <;> simp only [IntWidth.bytes, Schema.sintToNat] at hc h ⊢ <;> omega

end RT

end BorshSpec
