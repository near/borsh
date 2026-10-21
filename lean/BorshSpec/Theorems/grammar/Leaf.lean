import BorshSpec

/-!
# Helper lemmas: integers, floats and byte reading

The little-endian codec against the grammar's `leBytes`, the two's complement residue
against the grammar's `twosComplement`, and the NaN tests against the grammar's mask
form.  Also the reading primitives `takeExact`, `readLE`, `readU32` in the relational
form that the decoder proof uses.
-/

namespace BorshSpec

namespace GrammarProof

theorem toLE_eq_leBytes (w n : Nat) : toLE w n = leBytes w n := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toLE, leBytes, ih]

theorem length_leBytes (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem fromLE_leBytes (k n : Nat) : fromLE (leBytes k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [leBytes, fromLE]; omega
  | succ k ih =>
    simp only [leBytes, fromLE, ih]
    have h : (UInt8.ofNat (n % 256)).toNat = n % 256 := by simp
    rw [h, Nat.pow_succ', Nat.mod_mul]

theorem fromLE_lt (a : List UInt8) : fromLE a < 256 ^ a.length := by
  induction a with
  | nil => simp [fromLE]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [fromLE, List.length_cons, Nat.pow_succ']
    omega

theorem leBytes_fromLE (a : List UInt8) : leBytes a.length (fromLE a) = a := by
  induction a with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [fromLE, List.length_cons, leBytes]
    have h1 : (b.toNat + 256 * fromLE bs) % 256 = b.toNat := by omega
    have h2 : (b.toNat + 256 * fromLE bs) / 256 = fromLE bs := by omega
    rw [h1, h2, ih]
    simp

theorem sintToNat_eq_twosComplement (w : IntWidth) (i : Int) :
    Schema.sintToNat w i = twosComplement w.bytes i := by
  have h : ((256 ^ w.bytes : Nat) : Int) = 2 ^ (8 * w.bytes) := by
    have : (256 : Nat) ^ w.bytes = 2 ^ (8 * w.bytes) := by
      rw [Nat.pow_mul]
    rw [this]; push_cast; rfl
  simp only [Schema.sintToNat, twosComplement, h]

theorem isNaN32_iff (bits : UInt32) : isNaN32 bits = true ↔ IsNaN32 bits := by
  have _h := bits.toNat_lt
  have e : (2147483647 : Nat) = 2 ^ 31 - 1 := by decide
  simp [isNaN32, IsNaN32, UInt32.toNat_and]
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  omega
theorem isNaN64_iff (bits : UInt64) : isNaN64 bits = true ↔ IsNaN64 bits := by
  have _h := bits.toNat_lt
  have e : (9223372036854775807 : Nat) = 2 ^ 63 - 1 := by decide
  simp [isNaN64, IsNaN64, UInt64.toNat_and]
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem sintInRange_iff (w : IntWidth) (i : Int) : Schema.sintInRange w i = true ↔
    -((256 ^ w.bytes / 2 : Nat) : Int) ≤ i ∧ i < ((256 ^ w.bytes / 2 : Nat) : Int) := by
  unfold Schema.sintInRange
  rw [decide_eq_true_iff]
  cases w <;> simp [IntWidth.bytes]

theorem natToSint_of_lt (w : IntWidth) (n : Nat) (h : n < 2 ^ (8 * w.bytes - 1)) :
    Schema.natToSint w n = (n : Int) := by
  simp [Schema.natToSint, h]
theorem natToSint_of_ge (w : IntWidth) (n : Nat) (h : ¬ n < 2 ^ (8 * w.bytes - 1)) :
    Schema.natToSint w n = (n : Int) - 2 ^ (8 * w.bytes) := by
  simp [Schema.natToSint, h]

theorem natToSint_twos (w : IntWidth) (i : Int) (h : Schema.sintInRange w i = true) :
    Schema.natToSint w (twosComplement w.bytes i) = i := by
  have h' := (sintInRange_iff w i).1 h
  by_cases hc : twosComplement w.bytes i < 2 ^ (8 * w.bytes - 1)
  · rw [natToSint_of_lt w _ hc]
    cases w <;> simp only [twosComplement, IntWidth.bytes] at * <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv] at * <;> omega
  · rw [natToSint_of_ge w _ hc]
    cases w <;> simp only [twosComplement, IntWidth.bytes] at * <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Int.reducePow] at * <;> omega

theorem twos_natToSint (w : IntWidth) (n : Nat) (h : n < 256 ^ w.bytes) :
    twosComplement w.bytes (Schema.natToSint w n) = n := by
  by_cases hc : n < 2 ^ (8 * w.bytes - 1)
  · rw [natToSint_of_lt w n hc]
    cases w <;> simp only [twosComplement, IntWidth.bytes] at * <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub] at * <;> omega
  · rw [natToSint_of_ge w n hc]
    cases w <;> simp only [twosComplement, IntWidth.bytes] at * <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Int.reducePow] at * <;> omega

theorem sintInRange_natToSint (w : IntWidth) (n : Nat) (h : n < 256 ^ w.bytes) :
    Schema.sintInRange w (Schema.natToSint w n) = true := by
  apply decide_eq_true
  by_cases hc : n < 2 ^ (8 * w.bytes - 1)
  · rw [natToSint_of_lt w n hc]
    cases w <;> simp only [IntWidth.bytes] at * <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Int.reducePow, Int.reduceNeg] at * <;> omega
  · rw [natToSint_of_ge w n hc]
    cases w <;> simp only [IntWidth.bytes] at * <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Int.reducePow, Int.reduceNeg] at * <;> omega

theorem twos_lt (w : IntWidth) (i : Int) : twosComplement w.bytes i < 256 ^ w.bytes := by
  cases w <;> simp only [twosComplement, IntWidth.bytes] <;>
    simp only [Nat.reducePow] <;> omega

theorem takeExact_iff (n : Nat) (bs a r : List UInt8) :
    takeExact n bs = some (a, r) ↔ bs = a ++ r ∧ a.length = n := by
  unfold takeExact
  constructor
  · intro h
    split at h
    · rename_i hl
      obtain ⟨rfl, rfl⟩ := Option.some.inj h |> Prod.mk.inj
      exact ⟨(List.take_append_drop _ _).symm, hl⟩
    · simp at h
  · rintro ⟨rfl, rfl⟩
    simp

theorem readLE_iff (k : Nat) (bs : List UInt8) (n : Nat) (r : List UInt8) :
    readLE k bs = some (n, r) ↔ ∃ a, bs = a ++ r ∧ a.length = k ∧ n = fromLE a := by
  unfold readLE
  cases h : takeExact k bs with
  | none =>
    simp only [Option.map_none, reduceCtorEq, false_iff]
    rintro ⟨a, h1, h2, _⟩
    have := (takeExact_iff k bs a r).2 ⟨h1, h2⟩
    rw [h] at this
    exact absurd this (by simp)
  | some p =>
    obtain ⟨a, r'⟩ := p
    have h' := (takeExact_iff k bs a r').1 h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨a, h'.1, h'.2, rfl⟩
    · rintro ⟨a', h1, h2, h3⟩
      have := (takeExact_iff k bs a' r).2 ⟨h1, h2⟩
      rw [h] at this
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj this)
      exact ⟨h3.symm, rfl⟩

theorem readLE_leBytes_iff (k : Nat) (bs : List UInt8) (n : Nat) (r : List UInt8) :
    readLE k bs = some (n, r) ↔ n < 256 ^ k ∧ bs = leBytes k n ++ r := by
  rw [readLE_iff]
  constructor
  · rintro ⟨a, h1, h2, h3⟩
    subst h2 h3
    exact ⟨fromLE_lt a, by rw [leBytes_fromLE]; exact h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨leBytes k n, h2, length_leBytes k n, by rw [fromLE_leBytes, Nat.mod_eq_of_lt h1]⟩

theorem readLE_leBytes {k n : Nat} (h : n < 256 ^ k) (r : List UInt8) :
    readLE k (leBytes k n ++ r) = some (n, r) :=
  (readLE_leBytes_iff k _ n r).2 ⟨h, rfl⟩

theorem toNat_ofNat32 {n : Nat} (h : n < 256 ^ 4) : (UInt32.ofNat n).toNat = n := by
  have : n < 2 ^ 32 := by simpa using h
  simp [Nat.mod_eq_of_lt this]

theorem toNat_ofNat64 {n : Nat} (h : n < 256 ^ 8) : (UInt64.ofNat n).toNat = n := by
  have : n < 2 ^ 64 := by simpa using h
  simp [Nat.mod_eq_of_lt this]

theorem toNat_lt32 (x : UInt32) : x.toNat < 256 ^ 4 := by
  have := x.toNat_lt; simpa using this

theorem toNat_lt64 (x : UInt64) : x.toNat < 256 ^ 8 := by
  have := x.toNat_lt; simpa using this

end GrammarProof

end BorshSpec
