import BorshSpec

/-!
# Cost of the counted loops

Helper lemmas for `Theorems/Resources.lean`.  `decodeManyC` runs an element decoder
`d` (which reports the steps it took) `m` times.  For an element decoder whose cost on
`b` is at most `F * (b.length + 1)`, and whose cost on success is at most
`F * (bytes consumed + 1)`:

* if every success consumes a byte (`decodeManyC_bound_pos`), the loop costs at most
  `F * (2 * length + 1)` steps, and `2 * F * consumed` on success;
* if elements may consume nothing (`decodeManyC_bound_any`, the zero-sized array
  case), the loop costs at most `m * (F * (length + 1))` steps, and
  `m * (F * (consumed + 1))` on success.

Both also bound the sum of any per-element measure that the element cost dominates.
-/

namespace BorshSpec

namespace Schema

/-- Arithmetic of one loop iteration when elements consume at least one byte. -/
theorem iter_pos_fail (F L R k0 steps K : Nat) (hR : R < L) (hk0 : k0 ≤ F * (L - R + 1))
    (hK : K ≤ steps + k0 + F * (2 * R + 1)) : K ≤ steps + F * (2 * L + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, L = R + c + 1 := ⟨L - R - 1, by omega⟩
  have e : R + c + 1 - R + 1 = c + 2 := by omega
  rw [e] at hk0
  have h2 : F * (c + 2) ≤ F * (2 * (c + 1)) := Nat.mul_le_mul_left F (by omega)
  simp only [Nat.mul_add, Nat.mul_one] at *
  omega

/-- Arithmetic of one loop iteration when elements consume at least one byte (success). -/
theorem iter_pos_ok (F L R R' k0 steps K : Nat) (hR : R < L) (hR' : R' ≤ R)
    (hk0 : k0 ≤ F * (L - R + 1)) (hK : K ≤ steps + k0 + 2 * F * (R - R')) :
    K ≤ steps + 2 * F * (L - R') := by
  obtain ⟨c, rfl⟩ : ∃ c, L = R + c + 1 := ⟨L - R - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, R = R' + d := ⟨R - R', by omega⟩
  have e : R' + d + c + 1 - (R' + d) + 1 = c + 2 := by omega
  have e2 : R' + d - R' = d := by omega
  have e3 : R' + d + c + 1 - R' = d + c + 1 := by omega
  rw [e] at hk0
  rw [e2] at hK
  rw [e3]
  have h2 : F * (c + 2) ≤ F * (2 * (c + 1)) := Nat.mul_le_mul_left F (by omega)
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at *
  omega

/-- **Loop bound, elements that consume input.** -/
theorem decodeManyC_bound_pos {α : Type} (d : List UInt8 → Counted (α × List UInt8)) (F : Nat)
    (h1 : ∀ b, (d b).2 ≤ F * (b.length + 1))
    (h2 : ∀ b x r k, d b = (some (x, r), k) →
      r.length < b.length ∧ k ≤ F * (b.length - r.length + 1)) :
    ∀ (m : Nat) (acc : List α) (bs : List UInt8) (steps : Nat),
      (decodeManyC d m acc bs steps).2 ≤ steps + F * (2 * bs.length + 1) ∧
      ∀ xs r', (decodeManyC d m acc bs steps).1 = some (xs, r') →
        r'.length ≤ bs.length ∧
        (decodeManyC d m acc bs steps).2 ≤ steps + 2 * F * (bs.length - r'.length) ∧
        ∀ μ : α → Nat, (∀ b x r k, d b = (some (x, r), k) → μ x ≤ k) →
          (xs.map μ).sum + steps ≤ (acc.map μ).sum + (decodeManyC d m acc bs steps).2
  | 0, acc, bs, steps => by
    refine ⟨by simp [decodeManyC], fun xs r' h => ?_⟩
    simp only [decodeManyC, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨Nat.le_refl _, by simp, fun μ _ => ?_⟩
    simp
  | m + 1, acc, bs, steps => by
    simp only [decodeManyC]
    rcases hd : d bs with ⟨res, k0⟩
    cases res with
    | none =>
      have := h1 bs
      rw [hd] at this
      simp only at this
      refine ⟨?_, fun xs r' h => by simp at h⟩
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm F 2] at *
      omega
    | some p =>
      obtain ⟨x, r⟩ := p
      simp only
      obtain ⟨hlt, hk⟩ := h2 bs x r k0 hd
      obtain ⟨ihc, iho⟩ := decodeManyC_bound_pos d F h1 h2 m (x :: acc) r (steps + k0)
      refine ⟨iter_pos_fail F bs.length r.length k0 steps _ hlt hk ihc, fun xs r' h => ?_⟩
      obtain ⟨a, b, c⟩ := iho xs r' h
      refine ⟨by omega, iter_pos_ok F bs.length r.length r'.length k0 steps _ hlt a hk b, ?_⟩
      intro μ hμ
      have := c μ hμ
      have := hμ bs x r k0 hd
      simp only [List.map_cons, List.sum_cons] at *
      omega

/-- Arithmetic of one loop iteration, elements that may consume nothing (failure bound). -/
theorem iter_any_fail (F m L R k0 steps K : Nat) (hR : R ≤ L) (hk0 : k0 ≤ F * (L - R + 1))
    (hK : K ≤ steps + k0 + m * (F * (R + 1))) : K ≤ steps + (m + 1) * (F * (L + 1)) := by
  have h1 : F * (L - R + 1) ≤ F * (L + 1) := Nat.mul_le_mul_left F (by omega)
  have h2 : F * (R + 1) ≤ F * (L + 1) := Nat.mul_le_mul_left F (by omega)
  have h3 : m * (F * (R + 1)) ≤ m * (F * (L + 1)) := Nat.mul_le_mul_left m h2
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Arithmetic of one loop iteration, elements that may consume nothing (success bound). -/
theorem iter_any_ok (F m L R R' k0 steps K : Nat) (hR : R ≤ L) (hR' : R' ≤ R)
    (hk0 : k0 ≤ F * (L - R + 1)) (hK : K ≤ steps + k0 + m * (F * (R - R' + 1))) :
    K ≤ steps + (m + 1) * (F * (L - R' + 1)) := by
  have h1 : F * (L - R + 1) ≤ F * (L - R' + 1) := Nat.mul_le_mul_left F (by omega)
  have h2 : F * (R - R' + 1) ≤ F * (L - R' + 1) := Nat.mul_le_mul_left F (by omega)
  have h3 : m * (F * (R - R' + 1)) ≤ m * (F * (L - R' + 1)) := Nat.mul_le_mul_left m h2
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- **Loop bound, elements that may consume nothing.** -/
theorem decodeManyC_bound_any {α : Type} (d : List UInt8 → Counted (α × List UInt8)) (F : Nat)
    (h1 : ∀ b, (d b).2 ≤ F * (b.length + 1))
    (h2 : ∀ b x r k, d b = (some (x, r), k) →
      r.length ≤ b.length ∧ k ≤ F * (b.length - r.length + 1)) :
    ∀ (m : Nat) (acc : List α) (bs : List UInt8) (steps : Nat),
      (decodeManyC d m acc bs steps).2 ≤ steps + m * (F * (bs.length + 1)) ∧
      ∀ xs r', (decodeManyC d m acc bs steps).1 = some (xs, r') →
        r'.length ≤ bs.length ∧
        (decodeManyC d m acc bs steps).2 ≤ steps + m * (F * (bs.length - r'.length + 1)) ∧
        ∀ μ : α → Nat, (∀ b x r k, d b = (some (x, r), k) → μ x ≤ k) →
          (xs.map μ).sum + steps ≤ (acc.map μ).sum + (decodeManyC d m acc bs steps).2
  | 0, acc, bs, steps => by
    refine ⟨by simp [decodeManyC], fun xs r' h => ?_⟩
    simp only [decodeManyC, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨Nat.le_refl _, by simp, fun μ _ => ?_⟩
    simp
  | m + 1, acc, bs, steps => by
    simp only [decodeManyC]
    rcases hd : d bs with ⟨res, k0⟩
    cases res with
    | none =>
      have := h1 bs
      rw [hd] at this
      simp only at this
      refine ⟨?_, fun xs r' h => by simp at h⟩
      simp only
      rw [Nat.add_mul, Nat.one_mul]
      omega
    | some p =>
      obtain ⟨x, r⟩ := p
      simp only
      obtain ⟨hle, hk⟩ := h2 bs x r k0 hd
      obtain ⟨ihc, iho⟩ := decodeManyC_bound_any d F h1 h2 m (x :: acc) r (steps + k0)
      refine ⟨iter_any_fail F m bs.length r.length k0 steps _ hle hk ihc, fun xs r' h => ?_⟩
      obtain ⟨a, b, c⟩ := iho xs r' h
      refine ⟨by omega, iter_any_ok F m bs.length r.length r'.length k0 steps _ hle a hk b, ?_⟩
      intro μ hμ
      have := c μ hμ
      have := hμ bs x r k0 hd
      simp only [List.map_cons, List.sum_cons] at *
      omega

end Schema

end BorshSpec
