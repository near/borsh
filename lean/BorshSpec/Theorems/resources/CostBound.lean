import BorshSpec.Theorems.resources.Equiv
import BorshSpec.Theorems.resources.Progress
import BorshSpec.Theorems.resources.Loops
import BorshSpec.Theorems.resources.Basics

/-!
# The cost bound

Helper lemmas for `Theorems/Resources.lean`.  `Inv F bs c` says that the counted
result `c` of decoding `bs` obeys the bound with constant `F`:

* it costs at most `F * (bs.length + 1)` steps whatever happens;
* a success consumes `bs.length - rest.length` bytes and costs at most
  `F * (consumed + 1)` steps, and the value it returns is no larger than the cost:
  `size ≤ steps` and `elems + 1 ≤ steps`.

`decodeC_inv` proves `Inv s.factor bs (s.decodeC bs)` for every schema by induction
on the schema.  Each constructor has its own lemma, which takes the induction
hypothesis for its components as an assumption.
-/

namespace BorshSpec

namespace Schema

/-- The invariant of a counted decode; see the module docstring. -/
def Inv (F : Nat) (bs : List UInt8) (c : Counted (Value × List UInt8)) : Prop :=
  c.2 ≤ F * (bs.length + 1) ∧
  ∀ v r, c.1 = some (v, r) →
    r.length ≤ bs.length ∧ c.2 ≤ F * (bs.length - r.length + 1) ∧
    v.size ≤ c.2 ∧ v.elems + 1 ≤ c.2

/-- A step count of one for a failure. -/
theorem inv_fail (F : Nat) (hF : 1 ≤ F) (bs : List UInt8) : Inv F bs (none, 1) := by
  refine ⟨?_, fun v r h => by simp at h⟩
  simp only
  have : F * 1 ≤ F * (bs.length + 1) := Nat.mul_le_mul_left F (by omega)
  omega

/-- A value of size one and no elements, read from `w ≥ 1` bytes at the cost of one step. -/
theorem inv_leaf (F : Nat) (hF : 1 ≤ F) (bs r : List UInt8) (w : Nat)
    (hw : r.length + w = bs.length) (hw1 : 1 ≤ w) (v : Value) (hs : v.size = 1)
    (he : v.elems = 0) : Inv F bs (some (v, r), 1) := by
  have h1 : F * 1 ≤ F * (bs.length + 1) := Nat.mul_le_mul_left F (by omega)
  have h2 : F * 1 ≤ F * (bs.length - r.length + 1) := Nat.mul_le_mul_left F (by omega)
  refine ⟨?_, fun v' r' h => ?_⟩
  · simp only; omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [hs, he]
    omega

/-- The unsigned integers. -/
theorem inv_uint (w : IntWidth) (bs : List UInt8) :
    Inv 1 bs (decodeC (.uint w) bs) := by
  simp only [decodeC]
  cases hr : readLE w.bytes bs with
  | none => exact inv_fail 1 (Nat.le_refl _) bs
  | some p =>
    obtain ⟨n, r⟩ := p
    simp only [Option.map_some]
    exact inv_leaf 1 (Nat.le_refl _) bs r w.bytes (ResLemmas.readLE_length hr) (ResLemmas.bytes_pos w) _ (by simp [Value.size])
      (by simp [Value.elems])

/-- The signed integers. -/
theorem inv_sint (w : IntWidth) (bs : List UInt8) :
    Inv 1 bs (decodeC (.sint w) bs) := by
  simp only [decodeC]
  cases hr : readLE w.bytes bs with
  | none => exact inv_fail 1 (Nat.le_refl _) bs
  | some p =>
    obtain ⟨n, r⟩ := p
    simp only [Option.map_some]
    exact inv_leaf 1 (Nat.le_refl _) bs r w.bytes (ResLemmas.readLE_length hr) (ResLemmas.bytes_pos w) _ (by simp [Value.size])
      (by simp [Value.elems])

/-- `f32`. -/
theorem inv_f32 (bs : List UInt8) : Inv 1 bs (decodeC .f32 bs) := by
  simp only [decodeC]
  cases hr : readLE 4 bs with
  | none => exact inv_fail 1 (Nat.le_refl _) bs
  | some p =>
    obtain ⟨n, r⟩ := p
    simp only
    split
    · exact inv_fail 1 (Nat.le_refl _) bs
    · exact inv_leaf 1 (Nat.le_refl _) bs r 4 (ResLemmas.readLE_length hr) (by omega) _ (by simp [Value.size])
        (by simp [Value.elems])

/-- `f64`. -/
theorem inv_f64 (bs : List UInt8) : Inv 1 bs (decodeC .f64 bs) := by
  simp only [decodeC]
  cases hr : readLE 8 bs with
  | none => exact inv_fail 1 (Nat.le_refl _) bs
  | some p =>
    obtain ⟨n, r⟩ := p
    simp only
    split
    · exact inv_fail 1 (Nat.le_refl _) bs
    · exact inv_leaf 1 (Nat.le_refl _) bs r 8 (ResLemmas.readLE_length hr) (by omega) _ (by simp [Value.size])
        (by simp [Value.elems])

/-- `bool`. -/
theorem inv_bool (bs : List UInt8) : Inv 1 bs (decodeC .bool bs) := by
  simp only [decodeC]
  cases bs with
  | nil => exact inv_fail 1 (Nat.le_refl _) _
  | cons b r =>
    simp only
    split
    · exact inv_leaf 1 (Nat.le_refl _) (b :: r) r 1 (by simp) (Nat.le_refl _) _ (by simp [Value.size])
        (by simp [Value.elems])
    · split
      · exact inv_leaf 1 (Nat.le_refl _) (b :: r) r 1 (by simp) (Nat.le_refl _) _ (by simp [Value.size])
          (by simp [Value.elems])
      · exact inv_fail 1 (Nat.le_refl _) _

/-- `string`. -/
theorem inv_string (bs : List UInt8) : Inv 1 bs (decodeC .string bs) := by
  simp only [decodeC]
  cases hr : readU32 bs with
  | none => exact inv_fail 1 (Nat.le_refl _) bs
  | some p =>
    obtain ⟨n, r⟩ := p
    simp only
    cases hk : takeExact n r with
    | none => exact inv_fail 1 (Nat.le_refl _) bs
    | some q =>
      obtain ⟨body, r'⟩ := q
      simp only
      have h1 : r.length + 4 = bs.length := ResLemmas.readLE_length hr
      have h2 := ResLemmas.takeExact_length hk
      have h3 := ResLemmas.takeExact_fst_length hk
      split
      · refine ⟨?_, fun v r'' h => ?_⟩
        · simp only; omega
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Value.size, Value.elems]
          omega
      · refine ⟨?_, fun v r'' h => by simp at h⟩
        simp only; omega

/-! ### Arithmetic of the composite cases -/

/-- One extra step and an extra byte consumed (option, enum). -/
theorem ar_shift (n M D k : Nat) (h : k ≤ n + M * (D + 1)) :
    1 + k ≤ (1 + n + M) * (D + 1 + 1) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
  omega

/-- One extra step, no extra byte (tuple). -/
theorem ar_tuple (M C k : Nat) (h : k ≤ M * (C + 1)) : 1 + k ≤ (1 + M) * (C + 1) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
  omega

/-- `vec`, failure of the loop (or a later check). -/
theorem ar_vec_fail (Fs R L k : Nat) (hFs : 1 ≤ Fs) (hR : R ≤ L) (h : k ≤ 0 + Fs * (2 * R + 1)) :
    1 + k ≤ 2 * Fs * (L + 1) := by
  have h1 : Fs * R ≤ Fs * L := Nat.mul_le_mul_left Fs hR
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc,
    Nat.mul_left_comm Fs 2] at *
  omega

/-- `vec`, success. -/
theorem ar_vec_ok (Fs R R' L k : Nat) (hFs : 1 ≤ Fs) (hR : R ≤ L) (hR' : R' ≤ R)
    (h : k ≤ 0 + 2 * Fs * (R - R')) : 1 + k ≤ 2 * Fs * (L - R' + 1) := by
  have h1 : 2 * Fs * (R - R') ≤ 2 * Fs * (L - R') := Nat.mul_le_mul_left _ (by omega)
  simp only [Nat.mul_add, Nat.mul_one] at *
  omega

/-- `array` of elements that consume input, failure. -/
theorem ar_arr_fail (Fs L k : Nat) (h : k ≤ 0 + Fs * (2 * L + 1)) :
    1 + k ≤ (1 + 2 * Fs) * (L + 1) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc,
    Nat.mul_left_comm Fs 2] at *
  omega

/-- `array` of elements that consume input, success. -/
theorem ar_arr_ok (Fs C k : Nat) (h : k ≤ 0 + 2 * Fs * C) : 1 + k ≤ (1 + 2 * Fs) * (C + 1) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] at *
  omega

/-- `array` of zero-sized elements, failure. -/
theorem ar_arr0_fail (n Fs L k : Nat) (h : k ≤ 0 + n * (Fs * (L + 1))) :
    1 + k ≤ (1 + n * Fs) * (L + 1) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc, Nat.zero_add] at *
  omega

/-- `array` of zero-sized elements, success. -/
theorem ar_arr0_ok (n Fs C k : Nat) (h : k ≤ 0 + n * (Fs * (C + 1))) :
    1 + k ≤ (1 + n * Fs) * (C + 1) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc, Nat.zero_add] at *
  omega

/-- `set` and `map`, failure of the loop or of the order check. -/
theorem ar_set_fail (P R L c c' k : Nat) (hP : 1 ≤ P) (hR : R ≤ L)
    (hc : c ≤ 0 + P * (2 * R + 1)) (hc' : c' ≤ 2 * c) (hk : k ≤ 1 + c + c') :
    k ≤ 6 * P * (L + 1) := by
  have h1 : P * R ≤ P * L := Nat.mul_le_mul_left P hR
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc,
    Nat.mul_left_comm P 2, Nat.zero_add] at *
  omega

/-- `set` and `map`, success. -/
theorem ar_set_ok (P R R' L c c' k : Nat) (hP : 1 ≤ P) (hR : R ≤ L) (hR' : R' ≤ R)
    (hc : c ≤ 0 + 2 * P * (R - R')) (hc' : c' ≤ 2 * c) (hk : k ≤ 1 + c + c') :
    k ≤ 6 * P * (L - R' + 1) := by
  have h1 : 2 * P * (R - R') ≤ 2 * P * (L - R') := Nat.mul_le_mul_left _ (by omega)
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.zero_add] at *
  omega

/-! ### Composite cases -/

/-- `option`. -/
theorem inv_option (s : Schema) (ih : ∀ b, Inv s.factor b (s.decodeC b)) (bs : List UInt8) :
    Inv (1 + s.factor) bs (decodeC (.option s) bs) := by
  simp only [decodeC]
  cases bs with
  | nil => exact inv_fail _ (by omega) _
  | cons b r =>
    simp only
    split
    · exact inv_leaf _ (by omega) (b :: r) r 1 (by simp) (Nat.le_refl _) _ (by simp [Value.size])
        (by simp [Value.elems])
    · split
      · rcases hd : decodeC s r with ⟨res, k⟩
        obtain ⟨i1, i2⟩ := ih r
        rw [hd] at i1 i2
        simp only at i1 i2 ⊢
        refine ⟨?_, fun v r' h => ?_⟩
        · simp only [List.length_cons]
          exact ar_shift 0 s.factor r.length k (by simpa using i1)
        · rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨v', r''⟩, hv, hv'⟩ := h
          simp only [Prod.mk.injEq] at hv'
          obtain ⟨rfl, rfl⟩ := hv'
          obtain ⟨j1, j2, j3, j4⟩ := i2 v' r'' hv
          have e : (b :: r).length - r''.length + 1 = (r.length - r''.length) + 1 + 1 := by
            simp only [List.length_cons]; omega
          refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
          · simp only [e]
            have := ar_shift 0 s.factor (r.length - r''.length) k (by simpa using j2)
            simpa using this
          · simp only [Value.size]; omega
          · simp only [Value.elems]; omega
      · exact inv_fail _ (by omega) _

/-- A decode of the fields of a tuple; see `Inv`. -/
def FieldsInv (F : Nat) (bs : List UInt8) (c : Counted (List Value × List UInt8)) : Prop :=
  c.2 ≤ F * (bs.length + 1) ∧
  ∀ vs r, c.1 = some (vs, r) →
    r.length ≤ bs.length ∧ c.2 ≤ F * (bs.length - r.length + 1) ∧
    Value.sizeList vs ≤ c.2 ∧ Value.elemsList vs ≤ c.2

/-- `tuple`, given the bound for its fields. -/
theorem inv_tuple (fs : List Schema) (bs : List UInt8)
    (hf : FieldsInv (factorSum fs) bs (decodeFieldsC fs bs)) :
    Inv (1 + factorSum fs) bs (decodeC (.tuple fs) bs) := by
  simp only [decodeC]
  rcases hd : decodeFieldsC fs bs with ⟨res, k⟩
  rw [hd] at hf
  obtain ⟨f1, f2⟩ := hf
  simp only at f1 f2 ⊢
  refine ⟨ar_tuple _ _ _ f1, fun v r h => ?_⟩
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨vs, r'⟩, hv, hv'⟩ := h
  simp only [Prod.mk.injEq] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  obtain ⟨j1, j2, j3, j4⟩ := f2 vs r' hv
  refine ⟨j1, ar_tuple _ _ _ j2, ?_, ?_⟩
  · simp only [Value.size]; omega
  · simp only [Value.elems]; omega

/-- Read a success off an invariant, in terms of the step count `k`. -/
theorem Inv.succ {F : Nat} {bs : List UInt8} {c : Counted (Value × List UInt8)}
    (h : Inv F bs c) {x : Value} {r : List UInt8} {k : Nat} (hc : c = (some (x, r), k)) :
    r.length ≤ bs.length ∧ k ≤ F * (bs.length - r.length + 1) ∧ x.size ≤ k ∧ x.elems + 1 ≤ k := by
  subst hc
  exact h.2 x r rfl

/-- Read the unconditional bound off an invariant, in terms of the step count `k`. -/
theorem Inv.cost {F : Nat} {bs : List UInt8} {c : Counted (Value × List UInt8)}
    (h : Inv F bs c) {res : Option (Value × List UInt8)} {k : Nat} (hc : c = (res, k)) :
    k ≤ F * (bs.length + 1) := by
  subst hc
  exact h.1

/-- A success of `decodeC` is a success of `decode`. -/
theorem decode_of_decodeC {s : Schema} {b : List UInt8} {x : Value} {r : List UInt8} {k : Nat}
    (hk : s.decodeC b = (some (x, r), k)) : decode s b = some (x, r) := by
  have := decodeC_fst s b
  rw [hk] at this
  exact this.symm

/-- The elements-plus-one sum. -/
theorem sum_elems_succ : ∀ xs : List Value,
    (xs.map fun x => x.elems + 1).sum = (xs.map Value.elems).sum + xs.length
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_elems_succ xs]
    omega

/-- The elements-plus-one sum over entries. -/
theorem sum_pairs_elems_succ : ∀ kvs : List (Value × Value),
    (kvs.map fun p => p.1.elems + p.2.elems + 1).sum =
      (kvs.map fun p => p.1.elems + p.2.elems).sum + kvs.length
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_pairs_elems_succ xs]
    omega

/-- `vec`. -/
theorem inv_vec (s : Schema) (ih : ∀ b, Inv s.factor b (s.decodeC b)) (bs : List UInt8) :
    Inv (2 * s.factor) bs (decodeC (.vec s) bs) := by
  have hF := factor_pos_aux s
  simp only [decodeC]
  split
  · exact inv_fail _ (by omega) _
  · rename_i hz
    cases hr : readU32 bs with
    | none => exact inv_fail _ (by omega) _
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only
      have h1 : r.length + 4 = bs.length := ResLemmas.readLE_length hr
      have hz' : s.zeroSized = false := by simpa using hz
      obtain ⟨hl1, hl2⟩ := decodeManyC_bound_pos (fun b => decodeC s b) s.factor
        (fun b => (ih b).1)
        (fun b x r' k hk => by
          have a := (ih b).succ hk
          have c := (ResLemmas.decodeWith_length KeyPolicy.strict s b x r' (decode_of_decodeC hk)).2 hz'
          exact ⟨c, a.2.1⟩) n [] r 0
      rcases hd : decodeManyC (fun b => decodeC s b) n [] r 0 with ⟨res, k⟩
      rw [hd] at hl1 hl2
      simp only at hl1 hl2 ⊢
      refine ⟨ar_vec_fail s.factor r.length bs.length k hF (by omega) hl1, fun v r' h => ?_⟩
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨xs, r''⟩, hv, hv'⟩ := h
      simp only [Prod.mk.injEq] at hv'
      obtain ⟨rfl, rfl⟩ := hv'
      obtain ⟨j1, j2, j3⟩ := hl2 xs r'' hv
      have j4 := j3 Value.size (fun b x r k hk => ((ih b).succ hk).2.2.1)
      have j5 := j3 (fun x => x.elems + 1) (fun b x r k hk => ((ih b).succ hk).2.2.2)
      simp only [List.map_nil, List.sum_nil] at j4 j5
      refine ⟨by omega, ar_vec_ok s.factor r.length r''.length bs.length k hF (by omega) j1 j2,
        ?_, ?_⟩
      · simp only [Value.size, Value.sizeList_eq_sum]; omega
      · simp only [Value.elems, Value.elemsList_eq_sum]
        rw [sum_elems_succ] at j5
        omega

/-- `array`. -/
theorem inv_array (n : Nat) (s : Schema) (ih : ∀ b, Inv s.factor b (s.decodeC b))
    (bs : List UInt8) : Inv (Schema.factor (.array n s)) bs (decodeC (.array n s) bs) := by
  simp only [decodeC, factor]
  by_cases hz : s.zeroSized = true
  · simp only [hz, ite_true]
    obtain ⟨hl1, hl2⟩ := decodeManyC_bound_any (fun b => decodeC s b) s.factor
      (fun b => (ih b).1)
      (fun b x r' k hk => by
        have a := (ih b).succ hk
        exact ⟨a.1, a.2.1⟩) n [] bs 0
    rcases hd : decodeManyC (fun b => decodeC s b) n [] bs 0 with ⟨res, k⟩
    rw [hd] at hl1 hl2
    simp only at hl1 hl2 ⊢
    refine ⟨ar_arr0_fail n s.factor bs.length k hl1, fun v r' h => ?_⟩
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨xs, r''⟩, hv, hv'⟩ := h
    simp only [Prod.mk.injEq] at hv'
    obtain ⟨rfl, rfl⟩ := hv'
    obtain ⟨j1, j2, j3⟩ := hl2 xs r'' hv
    have j4 := j3 Value.size (fun b x r k hk => ((ih b).succ hk).2.2.1)
    have j5 := j3 (fun x => x.elems + 1) (fun b x r k hk => ((ih b).succ hk).2.2.2)
    simp only [List.map_nil, List.sum_nil] at j4 j5
    refine ⟨j1, ar_arr0_ok n s.factor _ k j2, ?_, ?_⟩
    · simp only [Value.size, Value.sizeList_eq_sum]; omega
    · simp only [Value.elems, Value.elemsList_eq_sum]
      rw [sum_elems_succ] at j5
      omega
  · have hz' : s.zeroSized = false := by simpa using hz
    simp only [hz', Bool.false_eq_true, ite_false]
    obtain ⟨hl1, hl2⟩ := decodeManyC_bound_pos (fun b => decodeC s b) s.factor
      (fun b => (ih b).1)
      (fun b x r' k hk => by
        have a := (ih b).succ hk
        have c := (ResLemmas.decodeWith_length KeyPolicy.strict s b x r' (decode_of_decodeC hk)).2 hz'
        exact ⟨c, a.2.1⟩) n [] bs 0
    rcases hd : decodeManyC (fun b => decodeC s b) n [] bs 0 with ⟨res, k⟩
    rw [hd] at hl1 hl2
    simp only at hl1 hl2 ⊢
    refine ⟨ar_arr_fail s.factor bs.length k hl1, fun v r' h => ?_⟩
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨xs, r''⟩, hv, hv'⟩ := h
    simp only [Prod.mk.injEq] at hv'
    obtain ⟨rfl, rfl⟩ := hv'
    obtain ⟨j1, j2, j3⟩ := hl2 xs r'' hv
    have j4 := j3 Value.size (fun b x r k hk => ((ih b).succ hk).2.2.1)
    have j5 := j3 (fun x => x.elems + 1) (fun b x r k hk => ((ih b).succ hk).2.2.2)
    simp only [List.map_nil, List.sum_nil] at j4 j5
    refine ⟨j1, ar_arr_ok s.factor _ k j2, ?_, ?_⟩
    · simp only [Value.size, Value.sizeList_eq_sum]; omega
    · simp only [Value.elems, Value.elemsList_eq_sum]
      rw [sum_elems_succ] at j5
      omega

/-- A decode of an enum payload; see `Inv`. -/
def VariantInv (n M : Nat) (bs : List UInt8) (c : Counted (Value × List UInt8)) : Prop :=
  c.2 ≤ n + M * (bs.length + 1) ∧
  ∀ v r, c.1 = some (v, r) →
    r.length ≤ bs.length ∧ c.2 ≤ n + M * (bs.length - r.length + 1) ∧
    v.size ≤ c.2 ∧ v.elems + 1 ≤ c.2

/-- `enum`, given the bound for its variants. -/
theorem inv_enum (vs : List (UInt8 × Schema)) (bs : List UInt8)
    (hv : ∀ t r, VariantInv vs.length (factorMax vs) r (decodeVariantC vs 0 t r)) :
    Inv (Schema.factor (.enum vs)) bs (decodeC (.enum vs) bs) := by
  simp only [decodeC, factor]
  cases bs with
  | nil => exact inv_fail _ (by omega) _
  | cons t r =>
    simp only
    rcases hd : decodeVariantC vs 0 t r with ⟨res, k⟩
    have h := hv t r
    rw [hd] at h
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2 ⊢
    refine ⟨ar_shift _ _ _ _ h1, fun v r' hr => ?_⟩
    obtain ⟨j1, j2, j3, j4⟩ := h2 v r' hr
    have e : (t :: r).length - r'.length + 1 = (r.length - r'.length) + 1 + 1 := by
      simp only [List.length_cons]; omega
    refine ⟨by simp only [List.length_cons]; omega, ?_, by omega, by omega⟩
    rw [e]
    exact ar_shift _ _ _ _ j2

/-- One step of the variant search. -/
theorem inv_variant_cons (t' : UInt8) (s : Schema) (vs : List (UInt8 × Schema)) (i : Nat)
    (t : UInt8) (bs : List UInt8) (ihs : ∀ b, Inv s.factor b (s.decodeC b))
    (ihv : VariantInv vs.length (factorMax vs) bs (decodeVariantC vs (i + 1) t bs)) :
    VariantInv ((t', s) :: vs).length (factorMax ((t', s) :: vs)) bs
      (decodeVariantC ((t', s) :: vs) i t bs) := by
  have hM : s.factor ≤ factorMax ((t', s) :: vs) := by
    simp only [factorMax]; exact Nat.le_max_left _ _
  have hM' : factorMax vs ≤ factorMax ((t', s) :: vs) := by
    simp only [factorMax]; exact Nat.le_max_right _ _
  simp only [decodeVariantC, List.length_cons]
  split
  · rcases hd : decodeC s bs with ⟨res, k⟩
    have h := ihs bs
    rw [hd] at h
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2 ⊢
    have m1 : s.factor * (bs.length + 1) ≤ factorMax ((t', s) :: vs) * (bs.length + 1) :=
      Nat.mul_le_mul_right _ hM
    refine ⟨by omega, fun v r hr => ?_⟩
    rw [Option.map_eq_some_iff] at hr
    obtain ⟨⟨v', r'⟩, hv, hv'⟩ := hr
    simp only [Prod.mk.injEq] at hv'
    obtain ⟨rfl, rfl⟩ := hv'
    obtain ⟨j1, j2, j3, j4⟩ := h2 v' r' hv
    have m2 : s.factor * (bs.length - r'.length + 1) ≤
        factorMax ((t', s) :: vs) * (bs.length - r'.length + 1) := Nat.mul_le_mul_right _ hM
    refine ⟨j1, by omega, ?_, ?_⟩
    · simp only [Value.size]; omega
    · simp only [Value.elems]; omega
  · rcases hd : decodeVariantC vs (i + 1) t bs with ⟨res, k⟩
    rw [hd] at ihv
    obtain ⟨h1, h2⟩ := ihv
    simp only at h1 h2 ⊢
    have m1 : factorMax vs * (bs.length + 1) ≤ factorMax ((t', s) :: vs) * (bs.length + 1) :=
      Nat.mul_le_mul_right _ hM'
    refine ⟨by omega, fun v r hr => ?_⟩
    obtain ⟨j1, j2, j3, j4⟩ := h2 v r hr
    have m2 : factorMax vs * (bs.length - r.length + 1) ≤
        factorMax ((t', s) :: vs) * (bs.length - r.length + 1) := Nat.mul_le_mul_right _ hM'
    exact ⟨j1, by omega, by omega, by omega⟩

/-- The end of the variant search: no variant carries the tag. -/
theorem inv_variant_nil (i : Nat) (t : UInt8) (bs : List UInt8) :
    VariantInv ([] : List (UInt8 × Schema)).length (factorMax []) bs
      (decodeVariantC [] i t bs) := by
  simp only [decodeVariantC]
  refine ⟨?_, fun v r h => by simp at h⟩
  simp [factorMax]

/-- `set`. -/
theorem inv_set (s : Schema) (ih : ∀ b, Inv s.factor b (s.decodeC b)) (bs : List UInt8) :
    Inv (6 * s.factor) bs (decodeC (.set s) bs) := by
  have hF := factor_pos_aux s
  simp only [decodeC]
  split
  · exact inv_fail _ (by omega) _
  · rename_i hz
    cases hr : readU32 bs with
    | none => exact inv_fail _ (by omega) _
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only
      have h1 : r.length + 4 = bs.length := ResLemmas.readLE_length hr
      have hz' : s.zeroSized = false := by simpa using hz
      obtain ⟨hl1, hl2⟩ := decodeManyC_bound_pos (fun b => decodeC s b) s.factor
        (fun b => (ih b).1)
        (fun b x r' k hk => by
          have a := (ih b).succ hk
          have c := (ResLemmas.decodeWith_length KeyPolicy.strict s b x r' (decode_of_decodeC hk)).2 hz'
          exact ⟨c, a.2.1⟩) n [] r 0
      rcases hd : decodeManyC (fun b => decodeC s b) n [] r 0 with ⟨res, c⟩
      rw [hd] at hl1 hl2
      simp only at hl1 hl2 ⊢
      cases res with
      | none =>
        refine ⟨?_, fun v r' h => by simp at h⟩
        exact ar_set_fail s.factor r.length bs.length c 0 (1 + c) hF (by omega) hl1
          (by omega) (by omega)
      | some q =>
        obtain ⟨xs, r''⟩ := q
        obtain ⟨j1, j2, j3⟩ := hl2 xs r'' rfl
        have j4 := j3 Value.size (fun b x r k hk => ((ih b).succ hk).2.2.1)
        have j5 := j3 (fun x => x.elems + 1) (fun b x r k hk => ((ih b).succ hk).2.2.2)
        simp only [List.map_nil, List.sum_nil] at j4 j5
        rw [sum_elems_succ] at j5
        obtain ⟨ok, c', ha⟩ : ∃ ok c', Value.strictAscC xs = (ok, c') := ⟨_, _, rfl⟩
        have hc' : c' ≤ 2 * c := by
          have := Value.strictAscC_snd_le xs
          rw [ha, Value.sizeList_eq_sum] at this
          simp only at this
          omega
        simp only [ha]
        refine ⟨ar_set_fail s.factor r.length bs.length c c' _ hF (by omega) hl1 hc' (by omega),
          fun v r' h => ?_⟩
        by_cases hok : ok = true
        · simp only [hok, ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by omega, ar_set_ok s.factor r.length r''.length bs.length c c' _ hF (by omega)
            j1 j2 hc' (by omega), ?_, ?_⟩
          · simp only [Value.size, Value.sizeList_eq_sum]; omega
          · simp only [Value.elems, Value.elemsList_eq_sum]; omega
        · simp [hok] at h

/-- The pair decoder of a map. -/
def pairC (k v : Schema) : List UInt8 → Counted ((Value × Value) × List UInt8) := fun b =>
  match decodeC k b with
  | (none, c₁) => (none, c₁)
  | (some (a, r₁), c₁) =>
    match decodeC v r₁ with
    | (none, c₂) => (none, c₁ + c₂)
    | (some (c, r₂), c₂) => (some ((a, c), r₂), c₁ + c₂)

/-- `decodeC` on a map, with the pair decoder named. -/
theorem decodeC_map (k v : Schema) (bs : List UInt8) : decodeC (.map k v) bs =
    if k.zeroSized then (none, 1)
    else
      match readU32 bs with
      | none => (none, 1)
      | some (n, r) =>
        match decodeManyC (pairC k v) n [] r 0 with
        | (none, c) => (none, 1 + c)
        | (some (kvs, r'), c) =>
          match Value.strictAscC (kvs.map Prod.fst) with
          | (ok, c') => (if ok then some (.map kvs, r') else none, 1 + c + c') := by
  rw [decodeC]
  rfl

/-- Arithmetic for a pair whose second component fails. -/
theorem ar_pair_fail (Fk Fv L R c1 c2 : Nat) (hR : R ≤ L) (h1 : c1 ≤ Fk * (L - R + 1))
    (h2 : c2 ≤ Fv * (R + 1)) : c1 + c2 ≤ (Fk + Fv) * (L + 1) := by
  have a1 : Fk * (L - R + 1) ≤ Fk * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  have a2 : Fv * (R + 1) ≤ Fv * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul]
  omega

/-- Arithmetic for a pair that succeeds. -/
theorem ar_pair_ok (Fk Fv L R R' c1 c2 : Nat) (hR : R ≤ L) (hR' : R' ≤ R)
    (h1 : c1 ≤ Fk * (L - R + 1)) (h2 : c2 ≤ Fv * (R - R' + 1)) :
    c1 + c2 ≤ (Fk + Fv) * (L - R' + 1) := by
  have a1 : Fk * (L - R + 1) ≤ Fk * (L - R' + 1) := Nat.mul_le_mul_left _ (by omega)
  have a2 : Fv * (R - R' + 1) ≤ Fv * (L - R' + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul]
  omega

/-- What the loop over map entries needs to know about the pair decoder. -/
theorem pairC_facts (k v : Schema) (ihk : ∀ b, Inv k.factor b (k.decodeC b))
    (ihv : ∀ b, Inv v.factor b (v.decodeC b)) (hz : k.zeroSized = false) (b : List UInt8) :
    (pairC k v b).2 ≤ (k.factor + v.factor) * (b.length + 1) ∧
    ∀ a d r, (pairC k v b).1 = some ((a, d), r) →
      r.length < b.length ∧ (pairC k v b).2 ≤ (k.factor + v.factor) * (b.length - r.length + 1) ∧
      a.size ≤ (pairC k v b).2 ∧ a.size + d.size ≤ (pairC k v b).2 ∧
      a.elems + d.elems + 1 ≤ (pairC k v b).2 := by
  rcases hk : decodeC k b with ⟨res1, c1⟩
  have i1 := ihk b
  rw [hk] at i1
  obtain ⟨i1a, i1b⟩ := i1
  simp only at i1a i1b
  cases res1 with
  | none =>
    simp only [pairC, hk]
    refine ⟨?_, fun a d r h => by simp at h⟩
    have a1 : k.factor * (b.length + 1) ≤ (k.factor + v.factor) * (b.length + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  | some q =>
    obtain ⟨a', r1⟩ := q
    obtain ⟨j1, j2, j3, j4⟩ := i1b a' r1 rfl
    have jl := (ResLemmas.decodeWith_length KeyPolicy.strict k b a' r1 (decode_of_decodeC hk)).2 hz
    rcases hv : decodeC v r1 with ⟨res2, c2⟩
    have i2 := ihv r1
    rw [hv] at i2
    obtain ⟨i2a, i2b⟩ := i2
    simp only at i2a i2b
    cases res2 with
    | none =>
      simp only [pairC, hk, hv]
      exact ⟨ar_pair_fail k.factor v.factor b.length r1.length c1 c2 j1 j2 i2a,
        fun a d r h => by simp at h⟩
    | some q2 =>
      obtain ⟨d', r2⟩ := q2
      obtain ⟨m1, m2, m3, m4⟩ := i2b d' r2 rfl
      simp only [pairC, hk, hv]
      refine ⟨?_, fun a d r h => ?_⟩
      · have := ar_pair_ok k.factor v.factor b.length r1.length r2.length c1 c2 j1 m1 j2 m2
        have e : b.length - r2.length + 1 ≤ b.length + 1 := by omega
        have := Nat.mul_le_mul_left (k.factor + v.factor) e
        omega
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨by omega, ar_pair_ok k.factor v.factor b.length r1.length r2.length c1 c2 j1 m1
          j2 m2, by omega, by omega, by omega⟩

/-- `map`. -/
theorem inv_map (k v : Schema) (ihk : ∀ b, Inv k.factor b (k.decodeC b))
    (ihv : ∀ b, Inv v.factor b (v.decodeC b)) (bs : List UInt8) :
    Inv (6 * (k.factor + v.factor)) bs (decodeC (.map k v) bs) := by
  have hFk := factor_pos_aux k
  rw [decodeC_map]
  split
  · exact inv_fail _ (by omega) _
  · rename_i hz
    cases hr : readU32 bs with
    | none => exact inv_fail _ (by omega) _
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only
      have h1 : r.length + 4 = bs.length := ResLemmas.readLE_length hr
      have hz' : k.zeroSized = false := by simpa using hz
      obtain ⟨hl1, hl2⟩ := decodeManyC_bound_pos (pairC k v) (k.factor + v.factor)
        (fun b => (pairC_facts k v ihk ihv hz' b).1)
        (fun b x r' c hc => by
          have a := (pairC_facts k v ihk ihv hz' b).2
          cases x with
          | mk x1 x2 =>
            obtain ⟨q1, q2, -⟩ := a x1 x2 r' (by rw [hc])
            rw [hc] at q2
            exact ⟨q1, q2⟩) n [] r 0
      rcases hd : decodeManyC (pairC k v) n [] r 0 with ⟨res, c⟩
      rw [hd] at hl1 hl2
      simp only at hl1 hl2 ⊢
      cases res with
      | none =>
        refine ⟨?_, fun v r' h => by simp at h⟩
        exact ar_set_fail (k.factor + v.factor) r.length bs.length c 0 (1 + c) (by omega)
          (by omega) hl1 (by omega) (by omega)
      | some q =>
        obtain ⟨kvs, r''⟩ := q
        obtain ⟨j1, j2, j3⟩ := hl2 kvs r'' rfl
        have j4 := j3 (fun p => p.1.size + p.2.size) (fun b x r' c' hc => by
          cases x with
          | mk x1 x2 =>
            have := ((pairC_facts k v ihk ihv hz' b).2 x1 x2 r' (by rw [hc])).2.2.2.1
            rw [hc] at this
            exact this)
        have j5 := j3 (fun p => p.1.elems + p.2.elems + 1) (fun b x r' c' hc => by
          cases x with
          | mk x1 x2 =>
            have := ((pairC_facts k v ihk ihv hz' b).2 x1 x2 r' (by rw [hc])).2.2.2.2
            rw [hc] at this
            exact this)
        have j6 := j3 (fun p => p.1.size) (fun b x r' c' hc => by
          cases x with
          | mk x1 x2 =>
            have := ((pairC_facts k v ihk ihv hz' b).2 x1 x2 r' (by rw [hc])).2.2.1
            rw [hc] at this
            exact this)
        simp only [List.map_nil, List.sum_nil] at j4 j5 j6
        rw [sum_pairs_elems_succ] at j5
        obtain ⟨ok, c', ha⟩ : ∃ ok c', Value.strictAscC (kvs.map Prod.fst) = (ok, c') :=
          ⟨_, _, rfl⟩
        have hc' : c' ≤ 2 * c := by
          have := Value.strictAscC_snd_le (kvs.map Prod.fst)
          rw [ha, Value.sizeList_keys] at this
          simp only at this
          omega
        simp only [ha]
        refine ⟨ar_set_fail (k.factor + v.factor) r.length bs.length c c' _ (by omega)
          (by omega) hl1 hc' (by omega), fun v' r' h => ?_⟩
        by_cases hok : ok = true
        · simp only [hok, ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by omega, ar_set_ok (k.factor + v.factor) r.length r''.length bs.length c c' _
            (by omega) (by omega) j1 j2 hc' (by omega), ?_, ?_⟩
          · simp only [Value.size, Value.sizePairs_eq_sum]; omega
          · simp only [Value.elems, Value.elemsPairs_eq_sum]; omega
        · simp [hok] at h

/-- The empty field list. -/
theorem inv_fields_nil (bs : List UInt8) : FieldsInv 0 bs (decodeFieldsC [] bs) := by
  simp only [decodeFieldsC]
  refine ⟨by simp, fun vs r h => ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [Value.sizeList, Value.elemsList]

/-- One field followed by the rest. -/
theorem inv_fields_cons (s : Schema) (fs : List Schema) (bs : List UInt8)
    (ihs : ∀ b, Inv s.factor b (s.decodeC b))
    (ihf : ∀ b, FieldsInv (factorSum fs) b (decodeFieldsC fs b)) :
    FieldsInv (factorSum (s :: fs)) bs (decodeFieldsC (s :: fs) bs) := by
  simp only [decodeFieldsC, factorSum]
  rcases hd : decodeC s bs with ⟨res, k⟩
  have i1 := ihs bs
  rw [hd] at i1
  obtain ⟨i1a, i1b⟩ := i1
  simp only at i1a i1b
  cases res with
  | none =>
    simp only
    refine ⟨?_, fun vs r h => by simp at h⟩
    have a1 : s.factor * (bs.length + 1) ≤ (s.factor + factorSum fs) * (bs.length + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  | some q =>
    obtain ⟨v, r⟩ := q
    obtain ⟨j1, j2, j3, j4⟩ := i1b v r rfl
    rcases hf : decodeFieldsC fs r with ⟨res2, k2⟩
    simp only [hf]
    have i2 := ihf r
    rw [hf] at i2
    obtain ⟨i2a, i2b⟩ := i2
    simp only at i2a i2b
    cases res2 with
    | none =>
      simp only
      exact ⟨ar_pair_fail s.factor (factorSum fs) bs.length r.length k k2 j1 j2 i2a,
        fun vs r h => by simp at h⟩
    | some q2 =>
      obtain ⟨vs, r2⟩ := q2
      obtain ⟨m1, m2, m3, m4⟩ := i2b vs r2 rfl
      simp only
      refine ⟨?_, fun vs' r' h => ?_⟩
      · have := ar_pair_ok s.factor (factorSum fs) bs.length r.length r2.length k k2 j1 m1 j2 m2
        have e : bs.length - r2.length + 1 ≤ bs.length + 1 := by omega
        have := Nat.mul_le_mul_left (s.factor + factorSum fs) e
        omega
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by omega, ar_pair_ok s.factor (factorSum fs) bs.length r.length r2.length k k2
          j1 m1 j2 m2, ?_, ?_⟩
        · simp only [Value.sizeList]; omega
        · simp only [Value.elemsList]; omega

mutual

/-- **The cost invariant holds for every schema.** -/
theorem decodeC_inv : ∀ (s : Schema) (bs : List UInt8), Inv s.factor bs (s.decodeC bs)
  | .uint w, bs => inv_uint w bs
  | .sint w, bs => inv_sint w bs
  | .f32, bs => inv_f32 bs
  | .f64, bs => inv_f64 bs
  | .bool, bs => inv_bool bs
  | .string, bs => inv_string bs
  | .option s, bs => inv_option s (fun b => decodeC_inv s b) bs
  | .vec s, bs => inv_vec s (fun b => decodeC_inv s b) bs
  | .array n s, bs => inv_array n s (fun b => decodeC_inv s b) bs
  | .tuple fs, bs => inv_tuple fs bs (decodeFieldsC_inv fs bs)
  | .enum vs, bs => inv_enum vs bs (fun t r => decodeVariantC_inv vs 0 t r)
  | .map k v, bs => inv_map k v (fun b => decodeC_inv k b) (fun b => decodeC_inv v b) bs
  | .set s, bs => inv_set s (fun b => decodeC_inv s b) bs

/-- The cost invariant for the fields of a tuple. -/
theorem decodeFieldsC_inv : ∀ (fs : List Schema) (bs : List UInt8),
    FieldsInv (factorSum fs) bs (decodeFieldsC fs bs)
  | [], bs => inv_fields_nil bs
  | s :: fs, bs =>
    inv_fields_cons s fs bs (fun b => decodeC_inv s b) (fun b => decodeFieldsC_inv fs b)

/-- The cost invariant for the variant search of an enum. -/
theorem decodeVariantC_inv : ∀ (vs : List (UInt8 × Schema)) (i : Nat) (t : UInt8)
    (bs : List UInt8), VariantInv vs.length (factorMax vs) bs (decodeVariantC vs i t bs)
  | [], i, t, bs => inv_variant_nil i t bs
  | (t', s) :: vs, i, t, bs =>
    inv_variant_cons t' s vs i t bs (fun b => decodeC_inv s b) (decodeVariantC_inv vs (i + 1) t bs)

end

end Schema

end BorshSpec
