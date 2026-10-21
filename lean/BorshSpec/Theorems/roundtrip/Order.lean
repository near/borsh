import BorshSpec.Theorems.roundtrip.Many

/-!
# The key order is a strict total order

Facts about `Value.cmp` needed by the round-trip and lenient-decoding proofs: it is
reflexive, says `.eq` only on equal values, is antisymmetric (swapping the arguments
swaps the result) and `.lt` is transitive.  Everything is in the namespace
`BorshSpec.RT`.
-/

namespace BorshSpec

namespace RT

open BorshSpec.Value

/-- `cmpBytes` on two non-empty lists: the head decides unless the heads are equal. -/
theorem cmpBytes_cons_lt (a b : UInt8) (as bs : List UInt8) :
    cmpBytes (a :: as) (b :: bs) = .lt ↔
      compare a b = .lt ∨ (compare a b = .eq ∧ cmpBytes as bs = .lt) := by
  simp only [cmpBytes]
  cases compare a b <;> simp

/-- `cmpBytes` on two non-empty lists is `.eq` when heads and tails are. -/
theorem cmpBytes_cons_eq (a b : UInt8) (as bs : List UInt8) :
    cmpBytes (a :: as) (b :: bs) = .eq ↔
      compare a b = .eq ∧ cmpBytes as bs = .eq := by
  simp only [cmpBytes]
  cases compare a b <;> simp

/-- Every byte string equals itself in `cmpBytes`. -/
theorem cmpBytes_self : ∀ (as : List UInt8), cmpBytes as as = .eq
  | [] => rfl
  | a :: as => by simp [cmpBytes_cons_eq, cmpBytes_self as]

/-- `cmpBytes` is `.eq` only on equal lists. -/
theorem cmpBytes_eq : ∀ (as bs : List UInt8), cmpBytes as bs = .eq → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpBytes] at h
  | _ :: _, [], h => by simp [cmpBytes] at h
  | a :: as, b :: bs, h => by
    obtain ⟨h1, h2⟩ := (cmpBytes_cons_eq ..).1 h
    rw [Std.compare_eq_iff_eq.1 h1, cmpBytes_eq as bs h2]

/-- `cmpBytes` is transitive for `.lt`. -/
theorem cmpBytes_trans : ∀ (as bs cs : List UInt8),
    cmpBytes as bs = .lt → cmpBytes bs cs = .lt → cmpBytes as cs = .lt
  | [], bs, cs, h1, h2 => by
    cases bs with
    | nil => simp [cmpBytes] at h1
    | cons b bs =>
      cases cs with
      | nil => simp [cmpBytes] at h2
      | cons c cs => simp [cmpBytes]
  | a :: as, bs, cs, h1, h2 => by
    cases bs with
    | nil => simp [cmpBytes] at h1
    | cons b bs =>
      cases cs with
      | nil => simp [cmpBytes] at h2
      | cons c cs =>
        rw [cmpBytes_cons_lt] at h1 h2 ⊢
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
        · exact .inl (Std.TransCmp.lt_trans h1 h2)
        · obtain rfl := Std.compare_eq_iff_eq.1 h2
          exact .inl h1
        · obtain rfl := Std.compare_eq_iff_eq.1 h1
          exact .inl h2
        · obtain rfl := Std.compare_eq_iff_eq.1 h1
          exact .inr ⟨h2, cmpBytes_trans as bs cs h1' h2'⟩

/-- Equal-order values have equal rank, i.e. the same constructor. -/
theorem rank_eq_of_cmp_eq (a b : Value) (h : cmp a b = .eq) : rank a = rank b := by
  cases a <;> cases b <;> simp_all [cmp, rank]

/-- `cmp a b = .lt` forces `rank a ≤ rank b`. -/
theorem rank_le_of_cmp_lt (a b : Value) (h : cmp a b = .lt) : rank a ≤ rank b := by
  cases a <;> cases b <;> simp_all [cmp, rank, Nat.compare_eq_lt]

/-- A smaller rank is a smaller value. -/
theorem cmp_lt_of_rank_lt (a b : Value) (h : rank a < rank b) : cmp a b = .lt := by
  cases a <;> cases b <;> simp_all [cmp, rank, Nat.compare_eq_lt]

/-- A value of the rank of `uint` is built with the `uint` constructor. -/
theorem eq_uint_of_rank {b : Value} (h : rank b = 0) : ∃ n, b = .uint n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `sint` is built with the `sint` constructor. -/
theorem eq_sint_of_rank {b : Value} (h : rank b = 1) : ∃ n, b = .sint n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `f32` is built with the `f32` constructor. -/
theorem eq_f32_of_rank {b : Value} (h : rank b = 2) : ∃ n, b = .f32 n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `f64` is built with the `f64` constructor. -/
theorem eq_f64_of_rank {b : Value} (h : rank b = 3) : ∃ n, b = .f64 n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `bool` is built with the `bool` constructor. -/
theorem eq_bool_of_rank {b : Value} (h : rank b = 4) : ∃ n, b = .bool n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `string` is built with the `string` constructor. -/
theorem eq_string_of_rank {b : Value} (h : rank b = 5) : ∃ n, b = .string n := by
  cases b <;> simp_all [rank]

/-- The only value of the rank of `optNone` is `optNone`. -/
theorem eq_optNone_of_rank {b : Value} (h : rank b = 6) : b = .optNone := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `optSome` is built with the `optSome` constructor. -/
theorem eq_optSome_of_rank {b : Value} (h : rank b = 7) : ∃ n, b = .optSome n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `vec` is built with the `vec` constructor. -/
theorem eq_vec_of_rank {b : Value} (h : rank b = 8) : ∃ n, b = .vec n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `array` is built with the `array` constructor. -/
theorem eq_array_of_rank {b : Value} (h : rank b = 9) : ∃ n, b = .array n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `tuple` is built with the `tuple` constructor. -/
theorem eq_tuple_of_rank {b : Value} (h : rank b = 10) : ∃ n, b = .tuple n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `enum` is built with the `enum` constructor. -/
theorem eq_enum_of_rank {b : Value} (h : rank b = 11) : ∃ t n, b = .enum t n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `map` is built with the `map` constructor. -/
theorem eq_map_of_rank {b : Value} (h : rank b = 12) : ∃ n, b = .map n := by
  cases b <;> simp_all [rank]

/-- A value of the rank of `set` is built with the `set` constructor. -/
theorem eq_set_of_rank {b : Value} (h : rank b = 13) : ∃ n, b = .set n := by
  cases b <;> simp_all [rank]

/-- `cmpList` on two non-empty lists: the head decides unless the heads are equal. -/
theorem cmpList_cons_lt (a b : Value) (as bs : List Value) :
    cmpList (a :: as) (b :: bs) = .lt ↔
      cmp a b = .lt ∨ (cmp a b = .eq ∧ cmpList as bs = .lt) := by
  simp only [cmpList]
  cases cmp a b <;> simp

/-- `cmpList` on two non-empty lists is `.eq` when heads and tails are. -/
theorem cmpList_cons_eq (a b : Value) (as bs : List Value) :
    cmpList (a :: as) (b :: bs) = .eq ↔ cmp a b = .eq ∧ cmpList as bs = .eq := by
  simp only [cmpList]
  cases cmp a b <;> simp

/-- `cmpPairs` on two non-empty lists, for `.lt`. -/
theorem cmpPairs_cons_lt (ka va kb vb : Value) (as bs : List (Value × Value)) :
    cmpPairs ((ka, va) :: as) ((kb, vb) :: bs) = .lt ↔
      cmp ka kb = .lt ∨ (cmp ka kb = .eq ∧ (cmp va vb = .lt ∨
        (cmp va vb = .eq ∧ cmpPairs as bs = .lt))) := by
  simp only [cmpPairs]
  cases cmp ka kb <;> cases cmp va vb <;> simp

/-- `cmpPairs` on two non-empty lists, for `.eq`. -/
theorem cmpPairs_cons_eq (ka va kb vb : Value) (as bs : List (Value × Value)) :
    cmpPairs ((ka, va) :: as) ((kb, vb) :: bs) = .eq ↔
      cmp ka kb = .eq ∧ cmp va vb = .eq ∧ cmpPairs as bs = .eq := by
  simp only [cmpPairs]
  cases cmp ka kb <;> cases cmp va vb <;> simp

/-- `cmp` on two enum values, for `.lt`. -/
theorem cmp_enum_lt (t u : Nat) (a b : Value) :
    cmp (.enum t a) (.enum u b) = .lt ↔
      compare t u = .lt ∨ (compare t u = .eq ∧ cmp a b = .lt) := by
  simp only [cmp]
  cases compare t u <;> simp

/-- `cmp` on two enum values, for `.eq`. -/
theorem cmp_enum_eq (t u : Nat) (a b : Value) :
    cmp (.enum t a) (.enum u b) = .eq ↔ compare t u = .eq ∧ cmp a b = .eq := by
  simp only [cmp]
  cases compare t u <;> simp

mutual

/-- Every value is `.eq` to itself in the key order. -/
theorem cmp_self : ∀ (a : Value), cmp a a = .eq
  | .uint n => by simp [cmp]
  | .sint n => by simp [cmp]
  | .f32 n => by simp [cmp]
  | .f64 n => by simp [cmp]
  | .bool n => by simp [cmp]
  | .string n => by simp [cmp, cmpBytes_self]
  | .optNone => by simp [cmp]
  | .optSome a => by simp [cmp, cmp_self a]
  | .vec xs => by simp [cmp, cmpList_self xs]
  | .array xs => by simp [cmp, cmpList_self xs]
  | .tuple xs => by simp [cmp, cmpList_self xs]
  | .enum t a => by simp [cmp_enum_eq, cmp_self a]
  | .map kvs => by simp [cmp, cmpPairs_self kvs]
  | .set xs => by simp [cmp, cmpList_self xs]

/-- Every list of values is `.eq` to itself in `cmpList`. -/
theorem cmpList_self : ∀ (xs : List Value), cmpList xs xs = .eq
  | [] => rfl
  | x :: xs => by simp [cmpList_cons_eq, cmp_self x, cmpList_self xs]

/-- Every list of entries is `.eq` to itself in `cmpPairs`. -/
theorem cmpPairs_self : ∀ (kvs : List (Value × Value)), cmpPairs kvs kvs = .eq
  | [] => rfl
  | (k, v) :: kvs => by simp [cmpPairs_cons_eq, cmp_self k, cmp_self v, cmpPairs_self kvs]

end

mutual

/-- `cmp` is `.eq` only on equal values. -/
theorem cmp_eq : ∀ (a b : Value), cmp a b = .eq → a = b
  | .uint n, b, h => by
    obtain ⟨m, rfl⟩ := eq_uint_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simpa [cmp] using h
  | .sint n, b, h => by
    obtain ⟨m, rfl⟩ := eq_sint_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simpa [cmp] using h
  | .f32 n, b, h => by
    obtain ⟨m, rfl⟩ := eq_f32_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simpa [cmp] using h
  | .f64 n, b, h => by
    obtain ⟨m, rfl⟩ := eq_f64_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simpa [cmp] using h
  | .bool n, b, h => by
    obtain ⟨m, rfl⟩ := eq_bool_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simpa [cmp] using h
  | .string n, b, h => by
    obtain ⟨m, rfl⟩ := eq_string_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simp only [cmp] at h
    rw [cmpBytes_eq n m h]
  | .optNone, b, h => by
    rw [eq_optNone_of_rank (rank_eq_of_cmp_eq _ _ h).symm]
  | .optSome a, b, h => by
    obtain ⟨m, rfl⟩ := eq_optSome_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simp only [cmp] at h
    rw [cmp_eq a m h]
  | .vec xs, b, h => by
    obtain ⟨ys, rfl⟩ := eq_vec_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simp only [cmp] at h
    rw [cmpList_eq xs ys h]
  | .array xs, b, h => by
    obtain ⟨ys, rfl⟩ := eq_array_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simp only [cmp] at h
    rw [cmpList_eq xs ys h]
  | .tuple xs, b, h => by
    obtain ⟨ys, rfl⟩ := eq_tuple_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simp only [cmp] at h
    rw [cmpList_eq xs ys h]
  | .enum t a, b, h => by
    obtain ⟨u, m, rfl⟩ := eq_enum_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    obtain ⟨h1, h2⟩ := (cmp_enum_eq ..).1 h
    rw [Std.compare_eq_iff_eq.1 h1, cmp_eq a m h2]
  | .map kvs, b, h => by
    obtain ⟨ys, rfl⟩ := eq_map_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simp only [cmp] at h
    rw [cmpPairs_eq kvs ys h]
  | .set xs, b, h => by
    obtain ⟨ys, rfl⟩ := eq_set_of_rank (rank_eq_of_cmp_eq _ _ h).symm
    simp only [cmp] at h
    rw [cmpList_eq xs ys h]

/-- `cmpList` is `.eq` only on equal lists. -/
theorem cmpList_eq : ∀ (xs ys : List Value), cmpList xs ys = .eq → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpList] at h
  | _ :: _, [], h => by simp [cmpList] at h
  | x :: xs, y :: ys, h => by
    obtain ⟨h1, h2⟩ := (cmpList_cons_eq ..).1 h
    rw [cmp_eq x y h1, cmpList_eq xs ys h2]

/-- `cmpPairs` is `.eq` only on equal lists. -/
theorem cmpPairs_eq : ∀ (xs ys : List (Value × Value)), cmpPairs xs ys = .eq → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpPairs] at h
  | _ :: _, [], h => by simp [cmpPairs] at h
  | (k, v) :: xs, (k', v') :: ys, h => by
    obtain ⟨h1, h2, h3⟩ := (cmpPairs_cons_eq ..).1 h
    rw [cmp_eq k k' h1, cmp_eq v v' h2, cmpPairs_eq xs ys h3]

end

/-- Transitivity of `cmp` reduces to the case of equal ranks. -/
theorem cmp_trans_dispatch (a b c : Value)
    (h : rank a = rank b → rank b = rank c → cmp a b = .lt → cmp b c = .lt →
      cmp a c = .lt)
    (h1 : cmp a b = .lt) (h2 : cmp b c = .lt) : cmp a c = .lt := by
  have r1 := rank_le_of_cmp_lt a b h1
  have r2 := rank_le_of_cmp_lt b c h2
  by_cases hab : rank a < rank b
  · exact cmp_lt_of_rank_lt a c (by omega)
  · by_cases hbc : rank b < rank c
    · exact cmp_lt_of_rank_lt a c (by omega)
    · exact h (by omega) (by omega) h1 h2

mutual

/-- **Transitivity.**  `cmp a b = .lt` is a transitive relation. -/
theorem cmp_trans : ∀ (a b c : Value), cmp a b = .lt → cmp b c = .lt → cmp a c = .lt
  | .uint n, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨m, rfl⟩ := eq_uint_of_rank hab.symm
      obtain ⟨k, rfl⟩ := eq_uint_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact Std.TransCmp.lt_trans h1 h2) h1 h2
  | .sint n, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨m, rfl⟩ := eq_sint_of_rank hab.symm
      obtain ⟨k, rfl⟩ := eq_sint_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact Std.TransCmp.lt_trans h1 h2) h1 h2
  | .f32 n, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨m, rfl⟩ := eq_f32_of_rank hab.symm
      obtain ⟨k, rfl⟩ := eq_f32_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact Std.TransCmp.lt_trans h1 h2) h1 h2
  | .f64 n, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨m, rfl⟩ := eq_f64_of_rank hab.symm
      obtain ⟨k, rfl⟩ := eq_f64_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact Std.TransCmp.lt_trans h1 h2) h1 h2
  | .bool n, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨m, rfl⟩ := eq_bool_of_rank hab.symm
      obtain ⟨k, rfl⟩ := eq_bool_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact Std.TransCmp.lt_trans h1 h2) h1 h2
  | .string n, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨m, rfl⟩ := eq_string_of_rank hab.symm
      obtain ⟨k, rfl⟩ := eq_string_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact cmpBytes_trans _ _ _ h1 h2) h1 h2
  | .optNone, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab _hbc h1 h2 => by
      rw [eq_optNone_of_rank hab.symm] at h1
      simp [cmp] at h1) h1 h2
  | .optSome a, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨m, rfl⟩ := eq_optSome_of_rank hab.symm
      obtain ⟨k, rfl⟩ := eq_optSome_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact cmp_trans a m k h1 h2) h1 h2
  | .vec xs, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨ys, rfl⟩ := eq_vec_of_rank hab.symm
      obtain ⟨zs, rfl⟩ := eq_vec_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact cmpList_trans xs ys zs h1 h2) h1 h2
  | .array xs, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨ys, rfl⟩ := eq_array_of_rank hab.symm
      obtain ⟨zs, rfl⟩ := eq_array_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact cmpList_trans xs ys zs h1 h2) h1 h2
  | .tuple xs, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨ys, rfl⟩ := eq_tuple_of_rank hab.symm
      obtain ⟨zs, rfl⟩ := eq_tuple_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact cmpList_trans xs ys zs h1 h2) h1 h2
  | .enum t a, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨u, m, rfl⟩ := eq_enum_of_rank hab.symm
      obtain ⟨p, k, rfl⟩ := eq_enum_of_rank hbc.symm
      rw [cmp_enum_lt] at h1 h2 ⊢
      rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
      · exact .inl (Std.TransCmp.lt_trans h1 h2)
      · obtain rfl := Std.compare_eq_iff_eq.1 h2
        exact .inl h1
      · obtain rfl := Std.compare_eq_iff_eq.1 h1
        exact .inl h2
      · obtain rfl := Std.compare_eq_iff_eq.1 h1
        exact .inr ⟨h2, cmp_trans a m k h1' h2'⟩) h1 h2
  | .map kvs, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨ys, rfl⟩ := eq_map_of_rank hab.symm
      obtain ⟨zs, rfl⟩ := eq_map_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact cmpPairs_trans kvs ys zs h1 h2) h1 h2
  | .set xs, b, c => fun h1 h2 => cmp_trans_dispatch _ b c (fun hab hbc h1 h2 => by
      obtain ⟨ys, rfl⟩ := eq_set_of_rank hab.symm
      obtain ⟨zs, rfl⟩ := eq_set_of_rank hbc.symm
      simp only [cmp] at h1 h2 ⊢
      exact cmpList_trans xs ys zs h1 h2) h1 h2

/-- `cmpList` is transitive for `.lt`. -/
theorem cmpList_trans : ∀ (as bs cs : List Value),
    cmpList as bs = .lt → cmpList bs cs = .lt → cmpList as cs = .lt
  | [], bs, cs, h1, h2 => by
    cases bs with
    | nil => simp [cmpList] at h1
    | cons b bs =>
      cases cs with
      | nil => simp [cmpList] at h2
      | cons c cs => simp [cmpList]
  | a :: as, bs, cs, h1, h2 => by
    cases bs with
    | nil => simp [cmpList] at h1
    | cons b bs =>
      cases cs with
      | nil => simp [cmpList] at h2
      | cons c cs =>
        rw [cmpList_cons_lt] at h1 h2 ⊢
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
        · exact .inl (cmp_trans a b c h1 h2)
        · obtain rfl := cmp_eq _ _ h2
          exact .inl h1
        · obtain rfl := cmp_eq _ _ h1
          exact .inl h2
        · obtain rfl := cmp_eq _ _ h1
          exact .inr ⟨h2, cmpList_trans as bs cs h1' h2'⟩

/-- `cmpPairs` is transitive for `.lt`. -/
theorem cmpPairs_trans : ∀ (as bs cs : List (Value × Value)),
    cmpPairs as bs = .lt → cmpPairs bs cs = .lt → cmpPairs as cs = .lt
  | [], bs, cs, h1, h2 => by
    cases bs with
    | nil => simp [cmpPairs] at h1
    | cons b bs =>
      cases cs with
      | nil => simp [cmpPairs] at h2
      | cons c cs => simp [cmpPairs]
  | (ka, va) :: as, bs, cs, h1, h2 => by
    cases bs with
    | nil => simp [cmpPairs] at h1
    | cons b bs =>
      obtain ⟨kb, vb⟩ := b
      cases cs with
      | nil => simp [cmpPairs] at h2
      | cons c cs =>
        obtain ⟨kc, vc⟩ := c
        rw [cmpPairs_cons_lt] at h1 h2 ⊢
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
        · exact .inl (cmp_trans ka kb kc h1 h2)
        · obtain rfl := cmp_eq _ _ h2
          exact .inl h1
        · obtain rfl := cmp_eq _ _ h1
          exact .inl h2
        · obtain rfl := cmp_eq _ _ h1
          refine .inr ⟨h2, ?_⟩
          rcases h1' with h1' | ⟨h1', h1''⟩ <;> rcases h2' with h2' | ⟨h2', h2''⟩
          · exact .inl (cmp_trans va vb vc h1' h2')
          · obtain rfl := cmp_eq _ _ h2'
            exact .inl h1'
          · obtain rfl := cmp_eq _ _ h1'
            exact .inl h2'
          · obtain rfl := cmp_eq _ _ h1'
            exact .inr ⟨h2', cmpPairs_trans as bs cs h1'' h2''⟩

end

/-- A strictly ascending list is pairwise `<`-related. -/
theorem strictAsc_pairwise : ∀ (xs : List Value), strictAsc xs = true →
    xs.Pairwise (fun a b => cmp a b = .lt)
  | [], _ => List.Pairwise.nil
  | [a], _ => by simp
  | a :: b :: rest, h => by
    simp only [strictAsc, Bool.and_eq_true, beq_iff_eq] at h
    have ih := strictAsc_pairwise (b :: rest) h.2
    have ih' := List.pairwise_cons.1 ih
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact cmp_trans a b x h.1 (ih'.1 x hx)

/-- A strictly ascending list has no duplicates. -/
theorem strictAsc_nodup {xs : List Value} (h : strictAsc xs = true) : xs.Nodup := by
  refine (strictAsc_pairwise xs h).imp ?_
  intro a b hab heq
  subst heq
  rw [cmp_self] at hab
  exact absurd hab (by decide)

/-- `cmpBytes` is antisymmetric: swapping the arguments swaps the result. -/
theorem cmpBytes_swap : ∀ (as bs : List UInt8), cmpBytes bs as = (cmpBytes as bs).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp only [cmpBytes]
    have hc : compare b a = (compare a b).swap := Std.OrientedCmp.eq_swap
    rw [hc]
    cases compare a b <;> simp [cmpBytes_swap as bs]

mutual

/-- `cmp` is antisymmetric: swapping the arguments swaps the result. -/
theorem cmp_swap : ∀ (a b : Value), cmp b a = (cmp a b).swap
  | (.uint _), (.uint _) => by simp only [cmp]; exact Std.OrientedCmp.eq_swap
  | (.uint _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.uint _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.sint _) => by simp only [cmp]; exact Std.OrientedCmp.eq_swap
  | (.sint _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.sint _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.f32 _) => by simp only [cmp]; exact Std.OrientedCmp.eq_swap
  | (.f32 _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f32 _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.f64 _) => by simp only [cmp]; exact Std.OrientedCmp.eq_swap
  | (.f64 _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.f64 _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.bool _) => by simp only [cmp]; exact Std.OrientedCmp.eq_swap
  | (.bool _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.bool _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.string _) => by simp only [cmp]; exact cmpBytes_swap _ _
  | (.string _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.string _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, .optNone => by simp [cmp]
  | .optNone, (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | .optNone, (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.optSome _) => by simp only [cmp]; exact cmp_swap _ _
  | (.optSome _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.optSome _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.vec _) => by simp only [cmp]; exact cmpList_swap _ _
  | (.vec _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.vec _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.array _) => by simp only [cmp]; exact cmpList_swap _ _
  | (.array _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.array _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.tuple _) => by simp only [cmp]; exact cmpList_swap _ _
  | (.tuple _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.tuple _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum ta aa), (.enum tb ab) => by
    simp only [cmp]
    have hc : compare tb ta = (compare ta tb).swap := Std.OrientedCmp.eq_swap
    rw [hc]
    cases compare ta tb <;> simp [cmp_swap aa ab]
  | (.enum _ _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.enum _ _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.map _), (.map _) => by simp only [cmp]; exact cmpPairs_swap _ _
  | (.map _), (.set _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.uint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.sint _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.f32 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.f64 _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.bool _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.string _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), .optNone => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.optSome _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.vec _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.array _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.tuple _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.enum _ _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.map _) => by first | (simp only [cmp]; exact Std.OrientedCmp.eq_swap) | simp [cmp]
  | (.set _), (.set _) => by simp only [cmp]; exact cmpList_swap _ _

/-- `cmpList` is antisymmetric. -/
theorem cmpList_swap : ∀ (xs ys : List Value), cmpList ys xs = (cmpList xs ys).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [cmpList]
    rw [cmp_swap x y]
    cases cmp x y <;> simp [cmpList_swap xs ys]

/-- `cmpPairs` is antisymmetric. -/
theorem cmpPairs_swap : ∀ (xs ys : List (Value × Value)), cmpPairs ys xs = (cmpPairs xs ys).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (k, v) :: xs, (k', v') :: ys => by
    simp only [cmpPairs]
    rw [cmp_swap k k', cmp_swap v v']
    cases cmp k k' <;> cases cmp v v' <;> simp [cmpPairs_swap xs ys]

end

/-- `cmp a b = .gt` exactly when `cmp b a = .lt`. -/
theorem cmp_gt_iff (a b : Value) : cmp a b = .gt ↔ cmp b a = .lt := by
  rw [cmp_swap b a]
  cases cmp b a <;> simp

end RT

end BorshSpec
