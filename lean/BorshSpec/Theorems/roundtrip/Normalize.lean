import BorshSpec.Theorems.roundtrip.Order

/-!
# Normalising sets and maps

Facts about `Lenient.normalizeSet` and `Lenient.normalizeMap`: a stable merge sort by
the key order followed by `Lenient.dedupLast`.  `dedupLast` is shown to be the
non-tail-recursive `dedup` (which drops an element when the next one has the same
key), and `dedup` is characterised on key-sorted lists.
-/

namespace BorshSpec

namespace RT

open BorshSpec.Value

/-- `cmp a b` is not `.gt` exactly when `a < b` or `a = b`. -/
theorem cmp_ne_gt_iff {a b : Value} : cmp a b ≠ .gt ↔ cmp a b = .lt ∨ a = b := by
  constructor
  · intro h
    cases e : cmp a b
    · exact .inl rfl
    · exact .inr (cmp_eq a b e)
    · exact absurd e h
  · rintro (h | rfl)
    · rw [h]; decide
    · rw [cmp_self]; decide

/-- `cmp a b = .eq` exactly when `a = b`. -/
theorem cmp_eq_iff' {a b : Value} : cmp a b = .eq ↔ a = b :=
  ⟨cmp_eq a b, fun h => h ▸ cmp_self a⟩

/-- `≤` in the key order is transitive. -/
theorem cmp_le_trans {a b c : Value} (h1 : cmp a b ≠ .gt) (h2 : cmp b c ≠ .gt) :
    cmp a c ≠ .gt := by
  rw [cmp_ne_gt_iff] at *
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact .inl (cmp_trans a b c h1 h2)
    · exact .inl h1
  · exact h2

/-- `a < b` and `b ≤ c` give `a < c`. -/
theorem cmp_lt_of_lt_of_le {a b c : Value} (h1 : cmp a b = .lt) (h2 : cmp b c ≠ .gt) :
    cmp a c = .lt := by
  rw [cmp_ne_gt_iff] at h2
  rcases h2 with h2 | rfl
  · exact cmp_trans a b c h1 h2
  · exact h1

/-- The key order is total: one of `a ≤ b`, `b ≤ a`. -/
theorem cmp_le_total (a b : Value) : cmp a b ≠ .gt ∨ cmp b a ≠ .gt := by
  rw [cmp_swap a b]
  cases cmp a b <;> simp

/-- `Lenient.keyLe` is `≤` in the key order. -/
theorem keyLe_iff {a b : Value} : Lenient.keyLe a b = true ↔ cmp a b ≠ .gt := by
  simp [Lenient.keyLe]

/-- `Lenient.keyLe` is transitive. -/
theorem keyLe_trans (a b c : Value) :
    Lenient.keyLe a b = true → Lenient.keyLe b c = true → Lenient.keyLe a c = true := by
  simp only [keyLe_iff]
  exact cmp_le_trans

/-- `Lenient.keyLe` is total. -/
theorem keyLe_total (a b : Value) : (Lenient.keyLe a b || Lenient.keyLe b a) = true := by
  simp only [Bool.or_eq_true, keyLe_iff]
  exact cmp_le_total a b

/-- The pair version of `keyLe`, comparing keys, is transitive. -/
theorem keyLe_fst_trans (a b c : Value × Value) :
    Lenient.keyLe a.1 b.1 = true → Lenient.keyLe b.1 c.1 = true →
      Lenient.keyLe a.1 c.1 = true :=
  keyLe_trans a.1 b.1 c.1

/-- The pair version of `keyLe`, comparing keys, is total. -/
theorem keyLe_fst_total (a b : Value × Value) :
    (Lenient.keyLe a.1 b.1 || Lenient.keyLe b.1 a.1) = true :=
  keyLe_total a.1 b.1

/-- A merge-sorted list of values is sorted for `≤`. -/
theorem sorted_set (xs : List Value) :
    (xs.mergeSort Lenient.keyLe).Pairwise (fun a b => cmp a b ≠ .gt) := by
  have := List.pairwise_mergeSort keyLe_trans keyLe_total xs
  exact this.imp (fun h => keyLe_iff.1 h)

/-- A merge-sorted list of entries is sorted by key for `≤`. -/
theorem sorted_map (kvs : List (Value × Value)) :
    (kvs.mergeSort fun a b => Lenient.keyLe a.1 b.1).Pairwise
      (fun a b => cmp a.1 b.1 ≠ .gt) := by
  have := List.pairwise_mergeSort keyLe_fst_trans keyLe_fst_total kvs
  exact this.imp (fun h => keyLe_iff.1 h)

/-! ### `dedup`, the pure form of `dedupLast` -/

/-- Drop each element whose successor has the same key; the pure form of
`Lenient.dedupLast`. -/
def dedup {α : Type} (same : α → α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if same x y then dedup same (y :: rest) else x :: dedup same (y :: rest)

/-- Equality of keys as a Boolean relation. -/
def sameBy {α : Type} (key : α → Value) (x y : α) : Bool := cmp (key x) (key y) == .eq

/-- `dedupLast` with a non-empty accumulator. -/
theorem dedupLast_acc {α : Type} (same : α → α → Bool) :
    ∀ (l : List α) (z : α) (acc : List α),
      Lenient.dedupLast same l (z :: acc) = acc.reverse ++ dedup same (z :: l)
  | [], z, acc => by simp [Lenient.dedupLast, dedup]
  | x :: rest, z, acc => by
    simp only [Lenient.dedupLast]
    split
    · rw [dedupLast_acc same rest x acc]
      simp [dedup, *]
    · rw [dedupLast_acc same rest x (z :: acc)]
      simp [dedup, *]

/-- `dedupLast` from the empty accumulator is `dedup`. -/
theorem dedupLast_nil {α : Type} (same : α → α → Bool) (l : List α) :
    Lenient.dedupLast same l [] = dedup same l := by
  cases l with
  | nil => rfl
  | cons x rest => simp [Lenient.dedupLast, dedupLast_acc]

/-- `dedup` keeps a sub-list. -/
theorem dedup_sublist {α : Type} (same : α → α → Bool) :
    ∀ l : List α, List.Sublist (dedup same l) l
  | [] => List.Sublist.slnil
  | [x] => by simp [dedup]
  | x :: y :: rest => by
    simp only [dedup]
    split
    · exact (dedup_sublist same (y :: rest)).cons x
    · exact (dedup_sublist same (y :: rest)).cons_cons x

/-- A pairwise strictly increasing list of values is `strictAsc`. -/
theorem strictAsc_of_pairwise :
    ∀ xs : List Value, xs.Pairwise (fun a b => cmp a b = .lt) → strictAsc xs = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    have h' := List.pairwise_cons.1 h
    simp only [strictAsc, Bool.and_eq_true, beq_iff_eq]
    exact ⟨h'.1 b (by simp), strictAsc_of_pairwise (b :: rest) h'.2⟩

/-- On a key-sorted list, `dedup` leaves a key-increasing list. -/
theorem dedup_pairwise_lt {α : Type} (key : α → Value) :
    ∀ l : List α, l.Pairwise (fun x y => cmp (key x) (key y) ≠ .gt) →
      (dedup (sameBy key) l).Pairwise (fun x y => cmp (key x) (key y) = .lt)
  | [], _ => by simp [dedup]
  | [x], _ => by simp [dedup]
  | x :: y :: rest, h => by
    have h' := List.pairwise_cons.1 h
    have ih := dedup_pairwise_lt key (y :: rest) h'.2
    have h'' := List.pairwise_cons.1 h'.2
    simp only [dedup]
    split
    · exact ih
    · rename_i hs
      refine List.pairwise_cons.2 ⟨?_, ih⟩
      have hxy : cmp (key x) (key y) = .lt := by
        have hle := h'.1 y (by simp)
        simp only [sameBy, beq_iff_eq] at hs
        cases e : cmp (key x) (key y)
        · rfl
        · exact absurd e (by simpa using hs)
        · exact absurd e hle
      intro z hz
      have hz' := (dedup_sublist (sameBy key) (y :: rest)).subset hz
      rcases List.mem_cons.1 hz' with rfl | hz'
      · exact hxy
      · exact cmp_lt_of_lt_of_le hxy (h''.1 z hz')

/-- `dedup` does nothing to a key-increasing list. -/
theorem dedup_of_pairwise_lt {α : Type} (key : α → Value) :
    ∀ l : List α, l.Pairwise (fun x y => cmp (key x) (key y) = .lt) →
      dedup (sameBy key) l = l
  | [], _ => by simp [dedup]
  | [x], _ => by simp [dedup]
  | x :: y :: rest, h => by
    have h' := List.pairwise_cons.1 h
    have hxy := h'.1 y (by simp)
    have hs : sameBy key x y = false := by simp [sameBy, hxy]
    simp only [dedup, hs, Bool.false_eq_true, ↓reduceIte]
    rw [dedup_of_pairwise_lt key (y :: rest) h'.2]

/-- Membership in `dedup` of a key-sorted list: the element has no later element with
the same key. -/
theorem mem_dedup_imp {α : Type} (key : α → Value) :
    ∀ (l : List α) (x : α), l.Pairwise (fun x y => cmp (key x) (key y) ≠ .gt) →
      x ∈ dedup (sameBy key) l →
      ∃ pre post, l = pre ++ x :: post ∧ ∀ y ∈ post, cmp (key x) (key y) ≠ .eq
  | [], x, _, hx => by simp [dedup] at hx
  | [x'], x, _, hx => by
    simp only [dedup, List.mem_singleton] at hx
    subst hx
    exact ⟨[], [], rfl, by simp⟩
  | a :: b :: rest, x, h, hx => by
    have h' := List.pairwise_cons.1 h
    have h'' := List.pairwise_cons.1 h'.2
    simp only [dedup] at hx
    split at hx
    · obtain ⟨pre, post, hl, hp⟩ := mem_dedup_imp key (b :: rest) x h'.2 hx
      exact ⟨a :: pre, post, by simp [hl], hp⟩
    · rename_i hs
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨[], b :: rest, rfl, ?_⟩
        have hab : cmp (key x) (key b) = .lt := by
          have hle := h'.1 b (by simp)
          simp only [sameBy, beq_iff_eq] at hs
          cases e : cmp (key x) (key b)
          · rfl
          · exact absurd e (by simpa using hs)
          · exact absurd e hle
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · rw [hab]; decide
        · rw [cmp_lt_of_lt_of_le hab (h''.1 y hy)]; decide
      · obtain ⟨pre, post, hl, hp⟩ := mem_dedup_imp key (b :: rest) x h'.2 hx
        exact ⟨a :: pre, post, by simp [hl], hp⟩

/-- Converse of `mem_dedup_imp`, valid for any list: an element with no later element of
the same key survives `dedup`. -/
theorem mem_dedup_of_decomp {α : Type} (key : α → Value) :
    ∀ (pre : List α) (x : α) (post : List α), (∀ y ∈ post, cmp (key x) (key y) ≠ .eq) →
      x ∈ dedup (sameBy key) (pre ++ x :: post)
  | [], x, [], _ => by simp [dedup]
  | [], x, y :: rest, h => by
    have hs : sameBy key x y = false := by
      have := h y (by simp)
      simp [sameBy, this]
    simp [dedup, hs]
  | p :: pre, x, post, h => by
    have ih := mem_dedup_of_decomp key pre x post h
    cases hl : pre ++ x :: post with
    | nil => simp at hl
    | cons z rest =>
      rw [hl] at ih
      simp only [List.cons_append, hl, dedup]
      split <;> simp [ih]

/-! ### Sets -/

/-- `normalizeSet` is `dedup` of the sorted list. -/
theorem normalizeSet_eq (xs : List Value) :
    Lenient.normalizeSet xs = dedup (sameBy id) (xs.mergeSort Lenient.keyLe) :=
  dedupLast_nil _ _

/-- The normalised set is a sub-list of the sorted input. -/
theorem normalizeSet_sublist (xs : List Value) :
    List.Sublist (Lenient.normalizeSet xs) (xs.mergeSort Lenient.keyLe) := by
  rw [normalizeSet_eq]
  exact dedup_sublist _ _

/-- Every element of the normalised set was in the input. -/
theorem normalizeSet_subset (xs : List Value) : ∀ y ∈ Lenient.normalizeSet xs, y ∈ xs := by
  intro y hy
  have := (normalizeSet_sublist xs).subset hy
  exact List.mem_mergeSort.1 this

/-- Normalising does not lengthen a set. -/
theorem normalizeSet_length (xs : List Value) : (Lenient.normalizeSet xs).length ≤ xs.length := by
  have := (normalizeSet_sublist xs).length_le
  simpa using this

/-- The elements of a normalised set are strictly ascending. -/
theorem normalizeSet_strictAsc' (xs : List Value) :
    Value.strictAsc (Lenient.normalizeSet xs) = true := by
  rw [normalizeSet_eq]
  apply strictAsc_of_pairwise
  exact dedup_pairwise_lt id _ (sorted_set xs)

/-- Normalising a set neither adds nor drops an element. -/
theorem normalizeSet_mem_iff' (xs : List Value) (x : Value) :
    x ∈ Lenient.normalizeSet xs ↔ x ∈ xs := by
  constructor
  · exact normalizeSet_subset xs x
  · intro hx
    rw [normalizeSet_eq]
    have hx' : x ∈ (xs.mergeSort Lenient.keyLe).reverse := by
      simpa using (List.mem_mergeSort (le := Lenient.keyLe)).2 hx
    obtain ⟨a, b, hab, hna⟩ := List.eq_append_cons_of_mem hx'
    have hS : xs.mergeSort Lenient.keyLe = b.reverse ++ x :: a.reverse := by
      have := congrArg List.reverse hab
      simpa using this
    rw [hS]
    apply mem_dedup_of_decomp
    intro y hy hyx
    have : x = y := cmp_eq x y (by simpa [cmp_eq_iff'] using hyx) |> fun h => h
    subst this
    exact hna (by simpa using hy)

/-- A key-increasing set is its own normal form. -/
theorem normalizeSet_of_strictAsc (xs : List Value) (h : Value.strictAsc xs = true) :
    Lenient.normalizeSet xs = xs := by
  have hp := strictAsc_pairwise xs h
  have hmerge : xs.mergeSort Lenient.keyLe = xs := by
    apply List.mergeSort_of_pairwise
    refine hp.imp ?_
    intro a b hab
    exact keyLe_iff.2 (by rw [hab]; decide)
  rw [normalizeSet_eq, hmerge]
  exact dedup_of_pairwise_lt id xs hp

/-! ### Maps -/

/-- `normalizeMap` is `dedup` of the sorted list. -/
theorem normalizeMap_eq (kvs : List (Value × Value)) :
    Lenient.normalizeMap kvs =
      dedup (sameBy Prod.fst) (kvs.mergeSort fun a b => Lenient.keyLe a.1 b.1) :=
  dedupLast_nil _ _

/-- The normalised map is a sub-list of the sorted input. -/
theorem normalizeMap_sublist (kvs : List (Value × Value)) :
    List.Sublist (Lenient.normalizeMap kvs)
      (kvs.mergeSort fun a b => Lenient.keyLe a.1 b.1) := by
  rw [normalizeMap_eq]
  exact dedup_sublist _ _

/-- Every entry of the normalised map was in the input. -/
theorem normalizeMap_subset (kvs : List (Value × Value)) :
    ∀ e ∈ Lenient.normalizeMap kvs, e ∈ kvs := by
  intro y hy
  exact List.mem_mergeSort.1 ((normalizeMap_sublist kvs).subset hy)

/-- Normalising does not lengthen a map. -/
theorem normalizeMap_length (kvs : List (Value × Value)) :
    (Lenient.normalizeMap kvs).length ≤ kvs.length := by
  have := (normalizeMap_sublist kvs).length_le
  simpa using this

/-- The keys of a normalised map are strictly ascending. -/
theorem normalizeMap_strictAsc' (kvs : List (Value × Value)) :
    Value.strictAsc ((Lenient.normalizeMap kvs).map Prod.fst) = true := by
  rw [normalizeMap_eq]
  apply strictAsc_of_pairwise
  rw [List.pairwise_map]
  exact dedup_pairwise_lt Prod.fst _ (sorted_map kvs)

/-- A map whose keys are strictly ascending is its own normal form. -/
theorem normalizeMap_of_strictAsc (kvs : List (Value × Value))
    (h : Value.strictAsc (kvs.map Prod.fst) = true) : Lenient.normalizeMap kvs = kvs := by
  have hp := strictAsc_pairwise _ h
  rw [List.pairwise_map] at hp
  have hmerge : (kvs.mergeSort fun a b => Lenient.keyLe a.1 b.1) = kvs := by
    apply List.mergeSort_of_pairwise
    refine hp.imp ?_
    intro a b hab
    exact keyLe_iff.2 (by rw [hab]; decide)
  rw [normalizeMap_eq, hmerge]
  exact dedup_of_pairwise_lt Prod.fst kvs hp

/-- An entry is the last of its key in a list: no later entry has its key. -/
def LastKey (e : Value × Value) (l : List (Value × Value)) : Prop :=
  ∃ pre post, l = pre ++ e :: post ∧ ∀ e' ∈ post, e'.1 ≠ e.1

/-- Unfolding `LastKey` on a cons. -/
theorem lastKey_cons (e a : Value × Value) (t : List (Value × Value)) :
    LastKey e (a :: t) ↔ (a = e ∧ ∀ e' ∈ t, e'.1 ≠ e.1) ∨ LastKey e t := by
  constructor
  · rintro ⟨pre, post, hl, hp⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact .inl ⟨rfl, hp⟩
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact .inr ⟨pre, post, rfl, hp⟩
  · rintro (⟨rfl, hp⟩ | ⟨pre, post, hl, hp⟩)
    · exact ⟨[], t, rfl, hp⟩
    · exact ⟨a :: pre, post, by simp [hl], hp⟩

/-- `LastKey` in terms of the entries sharing the key. -/
theorem lastKey_iff_filter (e : Value × Value) :
    ∀ l : List (Value × Value),
      LastKey e l ↔ (l.filter fun x => cmp x.1 e.1 == .eq).getLast? = some e
  | [] => by simp [LastKey]
  | a :: t => by
    have ih := lastKey_iff_filter e t
    rw [lastKey_cons, ih, List.filter_cons]
    by_cases hp : (cmp a.1 e.1 == .eq) = true
    · simp only [hp, ↓reduceIte]
      by_cases hnil : (t.filter fun x => cmp x.1 e.1 == .eq) = []
      · have h1 : (a :: t.filter fun x => cmp x.1 e.1 == .eq).getLast? = some a := by
          rw [hnil]; rfl
        have h2 : (t.filter fun x => cmp x.1 e.1 == .eq).getLast? = none := by
          rw [hnil]; rfl
        rw [h1, h2]
        constructor
        · rintro (⟨h, -⟩ | h)
          · rw [h]
          · exact absurd h (by simp)
        · intro h
          have h' : a = e := Option.some.inj h
          refine .inl ⟨h', ?_⟩
          intro e' he' heq
          have := List.filter_eq_nil_iff.1 hnil e' he'
          exact this (by rw [heq]; simp [cmp_self])
      · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hnil
        have hx' := List.mem_filter.1 hx
        have hxe : x.1 = e.1 := cmp_eq _ _ (by simpa using hx'.2)
        have h1 : (a :: t.filter fun x => cmp x.1 e.1 == .eq).getLast? =
            (t.filter fun x => cmp x.1 e.1 == .eq).getLast? := by
          cases hF : (t.filter fun x => cmp x.1 e.1 == .eq) with
          | nil => exact absurd hF hnil
          | cons y ys => simp [List.getLast?_cons_cons]
        rw [h1]
        constructor
        · rintro (⟨-, h⟩ | h)
          · exact absurd hxe (h x hx'.1)
          · exact h
        · intro h
          exact .inr h
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨rfl, -⟩ | h)
        · simp [cmp_self] at hp
        · exact h
      · intro h
        exact .inr h

/-- The entries of a key class stay in input order under the stable sort. -/
theorem mergeSort_filter_key (kvs : List (Value × Value)) (k : Value) :
    (kvs.mergeSort fun a b => Lenient.keyLe a.1 b.1).filter (fun x => cmp x.1 k == .eq) =
      kvs.filter (fun x => cmp x.1 k == .eq) := by
  have hmem : ∀ x ∈ kvs.filter (fun x => cmp x.1 k == .eq), x.1 = k := by
    intro x hx
    exact cmp_eq _ _ (by simpa using (List.mem_filter.1 hx).2)
  have hys : (kvs.filter (fun x => cmp x.1 k == .eq)).Pairwise
      (fun a b => Lenient.keyLe a.1 b.1 = true) := by
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    rw [keyLe_iff, hmem a ha, hmem b hb, cmp_self]
    decide
  have hsub := List.sublist_mergeSort keyLe_fst_trans keyLe_fst_total hys
    (List.filter_sublist (p := fun x => cmp x.1 k == .eq) (l := kvs))
  have hsub' := List.Sublist.filter (fun x : Value × Value => cmp x.1 k == .eq) hsub
  rw [List.filter_eq_self.2 (fun a ha => by simpa using hmem a ha ▸ cmp_self a.1)] at hsub'
  have hlen := (List.Perm.filter (fun x : Value × Value => cmp x.1 k == .eq)
    (List.mergeSort_perm kvs (fun a b => Lenient.keyLe a.1 b.1))).length_eq
  exact (hsub'.eq_of_length hlen.symm).symm

/-- **Last entry wins.**  An entry survives `normalizeMap` exactly when no later entry
has the same key. -/
theorem normalizeMap_mem_iff' (kvs : List (Value × Value)) (e : Value × Value) :
    e ∈ Lenient.normalizeMap kvs ↔ LastKey e kvs := by
  have hS : LastKey e (kvs.mergeSort fun a b => Lenient.keyLe a.1 b.1) ↔ LastKey e kvs := by
    rw [lastKey_iff_filter, lastKey_iff_filter, mergeSort_filter_key]
  rw [← hS, normalizeMap_eq]
  constructor
  · intro h
    obtain ⟨pre, post, hl, hp⟩ := mem_dedup_imp Prod.fst _ e (sorted_map kvs) h
    refine ⟨pre, post, hl, fun e' he' heq => hp e' he' ?_⟩
    rw [heq]
    exact cmp_self _
  · rintro ⟨pre, post, hl, hp⟩
    rw [hl]
    apply mem_dedup_of_decomp
    intro y hy hyx
    exact hp y hy (cmp_eq _ _ hyx).symm

end RT

end BorshSpec
