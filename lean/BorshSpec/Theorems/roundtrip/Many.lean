import BorshSpec.Theorems.roundtrip.Bytes

/-!
# Repeated decoding

Lemmas about `Schema.decodeMany` (the loop behind `vec`, `set`, `map` and `array`) and
about `List.mapM` in `Option`, which `encode` uses for the same collections.  They are
stated for an arbitrary element decoder `d` and element encoder `e`, so that the
three collection forms and the map entries share one proof.
-/

namespace BorshSpec

namespace RT

open Schema

/-- The accumulator of `decodeMany` is just prepended (reversed) to the result. -/
theorem decodeMany_acc {α : Type} (d : List UInt8 → Option (α × List UInt8)) :
    ∀ (n : Nat) (acc : List α) (bs : List UInt8),
      decodeMany d n acc bs =
        (decodeMany d n [] bs).map fun (xs, r) => (acc.reverse ++ xs, r)
  | 0, acc, bs => by simp [decodeMany]
  | n + 1, acc, bs => by
    unfold decodeMany
    cases hd : d bs with
    | none => simp
    | some p =>
      obtain ⟨x, r⟩ := p
      simp only [decodeMany_acc d n (x :: acc) r, decodeMany_acc d n [x] r]
      cases decodeMany d n [] r <;> simp

/-- If `e` encodes elements so that `d` reads them back, then `decodeMany` reads back
a list encoded by `mapM e`, given the right count. -/
theorem decodeMany_complete {α : Type} (d : List UInt8 → Option (α × List UInt8))
    (e : α → Option (List UInt8))
    (hd : ∀ x p, e x = some p → ∀ rest, d (p ++ rest) = some (x, rest)) :
    ∀ (xs : List α) (es : List (List UInt8)), xs.mapM e = some es →
      ∀ rest, decodeMany d xs.length [] (es.flatten ++ rest) = some (xs, rest)
  | [], es, h, rest => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp [decodeMany]
  | x :: xs, es, h, rest => by
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨p, hp, es', hes', rfl⟩ := h
    have ih := decodeMany_complete d e hd xs es' hes' rest
    simp only [List.length_cons, decodeMany, List.flatten_cons, List.append_assoc,
      hd x p hp (es'.flatten ++ rest), decodeMany_acc d xs.length [x],
      ih]
    simp

/-- Conversely, whatever `decodeMany` reads was produced by `e` on the consumed bytes,
element by element, and has the requested length.  The byte equation is only claimed
under the hypothesis `E`. -/
theorem decodeMany_sound {α : Type} (d : List UInt8 → Option (α × List UInt8))
    (e : α → Option (List UInt8)) (E : Prop)
    (hd : ∀ b x r, d b = some (x, r) → ∃ p, e x = some p ∧ (E → b = p ++ r)) :
    ∀ (n : Nat) (bs : List UInt8) (xs : List α) (r : List UInt8),
      decodeMany d n [] bs = some (xs, r) →
        xs.length = n ∧ (∀ x ∈ xs, ∃ p, e x = some p) ∧
          (E → ∃ es, xs.mapM e = some es ∧ bs = es.flatten ++ r)
  | 0, bs, xs, r, h => by
    simp only [decodeMany, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, bs, xs, r, h => by
    unfold decodeMany at h
    cases hdb : d bs with
    | none => simp [hdb] at h
    | some p =>
      obtain ⟨x, r₁⟩ := p
      rw [hdb] at h
      simp only [decodeMany_acc d n [x] r₁] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨ys, r₂⟩, hy, hxs⟩ := h
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        Prod.mk.injEq] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain ⟨hlen, hP, hb⟩ := decodeMany_sound d e E hd n r₁ ys r₂ hy
      obtain ⟨p, hep, hbs⟩ := hd bs x r₁ hdb
      refine ⟨by simp [hlen], ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨p, hep⟩
        · exact hP z hz
      · intro hE
        obtain ⟨es, hes, hb'⟩ := hb hE
        refine ⟨p :: es, ?_, ?_⟩
        · simp [List.mapM_cons, hep, hes, bind, pure]
        · simp [hbs hE, hb']

/-- If every element has an encoding, `mapM` produces all of them. -/
theorem mapM_isSome {α : Type} (e : α → Option (List UInt8)) :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ p, e x = some p) → ∃ es, xs.mapM e = some es
  | [], _ => ⟨[], by simp [List.mapM_nil, pure]⟩
  | x :: xs, h => by
    obtain ⟨p, hp⟩ := h x (List.mem_cons_self ..)
    obtain ⟨es, hes⟩ := mapM_isSome e xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact ⟨p :: es, by simp [List.mapM_cons, hp, hes, bind, pure]⟩

/-- Conversely, if `mapM` succeeds then every element has an encoding. -/
theorem mapM_forall {α : Type} (e : α → Option (List UInt8)) :
    ∀ (xs : List α) (es : List (List UInt8)), xs.mapM e = some es →
      ∀ x ∈ xs, ∃ p, e x = some p
  | [], _, _, x, hx => by simp at hx
  | y :: xs, es, h, x, hx => by
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨p, hp, es', hes', rfl⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨p, hp⟩
    · exact mapM_forall e xs es' hes' x hx

/-- Every iteration of the loop consumes at least `m` bytes, so `n` iterations consume
at least `n * m`. -/
theorem decodeMany_length {α : Type} (d : List UInt8 → Option (α × List UInt8)) (m : Nat)
    (hd : ∀ b x r, d b = some (x, r) → m + r.length ≤ b.length) :
    ∀ (n : Nat) (acc : List α) (bs : List UInt8) (xs : List α) (r : List UInt8),
      decodeMany d n acc bs = some (xs, r) → n * m + r.length ≤ bs.length
  | 0, acc, bs, xs, r, h => by
    simp only [decodeMany, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp
  | n + 1, acc, bs, xs, r, h => by
    unfold decodeMany at h
    cases hdb : d bs with
    | none => simp [hdb] at h
    | some p =>
      obtain ⟨x, r₁⟩ := p
      rw [hdb] at h
      have h1 := decodeMany_length d m hd n (x :: acc) r₁ xs r h
      have h2 := hd bs x r₁ hdb
      rw [Nat.succ_mul]
      omega

/-- Mapping the results of an element decoder maps the results of the loop.  The
accumulators must correspond. -/
theorem decodeMany_map {α β : Type} (d₁ : List UInt8 → Option (α × List UInt8))
    (d₂ : List UInt8 → Option (β × List UInt8)) (f : α → β)
    (hd : ∀ b, d₂ b = (d₁ b).map fun (x, r) => (f x, r)) :
    ∀ (n : Nat) (acc : List α) (bs : List UInt8),
      decodeMany d₂ n (acc.map f) bs =
        (decodeMany d₁ n acc bs).map fun (xs, r) => (xs.map f, r)
  | 0, acc, bs => by simp [decodeMany, List.map_reverse]
  | n + 1, acc, bs => by
    unfold decodeMany
    rw [hd bs]
    cases d₁ bs with
    | none => simp
    | some p =>
      obtain ⟨x, r⟩ := p
      simpa using decodeMany_map d₁ d₂ f hd n (x :: acc) r

/-- Monotonicity of the loop in the element decoder: whatever `d₁` reads, `d₂` reads. -/
theorem decodeMany_mono {α : Type} (d₁ d₂ : List UInt8 → Option (α × List UInt8))
    (hd : ∀ b r, d₁ b = some r → d₂ b = some r) :
    ∀ (n : Nat) (acc : List α) (bs : List UInt8) (r : List α × List UInt8),
      decodeMany d₁ n acc bs = some r → decodeMany d₂ n acc bs = some r
  | 0, acc, bs, r, h => by simpa [decodeMany] using h
  | n + 1, acc, bs, r, h => by
    unfold decodeMany at h ⊢
    cases hdb : d₁ bs with
    | none => simp [hdb] at h
    | some p =>
      obtain ⟨x, r₁⟩ := p
      rw [hdb] at h
      rw [hd bs _ hdb]
      exact decodeMany_mono d₁ d₂ hd n _ r₁ r h

end RT

end BorshSpec
