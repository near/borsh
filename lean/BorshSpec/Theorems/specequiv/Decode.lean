import BorshSpec

/-!
# `Spec.decode` equals `decode`

Proof helpers for `BorshSpec.Theorems.SpecEquiv`.  The two decoders have the same
recursion; they differ in how `decodeN` and `decodeMany` build lists, in
`do`-notation versus `match`, and in where the strict key check happens.
-/

namespace BorshSpec.SpecEquiv

open Schema

/-- The accumulating loop `decodeMany` is `decodeN` with the accumulator reversed in
front. -/
theorem decodeMany_eq {α : Type} (d : List UInt8 → Option (α × List UInt8)) (n : Nat) :
    ∀ (acc : List α) (bs : List UInt8),
    decodeMany d n acc bs =
      (Spec.decodeN d n bs).map fun p => (acc.reverse ++ p.1, p.2) := by
  induction n with
  | zero => intro acc bs; simp [decodeMany, Spec.decodeN]
  | succ n ih =>
    intro acc bs
    simp only [decodeMany, Spec.decodeN]
    cases hd : d bs with
    | none => simp
    | some p =>
      obtain ⟨x, r⟩ := p
      simp only [ih]
      cases hn : Spec.decodeN d n r with
      | none => simp [hn]
      | some q => simp [hn]

theorem decodeMany_nil {α : Type} (d : List UInt8 → Option (α × List UInt8)) (n : Nat)
    (bs : List UInt8) : decodeMany d n [] bs = Spec.decodeN d n bs := by
  rw [decodeMany_eq]
  cases Spec.decodeN d n bs <;> simp

/-- `decodeN` only depends on the extensional behaviour of its step. -/
theorem decodeN_congr {α : Type} {d₁ d₂ : List UInt8 → Option (α × List UInt8)}
    (h : ∀ bs, d₁ bs = d₂ bs) (n : Nat) (bs : List UInt8) :
    Spec.decodeN d₁ n bs = Spec.decodeN d₂ n bs := by
  have : d₁ = d₂ := funext h
  rw [this]

theorem strict_map (kvs : List (Value × Value)) :
    KeyPolicy.strict.map kvs =
      if Value.strictAsc (kvs.map Prod.fst) then some kvs else none := rfl

theorem strict_set (xs : List Value) :
    KeyPolicy.strict.set xs = if Value.strictAsc xs then some xs else none := rfl

mutual

theorem decode_eq : ∀ (s : Schema) (bs : List UInt8),
    Spec.decode s bs = decodeWith KeyPolicy.strict s bs
  | .uint w, bs => by
    simp only [Spec.decode, decodeWith]
    cases readLE w.bytes bs <;> rfl
  | .sint w, bs => by
    simp only [Spec.decode, decodeWith]
    cases readLE w.bytes bs <;> rfl
  | .f32, bs => by
    simp only [Spec.decode, decodeWith]
    cases readLE 4 bs <;> simp
  | .f64, bs => by
    simp only [Spec.decode, decodeWith]
    cases readLE 8 bs <;> simp
  | .bool, [] => by simp [Spec.decode, decodeWith]
  | .bool, b :: r => by
    by_cases h0 : b = 0
    · subst h0; simp [Spec.decode, decodeWith]
    · by_cases h1 : b = 1
      · subst h1; simp [Spec.decode, decodeWith]
      · simp [Spec.decode, decodeWith, h0, h1]
  | .string, bs => by
    simp only [Spec.decode, decodeWith]
    rcases Schema.readU32 bs with _ | ⟨n, r⟩
    · simp
    · rcases ht : takeExact n r with _ | ⟨body, r'⟩
      · simp [ht]
      · by_cases h : validUtf8 body = true <;> simp [ht, h]
  | .option _, [] => by simp [Spec.decode, decodeWith]
  | .option s, b :: r => by
    by_cases h0 : b = 0
    · subst h0; simp [Spec.decode, decodeWith]
    · by_cases h1 : b = 1
      · subst h1
        simp only [Spec.decode, decodeWith, decode_eq s r]
        cases decodeWith KeyPolicy.strict s r <;> simp
      · simp [Spec.decode, decodeWith, h0, h1]
  | .vec s, bs => by
    simp only [Spec.decode, decodeWith]
    by_cases hz : s.zeroSized = true
    · simp [hz]
    · simp only [hz]
      rcases Schema.readU32 bs with _ | ⟨n, r⟩
      · simp
      · have hf : ∀ b, decodeWith KeyPolicy.strict s b = Spec.decode s b :=
          fun b => (decode_eq s b).symm
        simp only [decodeMany_nil, decodeN_congr hf]
        rcases hd : Spec.decodeN (Spec.decode s) n r with _ | ⟨xs, r'⟩ <;> simp [hd]
  | .array n s, bs => by
    simp only [Spec.decode, decodeWith]
    have hf : ∀ b, decodeWith KeyPolicy.strict s b = Spec.decode s b :=
      fun b => (decode_eq s b).symm
    simp only [decodeMany_nil, decodeN_congr hf]
    cases Spec.decodeN (Spec.decode s) n bs <;> rfl
  | .tuple fs, bs => by
    simp only [Spec.decode, decodeWith]
    rw [decodeFields_eq fs bs]
    cases decodeFieldsWith KeyPolicy.strict fs bs <;> rfl
  | .enum _, [] => by simp [Spec.decode, decodeWith]
  | .enum vs, t :: r => by
    simp only [Spec.decode, decodeWith]
    exact decodeVariant_eq vs 0 t r
  | .map k v, bs => by
    simp only [Spec.decode, decodeWith]
    by_cases hz : k.zeroSized = true
    · simp [hz]
    · simp only [hz]
      rcases Schema.readU32 bs with _ | ⟨n, r⟩
      · simp
      · have hf : ∀ b, (do
              let (key, afterKey) ← Spec.decode k b
              let (value, afterValue) ← Spec.decode v afterKey
              pure ((key, value), afterValue)) =
            (match decodeWith KeyPolicy.strict k b with
              | none => none
              | some (a, r₁) =>
                match decodeWith KeyPolicy.strict v r₁ with
                | none => none
                | some (c, r₂) => some ((a, c), r₂)) := by
          intro b
          rw [decode_eq k b]
          rcases decodeWith KeyPolicy.strict k b with _ | ⟨a, r₁⟩
          · rfl
          · simp only [Bind.bind, Option.bind]
            rw [decode_eq v r₁]
            rcases decodeWith KeyPolicy.strict v r₁ with _ | ⟨c, r₂⟩ <;> rfl
        simp only [decodeMany_nil, decodeN_congr hf]
        rcases hd : Spec.decodeN (fun b =>
            match decodeWith KeyPolicy.strict k b with
            | none => none
            | some (a, r₁) =>
              match decodeWith KeyPolicy.strict v r₁ with
              | none => none
              | some (c, r₂) => some ((a, c), r₂)) n r with _ | ⟨kvs, r'⟩
        · simp [hd]
        · by_cases hs : Value.strictAsc (kvs.map Prod.fst) = true
          · simp [hd, Spec.requireAscending, strict_map, hs]
          · simp [hd, Spec.requireAscending, strict_map, hs]
  | .set s, bs => by
    simp only [Spec.decode, decodeWith]
    by_cases hz : s.zeroSized = true
    · simp [hz]
    · simp only [hz]
      rcases Schema.readU32 bs with _ | ⟨n, r⟩
      · simp
      · have hf : ∀ b, decodeWith KeyPolicy.strict s b = Spec.decode s b :=
          fun b => (decode_eq s b).symm
        simp only [decodeMany_nil, decodeN_congr hf]
        rcases hd : Spec.decodeN (Spec.decode s) n r with _ | ⟨xs, r'⟩
        · simp [hd]
        · by_cases hs : Value.strictAsc xs = true
          · simp [hd, Spec.requireAscending, strict_set, hs]
          · simp [hd, Spec.requireAscending, strict_set, hs]

theorem decodeFields_eq : ∀ (fs : List Schema) (bs : List UInt8),
    Spec.decodeFields fs bs = decodeFieldsWith KeyPolicy.strict fs bs
  | [], bs => by simp [Spec.decodeFields, decodeFieldsWith]
  | s :: fs, bs => by
    simp only [Spec.decodeFields, decodeFieldsWith]
    rw [decode_eq s bs]
    rcases decodeWith KeyPolicy.strict s bs with _ | ⟨v, r⟩
    · rfl
    · simp only [Bind.bind, Option.bind]
      rw [decodeFields_eq fs r]
      rcases decodeFieldsWith KeyPolicy.strict fs r with _ | ⟨vs, r'⟩ <;> rfl

theorem decodeVariant_eq : ∀ (vs : List (UInt8 × Schema)) (i : Nat) (t : UInt8)
    (bs : List UInt8),
    Spec.decodeVariant vs i t bs = decodeVariantWith KeyPolicy.strict vs i t bs
  | [], _, _, _ => by simp [Spec.decodeVariant, decodeVariantWith]
  | (t', s) :: vs, i, t, bs => by
    simp only [Spec.decodeVariant, decodeVariantWith]
    by_cases h : (t' == t) = true
    · simp only [h, ite_true]
      rw [decode_eq s bs]
      rcases decodeWith KeyPolicy.strict s bs with _ | ⟨v, r⟩ <;> rfl
    · simp only [h]
      exact decodeVariant_eq vs (i + 1) t bs

end

end BorshSpec.SpecEquiv
