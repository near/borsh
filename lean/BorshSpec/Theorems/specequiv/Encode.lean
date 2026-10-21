import BorshSpec

/-!
# `Spec.encode` equals `encode`

Proof helpers for `BorshSpec.Theorems.SpecEquiv`.  The two encoders have the same
recursion; the internal one uses `mapM` and `flatten` where the readable one uses
`encodeAll`, and checks the key order in the guard instead of in the `do` block.
-/

namespace BorshSpec.SpecEquiv

open Schema

/-- `encodeAll` is `mapM` followed by `flatten`. -/
theorem encodeAll_eq {α : Type} (enc : α → Option (List UInt8)) (xs : List α) :
    Spec.encodeAll enc xs = (xs.mapM enc).map List.flatten := by
  induction xs with
  | nil => simp [Spec.encodeAll]
  | cons x xs ih =>
    simp only [Spec.encodeAll, List.mapM_cons, ih]
    cases enc x with
    | none => simp
    | some b =>
      cases xs.mapM enc <;> simp

/-- Prefixing the concatenation of an optional list of byte lists. -/
theorem prefix_flatten (p : List UInt8) (o : Option (List (List UInt8))) :
    (Option.map List.flatten o).bind (fun body => some (p ++ body)) =
      Option.map ((fun x => p ++ x) ∘ List.flatten) o := by
  cases o <;> rfl

mutual

theorem encode_eq : ∀ (s : Schema) (v : Value),
    Spec.encode s v = Schema.encode s v
  | .uint w, v => by cases v <;> simp [Spec.encode, Schema.encode]
  | .sint w, v => by cases v <;> simp [Spec.encode, Schema.encode]
  | .f32, v => by cases v <;> simp [Spec.encode, Schema.encode]
  | .f64, v => by cases v <;> simp [Spec.encode, Schema.encode]
  | .bool, v => by cases v <;> simp [Spec.encode, Schema.encode]
  | .string, v => by cases v <;> simp [Spec.encode, Schema.encode, Spec.u32Prefix]
  | .option s, v => by
    cases v <;> simp only [Spec.encode, Schema.encode] <;> try rfl
    rename_i v
    rw [encode_eq s v]
    cases Schema.encode s v <;> rfl
  | .vec s, v => by
    cases v <;> simp only [Spec.encode, Schema.encode] <;> try rfl
    rename_i xs
    by_cases hg : (s.zeroSized || decide (2 ^ 32 ≤ xs.length)) = true
    · simp only [hg, ite_true]
    · simp only [hg, ite_false, Bool.false_eq_true, Spec.u32Prefix]
      rw [show Spec.encode s = Schema.encode s from funext (encode_eq s), encodeAll_eq]
      cases Schema.encode s |> xs.mapM <;> rfl
  | .array n s, v => by
    cases v <;> simp only [Spec.encode, Schema.encode] <;> try rfl
    rename_i xs
    by_cases hg : (xs.length == n) = true
    · simp only [hg, ite_true]
      rw [show Spec.encode s = Schema.encode s from funext (encode_eq s), encodeAll_eq]
    · simp only [hg, ite_false, Bool.false_eq_true]
  | .tuple fs, v => by
    cases v <;> simp only [Spec.encode, Schema.encode] <;> try rfl
    rename_i xs
    exact encodeFields_eq fs xs
  | .enum vs, v => by
    cases v <;> simp only [Spec.encode, Schema.encode] <;> try rfl
    rename_i i v
    exact encodeVariant_eq vs [] i v
  | .map k v, w => by
    cases w <;> simp only [Spec.encode, Schema.encode] <;> try rfl
    rename_i kvs
    by_cases g1 : (k.zeroSized || decide (2 ^ 32 ≤ kvs.length)) = true
    · simp [g1]
    · by_cases g2 : Value.strictAsc (kvs.map Prod.fst) = true
      · simp [g1, g2, Spec.requireAscending, Spec.u32Prefix, encodeAll_eq, prefix_flatten,
          show Spec.encode k = Schema.encode k from funext (encode_eq k),
          show Spec.encode v = Schema.encode v from funext (encode_eq v)]
      · simp [g1, g2, Spec.requireAscending]
  | .set s, v => by
    cases v <;> simp only [Spec.encode, Schema.encode] <;> try rfl
    rename_i xs
    by_cases g1 : (s.zeroSized || decide (2 ^ 32 ≤ xs.length)) = true
    · simp [g1]
    · by_cases g2 : Value.strictAsc xs = true
      · simp [g1, g2, Spec.requireAscending, Spec.u32Prefix, encodeAll_eq, prefix_flatten,
          show Spec.encode s = Schema.encode s from funext (encode_eq s)]
      · simp [g1, g2, Spec.requireAscending]

theorem encodeFields_eq : ∀ (fs : List Schema) (vs : List Value),
    Spec.encodeFields fs vs = Schema.encodeFields fs vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | s :: fs, v :: vs => by
    simp only [Spec.encodeFields, Schema.encodeFields]
    rw [encode_eq s v, encodeFields_eq fs vs]

theorem encodeVariant_eq : ∀ (vs : List (UInt8 × Schema)) (earlier : List UInt8) (i : Nat)
    (v : Value),
    Spec.encodeVariant vs earlier i v = Schema.encodeVariant vs earlier i v
  | [], _, _, _ => rfl
  | (t, s) :: vs, earlier, 0, v => by
    simp only [Spec.encodeVariant, Schema.encodeVariant]
    by_cases h : t ∈ earlier
    · simp [h]
    · simp only [List.contains_iff_mem, h, ite_false]
      rw [encode_eq s v]
      cases Schema.encode s v <;> rfl
  | (t, s) :: vs, earlier, i + 1, v => by
    simp only [Spec.encodeVariant, Schema.encodeVariant]
    exact encodeVariant_eq vs (t :: earlier) i v

end

end BorshSpec.SpecEquiv
