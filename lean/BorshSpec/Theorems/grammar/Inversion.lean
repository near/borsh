import BorshSpec.Theorems.grammar.Leaf

/-!
# Helper lemmas: inverting the grammar

One lemma for each schema constructor, saying what `Encodes` means for it, and the
corresponding lemmas for the three list relations.  Also the agreement of the Boolean
size and order tests with their relational forms.
-/

namespace BorshSpec

namespace GrammarProof

mutual

theorem zeroSized_iff : (s : Schema) → (s.zeroSized = true ↔ SizeZero s)
  | .uint _ => by simp [Schema.zeroSized]; intro h; cases h
  | .sint _ => by simp [Schema.zeroSized]; intro h; cases h
  | .f32 => by simp [Schema.zeroSized]; intro h; cases h
  | .f64 => by simp [Schema.zeroSized]; intro h; cases h
  | .bool => by simp [Schema.zeroSized]; intro h; cases h
  | .string => by simp [Schema.zeroSized]; intro h; cases h
  | .option _ => by simp [Schema.zeroSized]; intro h; cases h
  | .vec _ => by simp [Schema.zeroSized]; intro h; cases h
  | .enum _ => by simp [Schema.zeroSized]; intro h; cases h
  | .map _ _ => by simp [Schema.zeroSized]; intro h; cases h
  | .set _ => by simp [Schema.zeroSized]; intro h; cases h
  | .array n s => by
    have ih := zeroSized_iff s
    simp only [Schema.zeroSized, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro (rfl | h)
      · exact .arrayEmpty s
      · exact .arrayElem n s (ih.1 h)
    · intro h
      cases h with
      | arrayEmpty => exact Or.inl rfl
      | arrayElem _ _ h => exact Or.inr (ih.2 h)
  | .tuple fs => by
    have ih := zeroSizedAll_iff fs
    simp only [Schema.zeroSized]
    exact ⟨fun h => .tuple fs (ih.1 h), fun h => by cases h with | tuple _ h => exact ih.2 h⟩

theorem zeroSizedAll_iff : (fs : List Schema) → (Schema.zeroSizedAll fs = true ↔ SizeZeroAll fs)
  | [] => by simp [Schema.zeroSizedAll]; exact .nil
  | s :: fs => by
    have ih := zeroSizedAll_iff fs
    have ih' := zeroSized_iff s
    simp only [Schema.zeroSizedAll, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact .cons s fs (ih'.1 h1) (ih.1 h2)
    · intro h
      cases h with
      | cons _ _ h1 h2 => exact ⟨ih'.2 h1, ih.2 h2⟩

end

theorem ascending_cons_cons (a b : Value) (rest : List Value) :
    Ascending (a :: b :: rest) ↔ Value.cmp a b = .lt ∧ Ascending (b :: rest) := by
  constructor
  · intro h
    cases h with
    | cons _ _ _ h1 h2 => exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact .cons a b rest h1 h2

theorem strictAsc_iff : (l : List Value) → (Value.strictAsc l = true ↔ Ascending l)
  | [] => by simp [Value.strictAsc]; exact .nil
  | [a] => by simp [Value.strictAsc]; exact .single a
  | a :: b :: rest => by
    have ih := strictAsc_iff (b :: rest)
    rw [Value.strictAsc, ascending_cons_cons]
    simp [ih]

theorem variantAt_nil (i : Nat) (tag : UInt8) (s : Schema) : ¬ VariantAt [] i tag s := by
  intro h; cases h

theorem variantAt_zero (t : UInt8) (s' : Schema) (rest : List (UInt8 × Schema)) (tag : UInt8)
    (s : Schema) : VariantAt ((t, s') :: rest) 0 tag s ↔ tag = t ∧ s = s' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .here _ _ _

theorem variantAt_succ (t : UInt8) (s' : Schema) (rest : List (UInt8 × Schema)) (i : Nat)
    (tag : UInt8) (s : Schema) :
    VariantAt ((t, s') :: rest) (i + 1) tag s ↔ t ≠ tag ∧ VariantAt rest i tag s := by
  constructor
  · intro h
    cases h with
    | there _ _ _ _ _ _ h1 h2 => exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact .there _ _ _ _ _ _ h1 h2

/-! ## What `Encodes` says for each schema constructor -/

theorem enc_uint (w : IntWidth) (v : Value) (bs : List UInt8) :
    Encodes (.uint w) v bs ↔ ∃ n, v = .uint n ∧ n < 256 ^ w.bytes ∧ bs = leBytes w.bytes n := by
  constructor
  · intro h
    cases h with
    | uint _ n h => exact ⟨n, rfl, h, rfl⟩
  · rintro ⟨n, rfl, h, rfl⟩
    exact .uint w n h

theorem enc_sint (w : IntWidth) (v : Value) (bs : List UInt8) :
    Encodes (.sint w) v bs ↔ ∃ i, v = .sint i ∧
      -((256 ^ w.bytes / 2 : Nat) : Int) ≤ i ∧ i < ((256 ^ w.bytes / 2 : Nat) : Int) ∧
      bs = leBytes w.bytes (twosComplement w.bytes i) := by
  constructor
  · intro h
    cases h with
    | sint _ i h1 h2 => exact ⟨i, rfl, h1, h2, rfl⟩
  · rintro ⟨i, rfl, h1, h2, rfl⟩
    exact .sint w i h1 h2

theorem enc_f32 (v : Value) (bs : List UInt8) :
    Encodes .f32 v bs ↔ ∃ bits, v = .f32 bits ∧ ¬ IsNaN32 bits ∧ bs = leBytes 4 bits.toNat := by
  constructor
  · intro h
    cases h with
    | f32 bits h => exact ⟨bits, rfl, h, rfl⟩
  · rintro ⟨bits, rfl, h, rfl⟩
    exact .f32 bits h

theorem enc_f64 (v : Value) (bs : List UInt8) :
    Encodes .f64 v bs ↔ ∃ bits, v = .f64 bits ∧ ¬ IsNaN64 bits ∧ bs = leBytes 8 bits.toNat := by
  constructor
  · intro h
    cases h with
    | f64 bits h => exact ⟨bits, rfl, h, rfl⟩
  · rintro ⟨bits, rfl, h, rfl⟩
    exact .f64 bits h

theorem enc_bool (v : Value) (bs : List UInt8) :
    Encodes .bool v bs ↔ ∃ b, v = .bool b ∧ bs = [if b then 1 else 0] := by
  constructor
  · intro h
    cases h with
    | boolFalse => exact ⟨false, rfl, rfl⟩
    | boolTrue => exact ⟨true, rfl, rfl⟩
  · rintro ⟨b, rfl, rfl⟩
    cases b
    · exact .boolFalse
    · exact .boolTrue

theorem enc_string (v : Value) (bs : List UInt8) :
    Encodes .string v bs ↔ ∃ body, v = .string body ∧ WellFormedUtf8 body ∧
      body.length < 2 ^ 32 ∧ bs = leBytes 4 body.length ++ body := by
  constructor
  · intro h
    cases h with
    | string body h1 h2 => exact ⟨body, rfl, h1, h2, rfl⟩
  · rintro ⟨body, rfl, h1, h2, rfl⟩
    exact .string body h1 h2

theorem enc_option (s : Schema) (v : Value) (bs : List UInt8) :
    Encodes (.option s) v bs ↔ (v = .optNone ∧ bs = [0]) ∨
      ∃ x b, v = .optSome x ∧ bs = 1 :: b ∧ Encodes s x b := by
  constructor
  · intro h
    cases h with
    | optNone => exact Or.inl ⟨rfl, rfl⟩
    | optSome _ x b h => exact Or.inr ⟨x, b, rfl, rfl, h⟩
  · rintro (⟨rfl, rfl⟩ | ⟨x, b, rfl, rfl, h⟩)
    · exact .optNone s
    · exact .optSome s x b h

theorem enc_vec (s : Schema) (v : Value) (bs : List UInt8) :
    Encodes (.vec s) v bs ↔ ∃ xs b, v = .vec xs ∧ bs = leBytes 4 xs.length ++ b ∧
      ¬ SizeZero s ∧ xs.length < 2 ^ 32 ∧ EncodesAll s xs b := by
  constructor
  · intro h
    cases h with
    | vec _ xs b h1 h2 h3 => exact ⟨xs, b, rfl, rfl, h1, h2, h3⟩
  · rintro ⟨xs, b, rfl, rfl, h1, h2, h3⟩
    exact .vec s xs b h1 h2 h3

theorem enc_array (n : Nat) (s : Schema) (v : Value) (bs : List UInt8) :
    Encodes (.array n s) v bs ↔ ∃ xs, v = .array xs ∧ xs.length = n ∧ EncodesAll s xs bs := by
  constructor
  · intro h
    cases h with
    | array _ _ xs _ h1 h2 => exact ⟨xs, rfl, h1, h2⟩
  · rintro ⟨xs, rfl, h1, h2⟩
    exact .array n s xs bs h1 h2

theorem enc_tuple (fs : List Schema) (v : Value) (bs : List UInt8) :
    Encodes (.tuple fs) v bs ↔ ∃ xs, v = .tuple xs ∧ EncodesFields fs xs bs := by
  constructor
  · intro h
    cases h with
    | tuple _ xs _ h => exact ⟨xs, rfl, h⟩
  · rintro ⟨xs, rfl, h⟩
    exact .tuple fs xs bs h

theorem enc_enum (vs : List (UInt8 × Schema)) (v : Value) (bs : List UInt8) :
    Encodes (.enum vs) v bs ↔ ∃ i tag s x b, v = .enum i x ∧ bs = tag :: b ∧
      VariantAt vs i tag s ∧ Encodes s x b := by
  constructor
  · intro h
    cases h with
    | enum _ i tag s x b h1 h2 => exact ⟨i, tag, s, x, b, rfl, rfl, h1, h2⟩
  · rintro ⟨i, tag, s, x, b, rfl, rfl, h1, h2⟩
    exact .enum vs i tag s x b h1 h2

theorem enc_map (k w : Schema) (v : Value) (bs : List UInt8) :
    Encodes (.map k w) v bs ↔ ∃ kvs b, v = .map kvs ∧ bs = leBytes 4 kvs.length ++ b ∧
      ¬ SizeZero k ∧ kvs.length < 2 ^ 32 ∧ Ascending (kvs.map Prod.fst) ∧
      EncodesPairs k w kvs b := by
  constructor
  · intro h
    cases h with
    | map _ _ kvs b h1 h2 h3 h4 => exact ⟨kvs, b, rfl, rfl, h1, h2, h3, h4⟩
  · rintro ⟨kvs, b, rfl, rfl, h1, h2, h3, h4⟩
    exact .map k w kvs b h1 h2 h3 h4

theorem enc_set (s : Schema) (v : Value) (bs : List UInt8) :
    Encodes (.set s) v bs ↔ ∃ xs b, v = .set xs ∧ bs = leBytes 4 xs.length ++ b ∧
      ¬ SizeZero s ∧ xs.length < 2 ^ 32 ∧ Ascending xs ∧ EncodesAll s xs b := by
  constructor
  · intro h
    cases h with
    | set _ xs b h1 h2 h3 h4 => exact ⟨xs, b, rfl, rfl, h1, h2, h3, h4⟩
  · rintro ⟨xs, b, rfl, rfl, h1, h2, h3, h4⟩
    exact .set s xs b h1 h2 h3 h4

/-! ## The list relations -/

theorem all_nil (s : Schema) (bs : List UInt8) : EncodesAll s [] bs ↔ bs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil s

theorem all_cons (s : Schema) (x : Value) (xs : List Value) (bs : List UInt8) :
    EncodesAll s (x :: xs) bs ↔ ∃ b bs', bs = b ++ bs' ∧ Encodes s x b ∧ EncodesAll s xs bs' := by
  constructor
  · intro h
    cases h with
    | cons _ _ _ b bs' h1 h2 => exact ⟨b, bs', rfl, h1, h2⟩
  · rintro ⟨b, bs', rfl, h1, h2⟩
    exact .cons s x xs b bs' h1 h2

theorem fields_nil (vs : List Value) (bs : List UInt8) :
    EncodesFields [] vs bs ↔ vs = [] ∧ bs = [] := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil

theorem fields_cons (s : Schema) (fs : List Schema) (vs : List Value) (bs : List UInt8) :
    EncodesFields (s :: fs) vs bs ↔ ∃ x xs b bs', vs = x :: xs ∧ bs = b ++ bs' ∧
      Encodes s x b ∧ EncodesFields fs xs bs' := by
  constructor
  · intro h
    cases h with
    | cons _ _ x xs b bs' h1 h2 => exact ⟨x, xs, b, bs', rfl, rfl, h1, h2⟩
  · rintro ⟨x, xs, b, bs', rfl, rfl, h1, h2⟩
    exact .cons s fs x xs b bs' h1 h2

theorem pairs_nil (k w : Schema) (bs : List UInt8) : EncodesPairs k w [] bs ↔ bs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil k w

theorem pairs_cons (k w : Schema) (a c : Value) (kvs : List (Value × Value)) (bs : List UInt8) :
    EncodesPairs k w ((a, c) :: kvs) bs ↔ ∃ bk bv bs', bs = bk ++ bv ++ bs' ∧
      Encodes k a bk ∧ Encodes w c bv ∧ EncodesPairs k w kvs bs' := by
  constructor
  · intro h
    cases h with
    | cons _ _ _ _ _ bk bv bs' h1 h2 h3 => exact ⟨bk, bv, bs', rfl, h1, h2, h3⟩
  · rintro ⟨bk, bv, bs', rfl, h1, h2, h3⟩
    exact .cons k w a c kvs bk bv bs' h1 h2 h3

end GrammarProof

end BorshSpec
