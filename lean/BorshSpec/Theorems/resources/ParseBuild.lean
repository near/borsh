import BorshSpec.Theorems.resources.ParseTokens

/-!
# The schema parser on printed text

Second and third stage of `parse_print` (`Theorems/Resources.lean`): the tokens of
a printed schema build the S-expression `sexpOf s`, and `toSchema` reads that
S-expression back as `s`.
-/

namespace BorshSpec

namespace Parse

open Schema in
mutual

/-- The S-expression of a schema. -/
def sexpOf : Schema → Sexp
  | .uint w => .atom (String.ofList ('u' :: (IntWidth.bits w).toList))
  | .sint w => .atom (String.ofList ('i' :: (IntWidth.bits w).toList))
  | .f32 => .atom "f32"
  | .f64 => .atom "f64"
  | .bool => .atom "bool"
  | .string => .atom "string"
  | .option s => .list [.atom "option", sexpOf s]
  | .vec s => .list [.atom "vec", sexpOf s]
  | .array n s => .list [.atom "array", .atom (toString n), sexpOf s]
  | .tuple [] => .atom "unit"
  | .tuple (f :: fs) => .list (.atom "tuple" :: sexpsOf (f :: fs))
  | .enum vs => .list (.atom "enum" :: variantsOf vs)
  | .map k v => .list [.atom "map", sexpOf k, sexpOf v]
  | .set s => .list [.atom "set", sexpOf s]

/-- The S-expressions of the fields of a tuple. -/
def sexpsOf : List Schema → List Sexp
  | [] => []
  | s :: fs => sexpOf s :: sexpsOf fs

/-- The S-expressions of the variants of an enum. -/
def variantsOf : List (UInt8 × Schema) → List Sexp
  | [] => []
  | (t, s) :: vs => .list [.atom (toString t.toNat), sexpOf s] :: variantsOf vs

end

/-! ### Stage two: tokens to S-expression -/

mutual

/-- The tokens of a schema build its S-expression. -/
theorem buildSexp_toks : ∀ (s : Schema) (ts : List Token) (top : List Sexp)
    (stack : List (List Sexp)),
    buildSexp (toks s ++ ts) (top :: stack) = buildSexp ts ((sexpOf s :: top) :: stack)
  | .uint w, ts, top, stack => by simp [toks, sexpOf, buildSexp]
  | .sint w, ts, top, stack => by simp [toks, sexpOf, buildSexp]
  | .f32, ts, top, stack => by simp [toks, sexpOf, buildSexp]
  | .f64, ts, top, stack => by simp [toks, sexpOf, buildSexp]
  | .bool, ts, top, stack => by simp [toks, sexpOf, buildSexp]
  | .string, ts, top, stack => by simp [toks, sexpOf, buildSexp]
  | .tuple [], ts, top, stack => by simp [toks, sexpOf, buildSexp]
  | .option s, ts, top, stack => by
    simp only [toks, sexpOf, List.cons_append, buildSexp, List.append_assoc, List.nil_append]
    rw [buildSexp_toks s (.rparen :: ts) _ _]
    simp [buildSexp]
  | .vec s, ts, top, stack => by
    simp only [toks, sexpOf, List.cons_append, buildSexp, List.append_assoc, List.nil_append]
    rw [buildSexp_toks s (.rparen :: ts) _ _]
    simp [buildSexp]
  | .set s, ts, top, stack => by
    simp only [toks, sexpOf, List.cons_append, buildSexp, List.append_assoc, List.nil_append]
    rw [buildSexp_toks s (.rparen :: ts) _ _]
    simp [buildSexp]
  | .array n s, ts, top, stack => by
    simp only [toks, sexpOf, List.cons_append, buildSexp, List.append_assoc, List.nil_append]
    rw [buildSexp_toks s (.rparen :: ts) _ _]
    simp [buildSexp]
  | .map k v, ts, top, stack => by
    simp only [toks, sexpOf, List.cons_append, buildSexp, List.append_assoc, List.nil_append]
    rw [buildSexp_toks k (toks v ++ .rparen :: ts) _ _, buildSexp_toks v (.rparen :: ts) _ _]
    simp [buildSexp]
  | .tuple (f :: fs), ts, top, stack => by
    simp only [toks, sexpOf, List.cons_append, buildSexp, List.append_assoc, List.nil_append]
    rw [buildSexp_fields (f :: fs) (.rparen :: ts) _ _]
    simp [buildSexp]
  | .enum vs, ts, top, stack => by
    simp only [toks, sexpOf, List.cons_append, buildSexp, List.append_assoc, List.nil_append]
    rw [buildSexp_variants vs (.rparen :: ts) _ _]
    simp [buildSexp]

/-- The tokens of tuple fields build their S-expressions. -/
theorem buildSexp_fields : ∀ (fs : List Schema) (ts : List Token) (top : List Sexp)
    (stack : List (List Sexp)),
    buildSexp (toksFields fs ++ ts) (top :: stack) =
      buildSexp ts (((sexpsOf fs).reverse ++ top) :: stack)
  | [], ts, top, stack => by simp [toksFields, sexpsOf]
  | s :: fs, ts, top, stack => by
    simp only [toksFields, sexpsOf, List.append_assoc]
    rw [buildSexp_toks s _ _ _, buildSexp_fields fs ts _ _]
    simp

/-- The tokens of enum variants build their S-expressions. -/
theorem buildSexp_variants : ∀ (vs : List (UInt8 × Schema)) (ts : List Token)
    (top : List Sexp) (stack : List (List Sexp)),
    buildSexp (toksVariants vs ++ ts) (top :: stack) =
      buildSexp ts (((variantsOf vs).reverse ++ top) :: stack)
  | [], ts, top, stack => by simp [toksVariants, variantsOf]
  | (t, s) :: vs, ts, top, stack => by
    simp only [toksVariants, variantsOf, List.cons_append, buildSexp, List.append_assoc]
    rw [buildSexp_toks s (.rparen :: (toksVariants vs ++ ts)) _ _]
    simp only [buildSexp]
    rw [buildSexp_variants vs ts _ _]
    simp

end

/-! ### Stage three: S-expression to schema -/

/-- `toSchema` on a `tuple` form. -/
theorem toSchema_tuple (args : List Sexp) :
    toSchema (Sexp.list (Sexp.atom "tuple" :: args)) = (toSchemas args).map Schema.tuple := by
  unfold toSchema
  rfl

/-- `toSchema` on an `enum` form. -/
theorem toSchema_enum (args : List Sexp) :
    toSchema (Sexp.list (Sexp.atom "enum" :: args)) = (toVariants args).map Schema.enum := by
  unfold toSchema
  rfl

/-- `parseNat` on `Nat.repr`, which is what `toString` unfolds to. -/
theorem parseNat_repr (n : Nat) : parseNat n.repr = some n := parseNat_toString n

mutual

/-- `toSchema` reads the S-expression of a schema back as the schema. -/
theorem toSchema_sexpOf : ∀ s : Schema, toSchema (sexpOf s) = .ok s
  | .uint w => by cases w <;> rfl
  | .sint w => by cases w <;> rfl
  | .f32 => rfl
  | .f64 => rfl
  | .bool => rfl
  | .string => rfl
  | .tuple [] => rfl
  | .option s => by simp [sexpOf, toSchema, toSchema_sexpOf s, Except.map]
  | .vec s => by simp [sexpOf, toSchema, toSchema_sexpOf s, Except.map]
  | .set s => by simp [sexpOf, toSchema, toSchema_sexpOf s, Except.map]
  | .array n s => by simp [sexpOf, toSchema, toSchema_sexpOf s, parseNat_repr, Except.map]
  | .map k v => by simp [sexpOf, toSchema, toSchema_sexpOf k, toSchema_sexpOf v]
  | .tuple (f :: fs) => by
    simp only [sexpOf]
    rw [toSchema_tuple, toSchemas_sexpsOf (f :: fs)]
    rfl
  | .enum vs => by
    simp only [sexpOf]
    rw [toSchema_enum, toVariants_variantsOf vs]
    rfl

/-- `toSchemas` reads the S-expressions of tuple fields back. -/
theorem toSchemas_sexpsOf : ∀ fs : List Schema, toSchemas (sexpsOf fs) = .ok fs
  | [] => rfl
  | s :: fs => by simp [sexpsOf, toSchemas, toSchema_sexpOf s, toSchemas_sexpsOf fs]

/-- `toVariants` reads the S-expressions of enum variants back. -/
theorem toVariants_variantsOf : ∀ vs : List (UInt8 × Schema), toVariants (variantsOf vs) = .ok vs
  | [] => rfl
  | (t, s) :: vs => by
    have ht : t.toNat < 256 := UInt8.toNat_lt t
    simp [variantsOf, toVariants, parseNat_repr, ht, toSchema_sexpOf s,
      toVariants_variantsOf vs]

end

end Parse

end BorshSpec
