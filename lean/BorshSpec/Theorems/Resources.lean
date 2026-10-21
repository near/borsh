import BorshSpec
import BorshSpec.Theorems.resources.Equiv
import BorshSpec.Theorems.resources.CostBound
import BorshSpec.Theorems.resources.HexLemmas
import BorshSpec.Theorems.resources.ParseBuild

/-!
# Resource bounds, schema text and hex

* the cost bound `decode_steps_le`: the step count of the cost-instrumented decoder
  is at most `(input length + 1) * factor s`, with no hypothesis on the schema;
* the instrumented decoder computes the same result as `decode`;
* the element bound, which counts the slots of zero-sized arrays;
* the schema printer and parser are inverse;
* hex encoding and decoding are inverse.

The cost model is in `Tooling/Cost.lean`; read its module docstring for what a step is.
-/

namespace BorshSpec

/-! ## Cost of the strict decoder -/

/-- The instrumented decoder computes the same result as `decode`. -/
theorem decodeC_result (s : Schema) (bs : List UInt8) : (s.decodeC bs).1 = decode s bs :=
  Schema.decodeC_fst s bs

/-- Every schema has a positive factor. -/
theorem factor_pos (s : Schema) : 0 < s.factor :=
  Schema.factor_pos_aux s

/-- **Cost bound.**  Decoding takes at most `(input length + 1) * factor s` steps,
whether it succeeds or fails.  No hypothesis on the schema: the factor accounts for
zero-sized arrays, which produce elements out of no input. -/
theorem decode_steps_le (s : Schema) (bs : List UInt8) :
    (s.decodeC bs).2 ≤ (bs.length + 1) * s.factor := by
  rw [Nat.mul_comm]
  exact (Schema.decodeC_inv s bs).1

/-- The same bound in terms of the bytes consumed, when decoding succeeds. -/
theorem decode_steps_le_consumed (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8)
    (n : Nat) (h : s.decodeC bs = (some (v, rest), n)) :
    n ≤ (bs.length - rest.length + 1) * s.factor := by
  rw [Nat.mul_comm]
  exact ((Schema.decodeC_inv s bs).succ h).2.1

/-- The empty input costs at most the factor: this is where zero-sized arrays act. -/
theorem decode_steps_le_empty (s : Schema) : (s.decodeC []).2 ≤ s.factor := by
  simpa using decode_steps_le s []

/-- **The request guard is sound.**  If `(input length + 1) * factor` is within the cap
(`Schema.withinSteps`, the test the executable applies to each request), decoding takes
at most `cap` steps. -/
theorem decode_steps_le_of_withinSteps (s : Schema) (bs : List UInt8) (cap : Nat)
    (h : s.withinSteps bs.length cap = true) : (s.decodeC bs).2 ≤ cap := by
  simp only [Schema.withinSteps, decide_eq_true_eq] at h
  exact Nat.le_trans (decode_steps_le s bs) h

/-- **The schema guard bounds the constant.**  If the factor is within the cap
(`Schema.withinBudget`, the test the executable applies to each schema), an input of
`n` bytes takes at most `(n + 1) * cap` steps.  The cap does not bound the work on a
long input; that is the job of the request guard above. -/
theorem decode_steps_le_of_withinBudget (s : Schema) (bs : List UInt8) (cap : Nat)
    (h : s.withinBudget cap = true) : (s.decodeC bs).2 ≤ (bs.length + 1) * cap := by
  simp only [Schema.withinBudget, decide_eq_true_eq] at h
  exact Nat.le_trans (decode_steps_le s bs) (Nat.mul_le_mul_left _ h)

/-- The number of elements of a decoded value is at most the number of steps. -/
theorem decode_elems_le_steps (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8)
    (n : Nat) (h : s.decodeC bs = (some (v, rest), n)) : v.elems ≤ n := by
  have := ((Schema.decodeC_inv s bs).succ h).2.2.2
  omega

/-- **Element bound.**  A decoded value has at most `(consumed + 1) * factor s`
collection elements, array slots included.  (The version without the factor is false:
`(array 4294967295 unit)` decodes to four billion elements from no input.) -/
theorem decode_elems_le (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8)
    (h : decode s bs = some (v, rest)) :
    v.elems ≤ (bs.length - rest.length + 1) * s.factor := by
  obtain ⟨res, n, hres⟩ : ∃ res n, s.decodeC bs = (res, n) := ⟨_, _, rfl⟩
  have h1 : res = some (v, rest) := by
    have := decodeC_result s bs
    rw [hres] at this
    exact this.trans h
  subst h1
  exact Nat.le_trans (decode_elems_le_steps s bs v rest n hres)
    (decode_steps_le_consumed s bs v rest n hres)

/-! ## Schema text -/

/-- **Parse after print.**  Printing a schema and parsing the result gives the schema
back.  This holds for every schema, well-formed or not (the parser accepts `(enum)`
and leaves well-formedness to `Schema.wellFormed`). -/
theorem parse_print (s : Schema) : parseSchema s.print = .ok s := by
  have ht : Parse.tokenize s.print = .ok (Parse.toks s) := by
    simp only [Parse.tokenize, Schema.print, String.toList_ofList]
    have := Parse.tokenizeAux_print s [] [] (Or.inl rfl)
    simp only [List.append_nil] at this
    rw [this]
    simp [Parse.tokenizeAux, Parse.flushWord]
  have hb : Parse.buildSexp (Parse.toks s) [[]] = .ok (Parse.sexpOf s) := by
    have := Parse.buildSexp_toks s [] [] []
    simpa [Parse.buildSexp] using this
  simp only [parseSchema, ht, hb, bind, Except.bind]
  exact Parse.toSchema_sexpOf s

/-! ## Hex -/

/-- Decoding the hex text of a byte string returns the byte string. -/
theorem hex_decode_encode (bs : List UInt8) : Hex.decode (Hex.encode bs) = some bs := by
  simp only [Hex.decode, Hex.encode, String.toList_ofList]
  rw [Hex.decodeChars_flatMap]
  simp

/-- The hex text accepted by `Hex.decode` is exactly the one `Hex.encode` writes
(lowercase, even length). -/
theorem hex_encode_decode (h : String) (bs : List UInt8) (hd : Hex.decode h = some bs) :
    Hex.encode bs = h := by
  simp only [Hex.decode] at hd
  obtain ⟨bs', hbs, hout⟩ := Hex.decodeChars_inv _ _ _ hd
  simp only [List.reverse_nil, List.nil_append] at hout
  subst hout
  simp only [Hex.encode, ← hbs, String.ofList_toList]

end BorshSpec
