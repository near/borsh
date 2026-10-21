import BorshSpec.Theorems.grammar.Inversion
import BorshSpec.Theorems.grammar.Utf8

/-!
# Helper lemmas: `encode` against the grammar

`encode s v = some bs` exactly when `Encodes s v bs`.  The proof is by structural
recursion on the schema, with one case for each constructor; the list-valued cases
(`vec`, `array`, `set`, `map`) reduce to `List.mapM` against the list relations.
-/

namespace BorshSpec

namespace GrammarProof

theorem mapM_nil_some {α β : Type} (f : α → Option β) (es : List β) :
    ([] : List α).mapM f = some es ↔ es = [] := by
  simp [List.mapM_nil]

theorem mapM_cons_some {α β : Type} (f : α → Option β) (x : α) (xs : List α) (es : List β) :
    (x :: xs).mapM f = some es ↔ ∃ e es', es = e :: es' ∧ f x = some e ∧ xs.mapM f = some es' := by
  rw [List.mapM_cons]
  cases hx : f x with
  | none => simp
  | some e =>
    cases hxs : xs.mapM f with
    | none => simp
    | some es' => simp [eq_comm]

theorem map_flatten_some (m : Option (List (List UInt8))) (pre bs : List UInt8) :
    (m.map List.flatten).map (pre ++ ·) = some bs ↔ ∃ es, m = some es ∧ bs = pre ++ es.flatten := by
  cases m with
  | none => simp
  | some es => simp [eq_comm]

theorem map_cons_some (o : Option (List UInt8)) (t : UInt8) (bs : List UInt8) :
    o.map (t :: ·) = some bs ↔ ∃ b, o = some b ∧ bs = t :: b := by
  cases o <;> simp [eq_comm]

theorem map_flatten_some' (m : Option (List (List UInt8))) (bs : List UInt8) :
    m.map List.flatten = some bs ↔ ∃ es, m = some es ∧ bs = es.flatten := by
  cases m <;> simp [eq_comm]

theorem all_iff_mapM (s : Schema) (H : ∀ v bs, encode s v = some bs ↔ Encodes s v bs) :
    ∀ (xs : List Value) (bs : List UInt8),
      EncodesAll s xs bs ↔ ∃ es, xs.mapM (encode s) = some es ∧ bs = es.flatten
  | [], bs => by
    rw [all_nil]
    constructor
    · rintro rfl; exact ⟨[], (mapM_nil_some _ _).2 rfl, rfl⟩
    · rintro ⟨es, h, rfl⟩
      rw [mapM_nil_some] at h
      subst h; rfl
  | x :: xs, bs => by
    rw [all_cons]
    constructor
    · rintro ⟨b, bs', rfl, h1, h2⟩
      obtain ⟨es', h3, rfl⟩ := (all_iff_mapM s H xs bs').1 h2
      exact ⟨b :: es', (mapM_cons_some _ _ _ _).2 ⟨b, es', rfl, (H x b).2 h1, h3⟩, rfl⟩
    · rintro ⟨es, h, rfl⟩
      obtain ⟨e, es', rfl, h1, h2⟩ := (mapM_cons_some _ _ _ _).1 h
      exact ⟨e, es'.flatten, rfl, (H x e).1 h1, (all_iff_mapM s H xs _).2 ⟨es', h2, rfl⟩⟩

theorem pairs_iff_mapM (k w : Schema) (Hk : ∀ v bs, encode k v = some bs ↔ Encodes k v bs)
    (Hw : ∀ v bs, encode w v = some bs ↔ Encodes w v bs) :
    ∀ (kvs : List (Value × Value)) (bs : List UInt8),
      EncodesPairs k w kvs bs ↔ ∃ es, (kvs.mapM fun (a, b) => do
          let ea ← encode k a
          let eb ← encode w b
          pure (ea ++ eb)) = some es ∧ bs = es.flatten
  | [], bs => by
    rw [pairs_nil]
    constructor
    · rintro rfl; exact ⟨[], (mapM_nil_some _ _).2 rfl, rfl⟩
    · rintro ⟨es, h, rfl⟩
      rw [mapM_nil_some] at h
      subst h; rfl
  | (a, c) :: kvs, bs => by
    rw [pairs_cons]
    constructor
    · rintro ⟨bk, bv, bs', rfl, h1, h2, h3⟩
      obtain ⟨es', h4, rfl⟩ := (pairs_iff_mapM k w Hk Hw kvs bs').1 h3
      refine ⟨(bk ++ bv) :: es', (mapM_cons_some _ _ _ _).2 ⟨bk ++ bv, es', rfl, ?_, h4⟩, ?_⟩
      · simp [(Hk a bk).2 h1, (Hw c bv).2 h2]
      · simp
    · rintro ⟨es, h, rfl⟩
      obtain ⟨e, es', rfl, h1, h2⟩ := (mapM_cons_some _ _ _ _).1 h
      cases hk : encode k a with
      | none => simp [hk] at h1
      | some ea =>
        cases hw : encode w c with
        | none => simp [hk, hw] at h1
        | some eb =>
          simp [hk, hw] at h1
          subst h1
          exact ⟨ea, eb, es'.flatten, by simp, (Hk a ea).1 hk, (Hw c eb).1 hw,
            (pairs_iff_mapM k w Hk Hw kvs _).2 ⟨es', h2, rfl⟩⟩

mutual

theorem encode_iff : (s : Schema) → ∀ (v : Value) (bs : List UInt8),
    (encode s v = some bs ↔ Encodes s v bs)
  | .uint w => by
    intro v bs
    rw [enc_uint]
    have hp : (256 : Nat) ^ w.bytes = 2 ^ (8 * w.bytes) := by rw [Nat.pow_mul]
    cases v with
    | uint n =>
      simp only [encode, hp, Value.uint.injEq, exists_eq_left']
      by_cases hn : n < 2 ^ (8 * w.bytes)
      · simp [hn, toLE_eq_leBytes, eq_comm]
      · simp [hn]
    | _ => simp [encode]
  | .sint w => by
    intro v bs
    rw [enc_sint]
    cases v with
    | sint i =>
      simp only [encode, Value.sint.injEq, exists_eq_left']
      by_cases hn : Schema.sintInRange w i = true
      · have hn' := (sintInRange_iff w i).1 hn
        simp only [hn, ↓reduceIte, Option.some.injEq, sintToNat_eq_twosComplement,
          toLE_eq_leBytes]
        exact ⟨fun h => ⟨hn'.1, hn'.2, h.symm⟩, fun h => h.2.2.symm⟩
      · have hn' : ¬ (-((256 ^ w.bytes / 2 : Nat) : Int) ≤ i ∧ i < ((256 ^ w.bytes / 2 : Nat) : Int)) :=
          fun h => hn ((sintInRange_iff w i).2 h)
        simp only [hn, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
        intro ⟨h1, h2, _⟩
        exact hn' ⟨h1, h2⟩
    | _ => simp [encode]
  | .f32 => by
    intro v bs
    rw [enc_f32]
    cases v with
    | f32 bits =>
      simp only [encode, Value.f32.injEq, exists_eq_left']
      by_cases hn : isNaN32 bits = true
      · simp [hn, (isNaN32_iff bits).1 hn]
      · simp [hn, toLE_eq_leBytes, eq_comm, ← isNaN32_iff]
    | _ => simp [encode]
  | .f64 => by
    intro v bs
    rw [enc_f64]
    cases v with
    | f64 bits =>
      simp only [encode, Value.f64.injEq, exists_eq_left']
      by_cases hn : isNaN64 bits = true
      · simp [hn, (isNaN64_iff bits).1 hn]
      · simp [hn, toLE_eq_leBytes, eq_comm, ← isNaN64_iff]
    | _ => simp [encode]
  | .bool => by
    intro v bs
    rw [enc_bool]
    cases v with
    | bool b => simp [encode, eq_comm]
    | _ => simp [encode]
  | .string => by
    intro v bs
    rw [enc_string]
    cases v with
    | string body =>
      simp only [encode, Value.string.injEq, exists_eq_left']
      have hw := validUtf8_iff_wf body
      by_cases h1 : body.length < 2 ^ 32
      · by_cases h2 : validUtf8 body = true
        · simp [h1, h2, hw.1 h2, toLE_eq_leBytes, eq_comm]
        · simp [h1, h2, ← hw]
      · simp [h1]
    | _ => simp [encode]
  | .option s => by
    intro v bs
    have ih := encode_iff s
    rw [enc_option]
    cases v with
    | optNone => simp [encode, eq_comm]
    | optSome x =>
      simp only [encode, map_cons_some, ih, reduceCtorEq, false_and, Value.optSome.injEq,
        false_or]
      constructor
      · rintro ⟨a, h1, h2⟩
        exact ⟨x, a, rfl, h2, h1⟩
      · rintro ⟨x', a, rfl, h2, h1⟩
        exact ⟨a, h1, h2⟩
    | _ => simp [encode]
  | .vec s => by
    intro v bs
    have ih := encode_iff s
    rw [enc_vec]
    cases v with
    | vec xs =>
      simp only [encode, Value.vec.injEq]
      have hz := zeroSized_iff s
      by_cases hc : (s.zeroSized || decide (2 ^ 32 ≤ xs.length)) = true
      · simp only [hc, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨xs', b, rfl, _, h1, h2, _⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
        rcases hc with hc | hc
        · exact h1 (hz.1 hc)
        · omega
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
        have h1 : ¬ SizeZero s := fun h => hc.1 (hz.2 h)
        have h2 : xs.length < 2 ^ 32 := by omega
        rw [map_flatten_some]
        constructor
        · rintro ⟨es, hm, rfl⟩
          exact ⟨xs, es.flatten, rfl, by rw [toLE_eq_leBytes], h1, h2,
            (all_iff_mapM s ih xs _).2 ⟨es, hm, rfl⟩⟩
        · rintro ⟨xs', b, rfl, rfl, _, _, h4⟩
          obtain ⟨es, hm, rfl⟩ := (all_iff_mapM s ih xs b).1 h4
          exact ⟨es, hm, by rw [toLE_eq_leBytes]⟩
    | _ => simp [encode]
  | .array n s => by
    intro v bs
    have ih := encode_iff s
    rw [enc_array]
    cases v with
    | array xs =>
      simp only [encode, Value.array.injEq]
      by_cases hn : xs.length = n
      · simp only [beq_iff_eq, hn, ↓reduceIte, map_flatten_some']
        constructor
        · rintro ⟨es, hm, rfl⟩
          exact ⟨xs, rfl, hn, (all_iff_mapM s ih xs _).2 ⟨es, hm, rfl⟩⟩
        · rintro ⟨xs', rfl, _, h4⟩
          obtain ⟨es, hm, rfl⟩ := (all_iff_mapM s ih xs bs).1 h4
          exact ⟨es, hm, rfl⟩
      · simp only [beq_iff_eq, hn, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨xs', rfl, h, _⟩
        exact hn h
    | _ => simp [encode]
  | .tuple fs => by
    intro v bs
    have ih := fields_iff fs
    rw [enc_tuple]
    cases v with
    | tuple xs => simp [encode, ih]
    | _ => simp [encode]
  | .enum vs => by
    intro v bs
    have ih := variant_iff vs
    rw [enc_enum]
    cases v with
    | enum i x =>
      simp only [encode, ih, List.not_mem_nil, not_false_eq_true, true_and, Value.enum.injEq]
      constructor
      · rintro ⟨tag, s', b, rfl, h1, h2⟩
        exact ⟨i, tag, s', x, b, ⟨rfl, rfl⟩, rfl, h1, h2⟩
      · rintro ⟨i', tag, s', x', b, ⟨rfl, rfl⟩, rfl, h1, h2⟩
        exact ⟨tag, s', b, rfl, h1, h2⟩
    | _ => simp [encode]
  | .map k w => by
    intro v bs
    have ihk := encode_iff k
    have ihw := encode_iff w
    rw [enc_map]
    cases v with
    | map kvs =>
      simp only [encode, Value.map.injEq]
      have hz := zeroSized_iff k
      have hs := strictAsc_iff (kvs.map Prod.fst)
      by_cases hc : (k.zeroSized || decide (2 ^ 32 ≤ kvs.length) ||
          !Value.strictAsc (kvs.map Prod.fst)) = true
      · simp only [hc, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨kvs', b, rfl, _, h1, h2, h3, _⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        rcases hc with (hc | hc) | hc
        · exact h1 (hz.1 hc)
        · omega
        · have := hs.2 h3
          simp [this] at hc
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at hc
        have h1 : ¬ SizeZero k := fun h => hc.1.1 (hz.2 h)
        have h2 : kvs.length < 2 ^ 32 := by omega
        have h3 : Ascending (kvs.map Prod.fst) := by
          apply hs.1
          simpa using hc.2
        rw [map_flatten_some]
        constructor
        · rintro ⟨es, hm, rfl⟩
          exact ⟨kvs, es.flatten, rfl, by rw [toLE_eq_leBytes], h1, h2, h3,
            (pairs_iff_mapM k w ihk ihw kvs _).2 ⟨es, hm, rfl⟩⟩
        · rintro ⟨kvs', b, rfl, rfl, _, _, _, h4⟩
          obtain ⟨es, hm, rfl⟩ := (pairs_iff_mapM k w ihk ihw kvs b).1 h4
          exact ⟨es, hm, by rw [toLE_eq_leBytes]⟩
    | _ => simp [encode]
  | .set s => by
    intro v bs
    have ih := encode_iff s
    rw [enc_set]
    cases v with
    | set xs =>
      simp only [encode, Value.set.injEq]
      have hz := zeroSized_iff s
      have hs := strictAsc_iff xs
      by_cases hc : (s.zeroSized || decide (2 ^ 32 ≤ xs.length) ||
          !Value.strictAsc xs) = true
      · simp only [hc, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨xs', b, rfl, _, h1, h2, h3, _⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        rcases hc with (hc | hc) | hc
        · exact h1 (hz.1 hc)
        · omega
        · have := hs.2 h3
          simp [this] at hc
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at hc
        have h1 : ¬ SizeZero s := fun h => hc.1.1 (hz.2 h)
        have h2 : xs.length < 2 ^ 32 := by omega
        have h3 : Ascending xs := hs.1 (by simpa using hc.2)
        rw [map_flatten_some]
        constructor
        · rintro ⟨es, hm, rfl⟩
          exact ⟨xs, es.flatten, rfl, by rw [toLE_eq_leBytes], h1, h2, h3,
            (all_iff_mapM s ih xs _).2 ⟨es, hm, rfl⟩⟩
        · rintro ⟨xs', b, rfl, rfl, _, _, _, h4⟩
          obtain ⟨es, hm, rfl⟩ := (all_iff_mapM s ih xs b).1 h4
          exact ⟨es, hm, by rw [toLE_eq_leBytes]⟩
    | _ => simp [encode]

theorem fields_iff : (fs : List Schema) → ∀ (vs : List Value) (bs : List UInt8),
    (Schema.encodeFields fs vs = some bs ↔ EncodesFields fs vs bs)
  | [] => by
    intro vs bs
    rw [fields_nil]
    cases vs with
    | nil => simp [Schema.encodeFields, eq_comm]
    | cons x xs => simp [Schema.encodeFields]
  | s :: fs => by
    intro vs bs
    have ih := encode_iff s
    have ih' := fields_iff fs
    rw [fields_cons]
    cases vs with
    | nil => simp [Schema.encodeFields]
    | cons x xs =>
      simp only [Schema.encodeFields]
      cases h1 : encode s x with
      | none =>
        simp only [bind, Option.bind, reduceCtorEq, false_iff]
        rintro ⟨x', xs', b, bs', h, _, h2, _⟩
        obtain ⟨rfl, rfl⟩ := List.cons.inj h
        have := (ih x b).2 h2
        rw [h1] at this
        exact absurd this (by simp)
      | some e =>
        cases h2 : Schema.encodeFields fs xs with
        | none =>
          simp only [bind, Option.bind, reduceCtorEq, false_iff]
          rintro ⟨x', xs', b, bs', h, _, h3, h4⟩
          obtain ⟨rfl, rfl⟩ := List.cons.inj h
          have := (ih' xs bs').2 h4
          rw [h2] at this
          exact absurd this (by simp)
        | some es =>
          simp only [bind, Option.bind, pure, Option.some.injEq, List.cons.injEq]
          constructor
          · rintro rfl
            exact ⟨x, xs, e, es, ⟨rfl, rfl⟩, rfl, (ih x e).1 h1, (ih' xs es).1 h2⟩
          · rintro ⟨x', xs', b, bs', ⟨rfl, rfl⟩, rfl, h3, h4⟩
            have e1 := (ih x b).2 h3
            have e2 := (ih' xs bs').2 h4
            rw [h1] at e1
            rw [h2] at e2
            obtain rfl := Option.some.inj e1
            obtain rfl := Option.some.inj e2
            rfl

theorem variant_iff : (vs : List (UInt8 × Schema)) → ∀ (earlier : List UInt8) (i : Nat)
    (v : Value) (bs : List UInt8),
    (Schema.encodeVariant vs earlier i v = some bs ↔
      ∃ tag s b, bs = tag :: b ∧ VariantAt vs i tag s ∧ tag ∉ earlier ∧ Encodes s v b)
  | [] => by
    intro earlier i v bs
    simp [Schema.encodeVariant, variantAt_nil]
  | (t, s) :: vs => by
    intro earlier i v bs
    have ih := encode_iff s
    have ih' := variant_iff vs
    cases i with
    | zero =>
      simp only [Schema.encodeVariant, variantAt_zero]
      by_cases hm : earlier.contains t = true
      · simp only [hm, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨tag, s', b, _, ⟨rfl, _⟩, h2, _⟩
        exact h2 (List.contains_iff_mem.1 hm)
      · have hm' : t ∉ earlier := fun h => hm (List.contains_iff_mem.2 h)
        simp only [hm, Bool.false_eq_true, ↓reduceIte, map_cons_some, ih]
        constructor
        · rintro ⟨b, h1, rfl⟩
          exact ⟨t, s, b, rfl, ⟨rfl, rfl⟩, hm', h1⟩
        · rintro ⟨tag, s', b, rfl, ⟨rfl, rfl⟩, _, h1⟩
          exact ⟨b, h1, rfl⟩
    | succ i =>
      simp only [Schema.encodeVariant, ih', variantAt_succ, List.mem_cons, not_or]
      constructor
      · rintro ⟨tag, s', b, rfl, h1, ⟨h2, h3⟩, h4⟩
        exact ⟨tag, s', b, rfl, ⟨fun h => h2 h.symm, h1⟩, h3, h4⟩
      · rintro ⟨tag, s', b, rfl, ⟨h1, h2⟩, h3, h4⟩
        exact ⟨tag, s', b, rfl, h2, ⟨fun h => h1 h.symm, h3⟩, h4⟩

end

end GrammarProof

end BorshSpec
