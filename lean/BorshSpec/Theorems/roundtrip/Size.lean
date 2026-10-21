import BorshSpec.Theorems.roundtrip.Valid

/-!
# Sizes: progress, zero-sized schemas, the minimum is attained

* `progress`: a successful decode consumes at least `minSize s` bytes, for every key
  policy (the policy changes only what happens to the keys after they were read);
* `minSize_pos_iff`: `minSize` is positive exactly on the schemas that are not
  `zeroSized`;
* `encode_eq_nil_of_zeroSized`: a zero-sized schema encodes to nothing;
* `minSize_attained`: for a well-formed schema some value encodes in exactly
  `minSize` bytes.
-/

namespace BorshSpec

namespace RT

open Schema

/-- A successful `takeExact` leaves no more than the input. -/
theorem takeExact_rest_length {n : Nat} {bs a r : List UInt8}
    (h : takeExact n bs = some (a, r)) : n + r.length ≤ bs.length := by
  obtain ⟨hl, rfl⟩ := takeExact_eq_some h
  simp [hl]

mutual

/-- **Progress**, for any key policy: a successful decode consumes at least `minSize s`
bytes. -/
theorem progress_with (P : KeyPolicy) :
    ∀ (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8),
      decodeWith P s bs = some (v, rest) → s.minSize + rest.length ≤ bs.length
  | .uint w, bs, v, rest, h => by
    simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨n, r⟩, hr, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨_, rfl⟩ := hv
    simpa [minSize] using readLE_length hr
  | .sint w, bs, v, rest, h => by
    simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨n, r⟩, hr, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨_, rfl⟩ := hv
    simpa [minSize] using readLE_length hr
  | .f32, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i n r hr
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simpa [minSize] using readLE_length hr
  | .f64, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i n r hr
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simpa [minSize] using readLE_length hr
  | .bool, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · rename_i b r
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp only [minSize, List.length_cons]
        omega
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          simp only [minSize, List.length_cons]
          omega
        · simp at h
    · simp at h
  | .string, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i n r hr
      split at h
      · simp at h
      · rename_i body r' hk
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          have h1 := readLE_length hr
          have h2 := takeExact_rest_length hk
          simp only [minSize]
          omega
        · simp at h
  | .option s, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · rename_i b r
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp only [minSize, List.length_cons]
        omega
      · split at h
        · rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨v', r'⟩, hd, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨_, rfl⟩ := hv
          have := progress_with P s r v' r' hd
          simp only [minSize, List.length_cons]
          omega
        · simp at h
    · simp at h
  | .vec s, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i n r hr
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨xs, r'⟩, hm, hv⟩ := h
        simp only [Prod.mk.injEq] at hv
        obtain ⟨_, rfl⟩ := hv
        have h1 := readLE_length hr
        have h2 := decodeMany_length (fun b => decodeWith P s b) 0
          (fun b x r hb => by have := progress_with P s b x r hb; omega) n [] r xs r' hm
        simp only [minSize]
        omega
  | .array n s, bs, v, rest, h => by
    simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨xs, r⟩, hm, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨_, rfl⟩ := hv
    exact decodeMany_length (fun b => decodeWith P s b) s.minSize
      (fun b x r hb => progress_with P s b x r hb) n [] bs xs r hm
  | .tuple fs, bs, v, rest, h => by
    simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨xs, r⟩, hf, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨_, rfl⟩ := hv
    simpa [minSize] using progressFields P fs bs xs r hf
  | .enum vs, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · rename_i t r
      obtain ⟨m, hm, hle⟩ := progressVariant P vs 0 t r v rest h
      simp only [minSize, hm, Option.getD_some, List.length_cons]
      omega
    · simp at h
  | .map k s, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i n r hr
        split at h
        · simp at h
        · rename_i kvs r' hm
          rw [Option.map_eq_some_iff] at h
          obtain ⟨kvs', _, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨_, rfl⟩ := hv
          have h1 := readLE_length hr
          have h2 := decodeMany_length _ 0
            (fun b x r hb => by
              obtain ⟨a, c⟩ := x
              split at hb
              · simp at hb
              · rename_i a' r₁ ha
                split at hb
                · simp at hb
                · rename_i c' r₂ hc
                  simp only [Option.some.injEq, Prod.mk.injEq] at hb
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
                  have := progress_with P k b _ _ ha
                  have := progress_with P s r₁ _ _ hc
                  omega) n [] r kvs r' hm
          simp only [minSize]
          omega
  | .set s, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i n r hr
        split at h
        · simp at h
        · rename_i xs r' hm
          rw [Option.map_eq_some_iff] at h
          obtain ⟨xs', _, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨_, rfl⟩ := hv
          have h1 := readLE_length hr
          have h2 := decodeMany_length (fun b => decodeWith P s b) 0
            (fun b x r hb => by have := progress_with P s b x r hb; omega) n [] r xs r' hm
          simp only [minSize]
          omega

/-- Progress for the fields of a tuple. -/
theorem progressFields (P : KeyPolicy) :
    ∀ (fs : List Schema) (bs : List UInt8) (vs : List Value) (rest : List UInt8),
      decodeFieldsWith P fs bs = some (vs, rest) → minSizeAll fs + rest.length ≤ bs.length
  | [], bs, vs, rest, h => by
    simp only [decodeFieldsWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp [minSizeAll]
  | s :: fs, bs, vs, rest, h => by
    simp only [decodeFieldsWith] at h
    split at h
    · simp at h
    · rename_i v r hv
      split at h
      · simp at h
      · rename_i vs' r' hvs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have h1 := progress_with P s bs v r hv
        have h2 := progressFields P fs r vs' r' hvs
        simp only [minSizeAll]
        omega

/-- Progress for the payload of an enum variant: the least payload size of the listed
variants is at most what the found variant consumed. -/
theorem progressVariant (P : KeyPolicy) :
    ∀ (vs : List (UInt8 × Schema)) (j : Nat) (t : UInt8) (bs : List UInt8) (v : Value)
      (rest : List UInt8), decodeVariantWith P vs j t bs = some (v, rest) →
      ∃ m, minSizeVariants vs = some m ∧ m + rest.length ≤ bs.length
  | [], j, t, bs, v, rest, h => by simp [decodeVariantWith] at h
  | (t', s) :: vs, j, t, bs, v, rest, h => by
    by_cases ht : t' == t
    · simp only [decodeVariantWith, ht, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨w, r⟩, hd, hv⟩ := h
      simp only [Prod.mk.injEq] at hv
      obtain ⟨_, rfl⟩ := hv
      have := progress_with P s bs w r hd
      cases hm : minSizeVariants vs with
      | none => exact ⟨minSize s, by simp [minSizeVariants, hm], this⟩
      | some m => exact ⟨min (minSize s) m, by simp [minSizeVariants, hm], by omega⟩
    · simp only [decodeVariantWith, ht, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨m, hm, hle⟩ := progressVariant P vs (j + 1) t bs v rest h
      exact ⟨min (minSize s) m, by simp [minSizeVariants, hm], by omega⟩

end

mutual

/-- `minSize` is positive exactly for the schemas that are not zero-sized. -/
theorem minSize_pos_iff' : ∀ (s : Schema), 0 < s.minSize ↔ s.zeroSized = false
  | .uint w => by cases w <;> simp [minSize, zeroSized, IntWidth.bytes]
  | .sint w => by cases w <;> simp [minSize, zeroSized, IntWidth.bytes]
  | .f32 => by simp [minSize, zeroSized]
  | .f64 => by simp [minSize, zeroSized]
  | .bool => by simp [minSize, zeroSized]
  | .string => by simp [minSize, zeroSized]
  | .option _ => by simp [minSize, zeroSized]
  | .vec _ => by simp [minSize, zeroSized]
  | .array n s => by
    have ih := minSize_pos_iff' s
    simp only [minSize, zeroSized, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    rw [← ih]
    constructor
    · intro h
      exact ⟨fun hn => by simp [hn] at h, Nat.pos_of_mul_pos_left h⟩
    · rintro ⟨h1, h2⟩
      exact Nat.mul_pos (Nat.pos_of_ne_zero h1) h2
  | .tuple fs => by
    have ih := minSizeAll_pos_iff fs
    simpa [minSize, zeroSized] using ih
  | .enum _ => by
    simp only [zeroSized, minSize]
    exact ⟨fun _ => trivial, fun _ => by omega⟩
  | .map _ _ => by simp [minSize, zeroSized]
  | .set _ => by simp [minSize, zeroSized]

/-- `minSizeAll` is positive exactly when some schema of the list is not zero-sized. -/
theorem minSizeAll_pos_iff :
    ∀ (fs : List Schema), 0 < minSizeAll fs ↔ zeroSizedAll fs = false
  | [] => by simp [minSizeAll, zeroSizedAll]
  | s :: fs => by
    have h1 := minSize_pos_iff' s
    have h2 := minSizeAll_pos_iff fs
    simp only [minSizeAll, zeroSizedAll, Bool.and_eq_false_iff]
    rw [← h1, ← h2]
    omega

end

/-- Every element of the result of `mapM` is the encoding of some element. -/
theorem mapM_mem {α : Type} (e : α → Option (List UInt8)) :
    ∀ (xs : List α) (es : List (List UInt8)), xs.mapM e = some es →
      ∀ p ∈ es, ∃ x ∈ xs, e x = some p
  | [], es, h, p, hp => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp at hp
  | y :: xs, es, h, p, hp => by
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨q, hq, es', hes', rfl⟩ := h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨y, List.mem_cons_self .., hq⟩
    · obtain ⟨x, hx, hxe⟩ := mapM_mem e xs es' hes' p hp
      exact ⟨x, List.mem_cons_of_mem _ hx, hxe⟩

mutual

/-- A zero-sized schema encodes everything it accepts to nothing. -/
theorem encode_nil_of_zeroSized :
    ∀ (s : Schema), s.zeroSized = true → ∀ (v : Value) (bs : List UInt8),
      encode s v = some bs → bs = []
  | .uint _, hz, _, _, _ => by simp [zeroSized] at hz
  | .sint _, hz, _, _, _ => by simp [zeroSized] at hz
  | .f32, hz, _, _, _ => by simp [zeroSized] at hz
  | .f64, hz, _, _, _ => by simp [zeroSized] at hz
  | .bool, hz, _, _, _ => by simp [zeroSized] at hz
  | .string, hz, _, _, _ => by simp [zeroSized] at hz
  | .option _, hz, _, _, _ => by simp [zeroSized] at hz
  | .vec _, hz, _, _, _ => by simp [zeroSized] at hz
  | .enum _, hz, _, _, _ => by simp [zeroSized] at hz
  | .map _ _, hz, _, _, _ => by simp [zeroSized] at hz
  | .set _, hz, _, _, _ => by simp [zeroSized] at hz
  | .array n s, hz, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    rename_i xs
    split at h
    · rename_i hn
      rw [Option.map_eq_some_iff] at h
      obtain ⟨es, hes, rfl⟩ := h
      simp only [beq_iff_eq] at hn
      simp only [zeroSized, Bool.or_eq_true, beq_iff_eq] at hz
      rw [List.flatten_eq_nil_iff]
      intro p hp
      obtain ⟨x, hx, hxe⟩ := mapM_mem (encode s) xs es hes p hp
      rcases hz with rfl | hz
      · simp at hn
        subst hn
        simp at hx
      · exact encode_nil_of_zeroSized s hz x p hxe
    · simp at h
  | .tuple fs, hz, v, bs, h => by
    cases v <;> simp only [encode, reduceCtorEq] at h
    exact encodeFields_nil_of_zeroSized fs (by simpa [zeroSized] using hz) _ bs h

/-- A list of zero-sized schemas encodes to nothing. -/
theorem encodeFields_nil_of_zeroSized :
    ∀ (fs : List Schema), zeroSizedAll fs = true → ∀ (vs : List Value) (bs : List UInt8),
      encodeFields fs vs = some bs → bs = []
  | [], _, [], bs, h => by simpa [encodeFields] using h.symm
  | [], _, _ :: _, bs, h => by simp [encodeFields] at h
  | _ :: _, _, [], bs, h => by simp [encodeFields] at h
  | s :: fs, hz, v :: vs, bs, h => by
    simp only [zeroSizedAll, Bool.and_eq_true] at hz
    simp only [encodeFields, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨e, he, es, hes, rfl⟩ := h
    rw [encode_nil_of_zeroSized s hz.1 v e he, encodeFields_nil_of_zeroSized fs hz.2 vs es hes]
    rfl

end

/-- `mapM` over a replicated element. -/
theorem mapM_replicate {α : Type} (e : α → Option (List UInt8)) (x : α) (p : List UInt8)
    (h : e x = some p) :
    ∀ n, (List.replicate n x).mapM e = some (List.replicate n p)
  | 0 => by simp [List.mapM_nil, pure]
  | n + 1 => by
    simp [List.replicate_succ, List.mapM_cons, h, mapM_replicate e x p h n, bind, pure]

/-- Length of a flattened replicate. -/
theorem length_flatten_replicate (p : List UInt8) :
    ∀ n, (List.replicate n p).flatten.length = n * p.length
  | 0 => by simp
  | n + 1 => by
    simp only [List.replicate_succ, List.flatten_cons, List.length_append,
      length_flatten_replicate p n, Nat.succ_mul]
    omega

/-- With distinct tags, `encodeVariant` finds the variant at the given position. -/
theorem encodeVariant_get :
    ∀ (vs : List (UInt8 × Schema)) (earlier : List UInt8) (i : Nat) (t : UInt8)
      (s : Schema) (w : Value), vs[i]? = some (t, s) → (vs.map Prod.fst).Nodup →
      (∀ x ∈ earlier, x ∉ vs.map Prod.fst) →
        encodeVariant vs earlier i w = (encode s w).map (t :: ·)
  | [], _, _, _, _, _, h, _, _ => by simp at h
  | (t0, s0) :: vs, earlier, 0, t, s, w, h, _, hdis => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : ¬ t0 ∈ earlier := fun hm => hdis t0 hm (by simp)
    simp [encodeVariant, this]
  | (t0, s0) :: vs, earlier, i + 1, t, s, w, h, hnd, hdis => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [encodeVariant]
    refine encodeVariant_get vs (t0 :: earlier) i t s w h hnd.2 ?_
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hnd.1
    · intro hm
      exact hdis x hx (List.mem_cons_of_mem _ hm)

/-- The least payload size is attained by some variant. -/
theorem minSizeVariants_attained :
    ∀ (vs : List (UInt8 × Schema)) (m : Nat), minSizeVariants vs = some m →
      ∃ (i : Nat) (t : UInt8) (s : Schema), vs[i]? = some (t, s) ∧ minSize s = m
  | [], m, h => by simp [minSizeVariants] at h
  | (t, s) :: vs, m, h => by
    cases hm : minSizeVariants vs with
    | none =>
      simp only [minSizeVariants, hm, Option.some.injEq] at h
      exact ⟨0, t, s, by simp, h⟩
    | some m' =>
      simp only [minSizeVariants, hm, Option.some.injEq] at h
      by_cases hle : minSize s ≤ m'
      · exact ⟨0, t, s, by simp, by omega⟩
      · obtain ⟨i, t', s', hi, hs⟩ := minSizeVariants_attained vs m' hm
        exact ⟨i + 1, t', s', by simpa using hi, by omega⟩

mutual

/-- The witness lemma for `minSize_attained`. -/
theorem minSize_witness :
    ∀ (s : Schema), s.wellFormed = true →
      ∃ v bs, encode s v = some bs ∧ bs.length = s.minSize
  | .uint w, _ => ⟨.uint 0, toLE w.bytes 0, by simp [encode], by simp [minSize, toLE_length]⟩
  | .sint w, _ => ⟨.sint 0, toLE w.bytes (sintToNat w 0), by
      have : sintInRange w 0 = true := by cases w <;> decide
      simp [encode, this], by simp [minSize, toLE_length]⟩
  | .f32, _ => ⟨.f32 0, toLE 4 (0 : UInt32).toNat, by simp [encode, isNaN32], by
      simp [minSize, toLE_length]⟩
  | .f64, _ => ⟨.f64 0, toLE 8 (0 : UInt64).toNat, by simp [encode, isNaN64], by
      simp [minSize, toLE_length]⟩
  | .bool, _ => ⟨.bool false, [0], by simp [encode], by simp [minSize]⟩
  | .string, _ => ⟨.string [], toLE 4 0, by simp [encode, validUtf8], by
      simp [minSize, toLE_length]⟩
  | .option _, _ => ⟨.optNone, [0], by simp [encode], by simp [minSize]⟩
  | .vec s, hw => by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact ⟨.vec [], toLE 4 0, by simp [encode, hw.2], by simp [minSize, toLE_length]⟩
  | .array n s, hw => by
    obtain ⟨v0, e, he, hl⟩ := minSize_witness s hw
    refine ⟨.array (List.replicate n v0), (List.replicate n e).flatten, ?_, ?_⟩
    · simp [encode, mapM_replicate (encode s) _ e he n]
    · rw [length_flatten_replicate, hl, minSize]
  | .tuple fs, hw => by
    obtain ⟨vs, e, he, hl⟩ := minSizeFields_witness fs hw
    exact ⟨.tuple vs, e, by simpa [encode] using he, by simpa [minSize] using hl⟩
  | .enum vs, hw => by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw
    obtain ⟨⟨hne, hnd⟩, hv⟩ := hw
    have hne' : vs ≠ [] := by
      intro h
      simp [h] at hne
    obtain ⟨m, hm⟩ : ∃ m, minSizeVariants vs = some m := by
      cases vs with
      | nil => exact absurd rfl hne'
      | cons p vs' =>
        obtain ⟨t, s⟩ := p
        simp only [minSizeVariants]
        cases minSizeVariants vs' <;> exact ⟨_, rfl⟩
    obtain ⟨i, t, s, hi, hs⟩ := minSizeVariants_attained vs m hm
    obtain ⟨v0, e, he, hl⟩ := minSizeVariants_witness vs hv i t s hi
    refine ⟨.enum i v0, t :: e, ?_, ?_⟩
    · simp only [encode]
      rw [encodeVariant_get vs [] i t s v0 hi hnd (by simp), he]
      rfl
    · simp only [minSize, List.length_cons, hl, hm, Option.getD_some]
      omega
  | .map k s, hw => by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact ⟨.map [], toLE 4 0, by simp [encode, hw.1.2, Value.strictAsc],
      by simp [minSize, toLE_length]⟩
  | .set s, hw => by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact ⟨.set [], toLE 4 0, by simp [encode, hw.1.2, Value.strictAsc],
      by simp [minSize, toLE_length]⟩

/-- The tuple-field version of `minSize_witness`. -/
theorem minSizeFields_witness :
    ∀ (fs : List Schema), wellFormedAll fs = true →
      ∃ vs bs, encodeFields fs vs = some bs ∧ bs.length = minSizeAll fs
  | [], _ => ⟨[], [], by simp [encodeFields], by simp [minSizeAll]⟩
  | s :: fs, hw => by
    simp only [wellFormedAll, Bool.and_eq_true] at hw
    obtain ⟨v, e, he, hl⟩ := minSize_witness s hw.1
    obtain ⟨vs, es, hes, hls⟩ := minSizeFields_witness fs hw.2
    exact ⟨v :: vs, e ++ es, by simp [encodeFields, he, hes, bind, pure], by
      simp [minSizeAll, hl, hls]⟩

/-- The enum-variant version of `minSize_witness`: every listed payload has a value
encoded at its least size. -/
theorem minSizeVariants_witness :
    ∀ (vs : List (UInt8 × Schema)), wellFormedVariants vs = true →
      ∀ (i : Nat) (t : UInt8) (s : Schema), vs[i]? = some (t, s) →
        ∃ v bs, encode s v = some bs ∧ bs.length = minSize s
  | [], _, i, t, s, h => by simp at h
  | (t0, s0) :: vs, hw, 0, t, s, h => by
    simp only [wellFormedVariants, Bool.and_eq_true] at hw
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hs⟩ := h
    subst hs
    exact minSize_witness _ hw.1
  | (t0, s0) :: vs, hw, i + 1, t, s, h => by
    simp only [wellFormedVariants, Bool.and_eq_true] at hw
    simp only [List.getElem?_cons_succ] at h
    exact minSizeVariants_witness vs hw.2 i t s h

end

end RT

end BorshSpec
