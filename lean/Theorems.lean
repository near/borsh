import Spec

/-!
# Borsh: encode and decode are inverse

For every schema `s`: decoding an encoding returns the value and leaves the rest of the
input alone (`decode_encode`); anything the decoder accepts is exactly the encoding of the
value it returns (`encode_decode`); so the encoding is injective (`encode_injective`).
-/

namespace Borsh

/-! ## Little-endian numbers -/

theorem toLE_length (w n : Nat) : (toLE w n).length = w := by
  induction w generalizing n <;> simp [toLE, *]

theorem fromLE_toLE (w n : Nat) : fromLE (toLE w n) = n % 256 ^ w := by
  induction w generalizing n with
  | zero => simp [toLE, fromLE, Nat.mod_one]
  | succ w ih => simp [toLE, fromLE, ih, Nat.pow_succ, Nat.mul_comm _ 256, Nat.mod_mul]

theorem fromLE_lt : ∀ b : Bytes, fromLE b < 256 ^ b.length
  | [] => by simp [fromLE]
  | x :: b => by
    have := fromLE_lt b; have := x.toNat_lt
    simp [fromLE, Nat.pow_succ]; omega

theorem toLE_fromLE : ∀ b : Bytes, toLE b.length (fromLE b) = b
  | [] => rfl
  | x :: b => by
    have := x.toNat_lt
    simp [toLE, fromLE, show (x.toNat + 256 * fromLE b) / 256 = fromLE b by omega, toLE_fromLE b]

theorem take_append (a rest : Bytes) : take a.length (a ++ rest) = some (a, rest) := by
  simp [take]

theorem take_eq_some {n : Nat} {bs a r : Bytes} (h : take n bs = some (a, r)) :
    a.length = n ∧ bs = a ++ r := by
  unfold take at h
  split at h
  · cases h; rename_i hl; exact ⟨hl, (List.take_append_drop n bs).symm⟩
  · cases h

theorem readLE_toLE (w n : Nat) (rest : Bytes) :
    readLE w (toLE w n ++ rest) = some (n % 256 ^ w, rest) := by
  have := take_append (toLE w n) rest
  rw [toLE_length] at this
  simp [readLE, this, fromLE_toLE]

theorem readLE_eq_some {w n : Nat} {bs r : Bytes} (h : readLE w bs = some (n, r)) :
    n < 256 ^ w ∧ bs = toLE w n ++ r := by
  simp [readLE, Option.bind_eq_some_iff] at h
  obtain ⟨a, h, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := take_eq_some h
  exact ⟨fromLE_lt a, by rw [toLE_fromLE]⟩

/-! ## Integers -/

theorem two_pow (w : Nat) : (2 : Int) ^ (8 * w) = ((256 ^ w : Nat) : Int) := by
  rw [Int.natCast_pow, Int.pow_mul]; rfl

theorem emod_range {x : Int} {N : Nat} (h1 : -(N : Int) ≤ x) (h2 : x < N) :
    x % N = if 0 ≤ x then x else x + N := by
  split
  · exact Int.emod_eq_of_lt (by omega) h2
  · have := Int.add_mul_emod_self_right x 1 N
    rw [Int.one_mul] at this
    rw [← this, Int.emod_eq_of_lt (by omega) (by omega)]

theorem readLE_intLE (w : Nat) (x : Int) (rest : Bytes) :
    ∃ n : Nat, readLE w (intLE w x ++ rest) = some (n, rest) ∧ (n : Int) = x % 2 ^ (8 * w) := by
  refine ⟨_, by rw [intLE, readLE_toLE], ?_⟩
  rw [two_pow]
  have : 0 < 256 ^ w := Nat.pow_pos (by decide)
  generalize 256 ^ w = N at *
  have := Int.emod_nonneg x (b := N) (by omega)
  have := Int.emod_lt_of_pos x (b := N) (by omega)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem intLE_natCast {w n : Nat} (h : n < 256 ^ w) : intLE w n = toLE w n := by
  rw [intLE, two_pow, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

/-! ## Sequences: `List.mapM` against `repeatN` -/

theorem repeatN_mapM {α : Type} {f : α → Option Bytes} {g : Bytes → Option (α × Bytes)}
    (hfg : ∀ x bs rest, f x = some bs → g (bs ++ rest) = some (x, rest)) :
    ∀ (xs : List α) (ys : List Bytes) (rest : Bytes), xs.mapM f = some ys →
      repeatN g xs.length (ys.flatten ++ rest) = some (xs, rest)
  | [], ys, rest, h => by simp at h; subst h; rfl
  | x :: xs, ys, rest, h => by
    simp [List.mapM_cons, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    simp [repeatN, List.append_assoc, hfg x b _ hb, repeatN_mapM hfg xs bs rest hbs]

theorem mapM_repeatN {α : Type} {f : α → Option Bytes} {g : Bytes → Option (α × Bytes)}
    (hgf : ∀ bs x rest, g bs = some (x, rest) → ∃ pre, f x = some pre ∧ bs = pre ++ rest) :
    ∀ (n : Nat) (bs : Bytes) (xs : List α) (rest : Bytes), repeatN g n bs = some (xs, rest) →
      xs.length = n ∧ ∃ ys, xs.mapM f = some ys ∧ bs = ys.flatten ++ rest
  | 0, bs, xs, rest, h => by simp [repeatN] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | n + 1, bs, xs, rest, h => by
    simp [repeatN, Option.bind_eq_some_iff] at h
    obtain ⟨x, bs1, h1, xs', h2, rfl⟩ := h
    obtain ⟨pre, hf, rfl⟩ := hgf _ _ _ h1
    obtain ⟨hl, ys, hys, rfl⟩ := mapM_repeatN hgf n _ _ _ h2
    exact ⟨by simp [hl], pre :: ys, by simp [List.mapM_cons, hf, hys], by simp⟩

theorem enc_seq {α : Type} {p : Prop} [Decidable p] {f : α → Option Bytes}
    {g : Bytes → Option (α × Bytes)}
    (hgf : ∀ bs x rest, g bs = some (x, rest) → ∃ pre, f x = some pre ∧ bs = pre ++ rest)
    {n : Nat} {bs : Bytes} {xs : List α} {rest : Bytes} (h : repeatN g n bs = some (xs, rest))
    (hp : xs.length = n → ¬p) :
    ∃ pre, (if p then none else (toLE 4 xs.length ++ ·.flatten) <$> xs.mapM f) = some pre ∧
      toLE 4 n ++ bs = pre ++ rest := by
  obtain ⟨hl, ys, hys, rfl⟩ := mapM_repeatN hgf n bs xs rest h
  exact ⟨_, by rw [ite_eq_right (hp hl), hys, hl]; rfl, by simp⟩

/-! ## Decoding an encoding -/

mutual
theorem dec_enc : ∀ (s : Schema) (v : Value) (bs rest : Bytes),
    encode s v = some bs → decode s (bs ++ rest) = some (v, rest)
  | .uint w, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    rename_i x
    obtain ⟨⟨h1, h2⟩, rfl⟩ := h
    obtain ⟨n, hr, hn⟩ := readLE_intLE w x rest
    simp [decode, hr]
    rw [hn, Int.emod_eq_of_lt h1 h2]
  | .int w, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    rename_i x
    obtain ⟨⟨h1, h2⟩, rfl⟩ := h
    obtain ⟨n, hr, hn⟩ := readLE_intLE w x rest
    simp [decode, hr]
    rw [two_pow] at *
    rw [Nat.pow_mul]
    generalize 256 ^ w = N at *
    rw [emod_range (by omega) (by omega)] at hn
    split <;> split at hn <;> omega
  | .f32, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    rename_i x
    obtain ⟨⟨h1, h2, h3⟩, rfl⟩ := h
    obtain ⟨n, hr, hn⟩ := readLE_intLE 4 x rest
    rw [Int.emod_eq_of_lt h1 (by omega)] at hn
    subst hn
    simp_all [decode]
  | .f64, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    rename_i x
    obtain ⟨⟨h1, h2, h3⟩, rfl⟩ := h
    obtain ⟨n, hr, hn⟩ := readLE_intLE 8 x rest
    rw [Int.emod_eq_of_lt h1 (by omega)] at hn
    subst hn
    simp_all [decode]
  | .string, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    obtain ⟨⟨h1, h2⟩, rfl⟩ := h
    simp [decode, readLE_toLE, Nat.mod_eq_of_lt (show _ < 256 ^ 4 from h1), take_append, h2]
  | .vec t, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    obtain ⟨⟨hz, hl⟩, ys, hys, rfl⟩ := h
    simp [decode, hz, List.append_assoc, readLE_toLE, Nat.mod_eq_of_lt (show _ < 256 ^ 4 from hl),
      repeatN_mapM (dec_enc t) _ ys rest hys]
  | .tuple ts, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    simp [decode, dec_enc_fields ts _ bs rest h]
  | .enum vs, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    obtain ⟨tag, body, rfl, -, hd⟩ := dec_enc_variant vs [] _ _ bs h
    simpa [decode] using hd 0 rest
  | .map kt vt, v, bs, rest, h => by
    cases v <;> simp [encode] at h
    obtain ⟨⟨hz, hl, ha⟩, ys, hys, rfl⟩ := h
    simp [decode, hz, List.append_assoc, readLE_toLE, Nat.mod_eq_of_lt (show _ < 256 ^ 4 from hl)]
    rw [repeatN_mapM ?_ _ ys rest hys]
    · simp [ha]
    · intro e b r he
      split at he
      · simp [Option.bind_eq_some_iff] at he
        obtain ⟨p, hp, q, hq, rfl⟩ := he
        simp [List.append_assoc, dec_enc kt _ _ _ hp, dec_enc vt _ _ _ hq]
      · cases he

theorem dec_enc_fields : ∀ (ts : List Schema) (xs : List Value) (bs rest : Bytes),
    encodeFields ts xs = some bs → decodeFields ts (bs ++ rest) = some (xs, rest)
  | [], xs, bs, rest, h => by cases xs <;> simp [encodeFields] at h; subst h; rfl
  | t :: ts, xs, bs, rest, h => by
    cases xs <;> simp [encodeFields, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [decodeFields, List.append_assoc, dec_enc t _ a _ ha, dec_enc_fields ts _ b rest hb]

theorem dec_enc_variant : ∀ (vs : List (UInt8 × Schema)) (seen : List UInt8) (i : Nat)
    (x : Value) (bs : Bytes), encodeVariant vs seen i x = some bs →
    ∃ tag body, bs = tag :: body ∧ tag ∉ seen ∧
      ∀ j rest, decodeVariant vs j tag (body ++ rest) = some (.variant (j + i) x, rest)
  | [], _, _, _, _, h => by simp [encodeVariant] at h
  | (tag, t) :: vs, seen, 0, x, bs, h => by
    simp [encodeVariant] at h
    obtain ⟨hs, body, hb, rfl⟩ := h
    exact ⟨tag, body, rfl, hs, fun j rest => by simp [decodeVariant, dec_enc t x body rest hb]⟩
  | (tag', t) :: vs, seen, i + 1, x, bs, h => by
    obtain ⟨tag, body, rfl, hs, hd⟩ := dec_enc_variant vs (tag' :: seen) i x bs h
    simp at hs
    refine ⟨tag, body, rfl, hs.2, fun j rest => ?_⟩
    simp [decodeVariant, Ne.symm hs.1, hd, Nat.add_assoc, Nat.add_comm 1]
end

/-! ## Encoding what was decoded -/

mutual
theorem enc_dec : ∀ (s : Schema) (bs : Bytes) (v : Value) (rest : Bytes),
    decode s bs = some (v, rest) → ∃ pre, encode s v = some pre ∧ bs = pre ++ rest
  | .uint w, bs, v, rest, h => by
    simp [decode, Option.bind_eq_some_iff] at h
    obtain ⟨n, h1, rfl⟩ := h
    obtain ⟨hn, rfl⟩ := readLE_eq_some h1
    refine ⟨_, ?_, rfl⟩
    simp [encode, intLE_natCast hn, two_pow]
    simpa using Int.ofNat_lt.mpr hn
  | .int w, bs, v, rest, h => by
    simp [decode, Option.bind_eq_some_iff] at h
    obtain ⟨n, h1, rfl⟩ := h
    obtain ⟨hn, rfl⟩ := readLE_eq_some h1
    refine ⟨_, ?_, rfl⟩
    simp only [encode, intLE]
    rw [two_pow, Nat.pow_mul]
    generalize 256 ^ w = N at *
    generalize hy : (if n < N / 2 then (n : Int) else n - N) = y
    have hr : -(N : Int) / 2 ≤ y ∧ y < N / 2 := by split at hy <;> omega
    rw [emod_range (by omega) (by omega), ite_eq_left hr]
    congr
    split at hy <;> split <;> omega
  | .f32, bs, v, rest, h => by
    simp [decode, Option.bind_eq_some_iff] at h
    obtain ⟨n, _, h1, h2, rfl, rfl⟩ := h
    obtain ⟨hn, rfl⟩ := readLE_eq_some h1
    exact ⟨_, by simp [encode, h2, intLE_natCast hn]; omega, rfl⟩
  | .f64, bs, v, rest, h => by
    simp [decode, Option.bind_eq_some_iff] at h
    obtain ⟨n, _, h1, h2, rfl, rfl⟩ := h
    obtain ⟨hn, rfl⟩ := readLE_eq_some h1
    exact ⟨_, by simp [encode, h2, intLE_natCast hn]; omega, rfl⟩
  | .string, bs, v, rest, h => by
    simp [decode, Option.bind_eq_some_iff] at h
    obtain ⟨n, b, h1, s, _, h2, h3, rfl, rfl⟩ := h
    obtain ⟨hn, rfl⟩ := readLE_eq_some h1
    obtain ⟨rfl, rfl⟩ := take_eq_some h2
    exact ⟨toLE 4 s.length ++ s, by simp [encode, h3]; omega, by simp⟩
  | .vec t, bs, v, rest, h => by
    simp [decode, Option.bind_eq_some_iff] at h
    obtain ⟨hz, n, b, h1, xs, h2, rfl⟩ := h
    obtain ⟨hn, rfl⟩ := readLE_eq_some h1
    simp only [encode]
    exact enc_seq (enc_dec t) h2 (by simp [hz]; omega)
  | .tuple ts, bs, v, rest, h => by
    simp [decode, Option.bind_eq_some_iff] at h
    obtain ⟨xs, h, rfl⟩ := h
    simpa [encode] using enc_dec_fields ts bs xs rest h
  | .enum vs, [], v, rest, h => by simp [decode] at h
  | .enum vs, tag :: bs, v, rest, h => by
    obtain ⟨i, x, pre, rfl, he, rfl⟩ := enc_dec_variant vs 0 tag bs v rest (by simpa [decode] using h)
    exact ⟨tag :: pre, by simpa [encode] using he [] (by simp), rfl⟩
  | .map kt vt, bs, v, rest, h => by
    simp [decode, Option.bind_eq_some_iff] at h
    obtain ⟨hz, n, b, h1, es, b', h2, ha, rfl, rfl⟩ := h
    obtain ⟨hn, rfl⟩ := readLE_eq_some h1
    simp only [encode]
    refine enc_seq ?_ h2 (by simp [hz, ha]; omega)
    intro bs e r he
    simp [Option.bind_eq_some_iff] at he
    obtain ⟨a, b1, hda, b, hdb, rfl⟩ := he
    obtain ⟨p, hp, rfl⟩ := enc_dec kt _ _ _ hda
    obtain ⟨q, hq, rfl⟩ := enc_dec vt _ _ _ hdb
    exact ⟨p ++ q, by simp [hp, hq], by simp⟩

theorem enc_dec_fields : ∀ (ts : List Schema) (bs : Bytes) (xs : List Value) (rest : Bytes),
    decodeFields ts bs = some (xs, rest) → ∃ pre, encodeFields ts xs = some pre ∧ bs = pre ++ rest
  | [], bs, xs, rest, h => by
    simp [decodeFields] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | t :: ts, bs, xs, rest, h => by
    simp [decodeFields, Option.bind_eq_some_iff] at h
    obtain ⟨x, b, h1, xs, h2, rfl⟩ := h
    obtain ⟨p, hp, rfl⟩ := enc_dec t _ _ _ h1
    obtain ⟨q, hq, rfl⟩ := enc_dec_fields ts _ _ _ h2
    exact ⟨p ++ q, by simp [encodeFields, hp, hq], by simp⟩

theorem enc_dec_variant : ∀ (vs : List (UInt8 × Schema)) (j : Nat) (tag : UInt8) (bs : Bytes)
    (v : Value) (rest : Bytes), decodeVariant vs j tag bs = some (v, rest) →
    ∃ i x pre, v = .variant (j + i) x ∧
      (∀ seen, tag ∉ seen → encodeVariant vs seen i x = some (tag :: pre)) ∧ bs = pre ++ rest
  | [], _, _, _, _, _, h => by simp [decodeVariant] at h
  | (tag', t) :: vs, j, tag, bs, v, rest, h => by
    by_cases ht : tag' = tag
    · subst ht
      simp [decodeVariant] at h
      obtain ⟨x, h, rfl⟩ := h
      obtain ⟨pre, hp, rfl⟩ := enc_dec t _ _ _ h
      exact ⟨0, x, pre, rfl, fun seen hs => by simp [encodeVariant, hs, hp], rfl⟩
    · simp [decodeVariant, ht] at h
      obtain ⟨i, x, pre, rfl, he, rfl⟩ := enc_dec_variant vs (j + 1) tag bs v rest h
      refine ⟨i + 1, x, pre, by simp [Nat.add_assoc, Nat.add_comm 1], fun seen hs => ?_, rfl⟩
      exact he _ (by simp [hs, Ne.symm ht])
end

/-! ## Main theorems -/

/-- Decoding an encoding gives the value back, whatever follows it. -/
theorem decode_encode (s : Schema) (v : Value) (bs rest : Bytes)
    (h : encode s v = some bs) : decode s (bs ++ rest) = some (v, rest) :=
  dec_enc s v bs rest h

/-- The decoder accepts only encodings: whatever it reads is exactly the encoding of the value it returns. -/
theorem encode_decode (s : Schema) (bs : Bytes) (v : Value) (rest : Bytes)
    (h : decode s bs = some (v, rest)) : ∃ pre, encode s v = some pre ∧ bs = pre ++ rest :=
  enc_dec s bs v rest h

/-- Different values have different encodings. -/
theorem encode_injective (s : Schema) (v w : Value) (bs : Bytes)
    (hv : encode s v = some bs) (hw : encode s w = some bs) : v = w := by
  have := (decode_encode s v bs [] hv).symm.trans (decode_encode s w bs [] hw)
  simpa using this

/-- info: 'Borsh.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decode_encode

/-- info: 'Borsh.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms encode_decode

/-- info: 'Borsh.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms encode_injective

end Borsh
