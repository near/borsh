import BorshSpec.Theorems.roundtrip.Complete

/-!
# What the decoder accepts is encodable

For a key policy `P` whose results are strictly ascending sub-collections of what was
read (`PolicySound`), whatever `decodeWith P` returns can be encoded: `encode`
succeeds on it.  If moreover the policy keeps keys as read (`PolicyExact`, true for
the strict policy), the bytes consumed are exactly that encoding.
-/

namespace BorshSpec

namespace RT

open Schema

/-- The policy returns strictly ascending sub-collections of what it is given, and
no more of them. -/
def PolicySound (P : KeyPolicy) : Prop :=
  (∀ xs ys, P.set xs = some ys →
      Value.strictAsc ys = true ∧ (∀ y ∈ ys, y ∈ xs) ∧ ys.length ≤ xs.length) ∧
    (∀ kvs kvs', P.map kvs = some kvs' →
      Value.strictAsc (kvs'.map Prod.fst) = true ∧ (∀ e ∈ kvs', e ∈ kvs) ∧
        kvs'.length ≤ kvs.length)

/-- The policy returns what it is given, when it returns anything. -/
def PolicyExact (P : KeyPolicy) : Prop :=
  (∀ xs ys, P.set xs = some ys → ys = xs) ∧ (∀ kvs kvs', P.map kvs = some kvs' → kvs' = kvs)

/-- The strict policy is sound. -/
theorem sound_strict : PolicySound KeyPolicy.strict := by
  refine ⟨fun xs ys h => ?_, fun kvs kvs' h => ?_⟩
  · simp only [KeyPolicy.strict] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨by assumption, fun _ h => h, Nat.le_refl _⟩
    · simp at h
  · simp only [KeyPolicy.strict] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨by assumption, fun _ h => h, Nat.le_refl _⟩
    · simp at h

/-- The strict policy is exact. -/
theorem exact_strict : PolicyExact KeyPolicy.strict := by
  refine ⟨fun xs ys h => ?_, fun kvs kvs' h => ?_⟩
  · simp only [KeyPolicy.strict] at h
    split at h
    · simp only [Option.some.injEq] at h
      exact h.symm
    · simp at h
  · simp only [KeyPolicy.strict] at h
    split at h
    · simp only [Option.some.injEq] at h
      exact h.symm
    · simp at h

/-- Soundness for the leaf forms: integers, floats, `bool`, `string`. -/
theorem sound_leaf (P : KeyPolicy) (s : Schema) (bs : List UInt8) (v : Value)
    (rest : List UInt8)
    (hs : (∃ w, s = .uint w) ∨ (∃ w, s = .sint w) ∨ s = .f32 ∨ s = .f64 ∨ s = .bool ∨
      s = .string)
    (h : decodeWith P s bs = some (v, rest)) :
    ∃ pre, bs = pre ++ rest ∧ encode s v = some pre := by
  rcases hs with ⟨w, rfl⟩ | ⟨w, rfl⟩ | rfl | rfl | rfl | rfl
  · simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨n, r⟩, hr, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨hn, rfl⟩ := readLE_eq_some hr
    simp [encode, hn]
  · simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨n, r⟩, hr, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨hn, rfl⟩ := readLE_eq_some hr
    have hr' := sintInRange_natToSint w n hn
    simp [encode, hr', sintToNat_natToSint w n hn]
  · simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i n r hr
      split at h
      · simp at h
      · rename_i hnan
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hn, rfl⟩ := readLE_eq_some hr
        have hn' : n < 2 ^ 32 := by simpa using hn
        have hnan' : isNaN32 (UInt32.ofNat n) = false := by simpa using hnan
        simp [encode, hnan', UInt32.toNat_ofNat_of_lt' hn']
  · simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i n r hr
      split at h
      · simp at h
      · rename_i hnan
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hn, rfl⟩ := readLE_eq_some hr
        have hn' : n < 2 ^ 64 := by simpa using hn
        have hnan' : isNaN64 (UInt64.ofNat n) = false := by simpa using hnan
        simp [encode, hnan', UInt64.toNat_ofNat_of_lt' hn']
  · simp only [decodeWith] at h
    split at h
    · rename_i b r
      split at h
      · rename_i hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hb
        simp [encode]
      · split at h
        · rename_i hb0 hb
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          subst hb
          simp [encode]
        · simp at h
    · simp at h
  · simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i n r hr
      split at h
      · simp at h
      · rename_i body r' hk
        split at h
        · rename_i hv
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hn, rfl⟩ := readLE_eq_some hr
          obtain ⟨hl, rfl⟩ := takeExact_eq_some hk
          subst hl
          have hn' : body.length < 2 ^ 32 := by simpa using hn
          simp [encode, hv, hn']
        · simp at h

mutual

/-- **Soundness of decoding.**  If `decodeWith P s bs` succeeds with value `v` and
unread bytes `rest`, then `v` is encodable and, when the policy is exact, the bytes
consumed are exactly its encoding. -/
theorem sound (P : KeyPolicy) (hS : PolicySound P) :
    ∀ (s : Schema) (bs : List UInt8) (v : Value) (rest : List UInt8),
      decodeWith P s bs = some (v, rest) →
        ∃ pre, encode s v = some pre ∧ (PolicyExact P → bs = pre ++ rest)
  | .uint w, bs, v, rest, h => by
    obtain ⟨pre, hb, he⟩ := sound_leaf P _ bs v rest (.inl ⟨w, rfl⟩) h
    exact ⟨pre, he, fun _ => hb⟩
  | .sint w, bs, v, rest, h => by
    obtain ⟨pre, hb, he⟩ := sound_leaf P _ bs v rest (.inr (.inl ⟨w, rfl⟩)) h
    exact ⟨pre, he, fun _ => hb⟩
  | .f32, bs, v, rest, h => by
    obtain ⟨pre, hb, he⟩ := sound_leaf P _ bs v rest (.inr (.inr (.inl rfl))) h
    exact ⟨pre, he, fun _ => hb⟩
  | .f64, bs, v, rest, h => by
    obtain ⟨pre, hb, he⟩ := sound_leaf P _ bs v rest (.inr (.inr (.inr (.inl rfl)))) h
    exact ⟨pre, he, fun _ => hb⟩
  | .bool, bs, v, rest, h => by
    obtain ⟨pre, hb, he⟩ :=
      sound_leaf P _ bs v rest (.inr (.inr (.inr (.inr (.inl rfl))))) h
    exact ⟨pre, he, fun _ => hb⟩
  | .string, bs, v, rest, h => by
    obtain ⟨pre, hb, he⟩ :=
      sound_leaf P _ bs v rest (.inr (.inr (.inr (.inr (.inr rfl))))) h
    exact ⟨pre, he, fun _ => hb⟩
  | .option s, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · rename_i b r
      split at h
      · rename_i hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hb
        exact ⟨[0], by simp [encode], fun _ => by simp⟩
      · split at h
        · rename_i hb0 hb1
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨v', r'⟩, hd, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨rfl, rfl⟩ := hv
          obtain ⟨pre, he, hb⟩ := sound P hS s r v' r' hd
          subst hb1
          exact ⟨1 :: pre, by simp [encode, he], fun hE => by simp [hb hE]⟩
        · simp at h
    · simp at h
  | .vec s, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i hz
      split at h
      · simp at h
      · rename_i n r hr
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨xs, r'⟩, hm, hv⟩ := h
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        obtain ⟨hn, rfl⟩ := readLE_eq_some hr
        obtain ⟨hlen, hP, hb⟩ := decodeMany_sound (fun b => decodeWith P s b) (encode s)
          (PolicyExact P)
          (fun b x r hb => by
            obtain ⟨pre, he, hpre⟩ := sound P hS s b x r hb
            exact ⟨pre, he, hpre⟩) n r xs r' hm
        subst hlen
        have hz' : s.zeroSized = false := by simpa using hz
        have hn' : xs.length < 2 ^ 32 := by simpa using hn
        obtain ⟨es, hes⟩ := mapM_isSome (encode s) xs hP
        refine ⟨toLE 4 xs.length ++ es.flatten, by simp [encode, hz', hn', hes], fun hE => ?_⟩
        obtain ⟨es', hes', hb'⟩ := hb hE
        rw [hes] at hes'
        obtain rfl := Option.some.inj hes'
        simp [hb']
  | .array n s, bs, v, rest, h => by
    simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨xs, r⟩, hm, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨hlen, hP, hb⟩ := decodeMany_sound (fun b => decodeWith P s b) (encode s)
      (PolicyExact P)
      (fun b x r hb => by
        obtain ⟨pre, he, hpre⟩ := sound P hS s b x r hb
        exact ⟨pre, he, hpre⟩) n bs xs r hm
    obtain ⟨es, hes⟩ := mapM_isSome (encode s) xs hP
    refine ⟨es.flatten, by simp [encode, hlen, hes], fun hE => ?_⟩
    obtain ⟨es', hes', hb'⟩ := hb hE
    rw [hes] at hes'
    obtain rfl := Option.some.inj hes'
    exact hb'
  | .tuple fs, bs, v, rest, h => by
    simp only [decodeWith, Option.map_eq_some_iff] at h
    obtain ⟨⟨xs, r⟩, hf, hv⟩ := h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨pre, he, hb⟩ := soundFields P hS fs bs xs r hf
    exact ⟨pre, by simpa [encode] using he, hb⟩
  | .enum vs, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · rename_i t r
      obtain ⟨i, w, pre, hv, he, hb⟩ := soundVariant P hS vs 0 t r v rest h [] (by simp)
      subst hv
      refine ⟨t :: pre, by simpa [encode] using he, fun hE => ?_⟩
      simp [hb hE]
    · simp at h
  | .map k s, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i hz
      split at h
      · simp at h
      · rename_i n r hr
        split at h
        · simp at h
        · rename_i kvs r' hm
          rw [Option.map_eq_some_iff] at h
          obtain ⟨kvs', hpm, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨rfl, rfl⟩ := hv
          obtain ⟨hn, rfl⟩ := readLE_eq_some hr
          obtain ⟨hlen, hP, hb⟩ := decodeMany_sound _
            (fun (p : Value × Value) => do
              let ea ← encode k p.1
              let eb ← encode s p.2
              pure (ea ++ eb))
            (PolicyExact P)
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
                  obtain ⟨p1, he1, hp1⟩ := sound P hS k b _ _ ha
                  obtain ⟨p2, he2, hp2⟩ := sound P hS s r₁ _ _ hc
                  exact ⟨p1 ++ p2, by simp [he1, he2, bind, pure], fun hE => by
                    simp [hp1 hE, hp2 hE]⟩) n r kvs r' hm
          subst hlen
          obtain ⟨hsa, hsub, hlen'⟩ := hS.2 kvs kvs' hpm
          have hz' : k.zeroSized = false := by simpa using hz
          have hn' : kvs'.length < 2 ^ 32 := by
            have : kvs.length < 2 ^ 32 := by simpa using hn
            omega
          obtain ⟨es, hes⟩ := mapM_isSome _ kvs' (fun x hx => hP x (hsub x hx))
          refine ⟨toLE 4 kvs'.length ++ es.flatten, ?_, fun hE => ?_⟩
          · simp [encode, hz', hn', hsa]
            exact ⟨es, hes, rfl⟩
          · obtain rfl := hE.2 kvs kvs' hpm
            obtain ⟨es', hes', hb'⟩ := hb hE
            rw [hes] at hes'
            obtain rfl := Option.some.inj hes'
            simp [hb']
  | .set s, bs, v, rest, h => by
    simp only [decodeWith] at h
    split at h
    · simp at h
    · rename_i hz
      split at h
      · simp at h
      · rename_i n r hr
        split at h
        · simp at h
        · rename_i xs r' hm
          rw [Option.map_eq_some_iff] at h
          obtain ⟨xs', hpm, hv⟩ := h
          simp only [Prod.mk.injEq] at hv
          obtain ⟨rfl, rfl⟩ := hv
          obtain ⟨hn, rfl⟩ := readLE_eq_some hr
          obtain ⟨hlen, hP, hb⟩ := decodeMany_sound (fun b => decodeWith P s b) (encode s)
            (PolicyExact P)
            (fun b x r hb => by
              obtain ⟨pre, he, hpre⟩ := sound P hS s b x r hb
              exact ⟨pre, he, hpre⟩) n r xs r' hm
          subst hlen
          obtain ⟨hsa, hsub, hlen'⟩ := hS.1 xs xs' hpm
          have hz' : s.zeroSized = false := by simpa using hz
          have hn' : xs'.length < 2 ^ 32 := by
            have : xs.length < 2 ^ 32 := by simpa using hn
            omega
          obtain ⟨es, hes⟩ := mapM_isSome (encode s) xs' (fun x hx => hP x (hsub x hx))
          refine ⟨toLE 4 xs'.length ++ es.flatten, ?_, fun hE => ?_⟩
          · simp [encode, hz', hn', hsa, hes]
          · obtain rfl := hE.1 xs xs' hpm
            obtain ⟨es', hes', hb'⟩ := hb hE
            rw [hes] at hes'
            obtain rfl := Option.some.inj hes'
            simp [hb']

/-- Soundness of decoding for the fields of a tuple. -/
theorem soundFields (P : KeyPolicy) (hS : PolicySound P) :
    ∀ (fs : List Schema) (bs : List UInt8) (vs : List Value) (rest : List UInt8),
      decodeFieldsWith P fs bs = some (vs, rest) →
        ∃ pre, encodeFields fs vs = some pre ∧ (PolicyExact P → bs = pre ++ rest)
  | [], bs, vs, rest, h => by
    simp only [decodeFieldsWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [encodeFields], fun _ => by simp⟩
  | s :: fs, bs, vs, rest, h => by
    simp only [decodeFieldsWith] at h
    split at h
    · simp at h
    · rename_i v r hv
      split at h
      · simp at h
      · rename_i vs' r' hvs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨p1, he1, hp1⟩ := sound P hS s bs v r hv
        obtain ⟨p2, he2, hp2⟩ := soundFields P hS fs r vs' r' hvs
        exact ⟨p1 ++ p2, by simp [encodeFields, he1, he2, bind, pure], fun hE => by
          simp [hp1 hE, hp2 hE]⟩

/-- Soundness of decoding for the payload of an enum variant.  The decoder searches `vs`
from index `j` for the tag `t`; `earlier` holds the tags of the variants before `vs`,
none of which is `t`. -/
theorem soundVariant (P : KeyPolicy) (hS : PolicySound P) :
    ∀ (vs : List (UInt8 × Schema)) (j : Nat) (t : UInt8) (bs : List UInt8) (v : Value)
      (rest : List UInt8), decodeVariantWith P vs j t bs = some (v, rest) →
      ∀ (earlier : List UInt8), earlier.contains t = false →
        ∃ (i : Nat) (w : Value) (pre : List UInt8), v = .enum (j + i) w ∧
          encodeVariant vs earlier i w = some (t :: pre) ∧
          (PolicyExact P → bs = pre ++ rest)
  | [], j, t, bs, v, rest, h => by simp [decodeVariantWith] at h
  | (t', s) :: vs, j, t, bs, v, rest, h => by
    intro earlier hearlier
    by_cases ht : t' == t
    · simp only [decodeVariantWith, ht, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨w, r⟩, hd, hv⟩ := h
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨pre, he, hpre⟩ := sound P hS s bs _ _ hd
      have := eq_of_beq ht
      subst this
      have hn : ¬ t' ∈ earlier := by simpa using hearlier
      exact ⟨0, w, pre, by simp, by simp [encodeVariant, hn, he], hpre⟩
    · simp only [decodeVariantWith, ht, Bool.false_eq_true, ↓reduceIte] at h
      have hne : (t' :: earlier).contains t = false := by
        have h1 : ¬ t' = t := fun hh => ht (by simp [hh])
        have h2 : ¬ t ∈ earlier := by simpa using hearlier
        simp [h1, h2, eq_comm]
      obtain ⟨i, w, pre, hv, he, hpre⟩ := soundVariant P hS vs (j + 1) t bs v rest h (t' :: earlier) hne
      exact ⟨i + 1, w, pre, by rw [hv]; congr 1; omega, by simpa [encodeVariant] using he, hpre⟩

end

end RT

end BorshSpec
