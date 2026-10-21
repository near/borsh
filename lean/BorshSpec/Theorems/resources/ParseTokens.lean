import BorshSpec
import BorshSpec.Theorems.resources.HexLemmas

/-!
# The schema printer and the tokenizer

Helper lemmas for `parse_print` in `Theorems/Resources.lean`, first stage: the tokens
of the printed text.  `toks s` is the token list that `tokenize (print s)` produces;
`tokenize_print` says so.
-/

namespace BorshSpec

namespace Parse

/-- A character that may occur in a word: `a-z` or `0-9`. -/
def WordChar (c : Char) : Prop := ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9')

instance (c : Char) : Decidable (WordChar c) := inferInstanceAs (Decidable (_ ∨ _))

/-- A word character is none of the separators. -/
theorem WordChar.ne {c : Char} (h : WordChar c) : c ≠ ' ' ∧ c ≠ '(' ∧ c ≠ ')' := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;> revert h <;> decide

/-- Separators only: what may follow a word. -/
def Bnd (l : List Char) : Prop := l = [] ∨ l.head? = some ' ' ∨ l.head? = some ')'

/-- The tokenizer reads a run of word characters into the current word. -/
theorem tokenizeAux_word : ∀ (ds cur : List Char) (acc : List Token) (rest : List Char),
    (∀ c ∈ ds, WordChar c) →
    tokenizeAux (ds ++ rest) cur acc = tokenizeAux rest (ds.reverse ++ cur) acc
  | [], cur, acc, rest, _ => by simp
  | c :: ds, cur, acc, rest, h => by
    have hc := h c (by simp)
    obtain ⟨h1, h2, h3⟩ := hc.ne
    have h' : ∀ d ∈ ds, WordChar d := fun d hd => h d (by simp [hd])
    have hw : ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9') := hc
    simp only [List.cons_append, tokenizeAux, h1, h2, h3, hw, ite_false, ite_true]
    rw [tokenizeAux_word ds (c :: cur) acc rest h']
    simp

/-- A nonempty word followed by a separator (or the end) becomes one token. -/
theorem tokenizeAux_wordTok (ws : List Char) (acc : List Token) (rest : List Char)
    (hne : ws ≠ []) (hw : ∀ c ∈ ws, WordChar c) (hb : Bnd rest) :
    tokenizeAux (ws ++ rest) [] acc = tokenizeAux rest [] (.word (String.ofList ws) :: acc) := by
  rw [tokenizeAux_word ws [] acc rest hw]
  have hr : ws.reverse ≠ [] := by simpa using hne
  rcases hb with rfl | hb | hb
  · cases hws : ws.reverse with
    | nil => exact absurd hws hr
    | cons x xs =>
      simp only [List.append_nil, tokenizeAux, flushWord]
      rw [← List.reverse_reverse ws, hws]
  · cases rest with
    | nil => simp at hb
    | cons c cs =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      cases hws : ws.reverse with
      | nil => exact absurd hws hr
      | cons x xs =>
        simp only [List.append_nil, tokenizeAux, flushWord, ite_true]
        rw [← List.reverse_reverse ws, hws]
  · cases rest with
    | nil => simp at hb
    | cons c cs =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      cases hws : ws.reverse with
      | nil => exact absurd hws hr
      | cons x xs =>
        simp only [List.append_nil, tokenizeAux, flushWord]
        rw [← List.reverse_reverse ws, hws]
        simp

/-- The digits of a number are word characters. -/
theorem digits_word (n : Nat) : ∀ c ∈ (toString n).toList, WordChar c := by
  intro c hc
  have hc' : c ∈ Nat.toDigits 10 n := by simpa using hc
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc'
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
  right
  exact ⟨Char.le_def.2 this.1, Char.le_def.2 this.2⟩

/-- A number has at least one digit. -/
theorem digits_ne_nil (n : Nat) : (toString n).toList ≠ [] := by
  simp

/-- `parseNat` reads back the decimal text of a number. -/
theorem parseNat_toString (n : Nat) : parseNat (toString n) = some n := by
  unfold parseNat
  have hne := Nat.toDigits_ne_nil (n := n) (b := 10)
  have key : ∀ (l : List Char) (init : Nat), (∀ c ∈ l, '0' ≤ c ∧ c ≤ '9') →
      l.foldlM (fun acc c => if '0' ≤ c ∧ c ≤ '9' then some (acc * 10 + (c.toNat - '0'.toNat))
        else none) init = some (Nat.ofDigitChars 10 l init) := by
    intro l
    induction l with
    | nil => intro init _; simp
    | cons c cs ih =>
      intro init h
      have hc := h c (by simp)
      simp only [List.foldlM_cons, hc, and_self, ite_true]
      simp only [bind, Option.bind]
      rw [ih _ (fun d hd => h d (by simp [hd]))]
      rw [Nat.ofDigitChars_cons, Nat.mul_comm 10 init]
  have hd : ∀ c ∈ Nat.toDigits 10 n, '0' ≤ c ∧ c ≤ '9' := by
    intro c hc
    have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨Char.le_def.2 this.1, Char.le_def.2 this.2⟩
  have e : (toString n).toList = Nat.toDigits 10 n := by simp
  rw [e]
  obtain ⟨c, cs, hl⟩ : ∃ c cs, Nat.toDigits 10 n = c :: cs := by
    cases h : Nat.toDigits 10 n with
    | nil => exact absurd h hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  rw [hl]
  simp only
  rw [key (c :: cs) 0 (by rw [← hl]; exact hd)]
  rw [← hl, Nat.ofDigitChars_ten_toDigits]

/-- The tokenizer on a keyword form `(kw body)`, with `body` empty or starting with a
space. -/
theorem tokenizeAux_form (kw body rest : List Char) (acc : List Token) (hne : kw ≠ [])
    (hw : ∀ c ∈ kw, WordChar c) (hb : body = [] ∨ body.head? = some ' ') :
    tokenizeAux ('(' :: (kw ++ body ++ ')' :: rest)) [] acc =
      tokenizeAux (body ++ ')' :: rest) [] (.word (String.ofList kw) :: .lparen :: acc) := by
  simp only [tokenizeAux, flushWord, ite_false, ite_true, show ('(' : Char) ≠ ' ' by decide]
  rw [List.append_assoc, tokenizeAux_wordTok kw _ _ hne hw]
  rcases hb with rfl | hb
  · right; right; rfl
  · cases body with
    | nil => simp at hb
    | cons c cs =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      right; left; rfl

/-- The tokenizer on a closing parenthesis. -/
theorem tokenizeAux_close (rest : List Char) (acc : List Token) :
    tokenizeAux (')' :: rest) [] acc = tokenizeAux rest [] (.rparen :: acc) := by
  simp [tokenizeAux, flushWord]

/-- The tokenizer on a space. -/
theorem tokenizeAux_space (rest : List Char) (acc : List Token) :
    tokenizeAux (' ' :: rest) [] acc = tokenizeAux rest [] acc := by
  simp [tokenizeAux, flushWord]

open Schema in
mutual

/-- The tokens of the printed text of a schema. -/
def toks : Schema → List Token
  | .uint w => [.word (String.ofList ('u' :: (IntWidth.bits w).toList))]
  | .sint w => [.word (String.ofList ('i' :: (IntWidth.bits w).toList))]
  | .f32 => [.word "f32"]
  | .f64 => [.word "f64"]
  | .bool => [.word "bool"]
  | .string => [.word "string"]
  | .option s => .lparen :: .word "option" :: (toks s ++ [.rparen])
  | .vec s => .lparen :: .word "vec" :: (toks s ++ [.rparen])
  | .array n s => .lparen :: .word "array" :: .word (toString n) :: (toks s ++ [.rparen])
  | .tuple [] => [.word "unit"]
  | .tuple (f :: fs) => .lparen :: .word "tuple" :: (toksFields (f :: fs) ++ [.rparen])
  | .enum vs => .lparen :: .word "enum" :: (toksVariants vs ++ [.rparen])
  | .map k v => .lparen :: .word "map" :: (toks k ++ toks v ++ [.rparen])
  | .set s => .lparen :: .word "set" :: (toks s ++ [.rparen])

/-- The tokens of the printed fields of a tuple. -/
def toksFields : List Schema → List Token
  | [] => []
  | s :: fs => toks s ++ toksFields fs

/-- The tokens of the printed variants of an enum. -/
def toksVariants : List (UInt8 × Schema) → List Token
  | [] => []
  | (t, s) :: vs => .lparen :: .word (toString t.toNat) :: (toks s ++ .rparen :: toksVariants vs)

end

/-- A form `(kw <body>)` whose body is a single schema. -/
theorem tokenizeAux_unary (kw : List Char) (hne : kw ≠ []) (hw : ∀ c ∈ kw, WordChar c)
    (ps : List Char) (ts : List Token) (rest : List Char) (acc : List Token)
    (ih : ∀ rest acc, Bnd rest → tokenizeAux (ps ++ rest) [] acc =
      tokenizeAux rest [] (ts.reverse ++ acc)) :
    tokenizeAux (('(' :: (kw ++ (' ' :: ps) ++ [')'])) ++ rest) [] acc =
      tokenizeAux rest [] ((.lparen :: .word (String.ofList kw) :: (ts ++ [.rparen])).reverse ++
        acc) := by
  have e : ('(' :: (kw ++ (' ' :: ps) ++ [')'])) ++ rest =
      '(' :: (kw ++ (' ' :: ps) ++ ')' :: rest) := by simp
  rw [e, tokenizeAux_form kw _ rest acc hne hw (Or.inr rfl)]
  simp only [List.cons_append, tokenizeAux_space]
  rw [ih (')' :: rest) _ (Or.inr (Or.inr rfl)), tokenizeAux_close]
  simp


/-- What follows the printed fields of a tuple is still a boundary. -/
theorem printFields_bnd (fs : List Schema) (rest : List Char) (hb : Bnd rest) :
    Bnd (Schema.printFields fs ++ rest) := by
  cases fs with
  | nil => simpa [Schema.printFields] using hb
  | cons f fs => right; left; simp [Schema.printFields]

/-- What follows the printed variants of an enum is still a boundary. -/
theorem printVariants_bnd (vs : List (UInt8 × Schema)) (rest : List Char) (hb : Bnd rest) :
    Bnd (Schema.printVariants vs ++ rest) := by
  cases vs with
  | nil => simpa [Schema.printVariants] using hb
  | cons v vs => right; left; simp [Schema.printVariants]

/-- Printed fields are empty or start with a space. -/
theorem printFields_head (fs : List Schema) :
    Schema.printFields fs = [] ∨ (Schema.printFields fs).head? = some ' ' := by
  cases fs with
  | nil => left; simp [Schema.printFields]
  | cons f fs => right; simp [Schema.printFields]

/-- Printed variants are empty or start with a space. -/
theorem printVariants_head (vs : List (UInt8 × Schema)) :
    Schema.printVariants vs = [] ∨ (Schema.printVariants vs).head? = some ' ' := by
  cases vs with
  | nil => left; simp [Schema.printVariants]
  | cons v vs => right; simp [Schema.printVariants]

/-- The tokenizer on an opening parenthesis. -/
theorem tokenizeAux_open (rest : List Char) (acc : List Token) :
    tokenizeAux ('(' :: rest) [] acc = tokenizeAux rest [] (.lparen :: acc) := by
  simp [tokenizeAux, flushWord]

mutual

/-- The printed text of a schema tokenizes to `toks`. -/
theorem tokenizeAux_print : ∀ (s : Schema) (rest : List Char) (acc : List Token), Bnd rest →
    tokenizeAux (Schema.printChars s ++ rest) [] acc =
      tokenizeAux rest [] ((toks s).reverse ++ acc)
  | .uint w, rest, acc, hb => by
    have := tokenizeAux_wordTok ('u' :: (IntWidth.bits w).toList) acc rest (by simp)
      (by cases w <;> decide) hb
    simpa [Schema.printChars, toks] using this
  | .sint w, rest, acc, hb => by
    have := tokenizeAux_wordTok ('i' :: (IntWidth.bits w).toList) acc rest (by simp)
      (by cases w <;> decide) hb
    simpa [Schema.printChars, toks] using this
  | .f32, rest, acc, hb => by
    have := tokenizeAux_wordTok "f32".toList acc rest (by decide) (by decide) hb
    simpa [Schema.printChars, toks] using this
  | .f64, rest, acc, hb => by
    have := tokenizeAux_wordTok "f64".toList acc rest (by decide) (by decide) hb
    simpa [Schema.printChars, toks] using this
  | .bool, rest, acc, hb => by
    have := tokenizeAux_wordTok "bool".toList acc rest (by decide) (by decide) hb
    simpa [Schema.printChars, toks] using this
  | .string, rest, acc, hb => by
    have := tokenizeAux_wordTok "string".toList acc rest (by decide) (by decide) hb
    simpa [Schema.printChars, toks] using this
  | .tuple [], rest, acc, hb => by
    have := tokenizeAux_wordTok "unit".toList acc rest (by decide) (by decide) hb
    simpa [Schema.printChars, toks] using this
  | .option s, rest, acc, _ => by
    have := tokenizeAux_unary "option".toList (by decide) (by decide) (Schema.printChars s)
      (toks s) rest acc (fun rest acc hb => tokenizeAux_print s rest acc hb)
    simpa [Schema.printChars, toks] using this
  | .vec s, rest, acc, _ => by
    have := tokenizeAux_unary "vec".toList (by decide) (by decide) (Schema.printChars s)
      (toks s) rest acc (fun rest acc hb => tokenizeAux_print s rest acc hb)
    simpa [Schema.printChars, toks] using this
  | .set s, rest, acc, _ => by
    have := tokenizeAux_unary "set".toList (by decide) (by decide) (Schema.printChars s)
      (toks s) rest acc (fun rest acc hb => tokenizeAux_print s rest acc hb)
    simpa [Schema.printChars, toks] using this
  | .array n s, rest, acc, _ => by
    have e : Schema.printChars (.array n s) ++ rest =
        '(' :: ("array".toList ++ (' ' :: ((toString n).toList ++ ' ' :: Schema.printChars s)) ++
          ')' :: rest) := by
      simp [Schema.printChars]
    rw [e, tokenizeAux_form "array".toList _ rest acc (by decide) (by decide) (Or.inr rfl)]
    simp only [List.cons_append, List.append_assoc, tokenizeAux_space]
    rw [tokenizeAux_wordTok (toString n).toList _ _ (digits_ne_nil n) (digits_word n)
      (Or.inr (Or.inl rfl)), tokenizeAux_space,
      tokenizeAux_print s (')' :: rest) _ (Or.inr (Or.inr rfl)), tokenizeAux_close]
    simp only [toks, List.reverse_cons, List.reverse_append, List.append_assoc, List.cons_append, List.nil_append, List.reverse_nil, String.ofList_toList]
  | .tuple (f :: fs), rest, acc, _ => by
    have e : Schema.printChars (.tuple (f :: fs)) ++ rest =
        '(' :: ("tuple".toList ++ Schema.printFields (f :: fs) ++ ')' :: rest) := by
      simp [Schema.printChars]
    rw [e, tokenizeAux_form "tuple".toList _ rest acc (by decide) (by decide)
      (printFields_head _)]
    rw [tokenizeAux_fields (f :: fs) (')' :: rest) _ (Or.inr (Or.inr rfl)), tokenizeAux_close]
    simp only [toks, toksFields, List.reverse_cons, List.reverse_append, List.append_assoc, List.cons_append, List.nil_append, List.reverse_nil, String.ofList_toList]
  | .enum vs, rest, acc, _ => by
    have e : Schema.printChars (.enum vs) ++ rest =
        '(' :: ("enum".toList ++ Schema.printVariants vs ++ ')' :: rest) := by
      simp [Schema.printChars]
    rw [e, tokenizeAux_form "enum".toList _ rest acc (by decide) (by decide)
      (printVariants_head _)]
    rw [tokenizeAux_variants vs (')' :: rest) _ (Or.inr (Or.inr rfl)), tokenizeAux_close]
    simp only [toks, List.reverse_cons, List.reverse_append, List.append_assoc, List.cons_append, List.nil_append, List.reverse_nil, String.ofList_toList]
  | .map k v, rest, acc, _ => by
    have e : Schema.printChars (.map k v) ++ rest =
        '(' :: ("map".toList ++ (' ' :: (Schema.printChars k ++ ' ' :: Schema.printChars v)) ++
          ')' :: rest) := by
      simp [Schema.printChars]
    rw [e, tokenizeAux_form "map".toList _ rest acc (by decide) (by decide) (Or.inr rfl)]
    simp only [List.cons_append, List.append_assoc, tokenizeAux_space]
    rw [tokenizeAux_print k (' ' :: (Schema.printChars v ++ ')' :: rest)) _ (Or.inr (Or.inl rfl)),
      tokenizeAux_space, tokenizeAux_print v (')' :: rest) _ (Or.inr (Or.inr rfl)),
      tokenizeAux_close]
    simp only [toks, List.reverse_cons, List.reverse_append, List.append_assoc, List.cons_append, List.nil_append, List.reverse_nil, String.ofList_toList]

/-- The printed fields of a tuple tokenize to `toksFields`. -/
theorem tokenizeAux_fields : ∀ (fs : List Schema) (rest : List Char) (acc : List Token),
    Bnd rest → tokenizeAux (Schema.printFields fs ++ rest) [] acc =
      tokenizeAux rest [] ((toksFields fs).reverse ++ acc)
  | [], rest, acc, _ => by simp [Schema.printFields, toksFields]
  | s :: fs, rest, acc, hb => by
    have e : Schema.printFields (s :: fs) ++ rest =
        ' ' :: (Schema.printChars s ++ (Schema.printFields fs ++ rest)) := by
      simp [Schema.printFields]
    rw [e, tokenizeAux_space, tokenizeAux_print s _ acc (printFields_bnd fs rest hb),
      tokenizeAux_fields fs rest _ hb]
    simp only [toksFields, List.reverse_append, List.append_assoc]

/-- The printed variants of an enum tokenize to `toksVariants`. -/
theorem tokenizeAux_variants : ∀ (vs : List (UInt8 × Schema)) (rest : List Char)
    (acc : List Token), Bnd rest → tokenizeAux (Schema.printVariants vs ++ rest) [] acc =
      tokenizeAux rest [] ((toksVariants vs).reverse ++ acc)
  | [], rest, acc, _ => by simp [Schema.printVariants, toksVariants]
  | (t, s) :: vs, rest, acc, hb => by
    have e : Schema.printVariants ((t, s) :: vs) ++ rest =
        ' ' :: '(' :: ((toString t.toNat).toList ++ ' ' :: (Schema.printChars s ++
          ')' :: (Schema.printVariants vs ++ rest))) := by
      simp [Schema.printVariants]
    rw [e, tokenizeAux_space, tokenizeAux_open,
      tokenizeAux_wordTok (toString t.toNat).toList _ _ (digits_ne_nil _) (digits_word _)
        (Or.inr (Or.inl rfl)), tokenizeAux_space,
      tokenizeAux_print s (')' :: (Schema.printVariants vs ++ rest)) _ (Or.inr (Or.inr rfl)),
      tokenizeAux_close, tokenizeAux_variants vs rest _ hb]
    simp only [toksVariants, List.reverse_cons, List.reverse_append, List.append_assoc, List.cons_append, List.nil_append, String.ofList_toList]

end

end Parse

end BorshSpec
