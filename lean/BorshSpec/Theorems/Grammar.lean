import BorshSpec
import BorshSpec.Theorems.grammar.Decode
import BorshSpec.Theorems.grammar.Utf8Std

/-!
# Agreement with the relational grammar

`Encodes s v bs` (declared in `BorshSpec/Grammar.lean`) is the relational form of the
format: `bs` is the encoding of `v` under `s`.  `WellFormedUtf8 bs` (declared in
`BorshSpec/Utf8Grammar.lean`) is the UTF-8 grammar of RFC 3629 (Unicode Table 3-7),
written without reference to the executable validator.

`Encodes` describes the *canonical* format with all of its bans (zero-sized
`vec`/`set`/map-key elements, NaN, UTF-8, strictly ascending keys in the key order,
the first-variant rule for repeated enum tags), so the statements need no hypothesis
on the schema.  The grammar shares with the codec the key order `Value.cmp`, the
integer widths and the representation of values; it restates the structure, the
bans, the byte layout of integers and floats, and the UTF-8 rules independently.

The proofs are in the helper modules under `BorshSpec/Theorems/grammar/`:
`Utf8` (validator against Table 3-7), `Utf8Std` (against Lean's `validateUTF8`),
`Leaf` (little-endian bytes, two's complement, NaN tests, reading primitives),
`Inversion` (what `Encodes` means for each schema constructor), `Encode` (the
encoder) and `Decode` (the decoder).  Each theorem here only names the result it
needs from them.
-/

namespace BorshSpec

/-- `decode` reads a value from a prefix exactly when the prefix is related to the
value by the grammar: decoding `bs ++ rest` returns `(v, rest)` iff `Encodes s v bs`. -/
theorem decode_iff_encodes (s : Schema) (v : Value) (bs rest : List UInt8) :
    decode s (bs ++ rest) = some (v, rest) ↔ Encodes s v bs := by
  unfold decode
  rw [GrammarProof.decode_iff]
  constructor
  · rintro ⟨b, h, h2⟩
    obtain rfl := List.append_cancel_right h
    exact h2
  · intro h
    exact ⟨bs, rfl, h⟩

/-- `encode` produces exactly the bytes related to the value by the grammar. -/
theorem encode_iff_encodes (s : Schema) (v : Value) (bs : List UInt8) :
    encode s v = some bs ↔ Encodes s v bs :=
  GrammarProof.encode_iff s v bs

/-- The executable UTF-8 validator accepts exactly the well-formed byte sequences. -/
theorem validUtf8_iff (bs : List UInt8) : validUtf8 bs = true ↔ WellFormedUtf8 bs :=
  GrammarProof.validUtf8_iff_wf bs

/-! ## Agreement of the leaf definitions

The codec and the grammar write the little-endian bytes, the two's complement pattern
and the NaN test separately.  These statements say that the pairs agree. -/

/-- The codec's little-endian encoding is the grammar's `leBytes`. -/
theorem toLE_eq_leBytes (w n : Nat) : toLE w n = leBytes w n :=
  GrammarProof.toLE_eq_leBytes w n

/-- The codec's two's complement residue is the grammar's. -/
theorem sintToNat_eq_twosComplement (w : IntWidth) (i : Int) :
    Schema.sintToNat w i = twosComplement w.bytes i :=
  GrammarProof.sintToNat_eq_twosComplement w i

/-- The codec's `binary32` NaN test is the grammar's. -/
theorem isNaN32_iff (bits : UInt32) : isNaN32 bits = true ↔ IsNaN32 bits :=
  GrammarProof.isNaN32_iff bits

/-- The codec's `binary64` NaN test is the grammar's. -/
theorem isNaN64_iff (bits : UInt64) : isNaN64 bits = true ↔ IsNaN64 bits :=
  GrammarProof.isNaN64_iff bits

/-- The executable UTF-8 validator agrees with the validator of Lean's standard library
on every byte string.  This is the fact that `borsh-spec selftest-utf8` tests on a
bounded set of inputs, and it states `validUtf8_iff` once more without the table. -/
theorem validUtf8_iff_validateUTF8 (bs : List UInt8) :
    validUtf8 bs = true ↔ ByteArray.validateUTF8 (ByteArray.mk bs.toArray) = true :=
  GrammarProof.validUtf8_iff_validateUTF8 bs

end BorshSpec
