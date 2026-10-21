import BorshSpec.Theorems.RoundTrip
import BorshSpec.Theorems.Grammar
import BorshSpec.Theorems.Resources

/-!
# Axiom footprint

Every theorem listed here (the headline results of `RoundTrip.lean`, `Grammar.lean` and
`Resources.lean`) depends only on the three standard axioms of Lean's classical logic
(`propext`, `Classical.choice`, `Quot.sound`), or on fewer.  None depends on the
placeholder `sorryAx`, on `Lean.ofReduceBool` (which compiled evaluation would
introduce) or on a postulate declared in this repository.  The helper lemmas in the
lowercase directories are covered transitively: whatever they use, the theorems listed
here use at most.

Each check below fails the build if the reported list changes, so a new dependency on
an unfinished proof or on compiled evaluation is caught when it is introduced.
-/

namespace BorshSpec.Axioms

/-- info: 'BorshSpec.toLE_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BorshSpec.toLE_length

/-- info: 'BorshSpec.fromLE_toLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.fromLE_toLE

/-- info: 'BorshSpec.natToSint_sintToNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.natToSint_sintToNat

/-- info: 'BorshSpec.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_encode

/-- info: 'BorshSpec.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.encode_decode

/-- info: 'BorshSpec.decode_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_eq_some_iff

/-- info: 'BorshSpec.decode_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_append

/-- info: 'BorshSpec.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.encode_injective

/-- info: 'BorshSpec.encode_prefix_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.encode_prefix_free

/-- info: 'BorshSpec.encode_isSome_iff_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.encode_isSome_iff_valid

/-- info: 'BorshSpec.decode_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_valid

/-- info: 'BorshSpec.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.progress

/-- info: 'BorshSpec.minSize_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.minSize_pos_iff

/-- info: 'BorshSpec.encode_eq_nil_of_zeroSized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.encode_eq_nil_of_zeroSized

/-- info: 'BorshSpec.minSize_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.minSize_attained

/-- info: 'BorshSpec.decode_set_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_set_sorted

/-- info: 'BorshSpec.decode_map_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_map_sorted

/-- info: 'BorshSpec.Value.cmp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.Value.cmp_self

/-- info: 'BorshSpec.Value.cmp_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.Value.cmp_eq_iff

/-- info: 'BorshSpec.Value.cmp_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.Value.cmp_swap

/-- info: 'BorshSpec.Value.cmp_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.Value.cmp_trans

/-- info: 'BorshSpec.Value.beq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.Value.beq_iff

/-- info: 'BorshSpec.lenient_eq_strict_of_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.lenient_eq_strict_of_strict

/-- info: 'BorshSpec.lenient_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.lenient_canonical

/-- info: 'BorshSpec.lenient_eq_normalize_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.lenient_eq_normalize_raw

/-- info: 'BorshSpec.lenient_rest_eq_raw_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.lenient_rest_eq_raw_rest

/-- info: 'BorshSpec.normalizeMap_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.normalizeMap_mem_iff

/-- info: 'BorshSpec.normalizeMap_strictAsc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.normalizeMap_strictAsc

/-- info: 'BorshSpec.normalizeSet_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.normalizeSet_mem_iff

/-- info: 'BorshSpec.normalizeSet_strictAsc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.normalizeSet_strictAsc

/-- info: 'BorshSpec.lenient_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.lenient_progress

/-- info: 'BorshSpec.decode_iff_encodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_iff_encodes

/-- info: 'BorshSpec.encode_iff_encodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.encode_iff_encodes

/-- info: 'BorshSpec.validUtf8_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.validUtf8_iff

/-- info: 'BorshSpec.toLE_eq_leBytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BorshSpec.toLE_eq_leBytes

/-- info: 'BorshSpec.sintToNat_eq_twosComplement' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BorshSpec.sintToNat_eq_twosComplement

/-- info: 'BorshSpec.isNaN32_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.isNaN32_iff

/-- info: 'BorshSpec.isNaN64_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.isNaN64_iff

/-- info: 'BorshSpec.validUtf8_iff_validateUTF8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.validUtf8_iff_validateUTF8

/-- info: 'BorshSpec.decodeC_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decodeC_result

/-- info: 'BorshSpec.factor_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.factor_pos

/-- info: 'BorshSpec.decode_steps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_steps_le

/-- info: 'BorshSpec.decode_steps_le_consumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_steps_le_consumed

/-- info: 'BorshSpec.decode_steps_le_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_steps_le_empty

/-- info: 'BorshSpec.decode_steps_le_of_withinSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_steps_le_of_withinSteps

/-- info: 'BorshSpec.decode_steps_le_of_withinBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_steps_le_of_withinBudget

/-- info: 'BorshSpec.decode_elems_le_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_elems_le_steps

/-- info: 'BorshSpec.decode_elems_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.decode_elems_le

/-- info: 'BorshSpec.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.parse_print

/-- info: 'BorshSpec.hex_decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.hex_decode_encode

/-- info: 'BorshSpec.hex_encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BorshSpec.hex_encode_decode

end BorshSpec.Axioms
