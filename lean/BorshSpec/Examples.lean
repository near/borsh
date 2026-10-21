import BorshSpec.Encode
import BorshSpec.Lenient
import BorshSpec.Cost
import BorshSpec.Hex
import BorshSpec.Parse
import BorshSpec.Grammar

/-!
# Examples

Concrete encodings, checked when the library is built.  They pin the wire format of
representative forms and the behaviours that the prose specification leaves open
(key order of `Result`, strict versus lenient maps).  `#guard` evaluates the
compiled definitions; the `example` lines are checked by the kernel, including a few
facts about the relational grammar, positive and negative.

These are tests of particular inputs, not theorems about all of them.
-/

namespace BorshSpec

open Schema

/-- `parseSchema` for a schema known to parse (an unparsable one is `unit`). -/
def sch (s : String) : Schema :=
  match parseSchema s with
  | .ok x => x
  | .error _ => .unit

/-- Decode hex text under the strict decoder, showing the value's re-encoding and
the number of bytes left over. -/
def strictHex (s hex : String) : Option (String × Nat) :=
  match Hex.decode hex with
  | none => none
  | some bs =>
    match decode (sch s) bs with
    | none => none
    | some (v, rest) => (encode (sch s) v).map fun e => (Hex.encode e, rest.length)

/-- As `strictHex` with the lenient decoder. -/
def lenientHex (s hex : String) : Option (String × Nat) :=
  match Hex.decode hex with
  | none => none
  | some bs =>
    match Lenient.decode (sch s) bs with
    | none => none
    | some (v, rest) => (encode (sch s) v).map fun e => (Hex.encode e, rest.length)

-- Integers are little endian; trailing bytes are left over.
#guard strictHex "u32" "78563412ff" == some ("78563412", 1)
#guard strictHex "i16" "ff7f" == some ("ff7f", 0)
-- Strings carry a u32 byte length and must be valid UTF-8.
#guard strictHex "string" "0300000068656c" == some ("0300000068656c", 0)
#guard strictHex "string" "02000000c080" == none
-- Option and bool tags.
#guard strictHex "(option u8)" "0105" == some ("0105", 0)
#guard strictHex "(option u8)" "02" == none
#guard strictHex "bool" "02" == none
-- NaN is rejected, -0.0 is a distinct value.
#guard strictHex "f32" "0000c07f" == none
#guard strictHex "f32" "00000080" == some ("00000080", 0)
-- An enum writes its wire tag; the schema lists variants in key order.
#guard strictHex "(enum (1 u8) (0 string))" "0107" == some ("0107", 0)
#guard strictHex "(enum (1 u8) (0 string))" "00010000006e" == some ("00010000006e", 0)
#guard strictHex "(enum (1 u8) (0 string))" "02" == none
-- The decoded value carries the variant index, not the tag.
#guard decode (sch "(enum (1 u8) (0 u8))") [1, 7] == some (.enum 0 (.uint 7), [])
#guard decode (sch "(enum (1 u8) (0 u8))") [0, 7] == some (.enum 1 (.uint 7), [])
-- Result<u8, u8>: {Ok(5), Err(1)} is written Ok first, as borsh-rs writes it.
#guard strictHex "(set (enum (1 u8) (0 u8)))" "0200000001050001" == some ("0200000001050001", 0)
#guard strictHex "(set (enum (1 u8) (0 u8)))" "0200000000010105" == none
-- Signed keys sort numerically.
#guard strictHex "(map i32 u8)" "02000000ffffffff000000000001" ==
  some ("02000000ffffffff000000000001", 0)
#guard strictHex "(map i32 u8)" "020000000000000001ffffffff00" == none
-- Strict maps reject duplicate and unsorted keys; the lenient decoder normalises them.
#guard strictHex "(map u8 u8)" "0200000001070109" == none
#guard lenientHex "(map u8 u8)" "0200000001070109" == some ("010000000109", 0)
#guard lenientHex "(map u8 u8)" "0200000002010102" == some ("0200000001020201", 0)
#guard lenientHex "(set u8)" "03000000050505" == some ("0100000005", 0)
-- Zero-sized collections are ill-formed, and zero-sized arrays have a large factor.
#guard !(sch "(vec unit)").wellFormed
#guard !(sch "(enum (0 u8) (0 string))").wellFormed
#guard (sch "(array 1000 unit)").factor == 1001
#guard (sch "(vec (vec u8))").factor == 4
#guard !(sch "(array 4294967295 unit)").withinBudget
-- Steps and elements.
#guard ((sch "(vec u8)").decodeC [3, 0, 0, 0, 1, 2, 3]).2 == 4
#guard ((sch "(array 5 unit)").decodeC []).2 == 6
-- The printer and the parser agree on a schema with every form.
#guard ((parseSchema "(tuple u8 (vec (option string)) (map i128 (set bool)) (array 3 f32) (enum (1 unit) (0 u8)))").toOption.map Schema.print) ==
  some "(tuple u8 (vec (option string)) (map i128 (set bool)) (array 3 f32) (enum (1 unit) (0 u8)))"

-- Kernel-checked: the wire encoding of leaf forms and an enum (`rfl` where `Value` has no
-- decidable equality).
example : encode (.uint .w16) (.uint 0x1234) = some [0x34, 0x12] := by decide
example : encode (.sint .w8) (.sint (-1)) = some [0xff] := by decide
example : encode .bool (.bool true) = some [1] := by decide
example : encode (.enum [(1, .uint .w8), (0, .uint .w8)]) (.enum 0 (.uint 5)) = some [1, 5] := by decide
example : decode (.enum [(1, .uint .w8), (0, .uint .w8)]) [0, 5] = some (.enum 1 (.uint 5), []) := by
  rfl

-- Kernel-checked: the key order on small cases.
example : Value.cmp (.sint (-1)) (.sint 0) = .lt := by decide
example : Value.cmp (.uint 1) (.uint 256) = .lt := by decide
example : Value.cmp (.string [97]) (.string [97, 0]) = .lt := by decide
example : Value.cmp (.enum 0 (.uint 5)) (.enum 1 (.uint 1)) = .lt := by decide
example : Value.cmp .optNone (.optSome (.uint 0)) = .lt := by decide
example : (Value.uint 1 == Value.uint 1) = true := by decide
example : (Value.uint 1 == Value.uint 2) = false := by decide

-- Kernel-checked: sorted maps and sets, `-0.0`, and the rejected inputs.
example : encode (.map (.sint .w32) (.uint .w8))
    (.map [(.sint (-1), .uint 0), (.sint 0, .uint 1)]) =
    some [2, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 1] := by decide
example : encode (.set (.uint .w16)) (.set [.uint 1, .uint 256]) = some [2, 0, 0, 0, 1, 0, 0, 1] := by
  decide
example : encode (.set (.enum [(1, .uint .w8), (0, .uint .w8)]))
    (.set [.enum 0 (.uint 5), .enum 1 (.uint 1)]) = some [2, 0, 0, 0, 1, 5, 0, 1] := by decide
example : encode (.set (.uint .w8)) (.set [.uint 2, .uint 1]) = none := by decide
example : encode .f32 (.f32 0x80000000) = some [0, 0, 0, 0x80] := by decide
example : encode .f32 (.f32 0x7fc00000) = none := by decide
example : encode .string (.string [0xc0, 0x80]) = none := by decide
example : encode (.vec .unit) (.vec []) = none := by decide
example : (decode (.array 3 .unit) []).isSome = true := by decide

-- Kernel-checked: the relational grammar derives real encodings.
example : Encodes (.uint .w16) (.uint 258) [2, 1] := by
  have := Encodes.uint .w16 258 (by decide)
  simpa [leBytes, IntWidth.bytes] using this
example : Encodes (.sint .w8) (.sint (-1)) [255] := by
  have := Encodes.sint .w8 (-1) (by decide) (by decide)
  simpa [leBytes, twosComplement, IntWidth.bytes] using this
example : Encodes .bool (.bool true) [1] := Encodes.boolTrue
example : Encodes (.enum [(1, .uint .w8), (0, .uint .w8)]) (.enum 0 (.uint 5)) [1, 5] :=
  Encodes.enum _ 0 1 _ _ _ (VariantAt.here _ _ _) (Encodes.uint .w8 5 (by decide))
example : Encodes (.array 3 .unit) (.array [.unit, .unit, .unit]) [] := by
  have u := Encodes.tuple [] [] [] EncodesFields.nil
  have := Encodes.array 3 .unit [.unit, .unit, .unit] [] rfl
    (EncodesAll.cons _ _ _ [] [] u (EncodesAll.cons _ _ _ [] [] u
      (EncodesAll.cons _ _ _ [] [] u (EncodesAll.nil _))))
  simpa using this

-- Kernel-checked: the relational grammar refuses what the format refuses.
example : ¬ Encodes .bool (.bool true) [2] := by
  intro h; cases h
example : ¬ Encodes .bool (.bool false) [1] := by
  intro h; cases h
example : ¬ Encodes (.uint .w8) (.uint 256) (leBytes 1 256) := by
  intro h; cases h with | uint _ _ hn => exact absurd hn (by decide)
example : ¬ Encodes .f32 (.f32 0x7fc00000) (leBytes 4 0x7fc00000) := by
  intro h; cases h with | f32 _ hn => exact hn (by simp [IsNaN32])
example : ¬ Encodes (.vec .unit) (.vec []) [0, 0, 0, 0] := by
  intro h; cases h with | vec _ _ _ hz => exact hz (SizeZero.tuple [] SizeZeroAll.nil)
example : ¬ WellFormedUtf8 [0xc0, 0x80] := by
  intro h
  cases h <;> simp_all [InRange]

end BorshSpec
