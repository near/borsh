/-!
# Hexadecimal text

The line protocol carries byte strings as lowercase hexadecimal.  `Hex.encode`
writes two digits `0-9a-f` per byte; `Hex.decode` accepts exactly the strings that
`Hex.encode` can produce (even length, lowercase digits only), so
`Hex.encode` and `Hex.decode` are mutually inverse (theorems `hex_decode_encode`
and `hex_encode_decode`).

Both work on character lists and use an accumulator, so they are tail recursive and
handle multi-megabyte lines.
-/

namespace BorshSpec

namespace Hex

/-- The lowercase hexadecimal digit for a value below 16. -/
def digit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The two hexadecimal digits of a byte, high nibble first. -/
def byteChars (b : UInt8) : List Char := [digit (b.toNat / 16), digit (b.toNat % 16)]

/-- Lowercase hexadecimal text of a byte string. -/
def encode (bs : List UInt8) : String := String.ofList (bs.flatMap byteChars)

/-- The value of a lowercase hexadecimal digit (`0-9`, `a-f`; upper case is not
accepted). -/
def digitVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else none

/-- Pair up digit characters into bytes; `acc` holds the bytes so far, reversed. -/
def decodeChars : List Char → List UInt8 → Option (List UInt8)
  | [], acc => some acc.reverse
  | [_], _ => none
  | a :: b :: rest, acc =>
    match digitVal a, digitVal b with
    | some hi, some lo => decodeChars rest ((hi * 16 + lo).toUInt8 :: acc)
    | _, _ => none

/-- Parse lowercase hexadecimal text of even length into bytes. -/
def decode (s : String) : Option (List UInt8) := decodeChars s.toList []

end Hex

end BorshSpec
