/-!
# Well-formed UTF-8, as a grammar

`WellFormedUtf8` transcribes Table 3-7 ("Well-Formed UTF-8 Byte Sequences") of the
Unicode Standard, one constructor per row.  It is stated on its own, as a relation on
byte lists, and does not use any library validator.

| Code points          | 1st byte | 2nd byte | 3rd byte | 4th byte |
|----------------------|----------|----------|----------|----------|
| U+0000..U+007F       | 00..7F   |          |          |          |
| U+0080..U+07FF       | C2..DF   | 80..BF   |          |          |
| U+0800..U+0FFF       | E0       | A0..BF   | 80..BF   |          |
| U+1000..U+CFFF       | E1..EC   | 80..BF   | 80..BF   |          |
| U+D000..U+D7FF       | ED       | 80..9F   | 80..BF   |          |
| U+E000..U+FFFF       | EE..EF   | 80..BF   | 80..BF   |          |
| U+10000..U+3FFFF     | F0       | 90..BF   | 80..BF   | 80..BF   |
| U+40000..U+FFFFF     | F1..F3   | 80..BF   | 80..BF   | 80..BF   |
| U+100000..U+10FFFF   | F4       | 80..8F   | 80..BF   | 80..BF   |

A byte string is well-formed when it is a
concatenation of sequences of these shapes.  Anything else is ill-formed: a lone
continuation byte, `C0`, `C1`, `F5..FF`, an overlong form, a surrogate
(`ED A0..BF`), a code point above U+10FFFF, or a truncated sequence.
-/

namespace BorshSpec

/-- `InRange lo hi b` says that the byte `b` lies in the closed range `lo..hi`
(the "80..BF" notation of the table). -/
def InRange (lo hi b : UInt8) : Prop := lo ≤ b ∧ b ≤ hi

/-- A byte string is well-formed UTF-8: the empty string, or a sequence of one of the
nine rows of Unicode Table 3-7 followed by a well-formed string. -/
inductive WellFormedUtf8 : List UInt8 → Prop where
  /-- The empty byte string. -/
  | nil : WellFormedUtf8 []
  /-- Row U+0000..U+007F: `00..7F`. -/
  | row1 (b1 : UInt8) (rest : List UInt8)
      (h1 : InRange 0x00 0x7F b1) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: rest)
  /-- Row U+0080..U+07FF: `C2..DF`, `80..BF`. -/
  | row2 (b1 b2 : UInt8) (rest : List UInt8)
      (h1 : InRange 0xC2 0xDF b1) (h2 : InRange 0x80 0xBF b2) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: b2 :: rest)
  /-- Row U+0800..U+0FFF: `E0`, `A0..BF`, `80..BF`. -/
  | row3 (b1 b2 b3 : UInt8) (rest : List UInt8)
      (h1 : InRange 0xE0 0xE0 b1) (h2 : InRange 0xA0 0xBF b2)
      (h3 : InRange 0x80 0xBF b3) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: b2 :: b3 :: rest)
  /-- Row U+1000..U+CFFF: `E1..EC`, `80..BF`, `80..BF`. -/
  | row4 (b1 b2 b3 : UInt8) (rest : List UInt8)
      (h1 : InRange 0xE1 0xEC b1) (h2 : InRange 0x80 0xBF b2)
      (h3 : InRange 0x80 0xBF b3) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: b2 :: b3 :: rest)
  /-- Row U+D000..U+D7FF: `ED`, `80..9F`, `80..BF`. -/
  | row5 (b1 b2 b3 : UInt8) (rest : List UInt8)
      (h1 : InRange 0xED 0xED b1) (h2 : InRange 0x80 0x9F b2)
      (h3 : InRange 0x80 0xBF b3) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: b2 :: b3 :: rest)
  /-- Row U+E000..U+FFFF: `EE..EF`, `80..BF`, `80..BF`. -/
  | row6 (b1 b2 b3 : UInt8) (rest : List UInt8)
      (h1 : InRange 0xEE 0xEF b1) (h2 : InRange 0x80 0xBF b2)
      (h3 : InRange 0x80 0xBF b3) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: b2 :: b3 :: rest)
  /-- Row U+10000..U+3FFFF: `F0`, `90..BF`, `80..BF`, `80..BF`. -/
  | row7 (b1 b2 b3 b4 : UInt8) (rest : List UInt8)
      (h1 : InRange 0xF0 0xF0 b1) (h2 : InRange 0x90 0xBF b2)
      (h3 : InRange 0x80 0xBF b3) (h4 : InRange 0x80 0xBF b4) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: b2 :: b3 :: b4 :: rest)
  /-- Row U+40000..U+FFFFF: `F1..F3`, `80..BF`, `80..BF`, `80..BF`. -/
  | row8 (b1 b2 b3 b4 : UInt8) (rest : List UInt8)
      (h1 : InRange 0xF1 0xF3 b1) (h2 : InRange 0x80 0xBF b2)
      (h3 : InRange 0x80 0xBF b3) (h4 : InRange 0x80 0xBF b4) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: b2 :: b3 :: b4 :: rest)
  /-- Row U+100000..U+10FFFF: `F4`, `80..8F`, `80..BF`, `80..BF`. -/
  | row9 (b1 b2 b3 b4 : UInt8) (rest : List UInt8)
      (h1 : InRange 0xF4 0xF4 b1) (h2 : InRange 0x80 0x8F b2)
      (h3 : InRange 0x80 0xBF b3) (h4 : InRange 0x80 0xBF b4) :
      WellFormedUtf8 rest → WellFormedUtf8 (b1 :: b2 :: b3 :: b4 :: rest)

end BorshSpec
