/-!
# UTF-8 validation

`validUtf8` is meant to accept exactly the byte strings accepted by Rust's
`core::str::from_utf8`, i.e. the well-formed UTF-8 byte sequences of
Unicode 15 Table 3-7 (RFC 3629): no overlong forms, no surrogates
(`U+D800..U+DFFF`), nothing above `U+10FFFF`.  Agreement with the Unicode grammar is
the statement `validUtf8_iff` (`Theorems/Grammar.lean`).  Agreement with Rust's
`core::str::from_utf8` is tested, not proven: see "UTF-8" in `lean/README.md` for
exactly what was compared.

| first byte  | second byte | third / fourth byte |
|-------------|-------------|---------------------|
| `00..7F`    |             |                     |
| `C2..DF`    | `80..BF`    |                     |
| `E0`        | `A0..BF`    | `80..BF`            |
| `E1..EC`    | `80..BF`    | `80..BF`            |
| `ED`        | `80..9F`    | `80..BF`            |
| `EE..EF`    | `80..BF`    | `80..BF`            |
| `F0`        | `90..BF`    | `80..BF`, `80..BF`  |
| `F1..F3`    | `80..BF`    | `80..BF`, `80..BF`  |
| `F4`        | `80..8F`    | `80..BF`, `80..BF`  |

This is the specification's own validator; it is deliberately independent of
Lean's `ByteArray.validateUTF8`.  `borsh-spec selftest-utf8` compares the two
on a bounded set of inputs and prints per-length accept counts and digests, which
a ten-line Rust program over `core::str::from_utf8` reproduces (README, "UTF-8").
-/

namespace BorshSpec

/-- `inRange lo hi b` holds when `lo ≤ b ≤ hi`. -/
def inRange (lo hi b : UInt8) : Bool := lo ≤ b && b ≤ hi

/-- A UTF-8 continuation byte, `80..BF`. -/
def isCont (b : UInt8) : Bool := inRange 0x80 0xBF b

/-- Whether the byte string is well-formed UTF-8 (see the module docstring). -/
def validUtf8 : List UInt8 → Bool
  | [] => true
  | b0 :: rest =>
    if b0 ≤ 0x7F then validUtf8 rest
    else if inRange 0xC2 0xDF b0 then
      match rest with
      | b1 :: r => isCont b1 && validUtf8 r
      | _ => false
    else if b0 == 0xE0 then
      match rest with
      | b1 :: b2 :: r => inRange 0xA0 0xBF b1 && isCont b2 && validUtf8 r
      | _ => false
    else if inRange 0xE1 0xEC b0 || b0 == 0xEE || b0 == 0xEF then
      match rest with
      | b1 :: b2 :: r => isCont b1 && isCont b2 && validUtf8 r
      | _ => false
    else if b0 == 0xED then
      match rest with
      | b1 :: b2 :: r => inRange 0x80 0x9F b1 && isCont b2 && validUtf8 r
      | _ => false
    else if b0 == 0xF0 then
      match rest with
      | b1 :: b2 :: b3 :: r => inRange 0x90 0xBF b1 && isCont b2 && isCont b3 && validUtf8 r
      | _ => false
    else if inRange 0xF1 0xF3 b0 then
      match rest with
      | b1 :: b2 :: b3 :: r => isCont b1 && isCont b2 && isCont b3 && validUtf8 r
      | _ => false
    else if b0 == 0xF4 then
      match rest with
      | b1 :: b2 :: b3 :: r => inRange 0x80 0x8F b1 && isCont b2 && isCont b3 && validUtf8 r
      | _ => false
    else false

end BorshSpec
