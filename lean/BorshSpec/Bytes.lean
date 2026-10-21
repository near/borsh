/-!
# Byte-level helpers

Bytes are `List UInt8` throughout the specification, which keeps proofs simple.
This module has the little-endian integer codec and the bounded `takeExact` used by
every length-prefixed form, plus the IEEE-754 NaN tests on raw bit patterns.

Every function here is total and runs in time bounded by the *available* input,
never by an attacker-controlled length.
-/

namespace BorshSpec

/-- `toLE w n` is the `w`-byte little-endian encoding of `n`; bits of `n`
above `8 * w` are dropped. -/
def toLE : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => (n % 256).toUInt8 :: toLE w (n / 256)

/-- The natural number denoted by a little-endian byte list. -/
def fromLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * fromLE bs

/-- `takeExact n bs` splits off exactly `n` leading bytes, or fails if fewer
than `n` are available.  It inspects at most `min n bs.length` bytes, so a
hostile `n` (up to `2^32 - 1`) costs no more than the real input does. -/
def takeExact (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if (bs.take n).length = n then some (bs.take n, bs.drop n) else none

/-- Read a `w`-byte little-endian unsigned integer, returning the rest. -/
def readLE (w : Nat) (bs : List UInt8) : Option (Nat × List UInt8) :=
  (takeExact w bs).map fun (a, r) => (fromLE a, r)

/-- Whether a 32-bit pattern is an IEEE-754 binary32 NaN: all exponent bits set
and a non-zero mantissa (any payload, either sign).  Equivalently, in mask form,
`(bits &&& 0x7fffffff) > 0x7f800000`. -/
def isNaN32 (bits : UInt32) : Bool :=
  (bits.toNat / 2 ^ 23) % 2 ^ 8 == 2 ^ 8 - 1 && bits.toNat % 2 ^ 23 != 0

/-- Whether a 64-bit pattern is an IEEE-754 binary64 NaN.  In mask form,
`(bits &&& 0x7fffffffffffffff) > 0x7ff0000000000000`. -/
def isNaN64 (bits : UInt64) : Bool :=
  (bits.toNat / 2 ^ 52) % 2 ^ 11 == 2 ^ 11 - 1 && bits.toNat % 2 ^ 52 != 0

end BorshSpec
