import BorshSpec
import BorshSpec.Theorems.specequiv.Encode
import BorshSpec.Theorems.specequiv.Decode

/-!
# The readable codec equals the internal codec

`Spec.encode` and `Spec.decode` (`BorshSpec/Spec.lean`) are the codec written for
readers.  The theorems of this library are stated about `encode` and `decode`
(`BorshSpec/Encode.lean`, `Decode.lean`).  The two theorems below say the codec
functions are the same on every schema and every input, so every theorem
of this library holds for the readable codec as well.

Both proofs are by structural induction on the schema, following the shared
recursion arm by arm.  The differences they absorb are bookkeeping: `Spec.encodeAll`
against `mapM` and `flatten`, `Spec.decodeN` (front to back) against the accumulating
`decodeMany`, `do`-notation against `match`, and the strict key check, which the readable
decoder performs with `requireAscending` and the internal one through
`KeyPolicy.strict`.  The helper lemmas are in `specequiv/Encode.lean` and
`specequiv/Decode.lean`.
-/

namespace BorshSpec

/-- The readable encoder equals the internal encoder. -/
theorem spec_encode_eq (s : Schema) (v : Value) : Spec.encode s v = encode s v :=
  SpecEquiv.encode_eq s v

/-- The readable decoder equals the internal decoder. -/
theorem spec_decode_eq (s : Schema) (bs : List UInt8) : Spec.decode s bs = decode s bs :=
  SpecEquiv.decode_eq s bs

end BorshSpec
