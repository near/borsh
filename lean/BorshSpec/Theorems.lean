import BorshSpec.Theorems.RoundTrip
import BorshSpec.Theorems.Grammar
import BorshSpec.Theorems.Resources
import BorshSpec.Theorems.Axioms
import BorshSpec.Theorems.SpecEquiv

/-!
# BorshSpec.Theorems

Root of the theorem library `BorshSpecTheorems`: the theorems about the
definitions in `BorshSpec`.  The statements are in the files below; their proofs
are in helper modules in the directories `roundtrip/`, `grammar/`, `resources/` and
`specequiv/`.

* `Theorems.RoundTrip`: the codec laws, canonicity of both decoders, key order laws,
  progress;
* `Theorems.Grammar`: agreement of the codec with the relational grammar and of the
  UTF-8 validator with the UTF-8 grammar;
* `Theorems.Resources`: the cost bound, the element bound, the parser and printer,
  hex;
* `Theorems.Axioms`: pins the axioms each theorem depends on;
* `Theorems.SpecEquiv`: the readable codec `Spec.encode`/`Spec.decode` equals the
  internal codec (proven; these two theorems are in addition to the 51 of the three
  files above).

Nothing in `BorshSpec` or in the executable imports this module.
-/
