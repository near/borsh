import BorshSpec.Theorems.RoundTrip
import BorshSpec.Theorems.Grammar
import BorshSpec.Theorems.Resources
import BorshSpec.Theorems.Axioms

/-!
# BorshSpec.Theorems

Root of the theorem library `BorshSpecTheorems`: the theorems about the
definitions in `BorshSpec`.  The statements are in the three files below; their proofs
are in helper modules in the directories `roundtrip/`, `grammar/` and `resources/`.

* `Theorems.RoundTrip`: the codec laws, canonicity of both decoders, key order laws,
  progress;
* `Theorems.Grammar`: agreement of the codec with the relational grammar and of the
  UTF-8 validator with the UTF-8 grammar;
* `Theorems.Resources`: the cost bound, the element bound, the parser and printer,
  hex;
* `Theorems.Axioms`: pins the axioms each theorem depends on.

Nothing in `BorshSpec` or in the executable imports this module.
-/
