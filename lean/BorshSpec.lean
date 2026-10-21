import BorshSpec.Spec
import BorshSpec.Utf8
import BorshSpec.Utf8Grammar
import BorshSpec.Grammar
import BorshSpec.Schema
import BorshSpec.Typing
import BorshSpec.Encode
import BorshSpec.Decode
import BorshSpec.Tooling.Lenient
import BorshSpec.Tooling.Cost
import BorshSpec.Tooling.Hex
import BorshSpec.Tooling.Parse
import BorshSpec.Tooling.Examples

/-!
# BorshSpec

Executable specification of the Borsh binary format: the definitions only.  Start
with `Spec.lean`, which contains the whole format in one readable file.  The other
modules, in dependency order:

* `Spec`: schemas, values, little-endian integers, the key order, and the readable
  codec `Spec.encode` / `Spec.decode`;
* `Utf8`: the UTF-8 validator; `Utf8Grammar`, `Grammar`: the format as relational
  grammars, written from the prose without a decoder;
* `Schema`, `Typing`: well-formedness, `minSize`; `HasType`, `Canonical`, `Valid`;
* `Encode`, `Decode`: the internal codec that the theorems are stated about;
* `Tooling/`: the decoder of borsh-rs without `de_strict_order` (`Lenient`), the
  step-counting decoder and schema factor (`Cost`), the text forms used by the
  command line tool (`Hex`, `Parse`), and build-time checks of concrete encodings
  (`Examples`).

The theorems about these definitions are in `BorshSpec.Theorems`, which is built
separately.  See `lean/README.md` and `lean/DECISIONS.md`.
-/
