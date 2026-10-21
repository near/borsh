import BorshSpec.Schema
import BorshSpec.Bytes
import BorshSpec.Utf8
import BorshSpec.Value
import BorshSpec.Order
import BorshSpec.Typing
import BorshSpec.Encode
import BorshSpec.Decode
import BorshSpec.Lenient
import BorshSpec.Cost
import BorshSpec.Hex
import BorshSpec.Parse
import BorshSpec.Utf8Grammar
import BorshSpec.Grammar
import BorshSpec.Examples

/-!
# BorshSpec

Executable specification of the Borsh binary format: the definitions only.  The
modules follow the dependency order:

* `Schema`, `Value`: what a type and a value are;
* `Bytes`, `Utf8`: little-endian integers, NaN tests, the UTF-8 validator;
* `Order`: the key order `Value.cmp`;
* `Typing`: `HasType`, `Canonical`, `Valid`;
* `Encode`, `Decode`: the canonical codec;
* `Lenient`: the decoder of borsh-rs without `de_strict_order`;
* `Cost`: a step-counting decoder and the schema factor;
* `Hex`, `Parse`: the text forms used by the command line tool;
* `Examples`: build-time checks of concrete encodings.

The theorems about these definitions are in `BorshSpec.Theorems`, which is built
separately.  See `lean/README.md` and `lean/DECISIONS.md`.
-/
