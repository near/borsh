import BorshSpec.Decode

/-!
# Cost model of the strict decoder

This module is a resource model, not part of the definition of the format.  Nothing
in `Encode`, `Decode` or `Lenient` depends on it.  `decodeC` repeats the strict
decoder with a step counter so that the cost bound can be proved; the theorem
`decodeC_result` ties it to `decode`, which is the definition to read.

`decodeC s bs` is `decode s bs` instrumented with a step counter: it returns the
same result together with the number of steps the decoder took.  A *step* is

* one visit of a schema node (every call of the decoder on a schema, including
  each element of a `vec`, `array`, `set` or `map`);
* one byte validated as UTF-8 (a string of `n` bytes costs `1 + n`);
* one enum variant examined while looking for the variant with the wire tag read;
* for `set` and `map`, the order check on the decoded keys: each adjacent
  comparison costs `1 + min (size a) (size b)`, an upper bound on the work of
  `Value.cmp` on the two keys (it descends both in lock step).

The counter is a model of the work done, not a measurement.  The point of it is
the theorem `decode_steps_le`:

    (decodeC s bs).2 ≤ (bs.length + 1) * s.factor

so the work depends on the input length linearly with a constant, `Schema.factor`,
that depends only on the schema.  In particular a `0xffffffff` length prefix in
front of a short body costs no more than the body does.

The factor grows in two ways.  A zero-sized array (`array n s` with `s` zero-sized,
such as `(array 4294967295 unit)`) produces `n` elements out of no input: this is the
one amplification the format permits.  And it multiplies with nesting: every `vec`
doubles it and every `set` or `map` multiplies it by six, so it is exponential in
the depth of nested collections.  `factor` measures both.  The executable refuses
a schema whose factor exceeds `maxFactor`, and a request for which
`(length + 1) * factor` exceeds `maxSteps` (decision 18).

`Value.elems` counts the elements of every collection in a value, array slots
included, and is bounded by the same factor (theorem `decode_elems_le`).

Only the strict decoder is modelled.  The lenient decoder (`BorshSpec.Tooling.Lenient`)
does the same decoding work and then sorts the decoded keys, which costs
`O(n log n)` comparisons in the number `n` of keys and is not covered by a theorem.
-/

namespace BorshSpec

namespace Value

mutual

/-- The number of nodes of a value; a string counts one node per byte.  This is
the size used to charge key comparisons. -/
def size : Value → Nat
  | .string bs => 1 + bs.length
  | .optSome v => 1 + size v
  | .vec xs => 1 + sizeList xs
  | .array xs => 1 + sizeList xs
  | .tuple xs => 1 + sizeList xs
  | .enum _ v => 1 + size v
  | .map kvs => 1 + sizePairs kvs
  | .set xs => 1 + sizeList xs
  | .uint _ => 1
  | .sint _ => 1
  | .f32 _ => 1
  | .f64 _ => 1
  | .bool _ => 1
  | .optNone => 1

/-- Sum of `size` over a list. -/
def sizeList : List Value → Nat
  | [] => 0
  | x :: xs => size x + sizeList xs

/-- Sum of `size` over keys and values of a list of entries. -/
def sizePairs : List (Value × Value) → Nat
  | [] => 0
  | (k, v) :: kvs => size k + size v + sizePairs kvs

end

mutual

/-- The number of collection elements in a value, at every depth: the length of every
`vec`, `array`, `set` and `map` (one element per entry) it contains.  Array slots
count even when the element schema is zero-sized.  Strings do not count. -/
def elems : Value → Nat
  | .optSome v => elems v
  | .vec xs => xs.length + elemsList xs
  | .array xs => xs.length + elemsList xs
  | .tuple xs => elemsList xs
  | .enum _ v => elems v
  | .map kvs => kvs.length + elemsPairs kvs
  | .set xs => xs.length + elemsList xs
  | .uint _ => 0
  | .sint _ => 0
  | .f32 _ => 0
  | .f64 _ => 0
  | .bool _ => 0
  | .string _ => 0
  | .optNone => 0

/-- Sum of `elems` over a list. -/
def elemsList : List Value → Nat
  | [] => 0
  | x :: xs => elems x + elemsList xs

/-- Sum of `elems` over keys and values of a list of entries. -/
def elemsPairs : List (Value × Value) → Nat
  | [] => 0
  | (k, v) :: kvs => elems k + elems v + elemsPairs kvs

end

/-- `Value.strictAsc` with its step count: one comparison of two keys costs
`1 + min (size a) (size b)`, and the check stops at the first failure. -/
def strictAscC : List Value → Bool × Nat
  | a :: b :: rest =>
    let c := 1 + min a.size b.size
    if cmp a b == .lt then
      let r := strictAscC (b :: rest)
      (r.1, c + r.2)
    else (false, c)
  | _ => (true, 0)

end Value

namespace Schema

/-- A decoder result together with the number of steps taken. -/
abbrev Counted (α : Type) := Option α × Nat

/-- `decodeMany` with step counting; `steps` is the count so far.  Stops at the
first failure, whose steps are included. -/
def decodeManyC {α : Type} (d : List UInt8 → Counted (α × List UInt8)) :
    Nat → List α → List UInt8 → Nat → Counted (List α × List UInt8)
  | 0, acc, bs, steps => (some (acc.reverse, bs), steps)
  | n + 1, acc, bs, steps =>
    match d bs with
    | (none, k) => (none, steps + k)
    | (some (x, r), k) => decodeManyC d n (x :: acc) r (steps + k)

mutual

/-- The strict decoder with a step count; see the module docstring.  Its first
component is `decode s bs` (theorem `decodeC_result`). -/
def decodeC : Schema → List UInt8 → Counted (Value × List UInt8)
  | .uint w, bs => ((readLE w.bytes bs).map fun (n, r) => (.uint n, r), 1)
  | .sint w, bs => ((readLE w.bytes bs).map fun (n, r) => (.sint (natToSint w n), r), 1)
  | .f32, bs =>
    match readLE 4 bs with
    | none => (none, 1)
    | some (n, r) =>
      (if isNaN32 (UInt32.ofNat n) then none else some (.f32 (UInt32.ofNat n), r), 1)
  | .f64, bs =>
    match readLE 8 bs with
    | none => (none, 1)
    | some (n, r) =>
      (if isNaN64 (UInt64.ofNat n) then none else some (.f64 (UInt64.ofNat n), r), 1)
  | .bool, bs =>
    match bs with
    | b :: r =>
      (if b = 0 then some (.bool false, r) else if b = 1 then some (.bool true, r) else none, 1)
    | [] => (none, 1)
  | .string, bs =>
    match readU32 bs with
    | none => (none, 1)
    | some (n, r) =>
      match takeExact n r with
      | none => (none, 1)
      | some (body, r') =>
        (if validUtf8 body then some (.string body, r') else none, 1 + body.length)
  | .option s, bs =>
    match bs with
    | b :: r =>
      if b = 0 then (some (.optNone, r), 1)
      else if b = 1 then
        match decodeC s r with
        | (res, k) => (res.map fun (v, r') => (.optSome v, r'), 1 + k)
      else (none, 1)
    | [] => (none, 1)
  | .vec s, bs =>
    if s.zeroSized then (none, 1)
    else
      match readU32 bs with
      | none => (none, 1)
      | some (n, r) =>
        match decodeManyC (fun b => decodeC s b) n [] r 0 with
        | (res, k) => (res.map fun (xs, r') => (.vec xs, r'), 1 + k)
  | .array n s, bs =>
    match decodeManyC (fun b => decodeC s b) n [] bs 0 with
    | (res, k) => (res.map fun (xs, r) => (.array xs, r), 1 + k)
  | .tuple fs, bs =>
    match decodeFieldsC fs bs with
    | (res, k) => (res.map fun (xs, r) => (.tuple xs, r), 1 + k)
  | .enum vs, bs =>
    match bs with
    | t :: r =>
      match decodeVariantC vs 0 t r with
      | (res, k) => (res, 1 + k)
    | [] => (none, 1)
  | .map k v, bs =>
    if k.zeroSized then (none, 1)
    else
      match readU32 bs with
      | none => (none, 1)
      | some (n, r) =>
        let pair : List UInt8 → Counted ((Value × Value) × List UInt8) := fun b =>
          match decodeC k b with
          | (none, c₁) => (none, c₁)
          | (some (a, r₁), c₁) =>
            match decodeC v r₁ with
            | (none, c₂) => (none, c₁ + c₂)
            | (some (c, r₂), c₂) => (some ((a, c), r₂), c₁ + c₂)
        match decodeManyC pair n [] r 0 with
        | (none, c) => (none, 1 + c)
        | (some (kvs, r'), c) =>
          match Value.strictAscC (kvs.map Prod.fst) with
          | (ok, c') => (if ok then some (.map kvs, r') else none, 1 + c + c')
  | .set s, bs =>
    if s.zeroSized then (none, 1)
    else
      match readU32 bs with
      | none => (none, 1)
      | some (n, r) =>
        match decodeManyC (fun b => decodeC s b) n [] r 0 with
        | (none, c) => (none, 1 + c)
        | (some (xs, r'), c) =>
          match Value.strictAscC xs with
          | (ok, c') => (if ok then some (.set xs, r') else none, 1 + c + c')

/-- Tuple fields with step counting. -/
def decodeFieldsC : List Schema → List UInt8 → Counted (List Value × List UInt8)
  | [], bs => (some ([], bs), 0)
  | s :: fs, bs =>
    match decodeC s bs with
    | (none, k) => (none, k)
    | (some (v, r), k) =>
      match decodeFieldsC fs r with
      | (none, k') => (none, k + k')
      | (some (vs, r'), k') => (some (v :: vs, r'), k + k')

/-- Enum payload decoding with step counting; each variant examined costs one step. -/
def decodeVariantC : List (UInt8 × Schema) → Nat → UInt8 → List UInt8 →
    Counted (Value × List UInt8)
  | [], _, _, _ => (none, 0)
  | (t', s) :: vs, i, t, bs =>
    if t' == t then
      match decodeC s bs with
      | (res, k) => (res.map fun (v, r) => (.enum i v, r), 1 + k)
    else
      match decodeVariantC vs (i + 1) t bs with
      | (res, k) => (res, 1 + k)

end

mutual

/-- The schema factor: the constant in `steps ≤ (input length + 1) * factor`.

* leaves and strings: `1`;
* `option s`, `tuple fs`: one for the node plus the factor of what it contains (the
  sum over fields);
* `enum vs`: one for the node, one for each variant (the variant search), and the
  largest factor among the payloads;
* `vec s`: `2 * factor s`, because a successful element consumes at least one byte
  and costs at most `(its bytes + 1) * factor s`;
* `array n s` with `s` zero-sized: `1 + n * factor s`, the amplification case: the
  `n` elements are produced without consuming input;
* `array n s` otherwise: `1 + 2 * factor s`, as for `vec` (each element consumes
  at least one byte, so at most `length + 1` elements are ever attempted);
* `set s`, `map k v`: six times the element factor, covering the elements (twice, as
  for `vec`) and the order check, which costs at most twice the decoding of the keys.

The constants are not tight; they are what the proof of `decode_steps_le`
goes through with. -/
def factor : Schema → Nat
  | .uint _ => 1
  | .sint _ => 1
  | .f32 => 1
  | .f64 => 1
  | .bool => 1
  | .string => 1
  | .option s => 1 + factor s
  | .vec s => 2 * factor s
  | .array n s => if s.zeroSized then 1 + n * factor s else 1 + 2 * factor s
  | .tuple fs => 1 + factorSum fs
  | .enum vs => 1 + vs.length + factorMax vs
  | .map k v => 6 * (factor k + factor v)
  | .set s => 6 * factor s

/-- Sum of `factor` over a list of schemas. -/
def factorSum : List Schema → Nat
  | [] => 0
  | s :: fs => factor s + factorSum fs

/-- Largest `factor` among the payloads of an enum's variants. -/
def factorMax : List (UInt8 × Schema) → Nat
  | [] => 0
  | (_, s) :: vs => max (factor s) (factorMax vs)

end

end Schema

/-- The largest schema factor the executable accepts: `2^20`.

This bounds the *constant* in `decode_steps_le`, not the work on a long input: an input
of `n` bytes may take `(n + 1) * 2^20` steps, which is why the executable also bounds
the product (`maxSteps`).  The bound on the empty input, where zero-sized arrays act,
is `2^20` steps, about a millisecond.  A schema over the cap contains a zero-sized
array of about a million elements or more, or nests collections deeply enough that
the factor, which multiplies at each level, passes the cap: 21 levels of `vec`, or 8 of
`set` or `map`.  Schemas of real types do not come near either.  This is a limit of
the tool, not of the format. -/
def maxFactor : Nat := 2 ^ 20

/-- The largest value of `(input length + 1) * factor` the executable accepts for one
request: `2^26`, about 6.7e7 steps, a second or so of work on the machine the
throughput figures in `lean/README.md` were measured on.  By `decode_steps_le`, a
request under this bound takes at most this many steps, whatever the input and the
schema. -/
def maxSteps : Nat := 2 ^ 26

namespace Schema

/-- Whether the schema is cheap enough to decode: `factor s ≤ cap`. -/
def withinBudget (s : Schema) (cap : Nat := maxFactor) : Bool := s.factor ≤ cap

/-- Whether decoding an input of `len` bytes under the schema is within `cap` steps,
by the bound of `decode_steps_le`: `(len + 1) * factor s ≤ cap`. -/
def withinSteps (s : Schema) (len : Nat) (cap : Nat := maxSteps) : Bool :=
  (len + 1) * s.factor ≤ cap

end Schema

end BorshSpec
