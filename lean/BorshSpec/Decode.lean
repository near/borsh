import BorshSpec.Typing

/-!
# Decoding

`decode s bs` reads one value of schema `s` from a *prefix* of `bs` and returns
it together with the unread rest.  It is the strict, canonical decoder:

* `bool` bytes other than 0/1, `option` tags other than 0/1, enum tags that do not
  name a variant, NaN floats, and invalid UTF-8 are rejected;
* `set` elements and `map` keys must be strictly ascending in `Value.cmp`
  (`PROTOCOL.md`, "Decoding semantics"), so duplicates and unsorted keys are
  rejected;
* `vec`/`set`/map-key positions with a zero-sized element schema are rejected
  (the encoder rejects them too), so no loop below can run without consuming
  input.

The enum arm reads a tag byte and looks it up in the variant list; the decoded
value carries the *index* of the first variant with that tag.

## One decoder, two key policies

Everything except what happens to the list of decoded set elements or map entries
is shared with the lenient decoder (`BorshSpec.Tooling.Lenient`).  That difference is
isolated in a `KeyPolicy`; `decode` is `decodeWith KeyPolicy.strict`.

## Termination and resource use

`decodeWith` is structurally recursive on the schema; there is no fuel and no
`partial`.  The loop `decodeMany` is structural on its counter.

A length prefix is *never* used to allocate or to pre-size anything.  It only
bounds `decodeMany`'s counter, and that loop stops at the first element that
fails to decode.  Because the element schema is not zero-sized, every element
consumes at least one byte, so a prefix of `0xffffffff` followed by a short body
fails after at most `bs.length + 1` iterations.  `takeExact` likewise looks at
no more than the input.  The step-counting version of this argument is in
`BorshSpec.Tooling.Cost`; `array n s` with a zero-sized `s` is the one place where work is
not bounded by the input (DECISIONS.md, decision 18).
-/

namespace BorshSpec

/-- What the decoder does with the keys it has read, once it has read all of them
(decision 17).  Strict decoding accepts only strictly ascending keys; lenient
decoding normalises them.  Both see the keys in input order. -/
structure KeyPolicy where
  /-- Accept or transform the list of decoded set elements. -/
  set : List Value → Option (List Value)
  /-- Accept or transform the list of decoded map entries. -/
  map : List (Value × Value) → Option (List (Value × Value))

/-- The canonical policy: keys must be strictly ascending, and are kept unchanged. -/
def KeyPolicy.strict : KeyPolicy where
  set xs := if Value.strictAsc xs then some xs else none
  map kvs := if Value.strictAsc (kvs.map Prod.fst) then some kvs else none

/-- The policy that keeps keys exactly as read: no check, no reordering, nothing
dropped.  It does not decode any format anyone uses; it is the reference that the
lenient decoder is stated against (`lenient_eq_normalize_raw`): the lenient decoder
is this decoder followed by `Value.normalize`. -/
def KeyPolicy.raw : KeyPolicy where
  set xs := some xs
  map kvs := some kvs

namespace Schema

/-- Run a decoder `n` times in sequence and return the results in order, stopping
at the first failure.  (The results are accumulated in reverse and reversed at
the end, so the loop is tail recursive and long vectors do not overflow the
stack.  Semantically `decodeMany d n [] bs` is "run `d` `n` times in sequence".) -/
def decodeMany {α : Type} (d : List UInt8 → Option (α × List UInt8)) :
    Nat → List α → List UInt8 → Option (List α × List UInt8)
  | 0, acc, bs => some (acc.reverse, bs)
  | n + 1, acc, bs =>
    match d bs with
    | none => none
    | some (x, r) => decodeMany d n (x :: acc) r

mutual

/-- Prefix decoding under a key policy; see the module docstring. -/
def decodeWith (P : KeyPolicy) : Schema → List UInt8 → Option (Value × List UInt8)
  | .uint w, bs => (readLE w.bytes bs).map fun (n, r) => (.uint n, r)
  | .sint w, bs => (readLE w.bytes bs).map fun (n, r) => (.sint (natToSint w n), r)
  | .f32, bs =>
    match readLE 4 bs with
    | none => none
    | some (n, r) => if isNaN32 (UInt32.ofNat n) then none else some (.f32 (UInt32.ofNat n), r)
  | .f64, bs =>
    match readLE 8 bs with
    | none => none
    | some (n, r) => if isNaN64 (UInt64.ofNat n) then none else some (.f64 (UInt64.ofNat n), r)
  | .bool, bs =>
    match bs with
    | b :: r => if b = 0 then some (.bool false, r) else if b = 1 then some (.bool true, r) else none
    | [] => none
  | .string, bs =>
    match readU32 bs with
    | none => none
    | some (n, r) =>
      match takeExact n r with
      | none => none
      | some (body, r') => if validUtf8 body then some (.string body, r') else none
  | .option s, bs =>
    match bs with
    | b :: r =>
      if b = 0 then some (.optNone, r)
      else if b = 1 then (decodeWith P s r).map fun (v, r') => (.optSome v, r')
      else none
    | [] => none
  | .vec s, bs =>
    if s.zeroSized then none
    else
      match readU32 bs with
      | none => none
      | some (n, r) =>
        (decodeMany (fun b => decodeWith P s b) n [] r).map fun (xs, r') => (.vec xs, r')
  | .array n s, bs =>
    (decodeMany (fun b => decodeWith P s b) n [] bs).map fun (xs, r) => (.array xs, r)
  | .tuple fs, bs => (decodeFieldsWith P fs bs).map fun (xs, r) => (.tuple xs, r)
  | .enum vs, bs =>
    match bs with
    | t :: r => decodeVariantWith P vs 0 t r
    | [] => none
  | .map k v, bs =>
    if k.zeroSized then none
    else
      match readU32 bs with
      | none => none
      | some (n, r) =>
        let pair : List UInt8 → Option ((Value × Value) × List UInt8) := fun b =>
          match decodeWith P k b with
          | none => none
          | some (a, r₁) =>
            match decodeWith P v r₁ with
            | none => none
            | some (c, r₂) => some ((a, c), r₂)
        match decodeMany pair n [] r with
        | none => none
        | some (kvs, r') => (P.map kvs).map fun kvs' => (.map kvs', r')
  | .set s, bs =>
    if s.zeroSized then none
    else
      match readU32 bs with
      | none => none
      | some (n, r) =>
        match decodeMany (fun b => decodeWith P s b) n [] r with
        | none => none
        | some (xs, r') => (P.set xs).map fun xs' => (.set xs', r')

/-- Decode tuple fields in order.  Recursion depth is the number of fields,
which comes from the schema, not from the input. -/
def decodeFieldsWith (P : KeyPolicy) : List Schema → List UInt8 →
    Option (List Value × List UInt8)
  | [], bs => some ([], bs)
  | s :: fs, bs =>
    match decodeWith P s bs with
    | none => none
    | some (v, r) =>
      match decodeFieldsWith P fs r with
      | none => none
      | some (vs, r') => some (v :: vs, r')

/-- Decode the payload of the enum variant carrying the (already read) wire tag
`t`, searching the variant list from index `i`; the result carries the index of the
first variant with that tag.  An unknown tag is rejected. -/
def decodeVariantWith (P : KeyPolicy) : List (UInt8 × Schema) → Nat → UInt8 →
    List UInt8 → Option (Value × List UInt8)
  | [], _, _, _ => none
  | (t', s) :: vs, i, t, bs =>
    if t' == t then (decodeWith P s bs).map fun (v, r) => (.enum i v, r)
    else decodeVariantWith P vs (i + 1) t bs

end

/-- The strict, canonical decoder. -/
def decode (s : Schema) (bs : List UInt8) : Option (Value × List UInt8) :=
  decodeWith KeyPolicy.strict s bs

end Schema

export Schema (decode)

end BorshSpec
