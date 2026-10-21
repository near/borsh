import BorshSpec.Schema

/-!
# Schema text syntax: parser and printer

Parser for the one-line schema syntax of `PROTOCOL.md`:

```
schema := prim | "(" form ")"
prim   := u8 | u16 | u32 | u64 | u128 | i8 | i16 | i32 | i64 | i128
        | f32 | f64 | bool | unit | string
form   := option schema | vec schema | array N schema | tuple schema*
        | enum (TAG schema)* | map schema schema | set schema
```

Words are runs of `a-z0-9`; parentheses are their own tokens; runs of spaces
separate tokens (and may be omitted next to parentheses).  Any other character
(tabs included) is an error.  `unit` is `(tuple)`.  `(enum)` with no variants is
accepted by the parser and rejected by `Schema.wellFormed`, so that parsing and
well-formedness stay separate.

The parser works in three total steps, none needing fuel: `tokenize` (structural
on the characters), `buildSexp` (structural on the tokens, with an explicit stack
of open lists), and `toSchema` (structural on the S-expression).  Parsing only builds
a `Schema`.

`Schema.print` is the inverse: `parseSchema (print s) = .ok s` for every schema
(theorem `parse_print`).  The printer is not injective on text (`(tuple)` and `unit`
parse to the same schema) and prints `unit` for the empty tuple.
-/

namespace BorshSpec

namespace Parse

/-- A lexical token. -/
inductive Token where
  /-- Opening parenthesis. -/
  | lparen
  /-- Closing parenthesis. -/
  | rparen
  /-- A run of characters from `a-z0-9`. -/
  | word (w : String)
  deriving BEq, Repr

/-- A generic S-expression: an atom or a list. -/
inductive Sexp where
  /-- A bare word. -/
  | atom (w : String)
  /-- A parenthesised list. -/
  | list (xs : List Sexp)
  deriving BEq, Repr

/-- Flush the pending word (kept reversed) into the token list (kept reversed). -/
def flushWord (cur : List Char) (acc : List Token) : List Token :=
  match cur with
  | [] => acc
  | _ => .word (String.ofList cur.reverse) :: acc

/-- Split a character list into tokens.  `cur` is the current word, reversed;
`acc` the tokens so far, reversed. -/
def tokenizeAux : List Char → List Char → List Token → Except String (List Token)
  | [], cur, acc => .ok (flushWord cur acc).reverse
  | c :: cs, cur, acc =>
    if c = ' ' then tokenizeAux cs [] (flushWord cur acc)
    else if c = '(' then tokenizeAux cs [] (.lparen :: flushWord cur acc)
    else if c = ')' then tokenizeAux cs [] (.rparen :: flushWord cur acc)
    else if ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9') then tokenizeAux cs (c :: cur) acc
    else .error "unexpected character"

/-- Tokenise a schema line. -/
def tokenize (s : String) : Except String (List Token) := tokenizeAux s.toList [] []

/-- Build the S-expression from tokens.  `stack` holds the open lists, each
reversed, innermost first; it always has at least one frame. -/
def buildSexp : List Token → List (List Sexp) → Except String Sexp
  | [], [[x]] => .ok x
  | [], [_] => .error "expected exactly one schema"
  | [], _ => .error "unbalanced parentheses"
  | .word w :: ts, top :: rest => buildSexp ts ((.atom w :: top) :: rest)
  | .lparen :: ts, stack => buildSexp ts ([] :: stack)
  | .rparen :: ts, top :: parent :: rest =>
    buildSexp ts ((.list top.reverse :: parent) :: rest)
  | .rparen :: _, _ => .error "unbalanced parentheses"
  | _ :: _, [] => .error "internal: empty stack"

/-- Parse a decimal numeral: one or more ASCII digits. -/
def parseNat (w : String) : Option Nat :=
  match w.toList with
  | [] => none
  | cs => cs.foldlM (fun acc c => if '0' ≤ c ∧ c ≤ '9' then some (acc * 10 + (c.toNat - '0'.toNat)) else none) 0

/-- The primitive schema named by a word. -/
def primOf (w : String) : Except String Schema :=
  match w with
  | "u8" => .ok (.uint .w8)
  | "u16" => .ok (.uint .w16)
  | "u32" => .ok (.uint .w32)
  | "u64" => .ok (.uint .w64)
  | "u128" => .ok (.uint .w128)
  | "i8" => .ok (.sint .w8)
  | "i16" => .ok (.sint .w16)
  | "i32" => .ok (.sint .w32)
  | "i64" => .ok (.sint .w64)
  | "i128" => .ok (.sint .w128)
  | "f32" => .ok .f32
  | "f64" => .ok .f64
  | "bool" => .ok .bool
  | "unit" => .ok .unit
  | "string" => .ok .string
  | _ => .error "unknown type"

mutual

/-- Convert an S-expression to a schema. -/
def toSchema : Sexp → Except String Schema
  | .atom w => primOf w
  | .list [] => .error "empty form"
  | .list (.list _ :: _) => .error "form must start with a keyword"
  | .list (.atom head :: args) =>
    if head = "tuple" then (toSchemas args).map .tuple
    else if head = "enum" then (toVariants args).map .enum
    else
      match args with
      | [a] =>
        if head = "option" then (toSchema a).map .option
        else if head = "vec" then (toSchema a).map .vec
        else if head = "set" then (toSchema a).map .set
        else .error "unknown form"
      | [x, y] =>
        if head = "array" then
          match x with
          | .atom n =>
            match parseNat n with
            | none => .error "bad array length"
            | some len => (toSchema y).map (.array len)
          | .list _ => .error "bad array length"
        else if head = "map" then
          match toSchema x, toSchema y with
          | .ok k', .ok v' => .ok (.map k' v')
          | .error e, _ => .error e
          | _, .error e => .error e
        else .error "unknown form"
      | _ => .error "wrong number of arguments"

/-- Convert a list of S-expressions to schemas. -/
def toSchemas : List Sexp → Except String (List Schema)
  | [] => .ok []
  | x :: xs =>
    match toSchema x with
    | .error e => .error e
    | .ok s =>
      match toSchemas xs with
      | .error e => .error e
      | .ok ss => .ok (s :: ss)

/-- Convert `(TAG schema)` variant forms to tagged schemas. -/
def toVariants : List Sexp → Except String (List (UInt8 × Schema))
  | [] => .ok []
  | .list [.atom t, x] :: xs =>
    match parseNat t with
    | none => .error "bad enum tag"
    | some tag =>
      if tag < 256 then
        match toSchema x with
        | .error e => .error e
        | .ok s =>
          match toVariants xs with
          | .error e => .error e
          | .ok vs => .ok ((tag.toUInt8, s) :: vs)
      else .error "enum tag out of range"
  | _ :: _ => .error "enum variant must be (TAG schema)"

end

end Parse

/-- Parse a schema line (syntax only; see `Schema.wellFormed` for the rest). -/
def parseSchema (line : String) : Except String Schema := do
  let toks ← Parse.tokenize line
  let sexp ← Parse.buildSexp toks [[]]
  Parse.toSchema sexp

/-- The number of bits of an integer width, as decimal text (`"8"` for `u8` / `i8`). -/
def IntWidth.bits : IntWidth → String
  | .w8 => "8"
  | .w16 => "16"
  | .w32 => "32"
  | .w64 => "64"
  | .w128 => "128"

namespace Schema

mutual

/-- The schema text, as characters (see `print`). -/
def printChars : Schema → List Char
  | .uint w => 'u' :: (IntWidth.bits w).toList
  | .sint w => 'i' :: (IntWidth.bits w).toList
  | .f32 => "f32".toList
  | .f64 => "f64".toList
  | .bool => "bool".toList
  | .string => "string".toList
  | .option s => "(option ".toList ++ printChars s ++ [')']
  | .vec s => "(vec ".toList ++ printChars s ++ [')']
  | .array n s => "(array ".toList ++ (toString n).toList ++ ' ' :: printChars s ++ [')']
  | .tuple [] => "unit".toList
  | .tuple fs => "(tuple".toList ++ printFields fs ++ [')']
  | .enum vs => "(enum".toList ++ printVariants vs ++ [')']
  | .map k v => "(map ".toList ++ printChars k ++ ' ' :: printChars v ++ [')']
  | .set s => "(set ".toList ++ printChars s ++ [')']

/-- Each field schema preceded by a space. -/
def printFields : List Schema → List Char
  | [] => []
  | s :: fs => ' ' :: (printChars s ++ printFields fs)

/-- Each variant as ` (TAG schema)`. -/
def printVariants : List (UInt8 × Schema) → List Char
  | [] => []
  | (t, s) :: vs => " (".toList ++ (toString t.toNat).toList ++ ' ' :: (printChars s ++ ')' :: printVariants vs)

end

/-- The canonical text of a schema, in the syntax of `PROTOCOL.md`. -/
def print (s : Schema) : String := String.ofList (printChars s)

end Schema

end BorshSpec
