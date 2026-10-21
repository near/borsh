import Spec

/-! `borsh-spec`: decode Borsh against a schema, one `SCHEMA<TAB>HEX` line at a time.
The syntax and protocol are in `README.md`. -/

open Borsh

/-- Schemas larger than this many nodes are refused (`(array 4294967295 u8)` would
otherwise build a four-billion-field tuple before reading a byte). -/
def maxSize : Nat := 2 ^ 20

inductive Sexp where
  | atom (s : String)
  | list (xs : List Sexp)

/-- Parse one S-expression from the tokens, returning the unused ones. -/
partial def sexp : List String → Except String (Sexp × List String)
  | "(" :: ts => go [] ts
  | ")" :: _ => .error "unexpected )"
  | t :: ts => pure (.atom t, ts)
  | [] => .error "unexpected end"
where
  go (acc : List Sexp) : List String → Except String (Sexp × List String)
    | ")" :: ts => pure (.list acc.reverse, ts)
    | ts => do let (x, ts) ← sexp ts; go (x :: acc) ts

def tokens (s : String) : Except String (List String) := do
  if !s.all (fun c => c.isLower || c.isDigit || c == ' ' || c == '(' || c == ')') then
    throw "unexpected character"
  let spaced := (s.replace "(" " ( ").replace ")" " ) "
  pure ((spaced.splitOn " ").filter (· != ""))

/-- A schema and its size in nodes. -/
partial def schema : Sexp → Except String (Schema × Nat)
  | .atom a =>
    let widths := [("8", 1), ("16", 2), ("32", 4), ("64", 8), ("128", 16)]
    match a, widths.lookup (a.drop 1).toString with
    | "f32", _ => pure (.f32, 1)
    | "f64", _ => pure (.f64, 1)
    | "bool", _ => pure (.bool, 3)
    | "unit", _ => pure (.unit, 1)
    | "string", _ => pure (.string, 1)
    | _, some n => if a.startsWith "u" then pure (.uint n, 1)
        else if a.startsWith "i" then pure (.int n, 1) else .error s!"unknown type {a}"
    | _, none => .error s!"unknown type {a}"
  | .list [.atom "option", t] => do let (t, n) ← schema t; pure (.option t, n + 2)
  | .list [.atom "vec", t] => do let (t, n) ← schema t; pure (.vec t, n + 1)
  | .list [.atom "set", t] => do let (t, n) ← schema t; pure (.set t, n + 2)
  | .list [.atom "map", k, v] => do
    let (k, n) ← schema k
    let (v, m) ← schema v
    pure (.map k v, n + m + 1)
  | .list [.atom "array", .atom len, t] => do
    let (t, n) ← schema t
    let some len := len.toNat? | .error "bad array length"
    if len * n > maxSize then .error "schema too large"
    pure (.array len t, len * n + 1)
  | .list (.atom "tuple" :: ts) => do
    let ts ← ts.mapM schema
    pure (.tuple (ts.map (·.1)), (ts.map (·.2)).sum + 1)
  | .list (.atom "enum" :: vs) => do
    let vs ← vs.mapM fun
      | .list [.atom tag, t] => do
        let some tag := tag.toNat? | .error "bad tag"
        if tag ≥ 256 then .error "bad tag"
        let (t, n) ← schema t
        pure ((tag.toUInt8, t), n)
      | _ => .error "bad variant"
    pure (.enum (vs.map (·.1)), (vs.map (·.2)).sum + 1)
  | _ => .error "bad schema"

/-- Schemas Rust cannot have: zero-sized `Vec` elements and keys, float keys, enums
with no variants or a repeated tag. -/
partial def check : Schema → Except String Unit
  | .vec t => do
    if t.zeroSized then throw "zero-sized element"
    check t
  | .map k v => do
    if k.zeroSized then throw "zero-sized key"
    if hasFloat k then throw "float key"
    check k
    check v
  | .tuple ts => ts.forM check
  | .enum vs => do
    let tags := vs.map (·.1)
    if tags.isEmpty || tags.eraseDups.length != tags.length then throw "bad enum tags"
    vs.forM (check ·.2)
  | _ => pure ()
where
  hasFloat : Schema → Bool
    | .f32 | .f64 => true
    | .vec t => hasFloat t
    | .map k v => hasFloat k || hasFloat v
    | .tuple ts => ts.any hasFloat
    | .enum vs => vs.any (hasFloat ·.2)
    | _ => false

def parseSchema (s : String) : Except String Schema := do
  let (e, rest) ← sexp (← tokens s)
  if !rest.isEmpty then throw "trailing tokens"
  let (s, n) ← schema e
  if n > maxSize then throw "schema too large"
  check s
  pure s

def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

def fromHex : List Char → Option Bytes
  | [] => some []
  | a :: b :: cs => do pure ((16 * (← hexDigit a) + (← hexDigit b)).toUInt8 :: (← fromHex cs))
  | _ => none

def toHex (bs : Bytes) : String :=
  String.join (bs.map fun b => let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s)

/-- `ok<TAB>consumed<TAB>re-encoding`, `err<TAB>reason` or `bad<TAB>reason`. -/
def answer (line : String) : String :=
  match line.splitOn "\t" with
  | [s, hex] =>
    match parseSchema s, fromHex hex.toList with
    | .error e, _ => s!"bad\t{e}"
    | _, none => "bad\thex"
    | .ok s, some bs =>
      match decode s bs with
      | none => "err\trejected"
      | some (v, rest) => match encode s v with
        | some out => s!"ok\t{bs.length - rest.length}\t{toHex out}"
        | none => "bug\tdecoded value does not encode"
  | _ => "bad\tline is not SCHEMA<TAB>HEX"

/-- Each line of a vector file is `SCHEMA<TAB>HEX<TAB>EXPECTED`; a bare `err` or `bad`
matches on the first field only. -/
def checkFile (path : String) : IO Nat := do
  let mut failures := 0
  for line in (← IO.FS.lines path) do
    if line.isEmpty || line.startsWith "#" then continue
    let s :: hex :: expected := line.splitOn "\t" | throw (.userError s!"{path}: bad line {line}")
    let expected := "\t".intercalate expected
    let got := answer s!"{s}\t{hex}"
    let ok := if expected == "err" || expected == "bad" then got.startsWith (expected ++ "\t") else got == expected
    if !ok then
      IO.eprintln s!"{path}: {s}\t{hex}\n  expected {expected}\n  got      {got}"
      failures := failures + 1
  pure failures

def main : List String → IO UInt32
  | "check" :: files => do
    let failures ← files.foldlM (fun n f => (n + ·) <$> checkFile f) 0
    IO.println s!"{failures} failed"
    pure (if failures == 0 then 0 else 1)
  | "decode" :: flags => do
    let flush := flags == ["--line-buffered"]
    if !flush && !flags.isEmpty then
      IO.eprintln "usage: borsh-spec decode [--line-buffered]"
      return 2
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      stdout.putStrLn (answer (line.dropEndWhile (fun c => c == '\n' || c == '\r')).toString)
      if flush then stdout.flush
    pure 0
  | _ => do
    IO.eprintln "usage: borsh-spec decode < lines | borsh-spec check FILE..."
    pure 2
