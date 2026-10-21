import BorshSpec
import Std.Data.HashMap

/-!
# `borsh-spec`: command line front end of the Borsh specification

* `borsh-spec decode [--lenient] [--line-buffered] [--max-factor N] [--max-steps N]`: the line
  protocol of `PROTOCOL.md`.  Reads `SCHEMA<TAB>HEX` lines from stdin, writes one
  answer line per input line.
* `borsh-spec check [--lenient] FILE...`: runs vector files whose lines are
  `SCHEMA<TAB>HEX<TAB>EXPECTED` and exits non-zero on any mismatch.
* `borsh-spec selftest-utf8`: compares the UTF-8 validator with Lean's own.

All semantics live in the `BorshSpec` library; this file only handles I/O,
caching and the formatting of answers.
-/

open BorshSpec

namespace BorshSpecCli

/-- Which decoder answers a request. -/
inductive Mode where
  /-- The strict, canonical decoder (`decode`). -/
  | strict
  /-- The decoder of borsh-rs without `de_strict_order` (`Lenient.decode`). -/
  | lenient
  deriving BEq

/-- The decoder selected by a mode. -/
def Mode.decode : Mode → Schema → List UInt8 → Option (Value × List UInt8)
  | .strict => Schema.decode
  | .lenient => Lenient.decode

/-- Settings shared by all requests of one run. -/
structure Config where
  /-- The decoder to use. -/
  mode : Mode := .strict
  /-- Schemas with `factor` above this are answered `bad` (see `BorshSpec/Tooling/Cost.lean`). -/
  maxFactor : Nat := BorshSpec.maxFactor
  /-- Requests with `(input length + 1) * factor` above this are answered `bad`. -/
  maxSteps : Nat := BorshSpec.maxSteps

/-- Parse a schema line and require well-formedness and a factor within budget. -/
def schemaOfText (cfg : Config) (text : String) : Except String Schema :=
  match parseSchema text with
  | .error e => .error e
  | .ok s =>
    if !s.wellFormed then .error "schema is not well-formed"
    else if !s.withinBudget cfg.maxFactor then
      .error s!"resource limit: schema factor {s.factor} exceeds {cfg.maxFactor}"
    else .ok s

/-- The self-checks the executable runs on every decode, since they are the
conclusions of the theorems about the specification, run here on the compiled
code: the decoded value is valid and its encoding `out` exists; in strict mode
`out` is exactly the consumed bytes; in lenient mode `out` decodes strictly back to
the same value, with nothing left over.  `none` means all checks passed. -/
def selfCheck (mode : Mode) (s : Schema) (consumed : List UInt8) (v : Value)
    (out : List UInt8) : Option String :=
  if !(s.hasType v && s.canonical v) then some "decoded value is not valid"
  else
    match mode with
    | .strict =>
      if out != consumed then some "re-encoding differs from consumed bytes" else none
    | .lenient =>
      match Schema.decode s out with
      | some (v', []) => if v' == v then none else some "re-encoding decodes to another value"
      | _ => some "re-encoding is not canonical"

/-- The protocol answer for a parsed schema and a hex payload. -/
def respond (cfg : Config) (sch : Except String Schema) (hex : String) : String :=
  match sch with
  | .error e => "bad\t" ++ e
  | .ok s =>
    match Hex.decode hex with
    | none => "bad\tinvalid hex"
    | some bs =>
      if !s.withinSteps bs.length cfg.maxSteps then
        s!"bad\tresource limit: (input length + 1) * schema factor = " ++
          s!"{(bs.length + 1) * s.factor} exceeds {cfg.maxSteps}"
      else
        match cfg.mode.decode s bs with
        | none => "err\tdecode failed"
        | some (v, rest) =>
          let consumedLen := bs.length - rest.length
          match s.encode v with
          | none => "err\tinternal: re-encoding a decoded value failed"
          | some out =>
            match selfCheck cfg.mode s (bs.take consumedLen) v out with
            | some msg => "err\tinternal: " ++ msg
            | none => "ok\t" ++ toString consumedLen ++ "\t" ++ Hex.encode out

/-- Memoise schema parsing: consecutive lines usually share a handful of
schemas.  The table is emptied when it grows large, so memory stays bounded. -/
abbrev SchemaCache := Std.HashMap String (Except String Schema)

/-- Look a schema up in the cache, parsing it on a miss. -/
def lookupSchema (cfg : Config) (cache : SchemaCache) (text : String) :
    Except String Schema × SchemaCache :=
  match cache.get? text with
  | some r => (r, cache)
  | none =>
    let r := schemaOfText cfg text
    let cache := if cache.size ≥ 4096 then {} else cache
    (r, cache.insert text r)

/-- The answer line for a raw `SCHEMA<TAB>HEX` input line. -/
def answerLine (cfg : Config) (cache : SchemaCache) (line : String) : String × SchemaCache :=
  match line.splitOn "\t" with
  | [schemaText, hex] =>
    let (sch, cache) := lookupSchema cfg cache schemaText
    (respond cfg sch hex, cache)
  | _ => ("bad\tline must be SCHEMA<TAB>HEX", cache)

/-- Drop a trailing newline, and a carriage return before it, if any. -/
def chomp (line : String) : String :=
  let line := if line.back = '\n' then (line.dropEnd 1).toString else line
  if line.back = '\r' then (line.dropEnd 1).toString else line

/-- The `decode` subcommand. -/
def runDecode (cfg : Config) (lineBuffered : Bool) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut cache : SchemaCache := {}
  let mut pending : Nat := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let (out, cache') := answerLine cfg cache (chomp line)
    cache := cache'
    stdout.putStr out
    stdout.putStr "\n"
    pending := pending + 1
    if lineBuffered || pending ≥ 8192 then
      stdout.flush
      pending := 0
  stdout.flush
  return 0

/-- Whether an actual answer satisfies an expected one: exact match, or, when
the expectation is the bare category `err` or `bad`, a match on the category
only (the reason text is informative, not normative).  An answer whose reason
starts with `internal` (the decoder's own consistency checks failed) never
matches a bare category. -/
def answerMatches (expected actual : String) : Bool :=
  expected == actual ||
    ((expected == "err" || expected == "bad") && (actual.splitOn "\t").head? == some expected
      && !actual.startsWith "err\tinternal")

/-- Run one vector file; returns `(passed, failed)`.

Lines are `SCHEMA<TAB>HEX<TAB>EXPECTED`.  Blank lines and lines starting with `#` are
skipped; a line `@mode strict` or `@mode lenient` selects the decoder for the lines
after it (the default is `mode`).  In strict mode, every expected `ok` is also
required of the lenient decoder, which must return the same answer
(theorem `lenient_eq_strict_of_strict`, run here on the compiled code). -/
def checkFile (cfg : Config) (path : String) : IO (Nat × Nat) := do
  let lines ← try IO.FS.lines path catch e =>
    IO.eprintln s!"{path}: cannot read vector file: {e}"
    return (0, 1)
  let mut passed := 0
  let mut failed := 0
  let mut mode := cfg.mode
  let mut cache : SchemaCache := {}
  for h : i in [0:lines.size] do
    let line := lines[i]
    if line.isEmpty || line.startsWith "#" then continue
    if line.startsWith "@" then
      match line with
      | "@mode strict" => mode := .strict
      | "@mode lenient" => mode := .lenient
      | _ =>
        failed := failed + 1
        IO.eprintln s!"{path}:{i + 1}: unknown directive"
      continue
    match line.splitOn "\t" with
    | schemaText :: hex :: expectedParts@(_ :: _) =>
      let expected := "\t".intercalate expectedParts
      let cfg' := { cfg with mode := mode }
      let (out, cache') := answerLine cfg' cache (schemaText ++ "\t" ++ hex)
      cache := cache'
      let mut ok := answerMatches expected out
      let mut note := ""
      if ok && mode == .strict && expected.startsWith "ok\t" then
        let (out', cache'') := answerLine { cfg with mode := .lenient } cache (schemaText ++ "\t" ++ hex)
        cache := cache''
        if out' != out then
          ok := false
          note := s!"\n  lenient:  {out'} (must equal the strict answer)"
      if ok then
        passed := passed + 1
      else
        failed := failed + 1
        IO.eprintln s!"{path}:{i + 1}: MISMATCH\n  schema:   {schemaText}\n  input:    {hex}\n  expected: {expected}\n  actual:   {out}{note}"
    | _ =>
      failed := failed + 1
      IO.eprintln s!"{path}:{i + 1}: malformed vector line (need SCHEMA<TAB>HEX<TAB>EXPECTED)"
  return (passed, failed)

/-- The `check` subcommand. -/
def runCheck (cfg : Config) (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "usage: borsh-spec check [--lenient] FILE..."
    return 2
  let mut passed := 0
  let mut failed := 0
  for p in paths do
    let (a, b) ← checkFile cfg p
    passed := passed + a
    failed := failed + b
  IO.println s!"{passed} passed, {failed} failed"
  return if failed == 0 then 0 else 1

/-- Sample bytes for the third and fourth position in the 4-byte part of the
UTF-8 self-test: boundaries of every row of the well-formedness table. -/
def utf8Sample : List UInt8 :=
  [0x00, 0x41, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc2, 0xe0, 0xf0, 0xf4, 0xff]

/-- The `selftest-utf8` subcommand: compare `validUtf8` with Lean's own
`ByteArray.validateUTF8` on every byte string of length 1 to 3 and on length-4
strings whose last two bytes come from `utf8Sample`.  Prints, per length, the
number of accepted strings and an FNV-1a digest of the accept/reject bits in
enumeration order (first byte slowest), so the same enumeration run against
Rust's `core::str::from_utf8` can be compared. -/
def runUtf8Selftest : IO UInt32 := do
  let mut mismatches : Nat := 0
  let mut counts : Array Nat := #[0, 0, 0, 0]
  let mut hashes : Array UInt64 := #[0xcbf29ce484222325, 0xcbf29ce484222325,
    0xcbf29ce484222325, 0xcbf29ce484222325]
  let step (len : Nat) (bs : List UInt8) (mismatches : Nat) (counts : Array Nat)
      (hashes : Array UInt64) : Nat × Array Nat × Array UInt64 :=
    let mine := validUtf8 bs
    let ref := ByteArray.validateUTF8 (ByteArray.mk bs.toArray)
    let bit : UInt64 := if mine then 1 else 0
    (if mine == ref then mismatches else mismatches + 1,
      if mine then counts.modify (len - 1) (· + 1) else counts,
      hashes.modify (len - 1) fun h => (h ^^^ bit) * 0x100000001b3)
  for i in [0:256] do
    let b0 := i.toUInt8
    (mismatches, counts, hashes) := step 1 [b0] mismatches counts hashes
    for j in [0:256] do
      let b1 := j.toUInt8
      (mismatches, counts, hashes) := step 2 [b0, b1] mismatches counts hashes
      for k in [0:256] do
        let b2 := k.toUInt8
        (mismatches, counts, hashes) := step 3 [b0, b1, b2] mismatches counts hashes
      for b2 in utf8Sample do
        for b3 in utf8Sample do
          (mismatches, counts, hashes) := step 4 [b0, b1, b2, b3] mismatches counts hashes
  for len in [0:4] do
    IO.println s!"length {len + 1}: accepted {counts[len]!} digest {hashes[len]!}"
  IO.println s!"mismatches against ByteArray.validateUTF8: {mismatches}"
  return if mismatches == 0 then 0 else 1

/-- Usage text. -/
def usage : String :=
  "usage:\n" ++
  "  borsh-spec decode [--lenient] [--line-buffered]\n" ++
  "                     [--max-factor N] [--max-steps N]\n" ++
  "                                        (stdin: SCHEMA<TAB>HEX per line)\n" ++
  "  borsh-spec check [--lenient] FILE...  (lines: SCHEMA<TAB>HEX<TAB>EXPECTED)\n" ++
  "  borsh-spec selftest-utf8              (validUtf8 vs ByteArray.validateUTF8)"

/-- Options common to `decode` and `check`, and the arguments left over. -/
structure Options where
  /-- Settings for the decoder. -/
  cfg : Config := {}
  /-- Flush after every line. -/
  lineBuffered : Bool := false
  /-- Positional arguments. -/
  rest : List String := []
  /-- A malformed option. -/
  error : Option String := none

/-- Parse leading `--` options. -/
def parseOptions : List String → Options → Options
  | [], o => { o with rest := o.rest.reverse }
  | "--lenient" :: as, o => parseOptions as { o with cfg := { o.cfg with mode := .lenient } }
  | "--line-buffered" :: as, o => parseOptions as { o with lineBuffered := true }
  | "--max-factor" :: n :: as, o =>
    match n.toNat? with
    | some k => parseOptions as { o with cfg := { o.cfg with maxFactor := k } }
    | none => { o with error := some s!"--max-factor needs a number, got {n}" }
  | "--max-steps" :: n :: as, o =>
    match n.toNat? with
    | some k => parseOptions as { o with cfg := { o.cfg with maxSteps := k } }
    | none => { o with error := some s!"--max-steps needs a number, got {n}" }
  | a :: as, o =>
    if a.startsWith "--" then { o with error := some s!"unknown option {a}" }
    else parseOptions as { o with rest := a :: o.rest }

end BorshSpecCli

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "decode" :: as =>
    let o := BorshSpecCli.parseOptions as {}
    if o.error.isSome || !o.rest.isEmpty then
      IO.eprintln (o.error.getD "decode takes no file arguments")
      IO.eprintln BorshSpecCli.usage
      return 2
    BorshSpecCli.runDecode o.cfg o.lineBuffered
  | "check" :: as =>
    let o := BorshSpecCli.parseOptions as {}
    if let some e := o.error then
      IO.eprintln e
      return 2
    BorshSpecCli.runCheck o.cfg o.rest
  | ["selftest-utf8"] => BorshSpecCli.runUtf8Selftest
  | _ =>
    IO.eprintln BorshSpecCli.usage
    return 2
