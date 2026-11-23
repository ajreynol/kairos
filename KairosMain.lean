import Kairos.Checker.Api
import Cpc.Api

/-!
The `kairos` executable: read a CPC proof in s-expression syntax and report a
verdict, as Logos's `logos` executable does, with Kairos's checker in place of
Logos's.

* Parsing is Logos's parser (`Eo.parseProof`), unchanged.
* The refutation check is `kairos_checker_is_refutation`, which
  `kairos_refines_logos` proves accepts only what Logos's checker accepts.
* The two translation side conditions of Logos's theorem are Logos's own
  checks (`logos_check_translatableAssumptionList`,
  `logos_check_cmdListTranslationOk`), unchanged.

So the verdicts and exit codes are Logos's: `correct` (0), `incorrect` (1),
`incomplete` (2); a parse error exits 1.

Options:
* `--time`: report the time of each phase on stderr.
* `--compare`: also run Logos's checker, report its time, and fail (exit 3)
  if the two checkers disagree.
* `--no-translation`: skip the translation checks (report `correct` when the
  checker accepts), to time the checker alone.
-/

open Eo Kairos.Checker

def Eo.Verdict.word : Verdict → String
  | .correct => "correct"
  | .incorrect => "incorrect"
  | .incomplete => "incomplete"

def Eo.Verdict.status : Verdict → UInt32
  | .correct => 0
  | .incorrect => 1
  | .incomplete => 2

structure Opts where
  time : Bool := false
  compare : Bool := false
  translation : Bool := true

/-- Run `f` and return its result with the elapsed time in milliseconds. -/
def timed (f : Unit → α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0).toFloat / 1.0e6)

def ms (x : Float) : String :=
  let r := (x * 100).round / 100
  s!"{r} ms"

def checkProof (o : Opts) (path : String) : IO UInt32 := do
  let err ← IO.getStderr
  let note (s : String) : IO Unit := do if o.time then err.putStrLn s; err.flush
  let (proof, tRead) ← do
    let t0 ← IO.monoNanosNow
    let s ← IO.FS.readFile path
    let t1 ← IO.monoNanosNow
    pure (s, (t1 - t0).toFloat / 1.0e6)
  note s!"read:        {ms tRead}"
  let (parsed, tParse) ← timed fun _ => Eo.parseProof proof
  note s!"parse:       {ms tParse}"
  match parsed with
  | .error e =>
    IO.eprintln s!"Error parsing proof: {e}"
    return 1
  | .ok (assums, cmds) =>
    let F := logos_assumption_arglist assums
    let (ok, tK) ← timed fun _ => kairos_checker_is_refutation F cmds
    note s!"kairos:      {ms tK}  ({ok})"
    if o.compare then
      let (okL, tL) ← timed fun _ => logos_check_refutation assums cmds
      note s!"logos:       {ms tL}  ({okL})"
      if ok != okL then
        IO.eprintln s!"Error: Kairos says {ok}, Logos says {okL}"
        return 3
    let verdict ←
      if !ok then pure Verdict.incorrect
      else if !o.translation then pure Verdict.correct
      else
        let (tr, tT) ← timed fun _ =>
          logos_check_translatableAssumptionList assums && logos_check_cmdListTranslationOk cmds
        note s!"translation: {ms tT}  ({tr})"
        pure (if tr then Verdict.correct else Verdict.incomplete)
    let out ← IO.getStdout
    out.putStrLn verdict.word
    out.flush
    return verdict.status

def parseArgs : List String → Opts → Option (Opts × String)
  | "--time" :: r, o => parseArgs r { o with time := true }
  | "--compare" :: r, o => parseArgs r { o with compare := true }
  | "--no-translation" :: r, o => parseArgs r { o with translation := false }
  | [p], o => if p.startsWith "--" then none else some (o, p)
  | _, _ => none

def main (args : List String) : IO UInt32 := do
  let some (o, path) := parseArgs args {}
    | IO.eprintln "usage: kairos [--time] [--compare] [--no-translation] <path-to-proof-file>"
      return 1
  checkProof o path
