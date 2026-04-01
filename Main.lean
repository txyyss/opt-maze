import Cli
import OptMaze
import OptMaze.BitMatrix
import OptMaze.Smt

open Cli

/-- Handler: run the full pipeline with parsed CLI options. -/
def runOptMaze (p : Parsed) : IO UInt32 := do
  let inputStr : String := p.positionalArg! "input" |>.as! String
  let input : System.FilePath := ⟨inputStr⟩
  let solver :=
    match p.flag? "solver" with
    | some f => f.as! String
    | none => "z3"
  let minBound? : Option Nat :=
    match p.flag? "min" with
    | some f => some (f.as! Nat)
    | none => none
  let allowCross : Bool := !(p.hasFlag "nocross")

  let smtPath := input.withExtension "smt2"
  let solPath := input.withExtension "sol"
  let outPath := input.withExtension "out"

  -- 1) parse input and emit SMT2
  let m ← readBitMatrix input
  let falseCount := OptMaze.countFalseCells m
  IO.println s!"black cells: {falseCount}"
  let minBoundFinal ←
    if minBound?.isNone && solver != "z3" then
      IO.println s!"{solver} does not support maximize; using {falseCount} as lower bound"
      pure (some falseCount)
    else
      pure minBound?
  let smt := OptMaze.bitMatrixSmt2 m minBoundFinal allowCross
  let constraintCount := OptMaze.countSmtAssertions smt
  IO.println s!"constraints: {constraintCount}"
  IO.FS.writeFile smtPath smt
  IO.println s!"SMT2 written to {smtPath}"

  -- 2) call solver synchronously, capture stdout
  let tStart ← IO.monoMsNow
  let solverOut ← IO.Process.run { cmd := solver, args := #[smtPath.toString] }
  let tEnd ← IO.monoMsNow
  IO.FS.writeFile solPath solverOut
  IO.println s!"{solver} output written to {solPath}"
  IO.println s!"solver time: {OptMaze.formatDurationMs (tEnd - tStart)}"

  -- 3) inspect status and optionally parse model
  match OptMaze.parseSmtResult solverOut with
  | .ok (.sat asgns) =>
      let nonWhite := asgns.foldl (fun acc a => if a.value != 8 then acc + 1 else acc) 0
      IO.println s!"non-white tiles in model: {nonWhite}"
      let math := OptMaze.toMathematicaList asgns
      IO.FS.writeFile outPath math
      IO.println s!"Mathematica list written to {outPath}"
  | .ok .unsat =>
      IO.println "solver reported unsat; no model to parse."
  | .ok (.unknown st) =>
      throw <| IO.userError s!"Unknown solver status '{st}'."
  | .error msg =>
      throw <| IO.userError s!"Failed to parse solver output: {msg}"

  return 0

/-- CLI command definition. -/
def optMazeCmd : Cmd := `[Cli|
  "opt-maze" VIA runOptMaze;
  "Encode a 01 matrix to SMT, call a solver, and emit the model as a Mathematica list."

  FLAGS:
    solver : String; "Optional solver executable (default: z3)."
    min : Nat;       "Optional lower bound on non-white tiles; use with solvers without maximize."
    nocross;         "Disallow cross tiles (type 7)."

  ARGS:
    input : String; "01 matrix file path."
]

/-- Entrypoint: delegate to `optMazeCmd`. -/
def main (args : List String) : IO UInt32 :=
  if args.isEmpty then
    optMazeCmd.printHelp *> pure 0
  else
    optMazeCmd.validate args
