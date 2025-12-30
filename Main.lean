import OptMaze
import OptMaze.BitMatrix
import OptMaze.Smt

/-- Full pipeline: read 01 matrix, emit SMT2, call solver, write solution, emit Mathematica list.
    CLI:
    - `lake exe opt-maze <input>`                   -- default solver `z3`, maximize objective
    - `lake exe opt-maze <input> <solver>`          -- use given solver, maximize objective
    - `lake exe opt-maze <input> <min>`             -- default solver `z3`, assert non-white ≥ min
    - `lake exe opt-maze <input> <solver> <min>`    -- use given solver with lower bound
    If `min` is not a natural number, the argument is treated as solver. -/
def main (args : List String) : IO Unit := do
  match args with
  | inputStr :: rest =>
      let input : System.FilePath := ⟨inputStr⟩
      let smtPath := input.withExtension "smt2"
      let solPath := input.withExtension "sol"
      let outPath := input.withExtension "out"
      -- interpret optional solver / bound arguments
      let (solver, minBound?) ←
        match rest with
        | [] => pure ("z3", (none : Option Nat))
        | [a] =>
            match a.toNat? with
            | some n => pure ("z3", some n)
            | none => pure (a, none)
        | [a, b] =>
            match b.toNat? with
            | some n => pure (a, some n)
            | none => throw <| IO.userError s!"Cannot parse bound '{b}' as a Nat."
        | _ =>
            throw <| IO.userError "Too many arguments. Usage: lake exe opt-maze <input> [solver] [min]"
      -- 1) parse input and emit SMT2
      let m ← readBitMatrix input
      let falseCount := OptMaze.countFalseCells m
      IO.println s!"black cells: {falseCount}"
      let smt := OptMaze.bitMatrixSmt2 m minBound?
      IO.FS.writeFile smtPath smt
      IO.println s!"SMT2 written to {smtPath}"
      -- 2) call z3 synchronously, capture stdout
      let z3Cmd := solver
      let tStart ← IO.monoMsNow
      let z3Out ← IO.Process.run { cmd := z3Cmd, args := #[smtPath.toString] }
      let tEnd ← IO.monoMsNow
      IO.FS.writeFile solPath z3Out
      IO.println s!"{z3Cmd} output written to {solPath}"
      IO.println s!"solver time: {OptMaze.formatDurationMs (tEnd - tStart)}"
      -- 3) inspect status and optionally parse model
      match OptMaze.parseSmtResult z3Out with
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
  | _ =>
      IO.eprintln <|
        "Usage:\n" ++
        "  lake exe opt-maze <input> [solver] [min]\n" ++
        "    <input>  : 01 matrix file path\n" ++
        "    [solver] : optional solver executable (default: z3)\n" ++
        "    [min]    : optional Nat lower bound on non-white tiles; if only one optional\n" ++
        "               argument and numeric, it is treated as [min] with default solver."
