import OptMaze
import OptMaze.BitMatrix
import OptMaze.Smt

/-- Full pipeline: read 01 matrix, emit SMT2, call z3, write solution, emit Mathematica list. -/
def main (args : List String) : IO Unit := do
  match args with
  | inputStr :: z3Path? =>
      let input : System.FilePath := ⟨inputStr⟩
      let smtPath := input.withExtension "smt2"
      let solPath := input.withExtension "sol"
      let outPath := input.withExtension "out"
      -- 1) parse input and emit SMT2
      let m ← readBitMatrix input
      let falseCount := OptMaze.countFalseCells m
      IO.println s!"black cells: {falseCount}"
      let smt := OptMaze.bitMatrixToSmt2 m
      IO.FS.writeFile smtPath smt
      IO.println s!"SMT2 written to {smtPath}"
      -- 2) call z3 synchronously, capture stdout
      let z3Cmd := z3Path?.headD "z3"
      let tStart ← IO.monoMsNow
      let z3Out ← IO.Process.run { cmd := z3Cmd, args := #[smtPath.toString] }
      let tEnd ← IO.monoMsNow
      IO.FS.writeFile solPath z3Out
      IO.println s!"{z3Cmd} output written to {solPath}"
      IO.println s!"solver time: {OptMaze.formatDurationMs (tEnd - tStart)}"
      -- 3) parse model and emit Mathematica list
      match OptMaze.parseSmtSolution z3Out with
      | .ok asgns =>
          let nonWhite := asgns.foldl (fun acc a => if a.value != 8 then acc + 1 else acc) 0
          IO.println s!"non-white tiles in model: {nonWhite}"
          let math := OptMaze.toMathematicaList asgns
          IO.FS.writeFile outPath math
          IO.println s!"Mathematica list written to {outPath}"
      | .error msg =>
          throw <| IO.userError s!"Failed to parse solver output: {msg}"
  | _ =>
      IO.eprintln "Usage: lake exe opt-maze <input-file> [z3-path]"
