import OptMaze
import OptMaze.BitMatrix

/-- Entry point: read file path from CLI, parse matrix, print height/width. -/
def main (args : List String) : IO Unit := do
  match args with
  | file :: _ =>
      let m ← readBitMatrix file
      IO.println s!"height = {m.height}, width = {m.width}"
  | _ =>
      IO.eprintln "Usage: lake exe opt-maze <file>"
