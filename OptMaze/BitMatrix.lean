import Init.System.IO

/-- A rectangular 0/1 matrix backed by arrays for O(1) indexing. -/
structure BitMatrix where
  height : Nat
  width : Nat
  rows : Array (Array Bool)
  deriving Repr

namespace BitMatrix

/-- Safe lookup; returns `none` if the indices are out of bounds. -/
def get? (m : BitMatrix) (r c : Nat) : Option Bool := do
  let row ← m.rows[r]?
  row[c]?

end BitMatrix

private def parse01Line (line : String) : Except String (Array Bool) := do
  let mut row : Array Bool := #[]
  for ch in line.toList do
    if ch == '0' then
      row := row.push false
    else if ch == '1' then
      row := row.push true
    else if ch == '\r' then
      pure () -- tolerate Windows line endings
    else
      throw s!"Unexpected character '{ch}' in line: {line}"
  return row

/-- Parse a whole text content into a rectangular `BitMatrix`. -/
def parseBitMatrix (contents : String) : Except String BitMatrix := do
  let mut rows : Array (Array Bool) := #[]
  let mut width? : Option Nat := none
  for raw in contents.splitOn "\n" do
    if raw.trim.isEmpty then
      pure ()
    else
      match parse01Line raw with
      | .error msg => throw msg
      | .ok row =>
          if row.isEmpty then
            throw "Encountered an empty row."
          match width? with
          | none =>
              width? := some row.size
          | some w =>
              if row.size != w then
                throw s!"Row width {row.size} differs from expected {w}."
          rows := rows.push row
  let some width := width?
    | throw "No rows found."
  return { height := rows.size, width := width, rows := rows }

/-- Read a text file of 0/1 characters into a rectangular `BitMatrix`. -/
def readBitMatrix (path : System.FilePath) : IO BitMatrix := do
  try
    let contents ← IO.FS.readFile path
    match parseBitMatrix contents with
    | .ok m => pure m
    | .error msg => throw <| IO.userError s!"{path}: {msg}"
  catch err =>
    throw <| IO.userError s!"{path}: {err.toString}"
