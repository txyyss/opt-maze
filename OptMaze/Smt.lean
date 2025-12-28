import OptMaze.BitMatrix

namespace OptMaze

open BitMatrix
open Std

/-- Virtual node used for connectivity encoding (may split a cross into two nodes). -/
structure VirtNode where
  row : Nat
  col : Nat
  name : String
  kind : String
  active : String
  up : String
  right : String
  down : String
  left : String
  deriving DecidableEq, Inhabited

/-- SMT helpers for tile directions. -/
def smtPrelude : Array String := #[
  "(set-logic QF_LIA)",
  "(define-fun inRange ((t Int)) Bool (and (<= 1 t) (<= t 8)))",
  "(define-fun hasUp ((t Int))   Bool (or (= t 1) (= t 4) (= t 5) (= t 7)))",
  "(define-fun hasRight ((t Int)) Bool (or (= t 1) (= t 2) (= t 6) (= t 7)))",
  "(define-fun hasDown ((t Int)) Bool (or (= t 2) (= t 3) (= t 5) (= t 7)))",
  "(define-fun hasLeft ((t Int)) Bool (or (= t 3) (= t 4) (= t 6) (= t 7)))",
  "(define-fun nonWhite ((t Int)) Int (ite (= t 8) 0 1))"
]

private def dirConstr (dirName : String) (tileName : String) : String :=
  s!"({dirName} {tileName})"

private def dirFalse (dirName : String) (tileName : String) : String :=
  s!"(not ({dirName} {tileName}))"

private def declareTiles (m : BitMatrix) (lines : Array String) :
    Id (Array String × Array (Nat × Nat × String) × Array VirtNode) := do
  let mut lines := lines
  let mut tiles : Array (Nat × Nat × String) := #[]
  let mut nodes : Array VirtNode := #[]
  for r in List.range m.height do
    for c in List.range m.width do
      match m.get? r c with
      | some false =>
          let name := s!"tile_{r}_{c}"
          lines := lines.push s!"(declare-const {name} Int)"
          lines := lines.push s!"(assert (inRange {name}))"
          tiles := tiles.push (r, c, name)
          let baseActive := s!"(and (not (= {name} 7)) (= (nonWhite {name}) 1))"
          nodes := nodes.push {
            row := r, col := c, name := s!"node_{r}_{c}", kind := "base",
            active := baseActive,
            up := s!"(hasUp {name})", right := s!"(hasRight {name})",
            down := s!"(hasDown {name})", left := s!"(hasLeft {name})"
          }
          let crossActive := s!"(= {name} 7)"
          nodes := nodes.push {
            row := r, col := c, name := s!"nodeH_{r}_{c}", kind := "h",
            active := crossActive,
            up := "false", down := "false",
            left := s!"(hasLeft {name})", right := s!"(hasRight {name})"
          }
          nodes := nodes.push {
            row := r, col := c, name := s!"nodeV_{r}_{c}", kind := "v",
            active := crossActive,
            up := s!"(hasUp {name})", down := s!"(hasDown {name})",
            left := "false", right := "false"
          }
      | _ => pure ()
  return (lines, tiles, nodes)

private def addAdjacencyAndBoundary (m : BitMatrix) (lines : Array String)
    (tiles : Array (Nat × Nat × String)) : Array String :=
  Id.run do
    let mut lines := lines
    for (r, c, name) in tiles do
      let isLeft := c = 0
      let isRight := c + 1 = m.width
      let isTop := r = 0
      let isBottom := r + 1 = m.height
      -- boundary type restrictions
      if isLeft || isRight then
        lines := lines.push s!"(assert (= {name} 6))" -- horizontal only
      else if isTop || isBottom then
        lines := lines.push s!"(assert (= {name} 5))" -- vertical only
      -- adjacency constraints with boundary relaxation
      -- right neighbor
      if c + 1 < m.width then
        match m.get? r (c+1) with
        | some false =>
            let n := s!"tile_{r}_{c+1}"
            lines := lines.push s!"(assert (= (hasRight {name}) (hasLeft {n})))"
        | _ =>
            lines := lines.push s!"(assert {dirFalse "hasRight" name})"
      else if !isRight then
        lines := lines.push s!"(assert {dirFalse "hasRight" name})"
      -- left neighbor
      if c > 0 then
        match m.get? r (c-1) with
        | some false =>
            let n := s!"tile_{r}_{c-1}"
            lines := lines.push s!"(assert (= (hasLeft {name}) (hasRight {n})))"
        | _ =>
            lines := lines.push s!"(assert {dirFalse "hasLeft" name})"
      else if !isLeft then
        lines := lines.push s!"(assert {dirFalse "hasLeft" name})"
      -- down neighbor
      if r + 1 < m.height then
        match m.get? (r+1) c with
        | some false =>
            let n := s!"tile_{r+1}_{c}"
            lines := lines.push s!"(assert (= (hasDown {name}) (hasUp {n})))"
        | _ =>
            lines := lines.push s!"(assert {dirFalse "hasDown" name})"
      else if !isBottom then
        lines := lines.push s!"(assert {dirFalse "hasDown" name})"
      -- up neighbor
      if r > 0 then
        match m.get? (r-1) c with
        | some false =>
            let n := s!"tile_{r-1}_{c}"
            lines := lines.push s!"(assert (= (hasUp {name}) (hasDown {n})))"
        | _ =>
            lines := lines.push s!"(assert {dirFalse "hasUp" name})"
      else if !isTop then
        lines := lines.push s!"(assert {dirFalse "hasUp" name})"
    return lines

private def neighborCandidates (nodes : Array VirtNode) (r c : Nat) (dir : String) : Array VirtNode :=
  let candidates := nodes.filter (fun n => n.row = r && n.col = c && (
    match dir with
    | "R" => n.left ≠ "false"
    | "L" => n.right ≠ "false"
    | "U" => n.down ≠ "false"
    | "D" => n.up ≠ "false"
    | _ => False))
  let preferKind := match dir with
    | "R" | "L" => "h"
    | "U" | "D" => "v"
    | _ => "base"
  -- keep preferred kind first to preserve previous bias
  let (pref, rest) := candidates.partition (fun n => n.kind = preferKind)
  pref ++ rest

private def addConnectivity (m : BitMatrix) (lines : Array String)
    (nodes : Array VirtNode) : Array String :=
  Id.run do
    let mut lines := lines
    if nodes.size > 0 then
      let isBoundary (r c : Nat) : Bool :=
        r = 0 || c = 0 || r + 1 = m.height || c + 1 = m.width
      let (rootR, rootC) :=
        match nodes.find? (fun n => isBoundary n.row n.col) with
        | some v => (v.row, v.col)
        | none =>
            match nodes.toList.head? with
            | some v => (v.row, v.col)
            | none => unreachable!
      let maxRank := nodes.size
      -- declare ranks for all tiles first
      for n in nodes do
        let rankName := s!"rank_{n.row}_{n.col}_{n.kind}"
        let active := n.active
        lines := lines.push s!"(declare-const {rankName} Int)"
        if n.row = rootR ∧ n.col = rootC then
          lines := lines.push s!"(assert (=> {active} (= {rankName} 0)))"
        else
          lines := lines.push s!"(assert (=> {active} (and (>= {rankName} 1) (<= {rankName} {maxRank}))))"
      -- parent-choice connectivity
      for n in nodes do
        let rankName := s!"rank_{n.row}_{n.col}_{n.kind}"
        let active := n.active
        let isRoot := n.row = rootR ∧ n.col = rootC
        let pR := s!"pR_{n.row}_{n.col}_{n.kind}"
        let pL := s!"pL_{n.row}_{n.col}_{n.kind}"
        let pD := s!"pD_{n.row}_{n.col}_{n.kind}"
        let pU := s!"pU_{n.row}_{n.col}_{n.kind}"
        lines := lines.push s!"(declare-const {pR} Bool)"
        lines := lines.push s!"(declare-const {pL} Bool)"
        lines := lines.push s!"(declare-const {pD} Bool)"
        lines := lines.push s!"(declare-const {pU} Bool)"
        if isRoot then
          lines := lines.push s!"(assert (not {pR}))"
          lines := lines.push s!"(assert (not {pL}))"
          lines := lines.push s!"(assert (not {pD}))"
          lines := lines.push s!"(assert (not {pU}))"
        else
          lines := lines.push s!"(assert (=> {active} (or {pR} {pL} {pD} {pU})))"
        -- directional parent constraints
        if n.right = "false" then
          lines := lines.push s!"(assert (not {pR}))"
        else
          let cands := neighborCandidates nodes n.row (n.col+1) "R"
          if cands.isEmpty then
            lines := lines.push s!"(assert (not {pR}))"
          else
            let pieces := cands.map (fun nn =>
              let nRank := s!"rank_{nn.row}_{nn.col}_{nn.kind}"
              let nActive := nn.active
              s!"(and {active} {nActive} {n.right} {nn.left} (< {nRank} {rankName}))")
            let disj := String.intercalate " " pieces.toList
            lines := lines.push s!"(assert (=> {pR} (or {disj})))"
        if n.col > 0 then
          if n.left = "false" then
            lines := lines.push s!"(assert (not {pL}))"
        else
          lines := lines.push s!"(assert (not {pL}))"
        if n.col > 0 then
          let cands := neighborCandidates nodes n.row (n.col-1) "L"
          if cands.isEmpty then
            lines := lines.push s!"(assert (not {pL}))"
          else
            let pieces := cands.map (fun nn =>
              let nRank := s!"rank_{nn.row}_{nn.col}_{nn.kind}"
              let nActive := nn.active
              s!"(and {active} {nActive} {n.left} {nn.right} (< {nRank} {rankName}))")
            let disj := String.intercalate " " pieces.toList
            lines := lines.push s!"(assert (=> {pL} (or {disj})))"
        if n.down = "false" then
            lines := lines.push s!"(assert (not {pD}))"
        else
          let cands := neighborCandidates nodes (n.row+1) n.col "D"
          if cands.isEmpty then
            lines := lines.push s!"(assert (not {pD}))"
          else
            let pieces := cands.map (fun nn =>
              let nRank := s!"rank_{nn.row}_{nn.col}_{nn.kind}"
              let nActive := nn.active
              s!"(and {active} {nActive} {n.down} {nn.up} (< {nRank} {rankName}))")
            let disj := String.intercalate " " pieces.toList
            lines := lines.push s!"(assert (=> {pD} (or {disj})))"
        if n.row > 0 then
          if n.up = "false" then
            lines := lines.push s!"(assert (not {pU}))"
          else
            let cands := neighborCandidates nodes (n.row-1) n.col "U"
            if cands.isEmpty then
              lines := lines.push s!"(assert (not {pU}))"
            else
              let pieces := cands.map (fun nn =>
                let nRank := s!"rank_{nn.row}_{nn.col}_{nn.kind}"
                let nActive := nn.active
                s!"(and {active} {nActive} {n.up} {nn.down} (< {nRank} {rankName}))")
              let disj := String.intercalate " " pieces.toList
              lines := lines.push s!"(assert (=> {pU} (or {disj})))"
        else
          lines := lines.push s!"(assert (not {pU}))"
    return lines

/-- Build SMT-LIB text for a given `BitMatrix`. Cells with value `false` become tile variables; `true` cells are ignored (treated as absent). -/
def bitMatrixToSmt2 (m : BitMatrix) : String :=
  Id.run do
    let (lines0, tiles, nodes) := declareTiles m smtPrelude
    let lines1 := addAdjacencyAndBoundary m lines0 tiles
    let lines2 := addConnectivity m lines1 nodes
    let mut lines := lines2
    -- objective: maximize number of non-white tiles
    let objective :=
      if tiles.isEmpty then "(maximize 0)"
      else
        let terms := tiles.map (fun (_, _, n) => s!"(nonWhite {n})")
        s!"(maximize (+ {String.intercalate " " terms.toList}))"
    lines := lines.push objective
    lines := lines.push "(check-sat)"
    lines := lines.push "(get-model)"
    String.intercalate "\n" lines.toList

/-- A single tile assignment decoded from an SMT solver model. -/
structure TileAssignment where
  row : Nat
  col : Nat
  value : Int
  deriving Repr

private def parseTileName (name : String) : Option (Nat × Nat) := do
  let parts := name.splitOn "_"
  match parts with
  | ["tile", r, c] =>
      let r? := r.toNat?
      let c? := c.toNat?
      match r?, c? with
      | some r', some c' => some (r', c')
      | _, _ => none
  | _ => none

private def dropParensRight (s : String) : String :=
  s.dropRightWhile fun ch => ch = ')' || ch = '\r'

/-- Parse a single line of Z3 model output. Supports the usual
    `(define-fun tile_r_c () Int v)` shape. Non-matching lines return `none`. -/
private def parseModelLine (line : String) : Option (String × String) := do
  let t := line.trim
  if !t.startsWith "(define-fun tile_" then
    none
  else
    let parts := t.splitOn " "
    match parts with
    | _ :: name :: _ => some (name, t)
    | _ => none

/-- Parse all tile assignments from an SMT solver output string. Handles multi-line
    `(define-fun …)` blocks where the value appears on the next line. Non-matching
    lines are ignored. -/
def parseSmtSolution (contents : String) : Except String (Array TileAssignment) := do
  let lines := contents.splitOn "\n"
  let rec go : List String → Array TileAssignment → Except String (Array TileAssignment)
    | [], acc => .ok acc
    | ln :: rest, acc =>
        match parseModelLine ln.trim with
        | none => go rest acc
        | some (name, _) =>
            match rest with
            | valLn :: restTail =>
                let valStr := dropParensRight valLn.trim
                match valStr.toInt? with
                | none => throw s!"Failed to parse value for {name} from '{valLn}'."
                | some v =>
                    match parseTileName name with
                    | some (r, c) =>
                        go restTail (acc.push { row := r, col := c, value := v })
                    | none =>
                        throw s!"Bad tile name '{name}'."
            | [] =>
                throw s!"Missing value line for {name}."
  go lines #[]

/-- Read a solver output file and parse it into tile assignments. -/
def readSmtSolution (path : System.FilePath) : IO (Array TileAssignment) := do
  let contents ← IO.FS.readFile path
  match parseSmtSolution contents with
  | .ok arr => pure arr
  | .error msg => throw <| IO.userError s!"{path}: {msg}"

/-- Render assignments as a Mathematica-friendly list of triples `{{r, c, v}, …}`. -/
def toMathematicaList (asgns : Array TileAssignment) : String :=
  let items := asgns.map (fun a => "{" ++ toString a.row ++ ", " ++ toString a.col ++ ", " ++ toString a.value ++ "}")
  "{" ++ String.intercalate ", " items.toList ++ "}"

end OptMaze
