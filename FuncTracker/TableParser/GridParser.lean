import Lean
import Std.Internal.Parsec
import FuncTracker.BasicV2

namespace FuncTracker

open Std.Internal.Parsec
open Std.Internal.Parsec.String

/-- A cell in the 2D grid -/
inductive GridCell where
  | content : String → GridCell
  | border : Char → GridCell
  | empty : GridCell
  deriving Repr

/-- A 2D grid structure -/
structure Grid where
  cells : Array (Array String)
  rows : Nat
  cols : Nat
  deriving Repr

namespace GridParser

-- Import all the parser combinators from GridParser.lean
/-- Parse whitespace can have zero or more-/
def ows : Parser Unit := do
  let _ ← many (satisfy (fun c => c == ' ' || c == '\t'))
  pure ()

-- #eval ows "sdcas asdc".mkIterator


/-- Parse many characters satisfying a predicate -/
def manyChars (p : Char → Bool) : Parser String := do
  let chars ← many (satisfy p)
  return String.mk chars.toList
/-- Parse many1 characters satisfying a predicate -/
def many1Chars (p : Char → Bool) : Parser String := do
  let chars ← many1 (satisfy p)
  return String.mk chars.toList

/-- Test if a character is not a whitespace or border character -/
def test (c: Char): Bool:= c ∉ [' ', '║', '╠', '╣', '╦', '╩', '╔', '╚', '═', '╬', '╝', '╗']
-- #eval many1Chars test "sdjn  jdas".mkIterator


/-- Parse a specific character -/
def pchar (c : Char) : Parser Char :=
  satisfy (· == c)

-- #eval pchar 'x' "axpsdkf".mkIterator


/-- Parse horizontal border line: ═══ -/
def hBorder : Parser Unit := do
  let _ ← many1 (pchar '═')
  let _ ← optional (pchar '╦')
  let _ ← optional (pchar '╩')
  let _ ← optional (pchar '╬')
  pure ()

-- #eval hBorder "═╩══╦═══wfw".mkIterator


/-- Parse top border: ╔═╦═╦═╗ -/
def topBorder : Parser Unit := do
  let _ ← pchar '╔'
  let _ ← many hBorder
  let _ ← pchar '╗'
  let _ ← optional (pchar '\n')
  pure ()

-- #eval topBorder "╔════╗\nfvkmfv".mkIterator

/-- Parse bottom border: ╚═╩═╩═╝ -/
def bottomBorder : Parser Unit := do
  let _ ← pchar '╚'
  let _ ← many hBorder
  let _ ← pchar '╝'
  -- Don't consume anything after the border
  pure ()

/-- Parse separator border: ╠═══╣ -/
def separatorBorder : Parser Unit := do
  let _ ← pchar '╠'
  let _ ← many hBorder
  let _ ← pchar '╣'
  let _ ← optional (pchar '\n')
  pure ()


/-- Parse text up to a delimiter (non-inclusive) -/
def textUpto (delim : Char) : Parser String :=
  manyChars (· != delim)

def cell: Parser String := do
  let _ ← pchar '║'
  let _ ← ws
  let st ← manyChars test
  let _ ← ws
  pure (st)

def cells: Parser (Array String):= do
  let s ←  many cell
  return if s.size > 0 then s.shrink (s.size - 1) else s

#eval peek! "║   ✓  ║  ".mkIterator
#eval cell "║    ║  ".mkIterator
#eval cells "║  vfd  ║  h  ║j║  h  ║  h   ║ ".mkIterator

def binder (p1: Parser α) :β  -> Parser α :=
  fun _ => p1.bind (fun _ => p1)


/-- Parse complete table
Plan is parse top row than second row than
many seperator than cells
bottom row -/
def parseTable : Parser Grid := do
  -- Top border
  let _ ← topBorder

  -- Parse header row
  let head ← cells

  -- Parse data rows: many (optional separator followed by cells)
  let dataRows ← many (do
    optional separatorBorder >>= fun
    | some _ => cells  -- If separator parsed successfully, parse cells
    | none => fail "expected separator")

  -- Parse bottom border
  let _ ← bottomBorder

  -- Combine header with data rows
  let allRows := #[head].append dataRows

  -- Validate dimensions
  if allRows.size <= 1 then
    fail "table must have at least one data row"

  let cols := head.size
  for i in [1:allRows.size] do
    let row := allRows[i]!
    if row.size != cols then
      fail s!"inconsistent row width in row {i}: expected {cols}, got {row.size}"

  return {
    cells := allRows
    rows := allRows.size
    cols := cols
  }


def gridTableStr : String :=
  "╔═══════════════╦═══════════════╦═══════════════╗\n" ++
  "║ Function      ║ Status        ║ DependsOn     ║\n" ++
  "╠═══════════════╬═══════════════╬═══════════════╣\n" ++
  "║ func1         ║ ✓             ║      .        ║\n" ++
  "╠═══════════════╬═══════════════╬═══════════════╣\n" ++
  "║ func2         ║ ⋯             ║ ←             ║\n" ++
  "╠═══════════════╬═══════════════╬═══════════════╣\n" ++
  "║ func3         ║ ✓✓            ║        .      ║\n" ++
  "╠═══════════════╬═══════════════╬═══════════════╣\n" ++
  "║ func4         ║ ✗             ║   ←           ║\n" ++
  "╚═══════════════╩═══════════════╩═══════════════╝"

#eval parseTable gridTableStr.mkIterator
#eval bottomBorder "╚══════════╩═════════╝knd".mkIterator
/-- Run parser on a string -/
def run (input : String) : Except String Grid :=
  match parseTable input.mkIterator with
  | .success _ res => .ok res
  | .error it msg => .error s!"Parse error at position {repr it.i}: {msg}"

end GridParser

/-- Convert grid to FunctionTable with Names -/
def gridToFunctionTableV2 (grid : Grid) : Except String FunctionTable := do
  let mut functions : Array TrackedFunction := #[]

  for row in grid.cells do
    if row.size < 2 then
      throw "Row must have at least name and status columns"

    let nameStr := row[0]!
    let statusStr := row[1]!

    -- Convert string to Name
    let name := stringToName nameStr

    let status ← match statusStr with
      | "✗" => pure Status.notStarted
      | "⋯" => pure Status.inProgress
      | "✓" => pure Status.implemented
      | "✓✓" => pure Status.tested
      | "✓✓✓" => pure Status.documented
      | _ => throw s!"Invalid status symbol: {statusStr}"

    let file := if h : row.size > 2 then
      let f := row[2]
      if f == "-" || f == "" then none else some f
    else none

    let lines := if h : row.size > 3 then
      let l := row[3]
      if l == "-" || l == "" then none
      else
        -- Parse "10-20" format
        let parts := l.splitOn "-"
        if parts.length == 2 then
          match parts[0]!.toNat?, parts[1]!.toNat? with
          | some start, some «end» => some (start, «end»)
          | _, _ => none
        else none
    else none

    let complexity := if h : row.size > 4 then
      let c := row[4]
      if c == "-" || c == "" then none else some c
    else none

    -- Extract cross-refs from a "refs" column if present (column 5, index 4)
    let refs := if h : row.size > 4 then
      -- Check if this is actually refs or complexity
      let col := row[4]
      if col.contains ',' || col.contains '.' then
        -- Likely refs (contains dots or commas)
        let refStrs := col.splitOn ","
        refStrs.map (fun s => stringToName s.trim) |>.toArray
      else
        #[]
    else if h : row.size > 5 then
      let r := row[5]
      if r == "-" || r == "" then #[]
      else
        -- Parse comma-separated refs
        let refStrs := r.splitOn ","
        refStrs.map (fun s => stringToName s.trim) |>.toArray
    else #[]

    functions := functions.push {
      name := name
      status := status
      file := file
      lines := lines
      complexity := complexity
      docString := none  -- Would be filled by Verso integration
      refs := refs
    }

  return { functions := functions }

end FuncTracker
