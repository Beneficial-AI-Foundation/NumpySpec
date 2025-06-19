import Lean
import FuncTracker.Basic
import FuncTracker.Syntax

namespace FuncTracker

open Lean Lean.Macro

/-- Parse a single cell -/
def parseCell (stx : Syntax) : MacroM String := do
  match stx with
  | .ident _ _ n _ => pure n.toString
  | .atom _ val => 
    -- Check for specific tokens
    if val == "✗" || val == "⋯" || val == "✓✓✓" || val == "✓✓" || val == "✓" || val == "-" then
      pure val
    else
      Macro.throwError s!"Unknown atom: {val}"
  | .node _ _ args =>
    -- Check for num - num pattern
    if args.size == 3 && args[1]!.isToken "-" then
      match args[0]!, args[2]! with
      | .atom _ n1, .atom _ n2 => pure s!"{n1}-{n2}"
      | _, _ => Macro.throwError "Invalid line range format"
    else if args.size == 1 then
      -- String literal
      match args[0]! with
      | .atom _ s => pure (s.drop 1 |>.dropRight 1)  -- Remove quotes
      | _ => Macro.throwError "Invalid string format"
    else
      Macro.throwError s!"Unknown cell node with {args.size} args"
  | _ => Macro.throwError s!"Unknown cell type: {stx}"

/-- Extract cells from a row -/
def extractRowCells (row : Syntax) : MacroM (Array String) := do
  -- Row format: │ cell (│ cell)* │
  let mut cells : Array String := #[]
  let mut i := 1  -- Skip first │
  
  while i < row.getNumArgs - 1 do  -- Skip last │
    if row[i].isOfKind `table_cell then
      let cell ← parseCell row[i]
      cells := cells.push cell
    i := i + 2  -- Skip │ separator
  
  pure cells

/-- Parse a status symbol into a Status value -/
def parseStatus (s : String) : Option Status :=
  match s with
  | "✗" => some .notStarted
  | "⋯" => some .inProgress
  | "✓" => some .implemented
  | "✓✓" => some .tested
  | "✓✓✓" => some .documented
  | _ => none

/-- Parse table rows -/
def parseTableRows (rows : Array Syntax) : MacroM FunctionTable := do
  let mut allRows : Array (Array String) := #[]
  
  for row in rows do
    if row.isOfKind `table_row then
      let cells ← extractRowCells row
      allRows := allRows.push cells
  
  if allRows.size == 0 then
    Macro.throwError "Table must have at least one row"
  
  -- Skip header row if it looks like a header
  let dataRows := if allRows.size > 0 && allRows[0]!.any (fun s => s.trim == "Status" || s.trim == "status") then
    allRows.extract 1 allRows.size
  else
    allRows
  
  -- Parse function data from rows
  let functions ← dataRows.mapM fun row => do
    if row.size < 2 then
      Macro.throwError "Row must have at least name and status columns"
    
    let name := row[0]!.trim
    let statusStr := row[1]!.trim
    
    let some status := parseStatus statusStr
      | Macro.throwError s!"Invalid status symbol: {statusStr}"
    
    let file := if row.size > 2 && row[2]!.trim != "-" 
                then some row[2]!.trim else none
    
    let lines := if row.size > 3 && row[3]!.trim != "-" then 
      -- Parse "10-20" format
      let parts := row[3]!.trim.splitOn "-"
      if parts.length = 2 then
        match parts[0]!.toNat?, parts[1]!.toNat? with
        | some start, some «end» => some (start, «end»)
        | _, _ => none
      else none
    else none
    
    let complexity := if row.size > 4 && row[4]!.trim != "-" 
                      then some row[4]!.trim else none
    
    pure { name, status, file, lines, complexity : TrackedFunction }
  
  pure { functions }

end FuncTracker