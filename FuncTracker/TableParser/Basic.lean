import Lean

namespace FuncTracker

open Lean
-- Our objectif is to parse a table of functions and
-- end up with a list of lists of [function, status, dependancies]



/-- Status of a function implementation -/
inductive Status where
  /-- The function has not been started. -/
  | notStarted
  /-- The function is in progress. -/
  | inProgress
  /-- The function is implemented. -/
  | implemented
  /-- The function is tested. -/
  | tested
  /-- The function is documented. -/
  | documented
  deriving Repr, DecidableEq, BEq
/-- Convert a status to a symbol for display -/
def Status.toSymbol : Status → String
  | .notStarted => "✗"
  | .inProgress => "⋯"
  | .implemented => "✓"
  | .tested => "✓✓"
  | .documented => "✓✓✓"


/-- A tracked function ith its implementation status -/
structure TrackedFunction where
  /-- Name of the function as a Lean Name -/
  name : Name
  /-- Status of the function implementation -/
  status : Status
  /-- File containing the function implementation, if known. -/
  file : Option String := none
  /-- Line range of the function implementation, if known. Row, column indices. -/
  lines : Option (Nat × Nat) := none
  /-- Complexity of the function, if known. -/
  complexity : Option String := none
  /-- Documentation string from Verso, if available -/
  docString : Option String := none
  /-- URL to Verso documentation, if available -/
  versoLink : Option String := none
  /-- Cross-references to related functions (legacy - use typedRefs for new code) -/
  refs : Array Name := #[]
  /-- Version or commit hash when this entry was last updated -/
  version : Option String := none
  deriving Repr, BEq, DecidableEq


/-- Table data structure -/
structure FunctionTable where
  /-- Array of tracked functions -/
  functions : Array TrackedFunction
  /-- Module this table is tracking -/
  module : Option Name := none
  deriving Repr, BEq, DecidableEq

















-------------After Parsing -----------------

/-- Find a function by name in the table -/
def FunctionTable.find? (table : FunctionTable) (name : Name) : Option TrackedFunction :=
  table.functions.find? fun f => f.name == name

/-- Update a function's status by name -/
def FunctionTable.updateStatus (table : FunctionTable) (name : Name) (status : Status) : FunctionTable :=
  { table with
    functions := table.functions.map fun f =>
      if f.name == name then { f with status := status } else f }

/-- Get all functions with a specific status -/
def FunctionTable.filterByStatus (table : FunctionTable) (status : Status) : Array TrackedFunction :=
  table.functions.filter fun f => f.status == status

/-- Update a function's Verso link -/
def FunctionTable.updateVersoLink (table : FunctionTable) (name : Name) (link : String) : FunctionTable :=
  { table with
    functions := table.functions.map fun f =>
      if f.name == name then { f with versoLink := some link } else f }

/-- Generate a markdown documentation section for the function table -/
def FunctionTable.toMarkdown (table : FunctionTable) : String :=
  let header := "| Name | Status | File | Lines | Complexity |\n|------|--------|------|-------|------------|\n"
  let rows := table.functions.map fun f =>
    let file := f.file.getD "-"
    let lines := match f.lines with
      | some (s, e) => s!"{s}-{e}"
      | none => "-"
    let complexity := f.complexity.getD "-"
    s!"| {f.name} | {f.status.toSymbol} | {file} | {lines} | {complexity} |"
  header ++ String.intercalate "\n" rows.toList

end FuncTracker
