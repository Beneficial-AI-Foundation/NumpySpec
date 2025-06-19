import Lean
import FuncTracker.Basic
import FuncTracker.Syntax
import FuncTracker.Parser

namespace FuncTracker

open Lean Lean.Elab Term Meta

/-- Convert parsed table to term -/
def tableToTerm (table : FunctionTable) : MacroM (TSyntax `term) := do
  let functions ← table.functions.mapM fun f => do
    let status ← match f.status with
      | .notStarted => `(Status.notStarted)
      | .inProgress => `(Status.inProgress)
      | .implemented => `(Status.implemented)
      | .tested => `(Status.tested)
      | .documented => `(Status.documented)

    let file ← match f.file with
      | some f => `(some $(quote f))
      | none => `(none)

    let lines ← match f.lines with
      | some (s, e) => `(some ($(quote s), $(quote e)))
      | none => `(none)

    let complexity ← match f.complexity with
      | some c => `(some $(quote c))
      | none => `(none)

    `({ name := $(quote f.name),
        status := $status,
        file := $file,
        lines := $lines,
        complexity := $complexity : TrackedFunction })

  `({ functions := #[$functions,*] : FunctionTable })

/-- Macro for function tables -/
macro "funcTable!" "╔" "═"* "╗" rows:table_row* "╚" "═"* "╝" : term => do
  let parsedTable ← parseTableRows rows
  tableToTerm parsedTable

/-- Command to define a function tracking table -/
macro "track" "functions" name:(ident)? ":" "╔" "═"* "╗" rows:table_row* "╚" "═"* "╝" : command => do
  let name := name.getD (mkIdent `myFunctions)
  let parsedTable ← parseTableRows rows
  let tableTerm ← tableToTerm parsedTable
  `(def $name : FunctionTable := $tableTerm)

/-- Check that all functions in a table are implemented -/
def checkAllImplemented (table : FunctionTable) : Except String Unit := do
  let unimplemented := table.functions.filter fun f =>
    f.status != .implemented && f.status != .tested && f.status != .documented

  if unimplemented.size > 0 then
    let names := unimplemented.map (·.name)
    .error s!"The following functions are not implemented: {names}"
  else
    .ok ()

/-- Macro to enforce that all functions are implemented at compile time -/
macro "require" "all" "implemented" table:term : command =>
  `(command|
    #eval match checkAllImplemented $table with
      | Except.ok () => "All functions implemented ✓"
      | Except.error msg => panic! msg)

end FuncTracker
