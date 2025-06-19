import Lean

namespace FuncTracker

open Lean

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

/-- A tracked function with its implementation status -/
structure TrackedFunction where
  /-- Name of the function -/
  name : String
  /-- Status of the function implementation -/
  status : Status
  /-- File containing the function implementation, if known. -/
  file : Option String := none
  /-- Line range of the function implementation, if known. Row, column indices. -/
  lines : Option (Nat × Nat) := none
  /-- Complexity of the function, if known. -/
  complexity : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Table data structure -/
structure FunctionTable where
  /-- Array of tracked functions -/
  functions : Array TrackedFunction
  deriving Repr, BEq, DecidableEq

/-- Progress statistics -/
structure Progress where
  /-- Total number of functions in the table. -/
  total : Nat
  /-- Number of functions that have not been started. -/
  notStarted : Nat
  /-- Number of functions that are in progress. -/
  inProgress : Nat
  /-- Number of functions that are implemented. -/
  implemented : Nat
  /-- Number of functions that are tested. -/
  tested : Nat
  /-- Number of functions that are documented. -/
  documented : Nat
  deriving Repr, BEq, DecidableEq

/-- Compute the progress of a function table -/
def FunctionTable.computeProgress (table : FunctionTable) : Progress :=
  let counts := table.functions.foldl (init := (0, 0, 0, 0, 0)) fun (ns, ip, im, t, d) f =>
    match f.status with
    | .notStarted => (ns + 1, ip, im, t, d)
    | .inProgress => (ns, ip + 1, im, t, d)
    | .implemented => (ns, ip, im + 1, t, d)
    | .tested => (ns, ip, im, t + 1, d)
    | .documented => (ns, ip, im, t, d + 1)
  { total := table.functions.size
    notStarted := counts.1
    inProgress := counts.2.1
    implemented := counts.2.2.1
    tested := counts.2.2.2.1
    documented := counts.2.2.2.2 }

/-- Compute the percentage of functions that are implemented, tested, and documented -/
def Progress.percentComplete (p : Progress) : Float :=
  if p.total = 0 then 100.0
  else (p.implemented.toFloat + p.tested.toFloat + p.documented.toFloat) / p.total.toFloat * 100.0

end FuncTracker
