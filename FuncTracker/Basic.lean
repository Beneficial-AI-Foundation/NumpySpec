import Lean

namespace FuncTracker

open Lean

/-- Status of a function implementation -/
inductive Status where
  | notStarted
  | inProgress
  | implemented
  | tested
  | documented
  deriving Repr, DecidableEq

def Status.toSymbol : Status → String
  | .notStarted => "✗"
  | .inProgress => "⋯"
  | .implemented => "✓"
  | .tested => "✓✓"
  | .documented => "✓✓✓"

/-- A tracked function with its implementation status -/
structure TrackedFunction where
  name : String
  status : Status
  file : Option String := none
  lines : Option (Nat × Nat) := none
  complexity : Option String := none
  deriving Repr

/-- Table data structure -/
structure FunctionTable where
  functions : Array TrackedFunction
  deriving Repr

/-- Progress statistics -/
structure Progress where
  total : Nat
  notStarted : Nat
  inProgress : Nat
  implemented : Nat
  tested : Nat
  documented : Nat
  deriving Repr

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

def Progress.percentComplete (p : Progress) : Float :=
  if p.total = 0 then 100.0
  else (p.implemented.toFloat + p.tested.toFloat + p.documented.toFloat) / p.total.toFloat * 100.0

end FuncTracker