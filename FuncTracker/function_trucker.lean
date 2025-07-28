import Lean
open Lean Elab Term

/-
Improved Functracker - Fixed version of basic.lean with proper function name display
This version fixes the issue where functions show up as "<function>" instead of their actual names.
-/

-- Status enumeration matching basic.lean
inductive Status where
  | documented
  | completed
  | in_progress
  | failed
  deriving BEq, Repr

-- Syntax for status symbols
declare_syntax_cat function_status
syntax "✓"   : function_status
syntax "✓✓"  : function_status
syntax ".."   : function_status
syntax "✗"   : function_status

syntax function_status : term

macro_rules
| `(✓)   => `(Status.completed)
| `(✓✓)  => `(Status.documented)
| `(✗)   => `(Status.failed)
| `(..) => `(Status.in_progress)

-- Improved table structure that stores function names properly
structure Table where
  functions     : List String  -- Store actual function names as strings
  status        : List Status
  deriving Repr

-- Table parsing syntax (matches basic.lean structure)
declare_syntax_cat horizontal_border
syntax "═" : horizontal_border

declare_syntax_cat game_cell
syntax term : game_cell

declare_syntax_cat game_row
syntax "║" game_cell "║" game_cell "║" : game_row
declare_syntax_cat table_top_row
declare_syntax_cat table_bottom_row

syntax "\n╔"horizontal_border*"╦"horizontal_border*"╗\n" : table_top_row
syntax "╚" horizontal_border*"╩" horizontal_border*"╝\n" : table_bottom_row
syntax:max table_top_row game_row* table_bottom_row : term


open Lean Meta Elab Term

elab "showFnName%" f:term : term => do
  let e ← elabTerm f none
  let e ← withTransparency TransparencyMode.reducible do
    whnf e

  match e.getAppFn with
  | Expr.const name _ =>
    let str := toString name
    logInfo m!"[const] Function name is: {str}"
    return mkStrLit str
  | Expr.fvar fvarId =>
    let lctx ← getLCtx
    let decl := lctx.get! fvarId
    let name := decl.userName
    logInfo m!"[fvar] Function name is: {name}"
    return mkStrLit name.toString
  | _ =>
    logInfo m!"[anon] No name for this function"
    return mkStrLit "<anonymous>"
#eval showFnName% Nat.add

macro_rules
| `(╔ $tb1:horizontal_border*╦ $tb2:horizontal_border* ╗
    $rows:game_row*
    ╚ $bb1:horizontal_border*╩ $bb2:horizontal_border* ╝) => do
  -- `rows` is an array of the matched `fun_row`s.  We fold them into an
  -- explicit `List` expression, building from the right: `[ ]`, then
  -- `t :: []`, then `t₁ :: t₂ :: []`, …
  let mut funcs ← `(List.nil)
  let mut statuses ← `(List.nil)
  for row in rows.reverse do
    match row with
    | `(game_row| ║ $f:term ║ $s:term ║) =>
        funcs ← `(List.cons $f $funcs)
        statuses ← `(List.cons $s $statuses)
    | _ => Macro.throwError "unexpected row syntax"
  -- Return a tuple of the two lists
  `(($funcs, $statuses))





-- Helper macro for function syntax
syntax "fn" term : term
macro_rules | `(fn $name) => `($name)
#check fn Nat.add
-- Test functions
def testAdd (n m : Nat) : Nat := n + m
def testSub (n m : Nat) : Nat := n - m
def testMul (n m : Nat) : Nat := n * m
def testDiv (n m : Nat) : Nat := n / m

-- Example table that shows function names properly

def improvedTable :=
  ╔══════════════════╦════════╗
  ║ fn testAdd       ║   ✓    ║
  ║ fn testSub       ║   ✓✓   ║
  ║ fn testMul       ║   ..   ║
  ║ fn testDiv       ║   ✗    ║
  ╚══════════════════╩════════╝


#eval improvedTable.2

-- Enhanced table with proper function-status pairing
structure FunctionEntry where
  name : String
  status : Status
  deriving Repr

structure EnhancedTable where
  entries : List FunctionEntry
  deriving Repr

-- Helper functions for the enhanced table
namespace EnhancedTable

def addFunction (table : EnhancedTable) (name : String) (status : Status) : EnhancedTable :=
  { table with entries := table.entries ++ [⟨name, status⟩] }

def updateStatus (table : EnhancedTable) (name : String) (newStatus : Status) : EnhancedTable :=
  { table with entries := table.entries.map (fun entry =>
    if entry.name == name then ⟨name, newStatus⟩ else entry) }

def getFunctionNames (table : EnhancedTable) : List String :=
  table.entries.map (·.name)

def getByStatus (table : EnhancedTable) (targetStatus : Status) : List String :=
  table.entries.filterMap (fun entry =>
    if entry.status == targetStatus then some entry.name else none)

def display (table : EnhancedTable) : String :=
  let header := "╔══════════════════╦════════╗\n║ Function         ║ Status ║\n╠══════════════════╬════════╣\n"
  let footer := "╚══════════════════╩════════╝"
  let rows := table.entries.map (fun entry =>
    let statusSymbol := match entry.status with
      | Status.completed => "✓"
      | Status.documented => "✓✓"
      | Status.in_progress => ".."
      | Status.failed => "✗"
    let paddedName := entry.name ++ String.mk (List.replicate (16 - entry.name.length) ' ')
    s!"║ {paddedName} ║   {statusSymbol}    ║")
  header ++ String.intercalate "\n" rows ++ "\n" ++ footer

end EnhancedTable

-- Create comprehensive example following readme.md structure
def projectTable : EnhancedTable :=
  EnhancedTable.mk [
    ⟨"parseInput", Status.completed⟩,
    ⟨"validateInput", Status.documented⟩,
    ⟨"processData", Status.in_progress⟩,
    ⟨"generateOutput", Status.failed⟩
  ]

-- Test the enhanced functionality
#eval projectTable.getFunctionNames
#eval projectTable.getByStatus Status.completed
#eval projectTable.display

-- Helper to create table from list of (name, status) pairs
def createTableFromPairs (pairs : List (String × Status)) : EnhancedTable :=
  EnhancedTable.mk (pairs.map fun (name, status) => ⟨name, status⟩)
