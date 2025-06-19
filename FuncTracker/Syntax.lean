import Lean
import FuncTracker.Basic

namespace FuncTracker

open Lean Parser

/-! Syntax categories for 2D table representation -/

/-- Table definition -/
declare_syntax_cat func_table
/-- Row definition -/
declare_syntax_cat table_row
/-- Cell definition -/
declare_syntax_cat table_cell

/-- Basic cell types -/
syntax ident : table_cell
/-- String cell -/
syntax str : table_cell
/-- Not started -/
syntax "✗" : table_cell
/-- In progress -/
syntax "⋯" : table_cell
/-- Implemented -/
syntax "✓" : table_cell
/-- Tested -/
syntax "✓✓" : table_cell
/-- Documented -/
syntax "✓✓✓" : table_cell
/-- line range like "10-20" -/
syntax num "-" num : table_cell
/-- empty cell -/
syntax "-" : table_cell

/-- Row definition - using │ as cell separator -/
syntax:max "│" table_cell ("│" table_cell)* "│" : table_row

end FuncTracker
