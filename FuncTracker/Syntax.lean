import Lean
import FuncTracker.Basic

namespace FuncTracker

open Lean Parser

-- Syntax categories for 2D table representation
declare_syntax_cat func_table
declare_syntax_cat table_row  
declare_syntax_cat table_cell

-- Basic cell types
syntax ident : table_cell
syntax str : table_cell
syntax "✗" : table_cell     -- not started
syntax "⋯" : table_cell     -- in progress  
syntax "✓" : table_cell     -- implemented
syntax "✓✓" : table_cell    -- tested
syntax "✓✓✓" : table_cell   -- documented
syntax num "-" num : table_cell  -- line range like "10-20"
syntax "-" : table_cell     -- empty cell

-- Row definition - using │ as cell separator
syntax:max "│" table_cell ("│" table_cell)* "│" : table_row

-- Table structure with top/bottom borders
syntax:max "╔" "═"* "╗" table_row* "╚" "═"* "╝" : term

-- Macro for creating function tables
syntax "funcTable!" "╔" "═"* "╗" table_row* "╚" "═"* "╝" : term

end FuncTracker