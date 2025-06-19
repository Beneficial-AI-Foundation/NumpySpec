import FuncTracker.BasicV2
import FuncTracker.GridParserV2
import FuncTracker.SimpleValidation

/-!
# FuncTracker

A Lean 4 library for tracking function implementation progress using table syntax.

## Core Components

- `BasicV2`: Core data structures (Status, TrackedFunction, FunctionTable)
- `GridParserV2`: Parser for ASCII table format with borders
- `SimpleValidation`: Validated elaborator that checks function names exist

## Usage

```lean
-- Create a function tracking table with validation
def myProgress := funcTable! "╔═══════════════════════════╗
│ Function    │ Status │ File │
╠═══════════════════════════╣
│ List.map    │ ✓✓✓    │ -    │
│ Array.map   │ ✓✓     │ -    │
│ Option.map  │ ✓      │ -    │
╚═══════════════════════════╝"

-- Check progress
#eval myProgress.computeProgress.percentComplete
```

## Status Symbols

- `✗` - Not started
- `⋯` - In progress  
- `✓` - Implemented
- `✓✓` - Tested
- `✓✓✓` - Documented

The `funcTable!` syntax validates that all function names exist in the current environment.
-/

namespace FuncTracker

-- Re-export all main types and functions
open BasicV2 (Status TrackedFunction FunctionTable Progress)
open GridParserV2 (Grid GridCell)
open SimpleValidation (elabFuncTableValidated)

end FuncTracker