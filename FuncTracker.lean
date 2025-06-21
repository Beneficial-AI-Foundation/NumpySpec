import FuncTracker.BasicV2
import FuncTracker.GridParserV2
import FuncTracker.GridParserV3
import FuncTracker.SimpleValidation
import FuncTracker.RegionPredicates
import FuncTracker.VersoIntegration
-- Phase 1: Native 2D Table Syntax
import FuncTracker.TwoDSyntax
import FuncTracker.BoxDrawing
import FuncTracker.SpatialParser
import FuncTracker.Native2D

/-!
# FuncTracker

A Lean 4 library for tracking function implementation progress using table syntax.

## Core Components

- `BasicV2`: Core data structures (Status, TrackedFunction, FunctionTable) with enhanced cross-reference support
- `GridParserV2`: Parser for ASCII table format with borders
- `GridParserV3`: Enhanced parser with Racket 2D-inspired cell spanning and spatial constraints
- `SimpleValidation`: Validated elaborator that checks function names exist
- `RegionPredicates`: Compositional predicate checking for table regions
- `VersoIntegration`: Cross-reference database and documentation linking system

### Phase 1: Native 2D Table Syntax (NEW)

- `TwoDSyntax`: Core 2D parsing infrastructure with spatial positioning
- `BoxDrawing`: Unicode box-drawing character support and validation
- `SpatialParser`: 2D layout parsing engine for table structure recognition
- `Native2D`: `funcTable2d` macro implementation for native 2D syntax

## Usage

```lean
-- Create a function tracking table with validation
def myProgress := funcTable! "╔═══════════════════════════════════════════════════════════════╗
│ Name                 │ Status │ File       │ Lines     │ Complexity │
╠═══════════════════════════════════════════════════════════════╣
│ List.map             │ ✓✓✓    │ List.lean  │ 100-120   │ O(n)       │
│ Array.map            │ ✓✓     │ Array.lean │ 50-80     │ -          │
│ Option.map           │ ✓      │ -          │ -         │ -          │
│ Nat.add              │ ✗      │ -          │ -         │ -          │
╚═══════════════════════════════════════════════════════════════╝"

-- Check progress
#eval myProgress.computeProgress.percentComplete

-- Validate with predicates
let region := myProgress.wholeRegion.get!
let predicate := (statusAtLeast .implemented).and testedHasComplexity
validateTableRegion myProgress predicate region

-- Custom validation predicates
def implementedHasFile : RegionPredicate :=
  cellPredicate fun func pos =>
    if func.status ≥ .implemented then
      match func.file with
      | some _ => .success
      | none => .failure s!"Function {func.name} is implemented but missing file info" (some pos)
    else
      .success

-- Comprehensive validation combining multiple predicates
def comprehensiveValidation : RegionPredicate :=
  (statusAtLeast .notStarted).and
  (testedHasComplexity.and implementedHasFile)

-- NEW: Native 2D table syntax (Phase 1)
-- Simple table for testing the new syntax
def simpleProgress := simpleTable2d "╔══════════════╦═══════════╦═════════════╗
║ Function     ║ Status    ║ File        ║
╠══════════════╬═══════════╬═════════════╣
║ List.map     ║ ✓✓✓       ║ List.lean   ║
║ Array.map    ║ ✓✓        ║ Array.lean  ║
║ Option.map   ║ ✓         ║ -           ║
╚══════════════╩═══════════╩═════════════╝"

#eval simpleProgress.computeProgress.percentComplete
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

-- Re-export all main types and functions from the FuncTracker namespace
-- Since all modules are already in FuncTracker namespace, main types are already available

end FuncTracker
