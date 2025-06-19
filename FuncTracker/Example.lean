import FuncTracker

/-- Example: Tracking implementation status of Gaussian elimination functions -/

namespace Example

open FuncTracker

-- Define a function tracking table using 2D syntax
def gaussianFunctions := funcTable!
  ╔═══════════════════════════════════════════════════════════════════╗
  │ Function          │ Status │ File              │ Lines  │ Complexity │
  │ pivotRow          │ ✓      │ GaussianElim.lean │ 10-25  │ Low        │
  │ swapRows          │ ✓✓     │ GaussianElim.lean │ 30-40  │ Low        │
  │ scaleRow          │ ✓✓✓    │ GaussianElim.lean │ 45-55  │ Low        │
  │ eliminateColumn   │ ⋯      │ GaussianElim.lean │ 60-85  │ Medium     │
  │ backSubstitute    │ ✗      │ -                 │ -      │ High       │
  │ gaussianElim      │ ✗      │ -                 │ -      │ High       │
  │ computeInverse    │ ✗      │ -                 │ -      │ Very High  │
  ╚═══════════════════════════════════════════════════════════════════╝

-- You can also use the track functions command
track functions myProjectFuncs :
  ╔════════════════════════════════════════════╗
  │ Function   │ Status │ File      │ Lines     │
  │ parse      │ ✓✓     │ Parse.lean│ 100-150   │
  │ typecheck  │ ✓      │ Check.lean│ 200-300   │
  │ optimize   │ ⋯      │ Opt.lean  │ 50-75     │
  │ codegen    │ ✗      │ -         │ -         │
  ╚════════════════════════════════════════════╝

-- Example without header separator (auto-detects header)
def simpleFunctions := funcTable!
  ╔══════════════════════╗
  │ Function │ Status    │
  │ foo      │ ✓         │
  │ bar      │ ⋯         │
  │ baz      │ ✗         │
  ╚══════════════════════╝

-- Compute and display progress
#eval gaussianFunctions.computeProgress.pretty

-- Generate markdown report
#eval IO.println gaussianFunctions.toMarkdown

-- Check specific function status
#eval gaussianFunctions.functions.find? (·.name = "backSubstitute")

-- Count unimplemented functions
#eval gaussianFunctions.functions.filter (·.status = .notStarted) |>.size

end Example