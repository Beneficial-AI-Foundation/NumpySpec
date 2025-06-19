import FuncTracker

/-- Tests for FuncTracker 2D table syntax -/
namespace FuncTracker.Test

open FuncTracker

-- Test basic status symbols
#check Status.notStarted
#check Status.toSymbol Status.implemented = "✓"

-- Test creating a simple table
def testTable := funcTable!
  ╔════════════════════╗
  │ Function │ Status  │
  │ test1    │ ✗       │
  │ test2    │ ✓       │
  ╚════════════════════╝

-- Test table with all columns
def fullTable := funcTable!
  ╔══════════════════════════════════════════════════╗
  │ Function │ Status │ File     │ Lines │ Complexity │
  │ func1    │ ✓✓✓    │ Test.lean│ 1-10  │ Low        │
  │ func2    │ ✓✓     │ Test.lean│ 15-25 │ Medium     │
  │ func3    │ ✓      │ Test.lean│ 30-40 │ High       │
  │ func4    │ ⋯      │ -        │ -     │ -          │
  │ func5    │ ✗      │ -        │ -     │ -          │
  ╚══════════════════════════════════════════════════╝

-- Test progress computation
example : fullTable.computeProgress.total = 5 := by rfl
example : fullTable.computeProgress.documented = 1 := by rfl
example : fullTable.computeProgress.tested = 1 := by rfl
example : fullTable.computeProgress.implemented = 1 := by rfl
example : fullTable.computeProgress.inProgress = 1 := by rfl
example : fullTable.computeProgress.notStarted = 1 := by rfl

-- Test that we can access individual functions
example : fullTable.functions[0]!.name = "func1" := by rfl
example : fullTable.functions[0]!.status = Status.documented := by rfl
example : fullTable.functions[0]!.file = some "Test.lean" := by rfl
example : fullTable.functions[0]!.lines = some (1, 10) := by rfl

-- Test progress percentage calculation
#eval fullTable.computeProgress.percentComplete -- Should be 60.0

-- Test compile-time validation (commented out as it would fail)
-- require all implemented fullTable

-- Test HTML generation
#eval IO.FS.writeFile "test_report.html" fullTable.toHTML

end FuncTracker.Test