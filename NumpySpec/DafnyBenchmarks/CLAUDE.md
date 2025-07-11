# DafnyBenchmarks: Porting Dafny Specifications to Lean 4

## Overview

This directory contains Lean 4 ports of Dafny benchmark specifications from the vericoding repository. The goal is to translate Dafny method specifications (preconditions and postconditions) into Lean 4 using Hoare triple notation.

## IMPORTANT: "Keep Going" Instructions

**If you see "keep going" with no context:**
1. You are continuing the Dafny specification porting project
2. Current status: Completed batches 1-5 (90 new specs total)
3. Next action: Port Batch 6 - the 20 tasks listed in the "CRITICAL: Next Batch to Port" section below
4. Follow the "Complete Workflow" section step-by-step
5. Focus on numeric-only tasks (Int, Nat, Float) - SKIP all string operations
6. All implementations should be `sorry` - we only need type signatures and specifications

## Source

The original Dafny specifications come from:
- Repository: https://github.com/Beneficial-AI-Foundation/vericoding
- Path: `/dafny/benchmarks/dafny-bench_specs/atomizer_supported/`

## Porting Methodology

### 1. Specification Style

Each Dafny specification is ported using the Hoare triple style from `Std.Do.Triple`:

```lean
theorem spec_name {params} :
    ⦃⌜precondition⌝⦄
    function_call
    ⦃⇓result => ⌜postcondition⌝⦄ := by
  sorry  -- proof left for future work
```

### 2. Type Mappings

| Dafny Type | Lean 4 Type | Notes |
|------------|-------------|-------|
| `int` | `Int` | Unbounded integers |
| `nat` | `Nat` | Natural numbers |
| `array<T>` | `Array T` | Mutable arrays |
| `seq<T>` | `List T` | Immutable sequences |
| `set<T>` | `Std.HashSet T` | Sets (or List with uniqueness) |
| `map<K,V>` | `Std.HashMap K V` | Key-value maps |
| `bool` | `Bool` | Booleans |
| `char` | `Char` | Characters |
| `string` | `String` | Strings |

### 3. Naming Conventions

- Dafny file: `Clover_function_name_spec.dfy`
- Lean file: `FunctionName.lean`
- Module name: `NumpySpec.DafnyBenchmarks.FunctionName`

### 4. Common Patterns

#### Array Indexing
```lean
-- Dafny: a[i]
-- Lean: a[i.val]'(by sorry)  -- with bounds proof obligation
```

#### Multiset Equality
```lean
-- Helper function to count occurrences
def countOccurrences (a : Array α) (x : α) [DecidableEq α] : Nat :=
  a.foldl (fun acc y => if y = x then acc + 1 else acc) 0
```

#### Existential Quantification
```lean
-- Dafny: exists i :: 0 <= i < a.Length && a[i] == x
-- Lean: ∃ i : Fin a.size, a[i.val] = x
```

#### Array Construction
```lean
-- Creating new arrays with specific properties
Array.ofFn (fun i : Fin n => computation)
```

## Categories of Specifications

### Basic Operations (10 specs)
- Arithmetic: Abs, Avg, MinOfTwo, DoubleQuadruple
- Constants: ReturnSeven
- Predicates: IsEven

### Array Operations (15 specs)
- Transformations: ArrayAppend, ArrayConcat, ArrayCopy, RemoveFront, Reverse, Rotate
- Element-wise: ArrayProduct, ArraySum, DoubleArrayElements, Replace
- Filtering: EvenList
- Modifications: CopyPart, Insert, Modify2DArray

### Search & Sort (10 specs)
- Search: BinarySearch, Find, LinearSearch1/2/3, OnlineMax
- Sort: BubbleSort, SelectionSort
- Analysis: MaxArray, MinArray, OnlyOnce, CountLessThan

### String & Pattern (5 specs)
- Validation: AllDigits, IsPalindrome
- Matching: Match, LongestPrefix

### Mathematical (5 specs)
- Arithmetic: CalDiv, CalSum, Quotient
- Advanced: IntegerSquareRoot

### Advanced Algorithms (5 specs)
- BelowZero, CanyonSearch, ConvertMapKey, HasCloseElements, SlopeSearch
- MultiReturn, SwapArithmetic, SeqToArray, SetToSeq

## Implementation Notes

1. **Specifications Only**: These files contain only specifications (function signatures and theorem statements), not implementations. All function bodies are minimal placeholders that type-check, and all proofs are `sorry`. This follows the approach where specifications come first, and implementations can be filled in later.

2. **Proof Obligations**: All proofs are currently marked as `sorry`. Future work includes:
   - Proving termination for recursive functions
   - Verifying array bounds
   - Establishing functional correctness

3. **Monadic Context**: Most functions use the `Id` monad for pure computations. Some use `StateM` for array modifications.

4. **Error Handling**: Where Dafny uses `-1` for "not found", Lean versions typically use `Option` or explicit sentinel values.

5. **Generic Functions**: Lean versions often add typeclass constraints like `[DecidableEq α]` or `[Inhabited α]` where needed.

## Complete Workflow for Continuing Task Porting

### Step 1: Setup New Batch
```bash
# Create new jj change for next batch
jj new -m "feat: Port 20 more numeric-only Dafny synthesis tasks (batch N)"

# Check current status
jj status
```

### Step 2: Find Next Tasks to Port
1. Check [@REMAINING_TASKS.md](./REMAINING_TASKS.md) for next 20 tasks
2. Source Dafny files are in: `/Users/alokbeniwal/vericoding/dafny/benchmarks/dafny-bench_specs/synthesis_task/`
3. File pattern: `dafny-synthesis_task_id_XXX_spec.dfy`

### Step 3: Port Each Task
For each task, create a Lean file following this template:

```lean
-- Synthesis Task XXX: Brief description

namespace NumpySpec.DafnyBenchmarks.SynthesisTaskXXX

/-- Function description -/
def functionName (params : Types) : ReturnType :=
  sorry

/-- Specification: What the function does -/
theorem functionName_spec (params : Types) (preconditions) :
    functionName params = expected_result :=
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisTaskXXX
```

### Step 4: Common Fixes for Build Errors

1. **Float.pi Error**: Use numeric constant `3.14159265358979323846`
2. **String Indexing**: Avoid `String.Pos`, simplify specs or use `String.toList`
3. **Array Indexing**: Use `array[i]!` with `i : Nat` and bounds condition
4. **Fin Type Issues**: Change `∀ i : Fin n` to `∀ i : Nat, i < n →`
5. **List.toMultiset**: Not available, use custom implementations

### Step 5: Test Build
```bash
# Test individual file
lake build NumpySpec.DafnyBenchmarks.SynthesisTaskXXX

# Test all new files at once
lake build NumpySpec.DafnyBenchmarks.SynthesisTask{XXX,YYY,ZZZ,...}
```

### Step 6: Copy to Vericoding
```bash
# Copy all new files
for f in SynthesisTaskXXX SynthesisTaskYYY ...; do
  cp NumpySpec/DafnyBenchmarks/$f.lean /Users/alokbeniwal/vericoding/lean4/benchmarks/dafny-bench_specs/
done
```

### Step 7: Create PR
```bash
# Create bookmark
jj bookmark create dafnybench-batchN

# Push to GitHub
jj git push --bookmark dafnybench-batchN --allow-new

# Create PR
gh pr create --base main --head dafnybench-batchN \
  --title "feat: Port 20 more numeric-only Dafny synthesis tasks (batch N)" \
  --body "See PR description template below"
```

### PR Description Template
```
## Summary
Continue porting Dafny synthesis tasks, focusing exclusively on numeric types (Int, Nat, Float).

## Changes
- Add 20 numeric-only synthesis task specifications
- Tasks include: [list main categories]
- All implementations use `sorry` placeholders (type signatures only)

## Test plan
- [x] Run `lake build` to verify all files compile
- [x] Check that all 20 files build without errors
- [x] Verify no string types used (Int, Nat, Float only)

This continues the work from PR #XXX (batch N-1).

🤖 Generated with [Claude Code](https://claude.ai/code)
```

## Current Porting Status (as of context window limit)

### Stacked PR Approach
Using jj (Jujutsu) for managing stacked PRs on GitHub:

1. **PR #10** - Initial batch (110+ specifications)
   - Base PR with comprehensive porting of Dafny benchmarks
   - Fixed compilation issues, added Multiset stub

2. **PR #14** - Batch 2: 20 Dafny-Exercises 
   - Stacked on PR #10
   - Focus on exercise specifications
   - All implementations removed (type signatures only)
   - Fixed Multiset membership instance

3. **PR #15** - Batch 3: 20 Synthesis Tasks
   - Stacked on PR #14
   - Simple mathematical and algorithmic tasks
   - Simplified complex string specifications
   - Total reached: 50 new specifications

### Summary of New Specifications (Batches 2-4)

**Batch 2 - Dafny-Exercises (20 specs):**
- ExerciseCountMin, ExercisePeekSum, ExerciseBubbleSort
- ExerciseReplace, ExerciseSelSort, ExerciseSeparate
- ExerciseInsertionSort, ExerciseSeqMaxSum, ExerciseBarrier
- ExerciseFindMax, ExerciseExp, ExerciseSumElems
- ExerciseCountEven, ExerciseFirstZero, ExerciseFirstNegative
- ExerciseContained, ExerciseMaximum, ExercisePositive
- ExerciseAllEqual, ExerciseSquareRoot

**Batch 3 - Synthesis Tasks (20 specs):**
- Basic math: SquarePerimeter, IsDivisibleBy11, SphereSurfaceArea
- Array operations: SumOfNegatives, MaxDifference, KthElement
- String operations: RemoveChars, IsInteger
- Advanced: SharedElements, IsNonPrime, CountIdenticalPositions
- And 10 more mathematical/algorithmic tasks

**Batch 4 - More Synthesis Tasks (20 specs):**
- Array algorithms: SynthesisTask622 (median), SynthesisTask445 (element-wise mult)
- Math operations: SynthesisTask623 (power), SynthesisTask600 (isEven)
- String processing: SynthesisTask741 (allCharsSame), SynthesisTask424 (extract rear)
- Geometry: SynthesisTask458 (rectangle area), SynthesisTask581 (pyramid surface)
- And 12 more tasks covering various algorithms and computations

**Batch 5 - Numeric-Only Tasks (20 specs):**
- Arithmetic: SynthesisTask77 (divisible by 11), SynthesisTask406 (is odd)
- Geometry: SynthesisTask85 (sphere area), SynthesisTask82 (sphere volume)
- Number sequences: SynthesisTask135 (hexagonal), SynthesisTask59 (octagonal)
- Conversions: SynthesisTask606 (deg to rad), SynthesisTask264 (dog years)
- And 12 more numeric computations (no strings)

### Key Decisions Made

1. **No Implementations**: All functions use `sorry` for implementations
2. **Simplified Specifications**: Complex string/array access simplified where needed
3. **No Mathlib**: Custom Multiset stub to avoid dependencies
4. **Consistent Style**: All use Hoare triple notation
5. **Incremental Approach**: Small batches for easier review

### Next Steps (for continuation)

When continuing with more specifications:
1. Create new jj change
2. Port next batch of 20-30 specs
3. Focus on remaining synthesis tasks or other categories
4. Maintain same style and approach
5. Create stacked PR on top of PR #16

**Status Update**:
- Batch 4: PR #112 (completed) - 20 synthesis tasks
- Batch 5: PR #113 (completed) - 20 numeric-only tasks (Int, Nat, Float)

**Remaining Tasks**: See [@REMAINING_TASKS.md](./REMAINING_TASKS.md) for a comprehensive checklist of ~40 remaining numeric-only synthesis tasks to port.

## CRITICAL: Next Batch to Port (Batch 6)

**When you see "keep going", port these 20 tasks next:**

1. Task 616 - ElementWiseModulo
2. Task 470 - PairwiseAddition
3. Task 578 - Interleave
4. Task 240 - ReplaceLastElement
5. Task 572 - RemoveDuplicates
6. Task 586 - SplitAndAppend
7. Task 587 - ArrayToSeq
8. Task 460 - GetFirstElements
9. Task 610 - RemoveElement
10. Task 632 - MoveZeroesToEnd
11. Task 644 - Reverse
12. Task 625 - SwapFirstAndLast
13. Task 591 - SwapFirstAndLast (variant)
14. Task 307 - DeepCopySeq
15. Task 273 - SubtractSequences
16. Task 750 - AddTupleToList
17. Task 401 - IndexWiseAddition
18. Task 70 - AllSequencesEqualLength
19. Task 769 - Difference
20. Task 399 - BitwiseXOR

## Code Pattern Examples for Common Cases

### Array Operations Pattern
```lean
-- For element-wise operations
def elementWiseOp (a b : Array Int) : Array Int :=
  sorry

theorem elementWiseOp_spec (a b : Array Int) (h : a.size = b.size) :
    let result := elementWiseOp a b
    result.size = a.size ∧
    ∀ i : Nat, i < result.size → result[i]! = a[i]! op b[i]! :=
  sorry
```

### Sequence Manipulation Pattern
```lean
-- For operations that transform sequences
def transformSeq (s : List Int) : List Int :=
  sorry

theorem transformSeq_spec (s : List Int) :
    (transformSeq s).length = s.length ∧
    ∀ i : Nat, i < s.length → (transformSeq s)[i]! = transform s[i]! :=
  sorry
```

### Mathematical Check Pattern
```lean
-- For predicates
def checkProperty (n : Nat) : Bool :=
  sorry

theorem checkProperty_spec (n : Nat) :
    checkProperty n = (mathematical_property n) :=
  sorry
```

### Build Commands

```bash
# Build all DafnyBenchmarks
lake build NumpySpec.DafnyBenchmarks

# Build specific specification
lake build NumpySpec.DafnyBenchmarks.SpecName

# Test new additions
lake build $(ls NumpySpec/DafnyBenchmarks/NewSpec*.lean | sed 's|/|.|g' | sed 's|\.lean||')
```

## Quick Reference Card

### Essential Paths
- **Dafny source**: `/Users/alokbeniwal/vericoding/dafny/benchmarks/dafny-bench_specs/synthesis_task/`
- **Lean target**: `/Users/alokbeniwal/NumpySpec/NumpySpec/DafnyBenchmarks/`
- **Copy destination**: `/Users/alokbeniwal/vericoding/lean4/benchmarks/dafny-bench_specs/`

### File Naming
- **Dafny**: `dafny-synthesis_task_id_XXX_spec.dfy`
- **Lean**: `SynthesisTaskXXX.lean`
- **Namespace**: `NumpySpec.DafnyBenchmarks.SynthesisTaskXXX`

### Most Common Type Mappings
- `int` → `Int`
- `nat` → `Nat` 
- `real` → `Float`
- `array<T>` → `Array T`
- `seq<T>` → `List T`

### Quick Commands
```bash
# Start new batch
jj new -m "feat: Port 20 more numeric-only Dafny synthesis tasks (batch 6)"

# Read Dafny file
cat /Users/alokbeniwal/vericoding/dafny/benchmarks/dafny-bench_specs/synthesis_task/dafny-synthesis_task_id_XXX_spec.dfy

# Create Lean file
Write NumpySpec/DafnyBenchmarks/SynthesisTaskXXX.lean

# Test build
lake build NumpySpec.DafnyBenchmarks.SynthesisTaskXXX

# Copy to vericoding
cp NumpySpec/DafnyBenchmarks/SynthesisTaskXXX.lean /Users/alokbeniwal/vericoding/lean4/benchmarks/dafny-bench_specs/

# Push PR
jj bookmark create dafnybench-batch6
jj git push --bookmark dafnybench-batch6 --allow-new
gh pr create --base main --head dafnybench-batch6 --title "feat: Port 20 more numeric-only Dafny synthesis tasks (batch 6)"
```

### Remember
- NO string operations - numeric only
- All functions use `sorry`
- Fix `Float.pi` → `3.14159265358979323846`
- Array indexing: use `[i]!` with `i : Nat`
- Simplify complex specs if needed