# DafnyBenchmarks: Porting Dafny Specifications to Lean 4

## Overview

This directory contains Lean 4 ports of Dafny benchmark specifications from the vericoding repository. The goal is to translate Dafny method specifications (preconditions and postconditions) into Lean 4 using Hoare triple notation.

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

**Batch 4 is ready to be pushed as PR #16**

### Build Commands

```bash
# Build all DafnyBenchmarks
lake build NumpySpec.DafnyBenchmarks

# Build specific specification
lake build NumpySpec.DafnyBenchmarks.SpecName

# Test new additions
lake build $(ls NumpySpec/DafnyBenchmarks/NewSpec*.lean | sed 's|/|.|g' | sed 's|\.lean||')
```