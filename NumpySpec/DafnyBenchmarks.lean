import Std.Do.Triple
import Std.Tactic.Do

-- Import all ported benchmark modules (100+ specifications)
-- Phase 1: Initial 50 specifications
import NumpySpec.DafnyBenchmarks.Abs
import NumpySpec.DafnyBenchmarks.AllDigits
import NumpySpec.DafnyBenchmarks.ArrayAppend
import NumpySpec.DafnyBenchmarks.ArrayConcat
import NumpySpec.DafnyBenchmarks.ArrayCopy
import NumpySpec.DafnyBenchmarks.ArrayProduct
import NumpySpec.DafnyBenchmarks.ArraySum
import NumpySpec.DafnyBenchmarks.Avg
import NumpySpec.DafnyBenchmarks.BelowZero
import NumpySpec.DafnyBenchmarks.BinarySearch
import NumpySpec.DafnyBenchmarks.BubbleSort
import NumpySpec.DafnyBenchmarks.CalDiv
import NumpySpec.DafnyBenchmarks.CalSum
import NumpySpec.DafnyBenchmarks.CanyonSearch
import NumpySpec.DafnyBenchmarks.Compare
import NumpySpec.DafnyBenchmarks.ConvertMapKey
import NumpySpec.DafnyBenchmarks.CopyPart
import NumpySpec.DafnyBenchmarks.CountLessThan
import NumpySpec.DafnyBenchmarks.DoubleArrayElements
import NumpySpec.DafnyBenchmarks.DoubleQuadruple
import NumpySpec.DafnyBenchmarks.EvenList
import NumpySpec.DafnyBenchmarks.Find
import NumpySpec.DafnyBenchmarks.HasCloseElements
import NumpySpec.DafnyBenchmarks.Insert
import NumpySpec.DafnyBenchmarks.IntegerSquareRoot
import NumpySpec.DafnyBenchmarks.IsEven
import NumpySpec.DafnyBenchmarks.IsPalindrome
import NumpySpec.DafnyBenchmarks.LinearSearch1
import NumpySpec.DafnyBenchmarks.LinearSearch2
import NumpySpec.DafnyBenchmarks.LinearSearch3
import NumpySpec.DafnyBenchmarks.LongestPrefix
import NumpySpec.DafnyBenchmarks.Match
import NumpySpec.DafnyBenchmarks.MaxArray
import NumpySpec.DafnyBenchmarks.MinArray
import NumpySpec.DafnyBenchmarks.MinOfTwo
import NumpySpec.DafnyBenchmarks.Modify2DArray
import NumpySpec.DafnyBenchmarks.MultiReturn
import NumpySpec.DafnyBenchmarks.OnlineMax
import NumpySpec.DafnyBenchmarks.OnlyOnce
import NumpySpec.DafnyBenchmarks.Quotient
import NumpySpec.DafnyBenchmarks.RemoveFront
import NumpySpec.DafnyBenchmarks.Replace
import NumpySpec.DafnyBenchmarks.ReturnSeven
import NumpySpec.DafnyBenchmarks.Reverse
import NumpySpec.DafnyBenchmarks.Rotate
import NumpySpec.DafnyBenchmarks.SelectionSort
import NumpySpec.DafnyBenchmarks.SeqToArray
import NumpySpec.DafnyBenchmarks.SetToSeq
import NumpySpec.DafnyBenchmarks.SlopeSearch
import NumpySpec.DafnyBenchmarks.SwapArithmetic

-- Phase 2: Extended specifications (51-60)
import NumpySpec.DafnyBenchmarks.SwapArithReconstructed
import NumpySpec.DafnyBenchmarks.SwapBitvector
import NumpySpec.DafnyBenchmarks.SwapGeneral
import NumpySpec.DafnyBenchmarks.SwapInArray
import NumpySpec.DafnyBenchmarks.SwapSimultaneous
import NumpySpec.DafnyBenchmarks.TestArray
import NumpySpec.DafnyBenchmarks.Triple
import NumpySpec.DafnyBenchmarks.Triple2
import NumpySpec.DafnyBenchmarks.Triple3
import NumpySpec.DafnyBenchmarks.Triple4
import NumpySpec.DafnyBenchmarks.TwoSum

-- Phase 3: Next 50 specifications (61-110)
-- Batch 1 (61-70)
import NumpySpec.DafnyBenchmarks.UpdateArray
import NumpySpec.DafnyBenchmarks.UpdateMap
-- import NumpySpec.DafnyBenchmarks.BinarySearch  -- Already imported
import NumpySpec.DafnyBenchmarks.DPGradientDescent
import NumpySpec.DafnyBenchmarks.Gaussian
import NumpySpec.DafnyBenchmarks.SearchAddends
import NumpySpec.DafnyBenchmarks.MergeSort
import NumpySpec.DafnyBenchmarks.BinarySearchTree
import NumpySpec.DafnyBenchmarks.CMSC433Assignment
import NumpySpec.DafnyBenchmarks.PowerFunction

-- Batch 2 (71-80)
import NumpySpec.DafnyBenchmarks.FindMinimum3
import NumpySpec.DafnyBenchmarks.SimpleAssignment
import NumpySpec.DafnyBenchmarks.AddOne
import NumpySpec.DafnyBenchmarks.MultiplyAndAdd
-- import NumpySpec.DafnyBenchmarks.BubbleSort  -- Already imported
import NumpySpec.DafnyBenchmarks.StringOperations
import NumpySpec.DafnyBenchmarks.CumulativeSum
import NumpySpec.DafnyBenchmarks.ListFromArray
import NumpySpec.DafnyBenchmarks.Factorial
import NumpySpec.DafnyBenchmarks.HoareExamples

-- Batch 3 (81-90)
import NumpySpec.DafnyBenchmarks.PrefixSum
import NumpySpec.DafnyBenchmarks.SearchSort
import NumpySpec.DafnyBenchmarks.ContainerRanks
import NumpySpec.DafnyBenchmarks.SeqFromArray
import NumpySpec.DafnyBenchmarks.BinarySearch2
import NumpySpec.DafnyBenchmarks.Fibonacci
import NumpySpec.DafnyBenchmarks.Find2
import NumpySpec.DafnyBenchmarks.TwoSum2
import NumpySpec.DafnyBenchmarks.LongestPalindrome
import NumpySpec.DafnyBenchmarks.TwoSum3

-- Batch 4 (91-100)
import NumpySpec.DafnyBenchmarks.RemoveElement
import NumpySpec.DafnyBenchmarks.ClimbingStairs
import NumpySpec.DafnyBenchmarks.FindTheCelebrity
import NumpySpec.DafnyBenchmarks.Shuffle
-- import NumpySpec.DafnyBenchmarks.Factorial  -- Already imported
-- import NumpySpec.DafnyBenchmarks.Fibonacci  -- Already imported
import NumpySpec.DafnyBenchmarks.ExpressionOptimization
import NumpySpec.DafnyBenchmarks.FindZero
import NumpySpec.DafnyBenchmarks.Max
import NumpySpec.DafnyBenchmarks.LinearSearch

-- Batch 5 (101-110)
import NumpySpec.DafnyBenchmarks.BinarySearchDec
import NumpySpec.DafnyBenchmarks.InsertionSortMultiset
import NumpySpec.DafnyBenchmarks.SelectionSortMultiset
import NumpySpec.DafnyBenchmarks.QuickSelect
import NumpySpec.DafnyBenchmarks.SimpleSpecs
import NumpySpec.DafnyBenchmarks.InsertionSortSeq
import NumpySpec.DafnyBenchmarks.Search1000
import NumpySpec.DafnyBenchmarks.SumIntsLoop
import NumpySpec.DafnyBenchmarks.ListReverse
import NumpySpec.DafnyBenchmarks.DutchFlag

/-- DafnyBenchmarks: A collection of Dafny benchmark specifications ported to Lean 4
    
    This module contains specifications from the vericoding Dafny benchmarks,
    following the same Hoare triple style as the NumpySpec modules.
    
    Each specification includes:
    - Method signature with types
    - Preconditions (requires clauses in Dafny)
    - Postconditions (ensures clauses in Dafny)
    - Lean 4 proofs (where applicable)
-/

/-- The DafnyBenchmarks namespace contains all ported specifications -/
namespace NumpySpec.DafnyBenchmarks

/-!
This module serves as an index for all the Dafny benchmark specifications
that have been ported to Lean 4. The specifications are organized into
categories based on their functionality:

## Basic Operations
- Abs: Absolute value
- Avg: Average of two integers
- MinOfTwo: Minimum of two integers
- DoubleQuadruple: Double and quadruple operations
- ReturnSeven: Constant function
- IsEven: Parity checking

## Array Operations
- ArrayAppend: Append element to array
- ArrayConcat: Concatenate arrays
- ArrayCopy: Copy array
- ArrayProduct: Element-wise product
- ArraySum: Element-wise sum
- RemoveFront: Remove first element
- Reverse: Reverse array
- Rotate: Rotate array elements

## Array Algorithms
- BinarySearch: Binary search in sorted array
- LinearSearch1/2/3: Various linear search implementations
- Find: Find element index
- MaxArray: Find maximum element
- MinArray: Find minimum element
- OnlyOnce: Check unique occurrence
- CountLessThan: Count elements below threshold

## Sorting Algorithms
- BubbleSort: Bubble sort implementation
- SelectionSort: Selection sort implementation

## String Operations
- AllDigits: Check if all characters are digits
- IsPalindrome: Check palindrome
- LongestPrefix: Find longest common prefix
- Match: Pattern matching with wildcards

## Mathematical Operations
- CalDiv: Integer division example
- CalSum: Sum formula calculation
- IntegerSquareRoot: Integer square root
- Quotient: Division with remainder

## Advanced Operations
- BelowZero: Running balance checker
- CanyonSearch: Minimum difference in sorted arrays
- ConvertMapKey: Map key transformation
- HasCloseElements: Proximity detection
- SlopeSearch: 2D sorted array search
- MultiReturn: Multiple return values
- SwapArithmetic: Value swapping

## Data Structure Conversions
- SeqToArray: List to array conversion
- SetToSeq: Set to list conversion

## Array Modifications
- CopyPart: Partial array copy
- DoubleArrayElements: Double all elements
- EvenList: Filter even numbers
- Insert: Insert with shifting
- Modify2DArray: 2D array modification
- OnlineMax: Find first exceeding maximum
- Replace: Replace elements above threshold

Each specification follows the Hoare triple style with preconditions
and postconditions clearly specified.
-/

end NumpySpec.DafnyBenchmarks