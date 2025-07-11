# Remaining Dafny Benchmarks to Port

## Summary
- **Already Ported**: ~190 specifications across 5 batches
- **Remaining**: 40+ numeric-only synthesis tasks (avoiding string operations)

## Already Ported Synthesis Tasks
Tasks completed in batches 3-5: 3, 14, 17, 58, 59, 61, 77, 82, 85, 89, 106, 135, 139, 170, 171, 227, 257, 262, 264, 268, 279, 406, 424, 432, 435, 445, 452, 458, 565, 574, 581, 600, 606, 622, 623, 741, 762, 775, 790

## High Priority: Numeric-Only Tasks

### Basic Numeric Operations
- [ ] Task 616 - ElementWiseModulo: element-wise modulo operation on arrays
- [ ] Task 470 - PairwiseAddition: add consecutive pairs in array
- [ ] Task 273 - SubtractSequences: element-wise subtraction
- [ ] Task 566 - SumOfDigits: sum of digits of a number

### Array/Sequence Manipulation
- [ ] Task 578 - Interleave: interleave three sequences
- [ ] Task 240 - ReplaceLastElement: replace last element with another sequence
- [ ] Task 572 - RemoveDuplicates: remove duplicates from array
- [ ] Task 586 - SplitAndAppend: rotate sequence by n positions
- [ ] Task 587 - ArrayToSeq: convert array to sequence
- [ ] Task 460 - GetFirstElements: get first element from each sub-sequence
- [ ] Task 610 - RemoveElement: remove element at index k
- [ ] Task 632 - MoveZeroesToEnd: move all zeros to end preserving order
- [ ] Task 644 - Reverse: reverse array in-place
- [ ] Task 625 - SwapFirstAndLast: swap first and last elements
- [ ] Task 591 - SwapFirstAndLast (variant): similar to 625
- [ ] Task 307 - DeepCopySeq: create a deep copy of sequence

### Mathematical Operations
- [ ] Task 573 - UniqueProduct: product of unique elements
- [ ] Task 145 - MaxDifference: maximum difference between any two elements
- [ ] Task 803 - IsPerfectSquare: check if number is perfect square
- [ ] Task 476 - SumMinMax: sum of min and max elements
- [ ] Task 641 - NthNonagonalNumber: calculate nth nonagonal number

### Search and Comparison
- [ ] Task 433 - IsGreater: check if n is greater than all array elements
- [ ] Task 579 - InArray: check if element exists in array
- [ ] Task 808 - ContainsK: check if k is in sequence
- [ ] Task 809 - IsSmaller: element-wise comparison of sequences
- [ ] Task 793 - LastPosition: binary search for last occurrence
- [ ] Task 751 - IsMinHeap: verify min heap property

### Counting and Statistics
- [ ] Task 142 - CountIdenticalPositions: count positions where 3 sequences match
- [ ] Task 143 - CountArrays: count number of arrays
- [ ] Task 792 - CountLists: count number of lists
- [ ] Task 804 - IsProductEven: check if product of array is even

### Sequence Operations
- [ ] Task 290 - MaxLengthList: find list with maximum length
- [ ] Task 95 - SmallestListLength: find minimum length among sequences
- [ ] Task 94 - MinSecondValueFirst: complex min operation on sequences of sequences
- [ ] Task 101 - KthElement: get kth element (1-indexed)
- [ ] Task 750 - AddTupleToList: append tuple to list
- [ ] Task 401 - IndexWiseAddition: element-wise addition of 2D sequences
- [ ] Task 70 - AllSequencesEqualLength: check if all sequences have same length
- [ ] Task 769 - Difference: set difference between sequences

### Bitwise Operations
- [ ] Task 399 - BitwiseXOR: element-wise XOR on bit vectors

## Recommended Next Batches

### Batch 6 (20 tasks) - Array Manipulations
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

### Batch 7 (20 tasks) - Mathematical & Search Operations
1. Task 573 - UniqueProduct
2. Task 145 - MaxDifference
3. Task 803 - IsPerfectSquare
4. Task 476 - SumMinMax
5. Task 641 - NthNonagonalNumber
6. Task 566 - SumOfDigits
7. Task 433 - IsGreater
8. Task 579 - InArray
9. Task 808 - ContainsK
10. Task 809 - IsSmaller
11. Task 793 - LastPosition
12. Task 751 - IsMinHeap
13. Task 142 - CountIdenticalPositions
14. Task 143 - CountArrays
15. Task 792 - CountLists
16. Task 804 - IsProductEven
17. Task 290 - MaxLengthList
18. Task 95 - SmallestListLength
19. Task 94 - MinSecondValueFirst
20. Task 101 - KthElement

## Categories to Avoid (Per User Request)
- String/Character manipulation tasks
- Text processing tasks
- Tasks requiring complex string operations

## Additional Categories to Explore
- [ ] Check atomizer_supported directory for more specs
- [ ] Look for graph/tree algorithms
- [ ] Search for dynamic programming problems
- [ ] Find more complex mathematical algorithms

## Progress Tracking
- Total Ported: ~190 specifications
- Remaining Numeric-Only: ~40 tasks
- Completion: ~82% (excluding string tasks)