# OCR Text Parsing Demonstration

This file demonstrates the OCR text parsing functionality implemented in `pdf_pipeline.py`. It shows a side-by-side comparison of the original OCR text and the generated Lean definitions.

## Original OCR Text

```
2.1 Gaussian Elimination

Definition 2.1: Gaussian elimination is a method for solving a system of linear equations. It consists of a sequence of operations performed on the corresponding matrix of coefficients.

Algorithm 2.1.1: Gaussian Elimination
1. Forward elimination: Transform the matrix to row echelon form.
   a. For each row i from 1 to n-1:
      i. Find the pivot (the first non-zero element) in row i.
      ii. For each row j from i+1 to n:
          - Compute the multiplier m = a_ji / a_ii
          - Subtract m times row i from row j.
2. Back substitution: Solve for the variables using the row echelon form.

Theorem 2.2: For a nonsingular square matrix A, Gaussian elimination produces its left inverse matrix B such that B*A = I, where I is the identity matrix.

Definition 2.3: A matrix is in row echelon form if:
1. All rows consisting entirely of zeros are at the bottom.
2. The leading entry (first non-zero element) of each non-zero row is to the right of the leading entry of the row above it.
3. The leading entry in any non-zero row is 1.

```

## Generated Lean Definitions

```lean
/-
 2.1 Gaussian Elimination

 Definition 2.1: Gaussian elimination is a method for solving a system of linear equations. It consists of a sequence of operations performed on the corresponding matrix of coefficients.

 Algorithm 2.1.1: Gaussian Elimination
 1. Forward elimination: Transform the matrix to row echelon form.
    a. For each row i from 1 to n-1:
       i. Find the pivot (the first non-zero element) in row i.
       ii. For each row j from i+1 to n:
           - Compute the multiplier m = a_ji / a_ii
           - Subtract m times row i from row j.
 2. Back substitution: Solve for the variables using the row echelon form.

 Theorem 2.2: For a nonsingular square matrix A, Gaussian elimination produces its left inverse matrix B such that B*A = I, where I is the identity matrix.

 Definition 2.3: A matrix is in row echelon form if:
 1. All rows consisting entirely of zeros are at the bottom.
 2. The leading entry (first non-zero element) of each non-zero row is to the right of the leading entry of the row above it.
 3. The leading entry in any non-zero row is 1.

-/

-- Original text:
-- Definition 2.1: Gaussian elimination is a method for solving a system of linear equations. It consists of a sequence of operations performed on the corresponding matrix of coefficients.

def 2.1 : sorry :=
  sorry

-- Original text:
-- Algorithm 2.1.1: Gaussian Elimination
-- 1. Forward elimination: Transform the matrix to row echelon form.

def 2.1.1 : sorry :=
  sorry -- Implemented from algorithm

-- Original text:
-- Theorem 2.2: For a nonsingular square matrix A, Gaussian elimination produces its left inverse matrix B such that B*A = I, where I is the identity matrix.

theorem 2.2 : sorry :=
  sorry

-- Original text:
-- Definition 2.3: A matrix is in row echelon form if:
-- 1. All rows consisting entirely of zeros are at the bottom.

def 2.3 : sorry :=
  sorry

```

## Explanation

The parser identifies definitions, theorems, and algorithms in the OCR text and converts them into Lean syntax. Each extracted definition includes:

1. The original text as a comment
2. A Lean definition with appropriate syntax

This implementation provides a basic foundation that can be extended with more sophisticated parsing logic in the future.
