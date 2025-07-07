# NumPy Function Extraction Status

## Completed Extractions

1. **Linear Algebra** (numpy.linalg) ✓
   - Location: `full_numpy/linear_algebra/linalg_operations.json`
   - Functions: 32 functions extracted
   - Categories: Matrix products, Decompositions, Eigenvalues, Norms, Solving equations, Other operations

2. **Random Number Generation** (numpy.random) ✓
   - Location: `full_numpy/random/random_operations.json`
   - Functions: 100+ functions extracted
   - Categories: Generator methods, Legacy functions, Bit generators, Utilities

3. **Fast Fourier Transform** (numpy.fft) ✓
   - Location: `full_numpy/fft/fft_operations.json`
   - Functions: 18 functions extracted
   - Categories: Standard FFTs, Real FFTs, Hermitian FFTs, Helper functions

4. **Array Creation** ✓
   - Location: `full_numpy/array_creation/array_creation_operations.json`
   - Functions: 37 functions extracted
   - Categories: From shape/value, From existing data, Numerical ranges, Building matrices

5. **Mathematical Functions** ✓
   - Location: `full_numpy/mathematical_functions/math_operations.json`
   - Functions: 90 functions extracted
   - Categories: Trigonometric, Hyperbolic, Rounding, Sums/products, Exponents/logs, Arithmetic, etc.

6. **Polynomial Operations** (numpy.polynomial) ✓
   - Location: `full_numpy/polynomial/polynomial_operations.json`
   - Functions: 164 functions extracted
   - Categories: Polynomial, Chebyshev, Legendre, Hermite, Laguerre series

7. **Indexing and Slicing** ✓
   - Location: `full_numpy/indexing_slicing/indexing_operations.json`
   - Functions: 42 functions extracted
   - Categories: Generating index arrays, Indexing-like operations, Inserting data, Iterating

8. **I/O Operations** ✓
   - Location: `full_numpy/io_operations/io_operations.json`
   - Functions: 20 functions extracted
   - Categories: NumPy binary files, Text files, String formatting, Memory mapping, Base-n representations

9. **Sorting, Searching, and Counting** ✓
   - Location: `full_numpy/sorting_searching/sorting_searching_operations.json`
   - Functions: 21 functions extracted
   - Categories: Sorting, Searching, Counting

10. **Statistics** ✓
    - Location: `full_numpy/statistics/statistics_operations.json`
    - Functions: 27 functions extracted
    - Categories: Order statistics, Averages and variances, Correlating, Histograms

11. **Logic Functions** ✓
    - Location: `full_numpy/logic_functions/logic_operations.json`
    - Functions: 33 functions extracted
    - Categories: Truth value testing, Array contents, Array type testing, Logical operations, Comparison

12. **Bitwise Operations** ✓
    - Location: `full_numpy/bitwise_operations/bitwise_operations.json`
    - Functions: 10 functions extracted
    - Categories: Bit operations, Bit packing/unpacking

13. **Set Operations** ✓
    - Location: `full_numpy/set_operations/set_operations.json`
    - Functions: 7 functions extracted
    - Categories: Set operations on arrays

14. **String Operations** (numpy.strings) ✓
    - Location: `full_numpy/string_operations/string_operations.json`
    - Functions: 65 functions extracted
    - Categories: String operations, String transformation, String comparison, String information

15. **Datetime Support** ✓
    - Location: `full_numpy/datetime_support/datetime_operations.json`
    - Functions: 8 functions extracted
    - Categories: Datetime types, Datetime conversion, Datetime metadata, Business day operations

16. **Data Type Routines** ✓
    - Location: `full_numpy/data_type_routines/dtype_operations.json`
    - Functions: 28 functions extracted
    - Categories: Type casting/promotion, Data type information, Data type testing, Memory/striding, Utilities

17. **Array Manipulation** ✓
    - Location: `full_numpy/array_manipulation/array_manipulation_operations.json`
    - Functions: 47 functions extracted
    - Categories: Shape operations, Transpose operations, Joining/splitting arrays, Tiling, Adding/removing elements

18. **Masked Arrays** (numpy.ma) ✓
    - Location: `full_numpy/masked_arrays/ma_operations.json`
    - Functions: 98 functions extracted
    - Categories: Creation, Mask manipulation, Filling/compression, Statistics, Operations, I/O

19. **Testing Utilities** (numpy.testing) ✓
    - Location: `full_numpy/testing/testing_operations.json`
    - Functions: 24 functions extracted
    - Categories: Assertion functions, Testing utilities, Decorators, Overrides

20. **Typing Support** (numpy.typing) ✓
    - Location: `full_numpy/typing/typing_operations.json`
    - Functions: 30+ type definitions extracted
    - Categories: Type aliases, Protocol classes, Precision types, Character codes

21. **Constants** ✓
    - Location: `full_numpy/constants/constants_operations.json`
    - Functions: 15 constants extracted
    - Categories: Mathematical constants, Special float values, Indexing helpers, Boolean constants

22. **Universal Functions** (ufuncs) ✓
    - Location: `full_numpy/ufuncs/ufunc_operations.json`
    - Functions: Comprehensive ufunc documentation
    - Categories: Ufunc creation, Methods, Attributes, Available ufuncs by category

## Summary

- **Total Completed**: 22 major categories
- **Total Functions Documented**: 900+ functions with full documentation and source code
- **Coverage**: Comprehensive coverage of NumPy's public API

Each completed extraction includes:
- Full function documentation with parameters and return values
- Code examples demonstrating usage
- Actual source code implementation (Python) or C implementation references
- Proper categorization and organization
- URL references to official NumPy documentation

## Notes

All extractions follow the standard format established in `linear_algebra/linalg_operations.json`, ensuring consistency across the entire documentation set. The "code" field contains actual implementation code where available, or indicates "C implementation in [filename]" for C-based functions.