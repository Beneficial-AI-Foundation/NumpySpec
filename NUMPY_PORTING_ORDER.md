# NumPy Porting Order for Lean 4

This document outlines the recommended order for porting NumPy modules to Lean 4, based on dependency analysis of the NumPy codebase.

## Summary

- Total modules: 277
- Total dependencies: 790
- Dependency levels: 9

## Porting Order by Dependency Level

Modules are grouped by dependency level. All modules in a level can be ported in parallel as they have no dependencies on each other.

### Level 0 - Foundation

These modules have no dependencies and should be ported first:

- **numpy**
  - Required by: numpy___config__, numpy__array_api_info, numpy__core, numpy__core_memmap, numpy__core_printoptions and 38 more

- **numpy__configtool**
  - Required by: numpy_lib, numpy_lib__utils_impl, numpy_version

- **numpy__pyinstaller_tests**
  - Required by: numpy_testing

- **numpy_conftest**
  - Required by: numpy__core, numpy_testing, numpy_testing__private, numpy_testing__private_utils

- **numpy_core__dtype**
  - Required by: numpy__core, numpy__core__dtype, numpy_core__utils

- **numpy_core__dtype_ctypes**
  - Required by: numpy__core, numpy__core__dtype_ctypes, numpy_core__utils

- **numpy_core__internal**
  - Required by: numpy__core, numpy__core__internal, numpy_core__utils

- **numpy_core__multiarray_umath**
  - Required by: numpy__core, numpy_core__utils, numpy_version

- **numpy_core_arrayprint**
  - Required by: numpy__core, numpy__core_arrayprint, numpy_core__utils

- **numpy_core_defchararray**
  - Required by: numpy__core, numpy__core_defchararray, numpy_core__utils

- **numpy_core_einsumfunc**
  - Required by: numpy__core, numpy__core_einsumfunc, numpy_core__utils

- **numpy_core_fromnumeric**
  - Required by: numpy__core, numpy__core_fromnumeric, numpy_core__utils

- **numpy_core_function_base**
  - Required by: numpy__core, numpy__core_function_base, numpy_core__utils

- **numpy_core_getlimits**
  - Required by: numpy__core, numpy__core_getlimits, numpy_core__utils

- **numpy_core_multiarray**
  - Required by: numpy__core, numpy__core_multiarray, numpy_core__utils

- **numpy_core_numeric**
  - Required by: numpy__core, numpy__core_numeric, numpy_core__utils

- **numpy_core_numerictypes**
  - Required by: numpy__core, numpy__core_numerictypes, numpy_core__utils

- **numpy_core_overrides**
  - Required by: numpy__core, numpy__core_overrides, numpy_core__utils

- **numpy_core_records**
  - Required by: numpy__core, numpy__core_records, numpy_core__utils

- **numpy_core_shape_base**
  - Required by: numpy__core, numpy__core_shape_base, numpy_core__utils

- **numpy_core_umath**
  - Required by: numpy__core, numpy__core_umath, numpy_core__utils

- **numpy_f2py___main__**
  - Required by: numpy_f2py_f2py2e

- **numpy_f2py_tests**
  - Required by: numpy_testing

- **numpy_f2py_tests_test_abstract_interface**
  - Required by: numpy_f2py_crackfortran, numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_array_from_pyobj**
  - Required by: numpy__core, numpy__core__type_aliases, numpy_f2py_tests_util

- **numpy_f2py_tests_test_assumed_shape**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_block_docstring**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_callback**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_character**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_common**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_crackfortran**
  - Required by: numpy_f2py_crackfortran, numpy_f2py_tests_util

- **numpy_f2py_tests_test_data**
  - Required by: numpy_f2py_crackfortran, numpy_f2py_tests_util

- **numpy_f2py_tests_test_docs**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_f2cmap**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_f2py2e**
  - Required by: numpy_f2py_f2py2e, numpy_f2py_tests_util, numpy_testing, numpy_testing__private, numpy_testing__private_utils

- **numpy_f2py_tests_test_isoc**
  - Required by: numpy_f2py_auxfuncs, numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_kind**
  - Required by: numpy_f2py_crackfortran, numpy_f2py_tests_util

- **numpy_f2py_tests_test_mixed**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_modules**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_parameter**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_pyf_src**
  - Required by: numpy_f2py__src_pyf, numpy_testing

- **numpy_f2py_tests_test_quoted_character**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_regression**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_return_character**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_return_complex**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_return_integer**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_return_logical**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_return_real**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_routines**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_semicolon_split**
  - Required by: numpy_f2py_tests_util, numpy_testing

- **numpy_f2py_tests_test_size**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_string**
  - Required by: numpy_f2py_tests_util

- **numpy_f2py_tests_test_symbolic**
  - Required by: numpy_f2py_symbolic, numpy_f2py_tests_util

- **numpy_f2py_tests_test_value_attrspec**
  - Required by: numpy_f2py_tests_util

- **numpy_fft_tests_test_helper**
  - Required by: numpy__core, numpy_testing

- **numpy_fft_tests_test_pocketfft**
  - Required by: numpy_random, numpy_testing

- **numpy_lib_tests_test__datasource**
  - Required by: numpy_lib__datasource, numpy_testing

- **numpy_lib_tests_test__iotools**
  - Required by: numpy__core, numpy__core_numeric, numpy_lib__iotools, numpy_testing

- **numpy_lib_tests_test__version**
  - Required by: numpy_testing

- **numpy_lib_tests_test_array_utils**
  - Required by: numpy_lib_array_utils, numpy_testing

- **numpy_lib_tests_test_arraypad**
  - Required by: numpy_lib__arraypad_impl, numpy_testing

- **numpy_lib_tests_test_arraysetops**
  - Required by: numpy_exceptions, numpy_testing

- **numpy_lib_tests_test_arrayterator**
  - Required by: numpy_random, numpy_testing

- **numpy_lib_tests_test_format**
  - Required by: numpy_lib__utils_impl, numpy_lib_format, numpy_testing, numpy_testing__private, numpy_testing__private_utils

- **numpy_lib_tests_test_function_base**
  - Required by: numpy__core, numpy__core_numeric, numpy_exceptions, numpy_lib__function_base_impl, numpy_ma and 2 more

- **numpy_lib_tests_test_histograms**
  - Required by: numpy_testing

- **numpy_lib_tests_test_index_tricks**
  - Required by: numpy_lib__index_tricks_impl, numpy_testing

- **numpy_lib_tests_test_io**
  - Required by: numpy__utils, numpy_exceptions, numpy_lib__iotools, numpy_lib__npyio_impl, numpy_ma and 4 more

- **numpy_lib_tests_test_loadtxt**
  - Required by: numpy_ma, numpy_ma_testutils, numpy_testing

- **numpy_lib_tests_test_mixins**
  - Required by: numpy_testing

- **numpy_lib_tests_test_nanfunctions**
  - Required by: numpy__core, numpy__core_numeric, numpy_exceptions, numpy_lib__nanfunctions_impl, numpy_testing

- **numpy_lib_tests_test_packbits**
  - Required by: numpy_testing

- **numpy_lib_tests_test_polynomial**
  - Required by: numpy_polynomial, numpy_polynomial_polynomial, numpy_testing

- **numpy_lib_tests_test_recfunctions**
  - Required by: numpy_lib_recfunctions, numpy_ma, numpy_ma_mrecords, numpy_ma_testutils, numpy_testing

- **numpy_lib_tests_test_regression**
  - Required by: numpy_lib_recfunctions, numpy_testing

- **numpy_lib_tests_test_shape_base**
  - Required by: numpy_exceptions, numpy_random, numpy_testing

- **numpy_lib_tests_test_stride_tricks**
  - Required by: numpy__core, numpy_lib__stride_tricks_impl, numpy_testing

- **numpy_lib_tests_test_twodim_base**
  - Required by: numpy_testing

- **numpy_lib_tests_test_type_check**
  - Required by: numpy_testing

- **numpy_lib_tests_test_ufunclike**
  - Required by: numpy_testing

- **numpy_lib_tests_test_utils**
  - Required by: numpy_lib__utils_impl, numpy_testing

- **numpy_lib_user_array**
  - Required by: numpy_lib__user_array_impl

- **numpy_linalg_tests_test_deprecations**
  - Required by: numpy_testing

- **numpy_linalg_tests_test_regression**
  - Required by: numpy_testing

- **numpy_ma_tests_test_arrayobject**
  - Required by: numpy_testing

- **numpy_ma_tests_test_core**
  - Required by: numpy__core, numpy__core_fromnumeric, numpy__core_umath, numpy__utils, numpy_exceptions and 5 more

- **numpy_ma_tests_test_deprecations**
  - Required by: numpy_ma_core, numpy_ma_testutils, numpy_testing

- **numpy_ma_tests_test_extras**
  - Required by: numpy__core, numpy__core_numeric, numpy_ma_core, numpy_ma_extras, numpy_ma_testutils and 1 more

- **numpy_ma_tests_test_mrecords**
  - Required by: numpy__core, numpy__core_records, numpy_ma_mrecords, numpy_ma_testutils, numpy_testing

- **numpy_ma_tests_test_old_ma**
  - Required by: numpy__core, numpy__core_fromnumeric, numpy__core_umath, numpy_testing

- **numpy_ma_tests_test_regression**
  - Required by: numpy_testing

- **numpy_ma_tests_test_subclassing**
  - Required by: numpy_lib, numpy_lib_mixins, numpy_ma_core, numpy_ma_testutils, numpy_testing

- **numpy_matrixlib_tests_test_defmatrix**
  - Required by: numpy_linalg, numpy_testing

- **numpy_matrixlib_tests_test_interaction**
  - Required by: numpy_testing

- **numpy_matrixlib_tests_test_masked_matrix**
  - Required by: numpy_ma, numpy_ma_core, numpy_ma_extras, numpy_ma_testutils

- **numpy_matrixlib_tests_test_matrix_linalg**
  - Required by: numpy_linalg, numpy_linalg_tests, numpy_linalg_tests_test_linalg

- **numpy_matrixlib_tests_test_multiarray**
  - Required by: numpy_testing

- **numpy_matrixlib_tests_test_numeric**
  - Required by: numpy_testing

- **numpy_matrixlib_tests_test_regression**
  - Required by: numpy_testing

- **numpy_polynomial_tests_test_chebyshev**
  - Required by: numpy_polynomial_chebyshev, numpy_polynomial_polynomial, numpy_testing

- **numpy_polynomial_tests_test_classes**
  - Required by: numpy_exceptions, numpy_testing

- **numpy_polynomial_tests_test_hermite**
  - Required by: numpy_polynomial_hermite, numpy_polynomial_polynomial, numpy_testing

- **numpy_polynomial_tests_test_hermite_e**
  - Required by: numpy_polynomial_hermite_e, numpy_polynomial_polynomial, numpy_testing

- **numpy_polynomial_tests_test_laguerre**
  - Required by: numpy_polynomial_laguerre, numpy_polynomial_polynomial, numpy_testing

- **numpy_polynomial_tests_test_legendre**
  - Required by: numpy_polynomial_legendre, numpy_polynomial_polynomial, numpy_testing

- **numpy_polynomial_tests_test_polynomial**
  - Required by: numpy_polynomial_polynomial, numpy_polynomial_polyutils, numpy_testing

- **numpy_polynomial_tests_test_polyutils**
  - Required by: numpy_polynomial_polyutils, numpy_testing

- **numpy_polynomial_tests_test_printing**
  - Required by: numpy__core, numpy__core_printoptions, numpy_testing

- **numpy_polynomial_tests_test_symbol**
  - Required by: numpy__core, numpy_testing

- **numpy_random_tests_test_direct**
  - Required by: numpy_testing

- **numpy_random_tests_test_extending**
  - Required by: numpy__utils, numpy__utils__pep440, numpy_testing

- **numpy_random_tests_test_generator_mt19937**
  - Required by: numpy_exceptions, numpy_linalg, numpy_testing

- **numpy_random_tests_test_generator_mt19937_regressions**
  - Required by: numpy_testing

- **numpy_random_tests_test_random**
  - Required by: numpy_testing

- **numpy_random_tests_test_randomstate**
  - Required by: numpy_testing

- **numpy_random_tests_test_randomstate_regression**
  - Required by: numpy_testing

- **numpy_random_tests_test_regression**
  - Required by: numpy_testing

- **numpy_random_tests_test_seed_sequence**
  - Required by: numpy_testing

- **numpy_random_tests_test_smoke**
  - Required by: numpy_testing

- **numpy_testing_print_coercion_tables**
  - Required by: numpy__core, numpy__core_numerictypes

- **numpy_testing_tests_test_utils**
  - Required by: numpy__core

- **numpy_tests_test_configtool**
  - Required by: numpy__core, numpy_testing

- **numpy_tests_test_ctypeslib**
  - Required by: numpy_ctypeslib, numpy_testing

- **numpy_tests_test_lazyloading**
  - Required by: numpy_lib, numpy_lib_recfunctions

- **numpy_tests_test_matlib**
  - Required by: numpy_matlib, numpy_testing

- **numpy_tests_test_numpy_version**
  - Required by: numpy_testing

- **numpy_tests_test_public_api**
  - Required by: numpy__core, numpy_core, numpy_testing

- **numpy_tests_test_reloading**
  - Required by: numpy__globals, numpy_exceptions, numpy_testing

- **numpy_tests_test_scripts**
  - Required by: numpy_testing

- **numpy_typing_tests_test_isfile**
  - Required by: numpy_testing

- **numpy_typing_tests_test_runtime**
  - Required by: numpy__typing

### Level 1 - Dependencies: 1

These modules depend only on modules from levels 0-0:

- **numpy___config__**
  - Depends on: numpy
  - Required by: numpy__core

- **numpy__array_api_info**
  - Depends on: numpy
  - Required by: numpy__core

- **numpy__distributor_init**
  - Depends on: numpy

- **numpy__expired_attrs_2_0**
  - Depends on: numpy

- **numpy__utils__pep440**
  - Depends on: numpy_random_tests_test_extending

- **numpy_char**
  - Depends on: numpy
  - Required by: numpy__core, numpy__core_defchararray

- **numpy_core**
  - Depends on: numpy, numpy_tests_test_public_api
  - Required by: numpy__core, numpy_core__utils

- **numpy_ctypeslib**
  - Depends on: numpy, numpy_tests_test_ctypeslib
  - Required by: numpy_ctypeslib__ctypeslib

- **numpy_dtypes**
  - Depends on: numpy

- **numpy_f2py**
  - Depends on: numpy
  - Required by: numpy__pytesttester, numpy_exceptions, numpy_f2py_diagnose, numpy_f2py_f2py2e

- **numpy_f2py__src_pyf**
  - Depends on: numpy_f2py_tests_test_pyf_src

- **numpy_f2py_tests_util**
  - Depends on: numpy_f2py_tests_test_abstract_interface, numpy_f2py_tests_test_array_from_pyobj, numpy_f2py_tests_test_assumed_shape, numpy_f2py_tests_test_block_docstring, numpy_f2py_tests_test_callback, numpy_f2py_tests_test_character, numpy_f2py_tests_test_common, numpy_f2py_tests_test_crackfortran, numpy_f2py_tests_test_data, numpy_f2py_tests_test_docs, numpy_f2py_tests_test_f2cmap, numpy_f2py_tests_test_f2py2e, numpy_f2py_tests_test_isoc, numpy_f2py_tests_test_kind, numpy_f2py_tests_test_mixed, numpy_f2py_tests_test_modules, numpy_f2py_tests_test_parameter, numpy_f2py_tests_test_quoted_character, numpy_f2py_tests_test_regression, numpy_f2py_tests_test_return_character, numpy_f2py_tests_test_return_complex, numpy_f2py_tests_test_return_integer, numpy_f2py_tests_test_return_logical, numpy_f2py_tests_test_return_real, numpy_f2py_tests_test_routines, numpy_f2py_tests_test_semicolon_split, numpy_f2py_tests_test_size, numpy_f2py_tests_test_string, numpy_f2py_tests_test_symbolic, numpy_f2py_tests_test_value_attrspec
  - Required by: numpy__utils, numpy_f2py__backends, numpy_f2py__backends__meson, numpy_testing

- **numpy_fft**
  - Depends on: numpy
  - Required by: numpy__pytesttester, numpy_fft__helper, numpy_fft__pocketfft, numpy_fft_helper

- **numpy_lib__user_array_impl**
  - Depends on: numpy_lib_user_array
  - Required by: numpy__core, numpy__core_overrides

- **numpy_linalg_tests**
  - Depends on: numpy_matrixlib_tests_test_matrix_linalg

- **numpy_linalg_tests_test_linalg**
  - Depends on: numpy_matrixlib_tests_test_matrix_linalg
  - Required by: numpy__core, numpy_exceptions, numpy_linalg__linalg, numpy_testing

- **numpy_ma_testutils**
  - Depends on: numpy_lib_tests_test_io, numpy_lib_tests_test_loadtxt, numpy_lib_tests_test_recfunctions, numpy_ma_tests_test_core, numpy_ma_tests_test_deprecations, numpy_ma_tests_test_extras, numpy_ma_tests_test_mrecords, numpy_ma_tests_test_subclassing, numpy_matrixlib_tests_test_masked_matrix
  - Required by: numpy__core, numpy__core_umath, numpy_ma_core, numpy_testing

- **numpy_matlib**
  - Depends on: numpy, numpy_tests_test_matlib
  - Required by: numpy_matrixlib, numpy_matrixlib_defmatrix

- **numpy_polynomial**
  - Depends on: numpy, numpy_lib_tests_test_polynomial
  - Required by: numpy__pytesttester, numpy_polynomial__polybase, numpy_polynomial_chebyshev, numpy_polynomial_hermite, numpy_polynomial_hermite_e and 3 more

- **numpy_random**
  - Depends on: numpy, numpy_fft_tests_test_pocketfft, numpy_lib_tests_test_arrayterator, numpy_lib_tests_test_function_base, numpy_lib_tests_test_shape_base
  - Required by: numpy__pytesttester, numpy_random__pickle

- **numpy_rec**
  - Depends on: numpy
  - Required by: numpy__core, numpy__core_records

- **numpy_typing**
  - Depends on: numpy
  - Required by: numpy__pytesttester, numpy__typing, numpy__typing__add_docstring

### Level 2 - Dependencies: 2

These modules depend only on modules from levels 0-1:

- **numpy__core_defchararray**
  - Depends on: numpy_char, numpy_core_defchararray
  - Required by: numpy__core_multiarray, numpy__core_numeric, numpy__core_numerictypes, numpy__core_overrides, numpy__core_strings and 2 more

- **numpy__typing__add_docstring**
  - Depends on: numpy_typing
  - Required by: numpy__typing__array_like

- **numpy_core__utils**
  - Depends on: numpy_core, numpy_core__dtype, numpy_core__dtype_ctypes, numpy_core__internal, numpy_core__multiarray_umath, numpy_core_arrayprint, numpy_core_defchararray, numpy_core_einsumfunc, numpy_core_fromnumeric, numpy_core_function_base, numpy_core_getlimits, numpy_core_multiarray, numpy_core_numeric, numpy_core_numerictypes, numpy_core_overrides, numpy_core_records, numpy_core_shape_base, numpy_core_umath

- **numpy_ctypeslib__ctypeslib**
  - Depends on: numpy_ctypeslib
  - Required by: numpy__core, numpy__core__internal, numpy__core_multiarray, numpy__utils

- **numpy_f2py_diagnose**
  - Depends on: numpy_f2py
  - Required by: numpy_f2py_f2py2e

- **numpy_fft__pocketfft**
  - Depends on: numpy_fft
  - Required by: numpy__core, numpy__core_overrides, numpy_lib, numpy_lib_array_utils

- **numpy_fft_helper**
  - Depends on: numpy_fft
  - Required by: numpy_fft__helper

- **numpy_polynomial_chebyshev**
  - Depends on: numpy_polynomial, numpy_polynomial_tests_test_chebyshev
  - Required by: numpy_lib, numpy_lib_array_utils, numpy_linalg, numpy_polynomial__polybase, numpy_polynomial_polynomial and 1 more

- **numpy_polynomial_hermite**
  - Depends on: numpy_polynomial, numpy_polynomial_tests_test_hermite
  - Required by: numpy_lib, numpy_lib_array_utils, numpy_linalg, numpy_polynomial__polybase, numpy_polynomial_polynomial and 1 more

- **numpy_polynomial_hermite_e**
  - Depends on: numpy_polynomial, numpy_polynomial_tests_test_hermite_e
  - Required by: numpy_lib, numpy_lib_array_utils, numpy_linalg, numpy_polynomial__polybase, numpy_polynomial_polynomial and 1 more

- **numpy_polynomial_laguerre**
  - Depends on: numpy_polynomial, numpy_polynomial_tests_test_laguerre
  - Required by: numpy_lib, numpy_lib_array_utils, numpy_linalg, numpy_polynomial__polybase, numpy_polynomial_polynomial and 1 more

- **numpy_polynomial_legendre**
  - Depends on: numpy_polynomial, numpy_polynomial_tests_test_legendre
  - Required by: numpy_lib, numpy_lib_array_utils, numpy_linalg, numpy_polynomial__polybase, numpy_polynomial_polynomial and 1 more

- **numpy_random__pickle**
  - Depends on: numpy_random

### Level 3 - Dependencies: 3

These modules depend only on modules from levels 0-2:

- **numpy_f2py_f2py2e**
  - Depends on: numpy_f2py, numpy_f2py___main__, numpy_f2py_diagnose, numpy_f2py_tests_test_f2py2e
  - Required by: numpy_f2py___version__, numpy_f2py__backends, numpy_f2py_auxfuncs, numpy_f2py_capi_maps, numpy_f2py_cb_rules and 4 more

- **numpy_fft__helper**
  - Depends on: numpy_fft, numpy_fft_helper
  - Required by: numpy__core, numpy__core_overrides

- **numpy_polynomial_polynomial**
  - Depends on: numpy_lib_tests_test_polynomial, numpy_polynomial, numpy_polynomial_chebyshev, numpy_polynomial_hermite, numpy_polynomial_hermite_e, numpy_polynomial_laguerre, numpy_polynomial_legendre, numpy_polynomial_tests_test_chebyshev, numpy_polynomial_tests_test_hermite, numpy_polynomial_tests_test_hermite_e, numpy_polynomial_tests_test_laguerre, numpy_polynomial_tests_test_legendre, numpy_polynomial_tests_test_polynomial
  - Required by: numpy_lib, numpy_lib_array_utils, numpy_linalg, numpy_polynomial__polybase, numpy_polynomial_polyutils

- **numpy_strings**
  - Depends on: numpy, numpy__core_defchararray
  - Required by: numpy__core, numpy__core_strings

### Level 4 - Dependencies: 4

These modules depend only on modules from levels 0-3:

- **numpy__core_strings**
  - Depends on: numpy__core_defchararray, numpy_strings
  - Required by: numpy__core_multiarray, numpy__core_overrides, numpy__core_umath

- **numpy_f2py__backends**
  - Depends on: numpy_f2py_f2py2e, numpy_f2py_tests_util
  - Required by: numpy_f2py__backends__distutils, numpy_f2py__backends__meson

- **numpy_f2py_cb_rules**
  - Depends on: numpy_f2py_f2py2e
  - Required by: numpy_f2py___version__, numpy_f2py_auxfuncs, numpy_f2py_capi_maps, numpy_f2py_cfuncs

- **numpy_f2py_f90mod_rules**
  - Depends on: numpy_f2py_f2py2e
  - Required by: numpy_f2py_auxfuncs, numpy_f2py_capi_maps, numpy_f2py_crackfortran, numpy_f2py_func2subr, numpy_f2py_rules

- **numpy_polynomial__polybase**
  - Depends on: numpy_polynomial, numpy_polynomial_chebyshev, numpy_polynomial_hermite, numpy_polynomial_hermite_e, numpy_polynomial_laguerre, numpy_polynomial_legendre, numpy_polynomial_polynomial
  - Required by: numpy_polynomial_polyutils

### Level 5 - Dependencies: 5

These modules depend only on modules from levels 0-4:

- **numpy_f2py__backends__distutils**
  - Depends on: numpy_f2py__backends
  - Required by: numpy_exceptions, numpy_f2py__backends__backend

- **numpy_f2py__backends__meson**
  - Depends on: numpy_f2py__backends, numpy_f2py_tests_util
  - Required by: numpy_f2py__backends__backend

- **numpy_f2py_rules**
  - Depends on: numpy_f2py_f2py2e, numpy_f2py_f90mod_rules
  - Required by: numpy_f2py___version__, numpy_f2py_auxfuncs, numpy_f2py_capi_maps, numpy_f2py_cfuncs, numpy_f2py_common_rules and 2 more

- **numpy_polynomial_polyutils**
  - Depends on: numpy_polynomial__polybase, numpy_polynomial_chebyshev, numpy_polynomial_hermite, numpy_polynomial_hermite_e, numpy_polynomial_laguerre, numpy_polynomial_legendre, numpy_polynomial_polynomial, numpy_polynomial_tests_test_polynomial, numpy_polynomial_tests_test_polyutils
  - Required by: numpy__core, numpy__core_multiarray, numpy_exceptions

### Level 6 - Dependencies: 6

These modules depend only on modules from levels 0-5:

- **numpy_f2py__backends__backend**
  - Depends on: numpy_f2py__backends__distutils, numpy_f2py__backends__meson

- **numpy_f2py_common_rules**
  - Depends on: numpy_f2py_rules
  - Required by: numpy_f2py___version__, numpy_f2py_auxfuncs, numpy_f2py_capi_maps, numpy_f2py_crackfortran, numpy_f2py_func2subr

- **numpy_f2py_use_rules**
  - Depends on: numpy_f2py_rules
  - Required by: numpy_f2py_auxfuncs

### Level 7 - Dependencies: 7

These modules depend only on modules from levels 0-6:

- **numpy_f2py_func2subr**
  - Depends on: numpy_f2py_common_rules, numpy_f2py_f90mod_rules, numpy_f2py_rules
  - Required by: numpy_f2py__isocbind, numpy_f2py_auxfuncs

### Level 8 - Dependencies: 8

These modules depend only on modules from levels 0-7:

- **numpy__core**
  - Depends on: numpy, numpy___config__, numpy__array_api_info, numpy__typing__array_like, numpy_char, numpy_conftest, numpy_core, numpy_core__dtype, numpy_core__dtype_ctypes, numpy_core__internal, numpy_core__multiarray_umath, numpy_core_arrayprint, numpy_core_defchararray, numpy_core_einsumfunc, numpy_core_fromnumeric, numpy_core_function_base, numpy_core_getlimits, numpy_core_multiarray, numpy_core_numeric, numpy_core_numerictypes, numpy_core_overrides, numpy_core_records, numpy_core_shape_base, numpy_core_umath, numpy_ctypeslib__ctypeslib, numpy_f2py_tests_test_array_from_pyobj, numpy_fft__helper, numpy_fft__pocketfft, numpy_fft_tests_test_helper, numpy_lib, numpy_lib__array_utils_impl, numpy_lib__arraypad_impl, numpy_lib__arraysetops_impl, numpy_lib__function_base_impl, numpy_lib__histograms_impl, numpy_lib__index_tricks_impl, numpy_lib__iotools, numpy_lib__nanfunctions_impl, numpy_lib__npyio_impl, numpy_lib__polynomial_impl, numpy_lib__scimath_impl, numpy_lib__shape_base_impl, numpy_lib__stride_tricks_impl, numpy_lib__twodim_base_impl, numpy_lib__type_check_impl, numpy_lib__ufunclike_impl, numpy_lib__user_array_impl, numpy_lib__utils_impl, numpy_lib_introspect, numpy_lib_mixins, numpy_lib_recfunctions, numpy_lib_tests_test__iotools, numpy_lib_tests_test_function_base, numpy_lib_tests_test_nanfunctions, numpy_lib_tests_test_stride_tricks, numpy_linalg__linalg, numpy_linalg_tests_test_linalg, numpy_ma_core, numpy_ma_tests_test_core, numpy_ma_tests_test_extras, numpy_ma_tests_test_mrecords, numpy_ma_tests_test_old_ma, numpy_ma_testutils, numpy_matrixlib_defmatrix, numpy_polynomial_polyutils, numpy_polynomial_tests_test_printing, numpy_polynomial_tests_test_symbol, numpy_rec, numpy_strings, numpy_testing__private_utils, numpy_testing_overrides, numpy_testing_print_coercion_tables, numpy_testing_tests_test_utils, numpy_tests_test_configtool, numpy_tests_test_public_api
  - Required by: numpy__core__add_newdocs, numpy__core__add_newdocs_scalars, numpy__core__dtype, numpy__core__dtype_ctypes, numpy__core__internal and 15 more

- **numpy__core__add_newdocs**
  - Depends on: numpy__core
  - Required by: numpy__core_function_base, numpy__core_overrides

- **numpy__core__add_newdocs_scalars**
  - Depends on: numpy__core
  - Required by: numpy__core_function_base, numpy__core_numerictypes

- **numpy__core__asarray**
  - Depends on: numpy__core_numeric
  - Required by: numpy__core_multiarray, numpy__core_overrides

- **numpy__core__dtype**
  - Depends on: numpy__core, numpy__core_numerictypes, numpy_core__dtype

- **numpy__core__dtype_ctypes**
  - Depends on: numpy__core, numpy_core__dtype_ctypes

- **numpy__core__internal**
  - Depends on: numpy__core, numpy_core__internal, numpy_ctypeslib__ctypeslib
  - Required by: numpy__core_multiarray, numpy_exceptions

- **numpy__core__machar**
  - Depends on: numpy__core, numpy__core_getlimits
  - Required by: numpy__core__ufunc_config, numpy__core_fromnumeric

- **numpy__core__methods**
  - Depends on: numpy__core, numpy__core_fromnumeric
  - Required by: numpy__core_multiarray, numpy__core_numerictypes, numpy__core_umath, numpy__globals, numpy_lib and 1 more

- **numpy__core__string_helpers**
  - Depends on: numpy__core_numerictypes

- **numpy__core__type_aliases**
  - Depends on: numpy__core_numerictypes, numpy_f2py_tests_test_array_from_pyobj
  - Required by: numpy__core_multiarray

- **numpy__core__ufunc_config**
  - Depends on: numpy__core__machar, numpy__core_numeric
  - Required by: numpy__core_umath, numpy__utils

- **numpy__core_arrayprint**
  - Depends on: numpy__core_numeric, numpy__core_records, numpy_core_arrayprint
  - Required by: numpy__core_fromnumeric, numpy__core_multiarray, numpy__core_numerictypes, numpy__core_overrides, numpy__core_printoptions and 1 more

- **numpy__core_einsumfunc**
  - Depends on: numpy__core, numpy_core_einsumfunc
  - Required by: numpy__core_multiarray, numpy__core_numeric, numpy__core_overrides

- **numpy__core_fromnumeric**
  - Depends on: numpy__core, numpy__core__machar, numpy__core_arrayprint, numpy__core_numeric, numpy__core_shape_base, numpy_core_fromnumeric, numpy_lib__function_base_impl, numpy_lib__shape_base_impl, numpy_ma_tests_test_core, numpy_ma_tests_test_old_ma, numpy_testing__private_utils
  - Required by: numpy__core__methods, numpy__core_multiarray, numpy__core_numerictypes, numpy__core_overrides, numpy__core_umath and 1 more

- **numpy__core_function_base**
  - Depends on: numpy__core, numpy__core__add_newdocs, numpy__core__add_newdocs_scalars, numpy_core_function_base, numpy_lib
  - Required by: numpy__core_multiarray, numpy__core_numeric, numpy__core_overrides

- **numpy__core_getlimits**
  - Depends on: numpy__core, numpy_core_getlimits, numpy_lib__type_check_impl
  - Required by: numpy__core__machar, numpy__core_numeric, numpy__core_numerictypes, numpy__core_umath, numpy__utils

- **numpy__core_memmap**
  - Depends on: numpy, numpy__core
  - Required by: numpy__core_numeric, numpy__utils

- **numpy__core_multiarray**
  - Depends on: numpy__core, numpy__core__asarray, numpy__core__internal, numpy__core__methods, numpy__core__type_aliases, numpy__core_arrayprint, numpy__core_defchararray, numpy__core_einsumfunc, numpy__core_fromnumeric, numpy__core_function_base, numpy__core_numeric, numpy__core_numerictypes, numpy__core_shape_base, numpy__core_strings, numpy__typing__array_like, numpy_core_multiarray, numpy_ctypeslib__ctypeslib, numpy_lib__function_base_impl, numpy_lib__index_tricks_impl, numpy_lib__npyio_impl, numpy_lib__shape_base_impl, numpy_ma_core, numpy_polynomial_polyutils
  - Required by: numpy__core_overrides

- **numpy__core_numeric**
  - Depends on: numpy__core, numpy__core_defchararray, numpy__core_einsumfunc, numpy__core_function_base, numpy__core_getlimits, numpy__core_memmap, numpy__core_records, numpy__core_shape_base, numpy_core_numeric, numpy_lib__array_utils_impl, numpy_lib__function_base_impl, numpy_lib__index_tricks_impl, numpy_lib__iotools, numpy_lib__nanfunctions_impl, numpy_lib__polynomial_impl, numpy_lib__scimath_impl, numpy_lib__shape_base_impl, numpy_lib__stride_tricks_impl, numpy_lib__twodim_base_impl, numpy_lib__type_check_impl, numpy_lib__ufunclike_impl, numpy_lib_tests_test__iotools, numpy_lib_tests_test_function_base, numpy_lib_tests_test_nanfunctions, numpy_ma_core, numpy_ma_tests_test_extras, numpy_matrixlib_defmatrix
  - Required by: numpy__core__asarray, numpy__core__ufunc_config, numpy__core_arrayprint, numpy__core_fromnumeric, numpy__core_multiarray and 4 more

- **numpy__core_numerictypes**
  - Depends on: numpy__core, numpy__core__add_newdocs_scalars, numpy__core__methods, numpy__core_arrayprint, numpy__core_defchararray, numpy__core_fromnumeric, numpy__core_getlimits, numpy__core_numeric, numpy__core_records, numpy_core_numerictypes, numpy_lib__function_base_impl, numpy_lib__index_tricks_impl, numpy_lib__scimath_impl, numpy_ma_core, numpy_testing__private_utils, numpy_testing_print_coercion_tables
  - Required by: numpy__core__dtype, numpy__core__string_helpers, numpy__core__type_aliases, numpy__core_multiarray, numpy__utils

- **numpy__core_overrides**
  - Depends on: numpy__core__add_newdocs, numpy__core__asarray, numpy__core_arrayprint, numpy__core_defchararray, numpy__core_einsumfunc, numpy__core_fromnumeric, numpy__core_function_base, numpy__core_multiarray, numpy__core_numeric, numpy__core_shape_base, numpy__core_strings, numpy_core_overrides, numpy_fft__helper, numpy_fft__pocketfft, numpy_lib__arraypad_impl, numpy_lib__arraysetops_impl, numpy_lib__function_base_impl, numpy_lib__histograms_impl, numpy_lib__index_tricks_impl, numpy_lib__nanfunctions_impl, numpy_lib__npyio_impl, numpy_lib__polynomial_impl, numpy_lib__scimath_impl, numpy_lib__shape_base_impl, numpy_lib__stride_tricks_impl, numpy_lib__twodim_base_impl, numpy_lib__type_check_impl, numpy_lib__ufunclike_impl, numpy_lib__user_array_impl, numpy_lib_recfunctions, numpy_linalg__linalg, numpy_testing_overrides
  - Required by: numpy__utils, numpy__utils__inspect

- **numpy__core_printoptions**
  - Depends on: numpy, numpy__core_arrayprint, numpy_polynomial_tests_test_printing

- **numpy__core_records**
  - Depends on: numpy__core, numpy_core_records, numpy_ma_tests_test_mrecords, numpy_rec
  - Required by: numpy__core_arrayprint, numpy__core_numeric, numpy__core_numerictypes, numpy__utils

- **numpy__core_shape_base**
  - Depends on: numpy__core, numpy_core_shape_base, numpy_lib__shape_base_impl
  - Required by: numpy__core_fromnumeric, numpy__core_multiarray, numpy__core_numeric, numpy__core_overrides

- **numpy__core_umath**
  - Depends on: numpy__core, numpy__core__methods, numpy__core__ufunc_config, numpy__core_arrayprint, numpy__core_fromnumeric, numpy__core_getlimits, numpy__core_numeric, numpy__core_strings, numpy_core_umath, numpy_lib__function_base_impl, numpy_lib_mixins, numpy_ma_core, numpy_ma_tests_test_core, numpy_ma_tests_test_old_ma, numpy_ma_testutils, numpy_testing_overrides

- **numpy__globals**
  - Depends on: numpy, numpy__core__methods, numpy_linalg__linalg, numpy_tests_test_reloading
  - Required by: numpy__utils

- **numpy__pytesttester**
  - Depends on: numpy, numpy__core, numpy_f2py, numpy_fft, numpy_lib, numpy_linalg, numpy_ma, numpy_matrixlib, numpy_polynomial, numpy_random, numpy_typing
  - Required by: numpy_testing

- **numpy__typing**
  - Depends on: numpy_linalg__linalg, numpy_typing, numpy_typing_tests_test_runtime
  - Required by: numpy__typing__array_like, numpy__typing__char_codes, numpy__typing__dtype_like, numpy__typing__nbit, numpy__typing__nbit_base and 4 more

- **numpy__typing__array_like**
  - Depends on: numpy__typing, numpy__typing__add_docstring
  - Required by: numpy__core, numpy__core_multiarray, numpy__typing__nbit_base, numpy__typing__nested_sequence, numpy__typing__shape

- **numpy__typing__char_codes**
  - Depends on: numpy__typing, numpy__typing__dtype_like

- **numpy__typing__dtype_like**
  - Depends on: numpy__typing
  - Required by: numpy__typing__char_codes

- **numpy__typing__nbit**
  - Depends on: numpy__typing
  - Required by: numpy__typing__nbit_base

- **numpy__typing__nbit_base**
  - Depends on: numpy__typing, numpy__typing__array_like, numpy__typing__nbit
  - Required by: numpy__utils

- **numpy__typing__nested_sequence**
  - Depends on: numpy__typing, numpy__typing__array_like

- **numpy__typing__scalars**
  - Depends on: numpy__typing

- **numpy__typing__shape**
  - Depends on: numpy__typing, numpy__typing__array_like

- **numpy__typing__ufunc**
  - Depends on: numpy__typing

- **numpy__utils**
  - Depends on: numpy__core__ufunc_config, numpy__core_defchararray, numpy__core_fromnumeric, numpy__core_getlimits, numpy__core_memmap, numpy__core_numerictypes, numpy__core_overrides, numpy__core_records, numpy__globals, numpy__typing__nbit_base, numpy_ctypeslib__ctypeslib, numpy_f2py_tests_util, numpy_lib__array_utils_impl, numpy_lib__datasource, numpy_lib__format_impl, numpy_lib__function_base_impl, numpy_lib__index_tricks_impl, numpy_lib__iotools, numpy_lib__npyio_impl, numpy_lib__polynomial_impl, numpy_lib__type_check_impl, numpy_lib__utils_impl, numpy_lib_tests_test_io, numpy_linalg__linalg, numpy_ma_core, numpy_ma_tests_test_core, numpy_matrixlib_defmatrix, numpy_random_tests_test_extending
  - Required by: numpy__utils__convertions

- **numpy__utils__convertions**
  - Depends on: numpy__utils

- **numpy__utils__inspect**
  - Depends on: numpy__core_overrides, numpy_ma_core

- **numpy_exceptions**
  - Depends on: numpy, numpy__core__internal, numpy__core_numeric, numpy_f2py, numpy_f2py__backends__distutils, numpy_lib__polynomial_impl, numpy_lib_tests_test_arraysetops, numpy_lib_tests_test_function_base, numpy_lib_tests_test_io, numpy_lib_tests_test_nanfunctions, numpy_lib_tests_test_shape_base, numpy_linalg_tests_test_linalg, numpy_ma_tests_test_core, numpy_polynomial_polyutils, numpy_polynomial_tests_test_classes, numpy_random_tests_test_generator_mt19937, numpy_tests_test_reloading

- **numpy_f2py___version__**
  - Depends on: numpy_f2py_auxfuncs, numpy_f2py_capi_maps, numpy_f2py_cb_rules, numpy_f2py_cfuncs, numpy_f2py_common_rules, numpy_f2py_crackfortran, numpy_f2py_f2py2e, numpy_f2py_rules
  - Required by: numpy_version

- **numpy_f2py__isocbind**
  - Depends on: numpy_f2py_capi_maps, numpy_f2py_func2subr

- **numpy_f2py_auxfuncs**
  - Depends on: numpy_f2py_capi_maps, numpy_f2py_cb_rules, numpy_f2py_common_rules, numpy_f2py_crackfortran, numpy_f2py_f2py2e, numpy_f2py_f90mod_rules, numpy_f2py_func2subr, numpy_f2py_rules, numpy_f2py_tests_test_isoc, numpy_f2py_use_rules
  - Required by: numpy_f2py___version__, numpy_f2py_cfuncs

- **numpy_f2py_capi_maps**
  - Depends on: numpy_f2py_cb_rules, numpy_f2py_cfuncs, numpy_f2py_common_rules, numpy_f2py_f2py2e, numpy_f2py_f90mod_rules, numpy_f2py_rules
  - Required by: numpy_f2py___version__, numpy_f2py__isocbind, numpy_f2py_auxfuncs, numpy_f2py_crackfortran

- **numpy_f2py_cfuncs**
  - Depends on: numpy_f2py_auxfuncs, numpy_f2py_cb_rules, numpy_f2py_f2py2e, numpy_f2py_rules
  - Required by: numpy_f2py___version__, numpy_f2py_capi_maps

- **numpy_f2py_crackfortran**
  - Depends on: numpy_f2py_capi_maps, numpy_f2py_common_rules, numpy_f2py_f2py2e, numpy_f2py_f90mod_rules, numpy_f2py_tests_test_abstract_interface, numpy_f2py_tests_test_crackfortran, numpy_f2py_tests_test_data, numpy_f2py_tests_test_kind
  - Required by: numpy_f2py___version__, numpy_f2py_auxfuncs, numpy_f2py_symbolic

- **numpy_f2py_symbolic**
  - Depends on: numpy_f2py_crackfortran, numpy_f2py_tests_test_symbolic

- **numpy_lib**
  - Depends on: numpy, numpy__configtool, numpy__core__methods, numpy_fft__pocketfft, numpy_linalg__linalg, numpy_ma_extras, numpy_ma_tests_test_subclassing, numpy_polynomial_chebyshev, numpy_polynomial_hermite, numpy_polynomial_hermite_e, numpy_polynomial_laguerre, numpy_polynomial_legendre, numpy_polynomial_polynomial, numpy_testing_overrides, numpy_tests_test_lazyloading
  - Required by: numpy__core, numpy__core_function_base, numpy__pytesttester, numpy_lib__arraypad_impl, numpy_lib__arraysetops_impl and 21 more

- **numpy_lib__array_utils_impl**
  - Depends on: numpy_lib_array_utils
  - Required by: numpy__core, numpy__core_numeric, numpy__utils

- **numpy_lib__arraypad_impl**
  - Depends on: numpy, numpy_lib, numpy_lib_tests_test_arraypad
  - Required by: numpy__core, numpy__core_overrides, numpy_lib__index_tricks_impl

- **numpy_lib__arraysetops_impl**
  - Depends on: numpy, numpy_lib
  - Required by: numpy__core, numpy__core_overrides

- **numpy_lib__arrayterator_impl**
  - Depends on: numpy_lib

- **numpy_lib__datasource**
  - Depends on: numpy_lib__npyio_impl, numpy_lib_tests_test__datasource
  - Required by: numpy__utils

- **numpy_lib__format_impl**
  - Depends on: numpy_lib__npyio_impl, numpy_lib_format
  - Required by: numpy__utils, numpy_lib__utils_impl

- **numpy_lib__function_base_impl**
  - Depends on: numpy, numpy_lib, numpy_lib__index_tricks_impl, numpy_lib__nanfunctions_impl, numpy_lib__polynomial_impl, numpy_lib_tests_test_function_base, numpy_ma_extras
  - Required by: numpy__core, numpy__core_fromnumeric, numpy__core_multiarray, numpy__core_numeric, numpy__core_numerictypes and 5 more

- **numpy_lib__histograms_impl**
  - Depends on: numpy, numpy_lib, numpy_lib__function_base_impl
  - Required by: numpy__core, numpy__core_overrides

- **numpy_lib__index_tricks_impl**
  - Depends on: numpy, numpy_lib, numpy_lib__arraypad_impl, numpy_lib__shape_base_impl, numpy_lib_tests_test_index_tricks, numpy_ma_extras
  - Required by: numpy__core, numpy__core_multiarray, numpy__core_numeric, numpy__core_numerictypes, numpy__core_overrides and 4 more

- **numpy_lib__iotools**
  - Depends on: numpy_lib__npyio_impl, numpy_lib_recfunctions, numpy_lib_tests_test__iotools, numpy_lib_tests_test_io
  - Required by: numpy__core, numpy__core_numeric, numpy__utils

- **numpy_lib__nanfunctions_impl**
  - Depends on: numpy, numpy_lib, numpy_lib_tests_test_nanfunctions
  - Required by: numpy__core, numpy__core_numeric, numpy__core_overrides, numpy_lib__function_base_impl

- **numpy_lib__npyio_impl**
  - Depends on: numpy, numpy_lib, numpy_lib_npyio, numpy_lib_tests_test_io
  - Required by: numpy__core, numpy__core_multiarray, numpy__core_overrides, numpy__utils, numpy_lib__datasource and 5 more

- **numpy_lib__polynomial_impl**
  - Depends on: numpy, numpy_lib
  - Required by: numpy__core, numpy__core_numeric, numpy__core_overrides, numpy__utils, numpy_exceptions and 4 more

- **numpy_lib__scimath_impl**
  - Depends on: numpy_lib_scimath
  - Required by: numpy__core, numpy__core_numeric, numpy__core_numerictypes, numpy__core_overrides, numpy_lib__type_check_impl

- **numpy_lib__shape_base_impl**
  - Depends on: numpy, numpy_lib
  - Required by: numpy__core, numpy__core_fromnumeric, numpy__core_multiarray, numpy__core_numeric, numpy__core_overrides and 4 more

- **numpy_lib__stride_tricks_impl**
  - Depends on: numpy, numpy__core__methods, numpy_lib, numpy_lib__twodim_base_impl, numpy_lib_stride_tricks, numpy_lib_tests_test_stride_tricks
  - Required by: numpy__core, numpy__core_numeric, numpy__core_overrides

- **numpy_lib__twodim_base_impl**
  - Depends on: numpy, numpy_lib, numpy_lib__function_base_impl, numpy_lib__polynomial_impl, numpy_linalg__linalg
  - Required by: numpy__core, numpy__core_numeric, numpy__core_overrides, numpy_lib__stride_tricks_impl

- **numpy_lib__type_check_impl**
  - Depends on: numpy, numpy_lib, numpy_lib__polynomial_impl, numpy_lib__scimath_impl
  - Required by: numpy__core, numpy__core_getlimits, numpy__core_numeric, numpy__core_overrides, numpy__utils and 1 more

- **numpy_lib__ufunclike_impl**
  - Depends on: numpy, numpy_lib, numpy_lib__type_check_impl
  - Required by: numpy__core, numpy__core_numeric, numpy__core_overrides

- **numpy_lib__utils_impl**
  - Depends on: numpy, numpy__configtool, numpy_lib, numpy_lib__format_impl, numpy_lib_tests_test_format, numpy_lib_tests_test_utils
  - Required by: numpy__core, numpy__utils

- **numpy_lib__version**
  - Depends on: numpy_lib

- **numpy_lib_array_utils**
  - Depends on: numpy_fft__pocketfft, numpy_lib, numpy_lib_tests_test_array_utils, numpy_linalg__linalg, numpy_ma_extras, numpy_polynomial_chebyshev, numpy_polynomial_hermite, numpy_polynomial_hermite_e, numpy_polynomial_laguerre, numpy_polynomial_legendre, numpy_polynomial_polynomial
  - Required by: numpy_lib__array_utils_impl

- **numpy_lib_format**
  - Depends on: numpy_lib, numpy_lib__npyio_impl, numpy_lib_tests_test_format
  - Required by: numpy_lib__format_impl

- **numpy_lib_introspect**
  - Depends on: numpy_lib
  - Required by: numpy__core

- **numpy_lib_mixins**
  - Depends on: numpy_lib, numpy_ma_tests_test_subclassing
  - Required by: numpy__core, numpy__core_umath

- **numpy_lib_npyio**
  - Depends on: numpy_lib
  - Required by: numpy_lib__npyio_impl

- **numpy_lib_recfunctions**
  - Depends on: numpy_lib_tests_test_recfunctions, numpy_lib_tests_test_regression, numpy_testing_overrides, numpy_tests_test_lazyloading
  - Required by: numpy__core, numpy__core_overrides, numpy_lib__iotools, numpy_ma, numpy_ma_mrecords

- **numpy_lib_scimath**
  - Depends on: numpy, numpy_lib
  - Required by: numpy_lib__scimath_impl

- **numpy_lib_stride_tricks**
  - Depends on: numpy_lib, numpy_lib__index_tricks_impl
  - Required by: numpy_lib__stride_tricks_impl

- **numpy_linalg**
  - Depends on: numpy, numpy_lib__polynomial_impl, numpy_matrixlib_defmatrix, numpy_matrixlib_tests_test_defmatrix, numpy_matrixlib_tests_test_matrix_linalg, numpy_polynomial_chebyshev, numpy_polynomial_hermite, numpy_polynomial_hermite_e, numpy_polynomial_laguerre, numpy_polynomial_legendre, numpy_polynomial_polynomial, numpy_random_tests_test_generator_mt19937, numpy_testing__private_utils
  - Required by: numpy__pytesttester, numpy_linalg__linalg, numpy_linalg_linalg

- **numpy_linalg__linalg**
  - Depends on: numpy_linalg, numpy_linalg_linalg, numpy_linalg_tests_test_linalg
  - Required by: numpy__core, numpy__core_overrides, numpy__globals, numpy__typing, numpy__utils and 3 more

- **numpy_linalg_linalg**
  - Depends on: numpy_linalg
  - Required by: numpy_linalg__linalg

- **numpy_ma**
  - Depends on: numpy, numpy_lib__npyio_impl, numpy_lib_recfunctions, numpy_lib_tests_test_function_base, numpy_lib_tests_test_io, numpy_lib_tests_test_loadtxt, numpy_lib_tests_test_recfunctions, numpy_matrixlib_tests_test_masked_matrix
  - Required by: numpy__pytesttester, numpy_ma_core, numpy_ma_extras

- **numpy_ma_core**
  - Depends on: numpy_ma, numpy_ma_extras, numpy_ma_tests_test_core, numpy_ma_tests_test_deprecations, numpy_ma_tests_test_extras, numpy_ma_tests_test_subclassing, numpy_ma_testutils, numpy_matrixlib_tests_test_masked_matrix
  - Required by: numpy__core, numpy__core_multiarray, numpy__core_numeric, numpy__core_numerictypes, numpy__core_umath and 2 more

- **numpy_ma_extras**
  - Depends on: numpy_ma, numpy_ma_tests_test_extras, numpy_matrixlib_tests_test_masked_matrix
  - Required by: numpy_lib, numpy_lib__function_base_impl, numpy_lib__index_tricks_impl, numpy_lib_array_utils, numpy_ma_core

- **numpy_ma_mrecords**
  - Depends on: numpy_lib__npyio_impl, numpy_lib_recfunctions, numpy_lib_tests_test_recfunctions, numpy_ma_tests_test_mrecords

- **numpy_matrixlib**
  - Depends on: numpy, numpy_lib__index_tricks_impl, numpy_lib__shape_base_impl, numpy_matlib
  - Required by: numpy__pytesttester, numpy_matrixlib_defmatrix

- **numpy_matrixlib_defmatrix**
  - Depends on: numpy_lib__shape_base_impl, numpy_matlib, numpy_matrixlib
  - Required by: numpy__core, numpy__core_numeric, numpy__utils, numpy_linalg

- **numpy_testing**
  - Depends on: numpy, numpy__pyinstaller_tests, numpy__pytesttester, numpy_conftest, numpy_f2py_tests, numpy_f2py_tests_test_abstract_interface, numpy_f2py_tests_test_block_docstring, numpy_f2py_tests_test_callback, numpy_f2py_tests_test_character, numpy_f2py_tests_test_docs, numpy_f2py_tests_test_f2py2e, numpy_f2py_tests_test_isoc, numpy_f2py_tests_test_mixed, numpy_f2py_tests_test_modules, numpy_f2py_tests_test_pyf_src, numpy_f2py_tests_test_regression, numpy_f2py_tests_test_return_real, numpy_f2py_tests_test_semicolon_split, numpy_f2py_tests_util, numpy_fft_tests_test_helper, numpy_fft_tests_test_pocketfft, numpy_lib_tests_test__datasource, numpy_lib_tests_test__iotools, numpy_lib_tests_test__version, numpy_lib_tests_test_array_utils, numpy_lib_tests_test_arraypad, numpy_lib_tests_test_arraysetops, numpy_lib_tests_test_arrayterator, numpy_lib_tests_test_format, numpy_lib_tests_test_function_base, numpy_lib_tests_test_histograms, numpy_lib_tests_test_index_tricks, numpy_lib_tests_test_io, numpy_lib_tests_test_loadtxt, numpy_lib_tests_test_mixins, numpy_lib_tests_test_nanfunctions, numpy_lib_tests_test_packbits, numpy_lib_tests_test_polynomial, numpy_lib_tests_test_recfunctions, numpy_lib_tests_test_regression, numpy_lib_tests_test_shape_base, numpy_lib_tests_test_stride_tricks, numpy_lib_tests_test_twodim_base, numpy_lib_tests_test_type_check, numpy_lib_tests_test_ufunclike, numpy_lib_tests_test_utils, numpy_linalg_tests_test_deprecations, numpy_linalg_tests_test_linalg, numpy_linalg_tests_test_regression, numpy_ma_tests_test_arrayobject, numpy_ma_tests_test_core, numpy_ma_tests_test_deprecations, numpy_ma_tests_test_extras, numpy_ma_tests_test_mrecords, numpy_ma_tests_test_old_ma, numpy_ma_tests_test_regression, numpy_ma_tests_test_subclassing, numpy_ma_testutils, numpy_matrixlib_tests_test_defmatrix, numpy_matrixlib_tests_test_interaction, numpy_matrixlib_tests_test_multiarray, numpy_matrixlib_tests_test_numeric, numpy_matrixlib_tests_test_regression, numpy_polynomial_tests_test_chebyshev, numpy_polynomial_tests_test_classes, numpy_polynomial_tests_test_hermite, numpy_polynomial_tests_test_hermite_e, numpy_polynomial_tests_test_laguerre, numpy_polynomial_tests_test_legendre, numpy_polynomial_tests_test_polynomial, numpy_polynomial_tests_test_polyutils, numpy_polynomial_tests_test_printing, numpy_polynomial_tests_test_symbol, numpy_random_tests_test_direct, numpy_random_tests_test_extending, numpy_random_tests_test_generator_mt19937, numpy_random_tests_test_generator_mt19937_regressions, numpy_random_tests_test_random, numpy_random_tests_test_randomstate, numpy_random_tests_test_randomstate_regression, numpy_random_tests_test_regression, numpy_random_tests_test_seed_sequence, numpy_random_tests_test_smoke, numpy_tests_test_configtool, numpy_tests_test_ctypeslib, numpy_tests_test_matlib, numpy_tests_test_numpy_version, numpy_tests_test_public_api, numpy_tests_test_reloading, numpy_tests_test_scripts, numpy_typing_tests_test_isfile
  - Required by: numpy_testing__private, numpy_testing__private_extbuild, numpy_testing__private_utils, numpy_testing_overrides

- **numpy_testing__private**
  - Depends on: numpy_conftest, numpy_f2py_tests_test_f2py2e, numpy_lib_tests_test_format, numpy_lib_tests_test_io, numpy_ma_tests_test_core, numpy_testing

- **numpy_testing__private_extbuild**
  - Depends on: numpy_testing

- **numpy_testing__private_utils**
  - Depends on: numpy_conftest, numpy_f2py_tests_test_f2py2e, numpy_lib_tests_test_format, numpy_lib_tests_test_io, numpy_ma_tests_test_core, numpy_testing
  - Required by: numpy__core, numpy__core_fromnumeric, numpy__core_numerictypes, numpy_linalg

- **numpy_testing_overrides**
  - Depends on: numpy_testing
  - Required by: numpy__core, numpy__core_overrides, numpy__core_umath, numpy_lib, numpy_lib_recfunctions

- **numpy_version**
  - Depends on: numpy, numpy__configtool, numpy__core, numpy_core__multiarray_umath, numpy_f2py___version__

## Critical Modules

Modules that are most heavily depended upon (high-priority targets):

- **numpy** - 43 modules depend on it
- **numpy_lib** - 26 modules depend on it
- **numpy__core** - 20 modules depend on it
- **numpy_lib__npyio_impl** - 10 modules depend on it
- **numpy_ma_tests_test_core** - 10 modules depend on it
- **numpy_lib__function_base_impl** - 10 modules depend on it
- **numpy__typing** - 9 modules depend on it
- **numpy_lib_tests_test_io** - 9 modules depend on it
- **numpy_lib__index_tricks_impl** - 9 modules depend on it
- **numpy__core_numeric** - 9 modules depend on it
- **numpy_lib__polynomial_impl** - 9 modules depend on it
- **numpy_lib__shape_base_impl** - 9 modules depend on it
- **numpy_f2py_f2py2e** - 9 modules depend on it
- **numpy_polynomial** - 8 modules depend on it
- **numpy_linalg__linalg** - 8 modules depend on it
- **numpy_ma_core** - 7 modules depend on it
- **numpy_lib_tests_test_function_base** - 7 modules depend on it
- **numpy__core_defchararray** - 7 modules depend on it
- **numpy_f2py_rules** - 7 modules depend on it
- **numpy_polynomial_legendre** - 6 modules depend on it

## Implementation Strategy

1. **Start with Level 0**: Port all foundation modules that have no dependencies
2. **Progress level by level**: Complete each level before moving to the next
3. **Prioritize critical modules**: Within each level, prioritize modules that many others depend on
4. **Test incrementally**: Verify each module works correctly before moving on
5. **Document interfaces**: Clearly document the Lean interfaces for each ported module
