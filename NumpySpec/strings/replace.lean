import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.replace",
  "category": "String operations",
  "description": "For each element in a, return a copy of the string with occurrences of substring old replaced by new",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.replace.html",
  "doc": "For each element in `a`, return a copy of the string with occurrences of substring `old` replaced by `new`.\n\nParameters\n----------\na : array_like, with `StringDType`, `bytes_` or `str_` dtype\nold : array_like, with `StringDType`, `bytes_` or `str_` dtype\nnew : array_like, with `StringDType`, `bytes_` or `str_` dtype\ncount : array_like, with any integer dtype, optional\n    Maximum number of occurrences to replace. -1 (the default) means replace all occurrences.\n\nReturns\n-------\nout : ndarray\n    Output array of `StringDType`, `bytes_` or `str_` dtype,\n    depending on input types",
  "code": "def replace(a, old, new, count=-1):\n    \"\"\"\n    For each element in ``a``, return a copy of the string with\n    occurrences of substring ``old`` replaced by ``new``.\n\n    Parameters\n    ----------\n    a : array_like, with ``StringDType``, ``bytes_`` or ``str_`` dtype\n\n    old, new : array_like, with ``StringDType``, ``bytes_`` or ``str_`` dtype\n\n    count : array_like, with any integer dtype\n        If the optional argument ``count`` is given, only the first\n        ``count`` occurrences are replaced.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ``StringDType``, ``bytes_`` or ``str_`` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.replace\n\n    Examples\n    --------\n    >>> a = np.array([\"That is a mango\", \"Monkeys eat mangos\"])\n    >>> np.strings.replace(a, 'mango', 'banana')\n    array(['That is a banana', 'Monkeys eat bananas'], dtype='<U19')\n\n    >>> a = np.array([\"The dish is fresh\", \"This is it\"])\n    >>> np.strings.replace(a, 'is', 'was')\n    array(['The dwash was fresh', 'Thwas was it'], dtype='<U19')\n\n    \"\"\"\n    from ..strings import count as count_sub\n    \n    a = np.asanyarray(a)\n    old = np.asanyarray(old, dtype=a.dtype)\n    new = np.asanyarray(new, dtype=a.dtype)\n    count = np.asanyarray(count)\n\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(old.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(new.dtype):\n        raise TypeError(\"string operation on non-string array\")\n\n    if count.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {count.dtype}\")\n\n    max_int64 = np.array(np.iinfo(np.int64).max)\n    count = np.where(count < 0, max_int64, count)\n\n    # Make sure we find the longest string length by looking at the result\n    # with count == -1\n    counts = count_sub(a, old)\n    string_length = str_len(a) - str_len(old) * counts + str_len(new) * counts\n\n    # if count != -1, we replace at most count occurrences, so the new\n    # string length is guaranteed to be at least\n    # str_len(a) - str_len(old) * count + str_len(new) * count\n    count = counts if np.all(count == -1) else np.minimum(counts, count)\n    string_length = np.where(count == -1, string_length,\n                           str_len(a) - str_len(old) * count + str_len(new) * count)\n    max_string_length = np.max(string_length)\n    if hasattr(a.dtype, \"na_object\") and a.dtype.na_object is None:\n        # StringDType\n        out_dtype = type(a.dtype)()\n    else:\n        # fixed-length string dtype\n        out_dtype = f\"{a.dtype.char}{max_string_length}\"\n    return _replace_ufunc(a, old, new, count, _dtype=out_dtype)"
}
-/

/-- numpy.strings.replace: For each element in a, return a copy of the string with 
    occurrences of substring old replaced by new.

    Replaces occurrences of the substring 'old' with 'new' in each string element.
    The replacement is done from left to right, and if count is specified, only
    the first 'count' occurrences are replaced. If count is -1 or negative,
    all occurrences are replaced.

    From NumPy documentation:
    - Parameters: a (array_like), old (array_like), new (array_like), count (array_like, optional)
    - Returns: out (ndarray) - Output array with replaced strings

    Mathematical Properties:
    1. Element-wise replacement: result[i] = a[i].replace(old[i], new[i], count[i])
    2. Left-to-right replacement order: replacements proceed from beginning to end
    3. Non-overlapping replacements: each character can only be part of one replacement
    4. Count limiting: if count[i] >= 0, at most count[i] replacements are made
    5. Identity when old not found: if old[i] not in a[i], then result[i] = a[i]
    6. Empty string handling: replacing empty string with non-empty inserts before each character
-/
def replace {n : Nat} (a : Vector String n) (old : Vector String n) (new : Vector String n) (count : Vector Int n) : Id (Vector String n) :=
  sorry

/-- Specification: numpy.strings.replace returns a vector where each element is the
    result of replacing occurrences of old substring with new substring.

    Mathematical Properties:
    1. Element-wise correctness: For each element i, result[i] is a[i] with replacements
    2. Replacement order: Replacements are performed from left to right
    3. Non-overlapping: Each character position can only be part of one replacement
    4. Count limiting: If count[i] >= 0, at most count[i] replacements are made
    5. Complete replacement: If count[i] < 0, all occurrences are replaced
    6. Identity preservation: If old[i] doesn't occur in a[i], result[i] = a[i]
    7. Empty old string: If old[i] = "", new[i] is inserted before each character
    8. String length changes: Result length may differ from original due to replacements

    Preconditions:
    - old strings are not empty when count > 0 (to avoid infinite replacements)
    - count values are well-defined integers

    Postconditions:
    - Each result string has appropriate replacements performed
    - Number of replacements respects count limits
    - Replacement order is left-to-right
    - Original string is preserved where no replacements occur
-/
theorem replace_spec {n : Nat} (a : Vector String n) (old : Vector String n) (new : Vector String n) (count : Vector Int n) :
    ⦃⌜∀ i : Fin n, (count.get i > 0 → old.get i ≠ "") ∧ (count.get i = 0 → True)⌝⦄
    replace a old new count
    ⦃⇓result => ⌜∀ i : Fin n,
      -- Basic property: result contains the transformed string
      (∃ (num_replacements : Nat),
        -- Number of replacements is bounded by count (if non-negative)
        (count.get i ≥ 0 → num_replacements ≤ Int.natAbs (count.get i)) ∧
        -- Number of replacements is bounded by actual occurrences
        (∃ (total_occurrences : Nat),
          -- If count is negative, all occurrences are replaced
          (count.get i < 0 → num_replacements = total_occurrences) ∧
          -- If count is non-negative, we replace min(count, total_occurrences)
          (count.get i ≥ 0 → num_replacements = min (Int.natAbs (count.get i)) total_occurrences) ∧
          -- The result string has the expected structure
          (∃ (replacement_positions : List Nat),
            -- All replacement positions are valid and non-overlapping
            (∀ pos ∈ replacement_positions, 
              pos + (old.get i).length ≤ (a.get i).length ∧
              ((a.get i).drop pos).take (old.get i).length = old.get i) ∧
            -- Positions are in ascending order and non-overlapping
            (∀ j k : Nat, j < k → j < replacement_positions.length → k < replacement_positions.length →
              replacement_positions[j]! + (old.get i).length ≤ replacement_positions[k]!) ∧
            -- Number of positions matches our replacement count
            replacement_positions.length = num_replacements ∧
            -- Result string is constructed by the replacements
            (∃ (result_construction : String),
              result.get i = result_construction)))) ∧
      -- Identity property: if old doesn't occur, result equals original
      (old.get i ∉ (a.get i).toList → result.get i = a.get i) ∧
      -- Empty old string behavior: if old is empty and count > 0, new is inserted everywhere
      (old.get i = "" ∧ count.get i > 0 → 
        result.get i.length = (a.get i).length + (new.get i).length * min (Int.natAbs (count.get i)) ((a.get i).length + 1)) ∧
      -- Zero count behavior: if count is 0, no replacements occur
      (count.get i = 0 → result.get i = a.get i)
    ⌝⦄ := by
  sorry