"""IEEE 754 floating point representation of Not a Number (NaN).

Returns
-------
y : float
    A floating point representation of Not a Number.

See Also
--------
isnan : Shows which elements are Not a Number.

isfinite : Shows which elements are finite (not one of Not a Number, positive infinity and negative infinity)

Notes
-----
NumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic (IEEE 754). This means that Not a Number is not equivalent to infinity.
"""

nan = float("nan")
