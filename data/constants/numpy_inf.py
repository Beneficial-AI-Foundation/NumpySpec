"""IEEE 754 floating point representation of (positive) infinity.

Returns
-------
y : float
    A floating point representation of positive infinity.

See Also
--------
isinf : Shows which elements are positive or negative infinity
isposinf : Shows which elements are positive infinity
isneginf : Shows which elements are negative infinity
isnan : Shows which elements are Not a Number
isfinite : Shows which elements are finite (not one of Not a Number, positive infinity and negative infinity)

Notes
-----
NumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic (IEEE 754). This means that Not a Number is not equivalent to infinity. Also that positive infinity is not equivalent to negative infinity. But infinity is equivalent to positive infinity.
"""

inf = float("inf")
