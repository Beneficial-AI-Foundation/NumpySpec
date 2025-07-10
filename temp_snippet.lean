-- Test bitwise operators
example : Int := 13 ||| 16  -- Should be 29
example : Int := 13 &&& 16  -- Should be 0
example : Int := 13 ^^^ 16  -- Should be 29 (XOR)