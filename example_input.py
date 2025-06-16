"""
Example Python program for testing LLM-based Lean generation.

This file contains a simple Python function that will be used to test
the Python -> Lean code -> Lean spec pipeline.
"""

def factorial(n: int) -> int:
    """
    Calculate the factorial of a non-negative integer.
    
    The factorial of n (denoted n!) is the product of all positive integers 
    less than or equal to n. By definition, 0! = 1.
    
    Args:
        n: A non-negative integer
        
    Returns:
        The factorial of n
        
    Raises:
        ValueError: If n is negative
    """
    if n < 0:
        raise ValueError("Factorial is not defined for negative numbers")
    if n == 0 or n == 1:
        return 1
    
    result = 1
    for i in range(2, n + 1):
        result *= i
    return result
