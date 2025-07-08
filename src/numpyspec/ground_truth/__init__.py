"""Ground truth data generation using NumPy.

This module provides utilities for generating test data pairs from NumPy operations
to serve as lightweight specifications for the Lean implementation.
"""

from .generator import GroundTruthGenerator
from .formats import GroundTruthData, OperationSpec

__all__ = [
    "GroundTruthGenerator",
    "GroundTruthData",
    "OperationSpec",
]
