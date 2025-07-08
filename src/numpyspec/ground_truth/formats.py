"""Data formats for ground truth specifications."""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Union
import json
import numpy as np


@dataclass
class GroundTruthData:
    """Container for a single ground truth test case."""
    operation: str
    inputs: Dict[str, Any]
    output: Any
    dtype: Optional[str] = None
    shape: Optional[tuple] = None
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        result = {
            "operation": self.operation,
            "inputs": self._serialize_value(self.inputs),
            "output": self._serialize_value(self.output),
        }
        if self.dtype:
            result["dtype"] = self.dtype
        if self.shape:
            result["shape"] = self.shape
        if self.metadata:
            result["metadata"] = self.metadata
        return result
    
    def _serialize_value(self, value: Any) -> Any:
        """Serialize numpy arrays and other values for JSON."""
        if isinstance(value, dict):
            return {k: self._serialize_value(v) for k, v in value.items()}
        elif isinstance(value, (list, tuple)):
            return [self._serialize_value(v) for v in value]
        elif isinstance(value, np.ndarray):
            return {
                "type": "ndarray",
                "data": value.tolist(),
                "dtype": str(value.dtype),
                "shape": value.shape,
            }
        elif isinstance(value, (np.integer, np.floating)):
            return float(value) if isinstance(value, np.floating) else int(value)
        else:
            return value


@dataclass
class OperationSpec:
    """Specification for a NumPy operation."""
    name: str
    numpy_func: str
    description: str
    test_cases: List[GroundTruthData] = field(default_factory=list)
    lean_implementation: Optional[str] = None
    properties: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            "name": self.name,
            "numpy_func": self.numpy_func,
            "description": self.description,
            "test_cases": [tc.to_dict() for tc in self.test_cases],
            "lean_implementation": self.lean_implementation,
            "properties": self.properties,
        }
    
    def to_json(self, indent: int = 2) -> str:
        """Convert to JSON string."""
        return json.dumps(self.to_dict(), indent=indent)
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "OperationSpec":
        """Create from dictionary."""
        test_cases = [
            GroundTruthData(
                operation=tc["operation"],
                inputs=tc["inputs"],
                output=tc["output"],
                dtype=tc.get("dtype"),
                shape=tc.get("shape"),
                metadata=tc.get("metadata", {}),
            )
            for tc in data.get("test_cases", [])
        ]
        
        return cls(
            name=data["name"],
            numpy_func=data["numpy_func"],
            description=data["description"],
            test_cases=test_cases,
            lean_implementation=data.get("lean_implementation"),
            properties=data.get("properties", {}),
        )
