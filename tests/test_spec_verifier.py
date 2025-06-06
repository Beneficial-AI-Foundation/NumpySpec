import json
from pathlib import Path
from unittest.mock import patch

from gaussianspec.spec_verifier import verify_specs_from_json, SpecEvaluation
from gaussianspec.subagents import LeanBuildResult


def test_verify_specs(tmp_path: Path):
    data = [
        {
            "docstring": "Add one function",
            "python": "def add_one(n: int) -> int:\n    return n + 1",
            "lean_function": "def addOne (n : Nat) : Nat := n + 1",
            "lean_spec": "theorem addOne_spec (n : Nat) : addOne n = n + 1 := by rfl",
        }
    ]
    json_path = tmp_path / "specs.json"
    json_path.write_text(json.dumps(data))

    with patch('gaussianspec.subagents.LeanRemoteBuildSubagent.run') as mock_run:
        mock_run.return_value = LeanBuildResult(True, "ok")
        results = verify_specs_from_json(json_path)

    assert len(results) == 1
    res = results[0]
    assert isinstance(res, SpecEvaluation)
    assert res.docstring == "Add one function"
    assert res.success
