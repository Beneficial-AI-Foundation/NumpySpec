import pytest
from pathlib import Path
from gaussianspec.subagents import TranslatePageSubagent


def test_translate_first_page(tmp_path: Path):
    # Prepare fake OCR txt with two pages separated by form-feed
    txt = "Page ONE line 1\nPage ONE line 2\fPage TWO line 1"
    txt_path = tmp_path / "sample.txt"
    txt_path.write_text(txt)

    out_dir = tmp_path / "out"

    res = TranslatePageSubagent(txt_path=txt_path, page_num=1, out_dir=out_dir).run()

    assert res.success, f"Translation failed: {res.error}"
    assert res.out_file.exists(), "Output Lean file was not created"

    content = res.out_file.read_text()
    # The Lean file should wrap the original text in a comment block
    assert "Page ONE line 1" in content
    assert content.startswith("/-") and content.rstrip().endswith("-/"), (
        "Not wrapped in Lean comment"
    )
