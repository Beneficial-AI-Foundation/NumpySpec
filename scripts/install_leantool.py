import subprocess, sys, tempfile, shutil, pathlib, re
from pathlib import Path


def main():
    repo_url = "https://github.com/GasStationManager/LeanTool.git"
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        subprocess.check_call(["git", "clone", "--depth", "1", repo_url, str(tmp_path)])
        pyproj = tmp_path / "pyproject.toml"
        text = pyproj.read_text()
        # Replace pantograph direct-url with version constraint
        text = re.sub(r"pantograph\s*=\s*\{[^}]*\}", 'pantograph = ">=0.3.0"', text)
        pyproj.write_text(text)
        # Delete top-level leantool.py that conflicts with leantool package dir during build
        dupe = tmp_path / "leantool.py"
        if dupe.exists():
            dupe.unlink()
        subprocess.check_call(["uv", "pip", "install", str(tmp_path)])


if __name__ == "__main__":
    main()
