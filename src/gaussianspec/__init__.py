try:
    from .rl_env import LeanEnv, EditLibrary
except ModuleNotFoundError:  # optional gymnasium dependency
    LeanEnv = None  # type: ignore
    EditLibrary = None  # type: ignore

# Auto-load environment variables from a local .env if present
try:
    from pathlib import Path
    from dotenv import load_dotenv

    env_path = Path(__file__).resolve().parent.parent.parent / ".env"
    if env_path.exists():
        load_dotenv(dotenv_path=env_path)  # type: ignore[call-arg]
except ModuleNotFoundError:
    # python-dotenv is optional; skip if absent
    pass


def main() -> None:
    print("Hello from gaussianspec!")
