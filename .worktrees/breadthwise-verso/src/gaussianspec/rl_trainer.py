from __future__ import annotations
"""Simple PPO trainer for LeanEnv.

Usage:
    uv run src/gaussianspec/rl_trainer.py --steps 10000

The trainer loads a tiny GPT‑2 policy via stable‑baselines3's MLP (text encoded)
for now. This is a placeholder until we integrate Kimina‑Prover as policy.
"""

import argparse
from pathlib import Path

import gymnasium as gym  # type: ignore
from stable_baselines3 import PPO  # type: ignore
from stable_baselines3.common.env_util import make_vec_env  # type: ignore

from .rl_env import LeanEnv, EditLibrary
from .agent import LeanEdit


def build_env(project_root: Path) -> gym.Env:
    # Minimal library with a no‑op edit (comment append)
    edit = LeanEdit(
        file=project_root / "GaussianSpec.lean",
        edit="-- noop\n",
        description="No‑op append comment",
    )
    lib = EditLibrary((edit,))
    return LeanEnv(project_root=project_root, edit_library=lib, max_steps=10)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=10000)
    parser.add_argument("--project-root", type=Path, default=Path(__file__).parent.parent.parent)
    args = parser.parse_args()

    env = make_vec_env(lambda: build_env(args.project_root), n_envs=1)
    model = PPO("MlpPolicy", env, verbose=1)
    model.learn(total_timesteps=args.steps)
    save_path = Path("models/ppo_leanenv")
    save_path.parent.mkdir(parents=True, exist_ok=True)
    model.save(save_path)
    print(f"Model saved to {save_path}")


if __name__ == "__main__":
    main() 