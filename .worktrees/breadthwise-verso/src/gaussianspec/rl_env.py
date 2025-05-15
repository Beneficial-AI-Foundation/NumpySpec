from __future__ import annotations

"""Reinforcement-learning scaffolding for Lean agent.
Provides Gymnasium-compatible environment so that classical RL algorithms
(e.g. PPO, SAC) can be applied to Lean proof search / code synthesis tasks.

Key abstractions
----------------
State  : text observation (build feedback)
Action : index into a predefined edit library (`LeanEdit` templates)
Reward : +1 when build succeeds, -0.1 per step, -1 on build error

This is deliberately minimal; downstream projects can subclass
`LeanEnv` or wrap it with text encoders.
"""

from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple, Dict, Any, Optional

import gymnasium as gym
from gymnasium import spaces
import numpy as np

from .agent import (
    LeanEdit,
    run_lake_build,
    apply_lean_edit,
    parse_build_feedback,
)

Observation = str


@dataclass(frozen=True)
class EditLibrary:
    """Immutable collection of templated Lean edits."""

    edits: Tuple[LeanEdit, ...]

    def __len__(self) -> int:
        return len(self.edits)

    def __getitem__(self, idx: int) -> LeanEdit:
        return self.edits[idx]


class LeanEnv(gym.Env):
    """Gymnasium environment for Lean build-feedback interaction."""

    metadata = {"render_modes": ["ansi"], "render_fps": 4}

    def __init__(
        self,
        project_root: Path,
        edit_library: EditLibrary,
        max_steps: int = 50,
    ) -> None:
        super().__init__()
        self.project_root = project_root
        self.library = edit_library
        self.max_steps = max_steps

        # Discrete action space over edit templates
        self.action_space = spaces.Discrete(len(edit_library))
        # Observation: fixed-length uint8 vector (ASCII codes) so that Stable
        # Baselines's VecEnv can stack them into NumPy arrays.  We reserve 0 as
        # padding; printable ASCII starts at 32.
        self.obs_len = 1024
        self.observation_space = spaces.Box(
            low=0,
            high=255,
            shape=(self.obs_len,),
            dtype=np.uint8,
        )

        # Internal state
        self._step_count: int = 0
        self._last_feedback: str = "start"
        self._current_edit_idx: Optional[int] = None
        self._last_obs: np.ndarray = self._encode_obs("start")

    def reset(
        self, *, seed: Optional[int] = None, options: Optional[Dict[str, Any]] = None
    ):
        super().reset(seed=seed)
        self._step_count = 0
        self._last_feedback = "start"
        self._last_obs = self._encode_obs(self._last_feedback)
        obs = self._last_obs
        info = {}
        return obs, info

    def step(self, action: int):
        assert self.action_space.contains(action)
        self._current_edit_idx = action
        edit = self.library[action]
        apply_lean_edit(edit)
        build_result = run_lake_build(self.project_root)
        feedback = parse_build_feedback(build_result.output)
        self._last_feedback = feedback
        self._last_obs = self._encode_obs(feedback)

        # Reward shaping
        done = False
        reward = -0.1  # small step penalty
        if feedback == "success":
            reward = 1.0
            done = True
        elif "error:" in feedback:
            reward = -1.0
            done = True

        self._step_count += 1
        if self._step_count >= self.max_steps:
            done = True

        return self._last_obs, reward, done, False, {}

    def render(self, mode: str = "ansi"):
        if mode != "ansi":
            raise NotImplementedError
        return self._last_feedback

    def close(self):
        pass

    # --- helpers -------------------------------------------------

    def _encode_obs(self, text: str) -> np.ndarray:
        """Convert *text* into fixed-size ASCII-encoded NumPy vector."""
        arr = np.zeros(self.obs_len, dtype=np.uint8)
        encoded = text.encode("ascii", "ignore")[: self.obs_len]
        arr[: len(encoded)] = list(encoded)
        return arr
