# Justfile for GaussianSpec project
# Usage: just run


# Local lake build (rare)
build-local:
    lake build

# Build all Lean targets
build-all:
    lake build allLibs

# Test suite
test:
    uv run -m pytest -q

# Train PPO on LeanEnv for 1k steps (quick smoke)
train steps='1000':
    uv run src/gaussianspec/rl_trainer.py --steps {{steps}}



# Pull latest MorphCloud examples worktree
pull-morph:
	git -C external/morphcloud-examples-public pull --ff-only

# ---------------------------------------------
#  Developer environment bootstrapping
# ---------------------------------------------

# Install Rust/cargo, elan (Lean toolchain manager) and uv (Python dependency
# manager) in one go. By default PATH additions are appended to `$HOME/.zshrc`.
#
# Usage:
#   just bootstrap
#   just bootstrap rc_file="$HOME/.bashrc"
bootstrap rc_file='$HOME/.zshrc':
    #!/usr/bin/env bash
    set -euo pipefail

    # 1. Rust + cargo -------------------------------------------------
    if ! command -v cargo >/dev/null; then
        curl https://sh.rustup.rs -sSf | sh -s -- -y
        source "$HOME/.cargo/env"
    fi
    cargo --version

    # 2. Elan (Lean toolchain manager) -------------------------------
    if ! command -v elan >/dev/null; then
        curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
            | bash -s -- --default-toolchain leanprover/lean4:stable --no-modify-path -y
        source "$HOME/.elan/env"
    fi
    elan --version

    # 3. uv (Python dep manager) -------------------------------------
    if ! command -v uv >/dev/null; then
        curl -Ls https://astral.sh/uv/install.sh | bash
    fi
    uv --version

    # 4. Persist PATH additions -------------------------------------
    if ! grep -q "# Devin toolchain" "{{rc_file}}" 2>/dev/null; then
        echo '# Devin toolchain — cargo / elan / uv' >> "{{rc_file}}"
        echo 'export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"' >> "{{rc_file}}"
    fi

    # 5. Final verification -----------------------------------------
    echo "✔ Installed tools:"
    which cargo
    which elan
    which uv

# ---------------------------------------------
#  Dependency management
# ---------------------------------------------

sync:
    uv sync

# ---------------------------------------------
#  Linting & Git hooks (Ruff)
# ---------------------------------------------

# Run Ruff with auto-fix, then format.  Useful in CI or locally.
lint:
    uv run ruff check --fix .
    uv run ruff format .

# Install local git hooks (points core.hooksPath to .githooks)
install-hooks:
    git config core.hooksPath .githooks
