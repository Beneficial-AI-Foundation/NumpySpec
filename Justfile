# Justfile for NumpySpec project
# Usage: just <command>

# Default recipe shows help
default:
    @just --list

# Build Lean project
build:
    lake build --try-cache

# Run Python test suite
test:
    uv run -m pytest -q

# Setup build caches for faster compilation
cache-setup:
    #!/usr/bin/env bash
    set -euo pipefail
    
    echo "🔄 Setting up build caches..."
    
    # Try to download release builds for dependencies
    echo "📦 Attempting to download pre-built dependencies..."
    lake build --try-cache --no-build || true
    
    # If mathlib is in the manifest, try to get its cache
    if grep -q "mathlib" lake-manifest.json 2>/dev/null; then
        echo "📚 Fetching mathlib cache..."
        if lake exe cache --help >/dev/null 2>&1; then
            lake exe cache get || echo "⚠️  Failed to fetch mathlib cache"
        else
            echo "ℹ️  Mathlib cache tool not available"
        fi
    fi
    
    echo "✅ Cache setup complete"

# ---------------------------------------------
#  Setup (for CI and local)
# ---------------------------------------------

# Main setup entrypoint - detects environment and runs appropriate setup
setup:
    #!/usr/bin/env bash
    set -euo pipefail
    
    # Detect if we're in CI or local environment
    if [ "${GITHUB_ACTIONS:-false}" = "true" ]; then
        echo "🏭 Running CI setup..."
        just setup-ci
    else
        echo "💻 Running local setup..."
        just setup-local
    fi

# CI-specific setup (GitHub Actions)
setup-ci:
    #!/usr/bin/env bash
    set -euo pipefail
    
    # System dependencies based on runner OS
    if [[ "$OSTYPE" == "linux-gnu"* ]]; then
        sudo apt-get update
        sudo apt-get install -y build-essential pkg-config libssl-dev
    fi
    
    # Run common setup
    just _setup-common
    
    # CI-specific: Add to GITHUB_PATH instead of shell RC
    echo "$HOME/.cargo/bin" >> $GITHUB_PATH
    echo "$HOME/.elan/bin" >> $GITHUB_PATH  
    echo "$HOME/.local/bin" >> $GITHUB_PATH

# Local developer setup
setup-local:
    #!/usr/bin/env bash
    set -euo pipefail
    
    # Detect shell RC file
    if [[ "$SHELL" == *"zsh"* ]]; then
        RC_FILE="$HOME/.zshrc"
    elif [[ "$SHELL" == *"bash"* ]]; then
        RC_FILE="$HOME/.bashrc"
    else
        RC_FILE="$HOME/.profile"
    fi
    
    # Run common setup
    just _setup-common
    
    # Add to shell RC if not already present
    if ! grep -q "# NumpySpec toolchain" "$RC_FILE" 2>/dev/null; then
        echo '# NumpySpec toolchain — cargo / elan / uv' >> "$RC_FILE"
        echo 'export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"' >> "$RC_FILE"
        echo "✅ Added PATH to $RC_FILE - restart your shell or run: source $RC_FILE"
    fi

# Common setup logic (private recipe, called by others)
_setup-common:
    #!/usr/bin/env bash
    set -euo pipefail
    
    # Ensure paths are available in current session
    export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
    
    # 1. Rust + cargo
    if ! command -v cargo >/dev/null 2>&1; then
        echo "📦 Installing Rust..."
        curl https://sh.rustup.rs -sSf | sh -s -- -y --no-modify-path
        source "$HOME/.cargo/env"
    fi
    
    # 2. Elan (Lean toolchain manager)
    if ! command -v elan >/dev/null 2>&1; then
        echo "📦 Installing Elan..."
        curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
            bash -s -- --default-toolchain leanprover/lean4:stable --no-modify-path -y
    fi
    
    # 3. uv (Python package manager)
    if ! command -v uv >/dev/null 2>&1; then
        echo "📦 Installing uv..."
        curl -LsSf https://astral.sh/uv/install.sh | sh
    fi
    
    # 4. CLI tools
    just install-cli-tools
    
    # 5. Python setup
    just setup-python
    
    # 6. Lean setup  
    just setup-lean
    
    # 7. Verify everything
    just verify-setup

# Install CLI tools (ripgrep, fd, etc.)
install-cli-tools:
    #!/usr/bin/env bash
    set -euo pipefail
    
    echo "📦 Installing CLI tools..."
    
    # Ensure cargo is in PATH
    export PATH="$HOME/.cargo/bin:$PATH"
    
    # Install tools via cargo (skip if already installed)
    # Format: package_name:command_name
    tools=(
        "ripgrep:rg"
        "fd-find:fd"
        "bat:bat"
        "eza:eza"
        "starship:starship"
        "du-dust:dust"
        "bottom:btm"
        "gitui:gitui"
        "ast-grep:ast-grep"
    )
    
    for tool_spec in "${tools[@]}"; do
        IFS=':' read -r tool cmd <<< "$tool_spec"
        if ! command -v "$cmd" >/dev/null 2>&1; then
            echo "Installing $tool..."
            cargo install --locked "$tool" || echo "⚠️  Failed to install $tool"
        fi
    done
    

    if [[ "$OSTYPE" == "darwin"* ]]; then
        if ! command -v terminal-notifier >/dev/null 2>&1; then
            brew install terminal-notifier || echo "⚠️  Failed to install terminal-notifier"
        fi
    fi

# Setup Python environment
setup-python:
    #!/usr/bin/env bash
    set -euo pipefail
    
    echo "🐍 Setting up Python environment..."
    export PATH="$HOME/.local/bin:$PATH"
    
    # Create virtual environment and install dependencies
    uv venv
    uv sync
    
    # Install development dependencies
    uv add --dev pytest pytest-asyncio pytest-cov

# Setup Lean environment
setup-lean:
    #!/usr/bin/env bash
    set -euo pipefail
    
    echo "📐 Setting up Lean environment..."
    export PATH="$HOME/.elan/bin:$PATH"
    
    # Update elan and install lean toolchain
    elan self update || true
    elan default leanprover/lean4:stable
    
    # Setup caches
    just cache-setup
    
    # Build the project
    lake build --try-cache

# Verify all tools are installed correctly
verify-setup:
    #!/usr/bin/env bash
    set -euo pipefail
    
    echo "🔍 Verifying installation..."
    echo ""
    
    # Core tools
    echo "=== Core Tools ==="
    command -v cargo >/dev/null && cargo --version || echo "❌ cargo not found"
    command -v elan >/dev/null && elan --version || echo "❌ elan not found"
    command -v lean >/dev/null && lean --version || echo "❌ lean not found"
    command -v lake >/dev/null && lake --version || echo "❌ lake not found"
    command -v uv >/dev/null && uv --version || echo "❌ uv not found"
    command -v python >/dev/null && python --version || echo "❌ python not found"
    
    echo ""
    echo "=== CLI Tools ==="
    command -v rg >/dev/null && rg --version | head -1 || echo "❌ ripgrep not found"
    command -v fd >/dev/null && fd --version || echo "❌ fd not found"
    command -v bat >/dev/null && bat --version | head -1 || echo "❌ bat not found"
    
    echo ""
    echo "✅ Setup verification complete!"



# ---------------------------------------------
#  Linting & Formatting
# ---------------------------------------------

# Run linting and formatting
lint:
    uv run ruff check --fix .
    uv run ruff format .

# Install local git hooks (points core.hooksPath to .githooks)
install-hooks:
    git config core.hooksPath .githooks

# ---------------------------------------------
#  Maintenance & Utilities
# ---------------------------------------------

# Clean build artifacts
clean:
    lake clean
    rm -rf .cache logs/*.log

# Show system information
info:
    @echo "📊 System information:"
    @echo "Python: $(python --version 2>&1)"
    @echo "Lean: $(lean --version 2>&1)"
    @echo "Lake: $(lake --version 2>&1)"
    @echo "UV: $(uv --version 2>&1)"
    @echo "Just: $(just --version 2>&1)"
