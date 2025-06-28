# Justfile for NumpySpec project
# Usage: just <command>

# Settings
set dotenv-load := true
set shell := ["bash", "-uc"]
set windows-shell := ["powershell.exe", "-NoLogo", "-Command"]

# Variables
home_dir := env_var('HOME')
cargo_bin := join(home_dir, ".cargo", "bin")
elan_bin := join(home_dir, ".elan", "bin") 
local_bin := join(home_dir, ".local", "bin")
export PATH := local_bin + ":" + elan_bin + ":" + cargo_bin + ":" + env_var('PATH')

# Platform detection
is_ci := if env("GITHUB_ACTIONS", "false") == "true" { "true" } else { "false" }
is_macos := if os() == "macos" { "true" } else { "false" }
is_linux := if os() == "linux" { "true" } else { "false" }
is_windows := if os() == "windows" { "true" } else { "false" }
shell_name := if os() == "windows" { "powershell" } else { env("SHELL", "/bin/bash") }

# Default recipe shows help
default:
    @just --list


# ---------------------------------------------
#  Core Commands
# ---------------------------------------------

# Build Lean project
build: setup-lean
    lake build --try-cache

# Run Python test suite  
test: setup-python
    uv run -m pytest -q

# Run linting and formatting
lint: setup-python
    uv run ruff check --fix .
    uv run ruff format .

# ---------------------------------------------
#  Setup Commands
# ---------------------------------------------

# Main setup entrypoint
setup:
    @if [ "{{is_ci}}" = "true" ]; then just _setup-ci; else just _setup-local; fi

# CI-specific setup
[private]
_setup-ci: _install-system-deps _ensure-rust _ensure-elan _ensure-uv install-cli-tools setup-python setup-lean verify-setup
    @echo "🏭 CI setup complete!"
    @echo "$HOME/.cargo/bin" >> $GITHUB_PATH
    @echo "$HOME/.elan/bin" >> $GITHUB_PATH
    @echo "$HOME/.local/bin" >> $GITHUB_PATH

# Local developer setup
[private]
_setup-local: _ensure-rust _ensure-elan _ensure-uv install-cli-tools setup-python setup-lean verify-setup
    @echo "💻 Local setup complete!"
    @just _update-shell-rc

# Install system dependencies (Linux only)
[private]
_install-system-deps:
    #!/usr/bin/env bash
    if [[ "{{os()}}" == "linux" ]]; then
        sudo apt-get update
        sudo apt-get install -y build-essential pkg-config libssl-dev
    fi

# Update shell RC file with PATH
[private]
_update-shell-rc:
    #!/usr/bin/env bash
    RC_FILE=$(if [[ "{{shell_name}}" == *"zsh"* ]]; then echo "$HOME/.zshrc"; elif [[ "{{shell_name}}" == *"bash"* ]]; then echo "$HOME/.bashrc"; else echo "$HOME/.profile"; fi)
    if ! grep -q "# NumpySpec toolchain" "$RC_FILE" 2>/dev/null; then
        echo '# NumpySpec toolchain — cargo / elan / uv' >> "$RC_FILE"
        echo 'export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"' >> "$RC_FILE"
        echo "✅ Added PATH to $RC_FILE - restart your shell or run: source $RC_FILE"
    fi

# ---------------------------------------------
#  Tool Installation
# ---------------------------------------------

# Ensure Rust is installed
[private]
_ensure-rust:
    #!/usr/bin/env bash
    if ! command -v cargo >/dev/null 2>&1; then
        echo "📦 Installing Rust..."
        curl https://sh.rustup.rs -sSf | sh -s -- -y --no-modify-path
        source "$HOME/.cargo/env"
    fi

# Ensure Elan is installed
[private]
_ensure-elan:
    #!/usr/bin/env bash
    if ! command -v elan >/dev/null 2>&1; then
        echo "📦 Installing Elan..."
        curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
            bash -s -- --default-toolchain leanprover/lean4:stable --no-modify-path -y
    fi

# Ensure UV is installed
[private]
_ensure-uv:
    #!/usr/bin/env bash
    if ! command -v uv >/dev/null 2>&1; then
        echo "📦 Installing uv..."
        curl -LsSf https://astral.sh/uv/install.sh | sh
    fi

# Install a single cargo tool if not present
[private]
_install-cargo-tool package cmd:
    #!/usr/bin/env bash
    if ! command -v "{{cmd}}" >/dev/null 2>&1; then
        echo "Installing {{package}}..."
        cargo install --locked "{{package}}" || echo "⚠️  Failed to install {{package}}"
    fi

# Install a single brew tool if not present (macOS only)
[private]
_install-brew-tool package:
    #!/usr/bin/env bash
    if ! command -v "{{package}}" >/dev/null 2>&1; then
        echo "Installing {{package}}..."
        brew install "{{package}}" || echo "⚠️  Failed to install {{package}}"
    fi

# Install CLI tools
install-cli-tools: _ensure-rust
    @echo "📦 Installing CLI tools..."
    @just _install-cargo-tool "ripgrep" "rg"
    @just _install-cargo-tool "fd-find" "fd"
    @just _install-cargo-tool "bat" "bat"
    @just _install-cargo-tool "eza" "eza"
    @just _install-cargo-tool "starship" "starship"
    @just _install-cargo-tool "du-dust" "dust"
    @just _install-cargo-tool "bottom" "btm"
    @just _install-cargo-tool "gitui" "gitui"
    @just _install-cargo-tool "ast-grep" "ast-grep"
    {{ if is_macos == "true" { "@just _install-brew-tool terminal-notifier" } else { "" } }}

# ---------------------------------------------
#  Language-Specific Setup
# ---------------------------------------------

# Setup Python environment
setup-python: _ensure-uv
    @echo "🐍 Setting up Python environment..."
    uv venv
    uv sync
    uv add --dev pytest pytest-asyncio pytest-cov

# Setup Lean environment
setup-lean: _ensure-elan cache-setup
    @echo "📐 Setting up Lean environment..."
    elan self update || true
    elan default leanprover/lean4:stable
    lake build --try-cache

# Setup build caches for faster compilation
cache-setup:
    @echo "🔄 Setting up build caches..."
    @echo "📦 Attempting to download pre-built dependencies..."
    -@lake build --try-cache --no-build
    @just _fetch-mathlib-cache
    @echo "✅ Cache setup complete"

# Fetch mathlib cache if available
[private]
_fetch-mathlib-cache:
    #!/usr/bin/env bash
    if grep -q "mathlib" lake-manifest.json 2>/dev/null; then
        echo "📚 Fetching mathlib cache..."
        if lake exe cache --help >/dev/null 2>&1; then
            lake exe cache get || echo "⚠️  Failed to fetch mathlib cache"
        else
            echo "ℹ️  Mathlib cache tool not available"
        fi
    fi

# ---------------------------------------------
#  Verification & Info
# ---------------------------------------------

# Verify tool versions
[private]
_check-tool cmd name:
    @command -v {{cmd}} >/dev/null && {{cmd}} --version || echo "❌ {{name}} not found"

# Verify all tools are installed correctly
verify-setup:
    @echo "🔍 Verifying installation..."
    @echo ""
    @echo "=== Core Tools ==="
    @just _check-tool "cargo" "cargo"
    @just _check-tool "elan" "elan"
    @just _check-tool "lean" "lean"
    @just _check-tool "lake" "lake"
    @just _check-tool "uv" "uv"
    @just _check-tool "python" "python"
    @echo ""
    @echo "=== CLI Tools ==="
    @command -v rg >/dev/null && rg --version | head -1 || echo "❌ ripgrep not found"
    @command -v fd >/dev/null && fd --version || echo "❌ fd not found"
    @command -v bat >/dev/null && bat --version | head -1 || echo "❌ bat not found"
    @echo ""
    @echo "✅ Setup verification complete!"

# Show system information
info:
    @echo "📊 System information:"
    @echo "OS: {{os()}} ({{os_family()}})"
    @echo "Arch: {{arch()}}"
    @echo "CPUs: {{num_cpus()}}"
    @echo "Shell: {{shell_name}}"
    @echo "Home: {{home_dir}}"
    @echo "Just: {{just_executable()}} at {{justfile()}}"
    @echo "Working dir: {{invocation_directory()}}"
    @echo ""
    @echo "=== Environment ==="
    @echo "CI: {{is_ci}}"
    @echo "PATH: {{env_var('PATH')}}"
    @echo ""
    @echo "=== Tool Versions ==="
    @-python --version
    @-lean --version
    @-lake --version
    @-uv --version
    @-cargo --version

# ---------------------------------------------
#  Maintenance
# ---------------------------------------------

# Clean build artifacts
clean:
    lake clean
    -rm -rf .cache 
    -rm -f logs/*.log

# Install local git hooks
install-hooks:
    git config core.hooksPath .githooks

# Create a new release (GitHub)
release version:
    @echo "📦 Creating release {{version}}..."
    lake upload {{version}}

# Update dependencies
update:
    @echo "📦 Updating dependencies..."
    lake update
    uv sync --upgrade

# Run all checks (build, test, lint)
check: build test lint
    @echo "✅ All checks passed!"

# Watch for changes and rebuild
watch:
    @echo "👀 Watching for changes..."
    watchexec -e lean,toml,json -- just build

# Format all code
fmt: lint
    @echo "✨ Code formatted!"

# Run specific test
test-one name:
    uv run -m pytest -k {{name}} -v

# Show outdated dependencies
outdated:
    @echo "=== Python Dependencies ==="
    @-uv pip list --outdated
    @echo ""
    @echo "=== Lean Dependencies ==="
    @-lake update --dry-run