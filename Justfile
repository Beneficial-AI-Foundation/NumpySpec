# Justfile for GaussianSpec project
# Usage: just run

# Ensure dependencies are installed and run the agent
run:
    uv sync
    uv run src/gaussianspec/agent.py

# Test suite
test:
    uv run -m pytest -q

# Train PPO on LeanEnv for 1k steps (quick smoke)
train steps='1000':
    uv run src/gaussianspec/rl_trainer.py --steps {{steps}}

# Check and install poppler if needed
check-poppler:
    #!/usr/bin/env bash
    if ! command -v pdftoppm &> /dev/null; then
        if [[ "$OSTYPE" == "darwin"* ]]; then
            brew install poppler
        elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
            if command -v apt-get &> /dev/null; then
                sudo apt-get install -y poppler-utils
            elif command -v yum &> /dev/null; then
                sudo yum install -y poppler-utils
            else
                echo "Unsupported Linux distribution"
                exit 1
            fi
        else
            echo "Unsupported OS"
            exit 1
        fi
    fi

# OCR pipeline (defaults to project textbook)
# page 149 is end of chapter 2, the first substantive chapter
ocr pages='1-149' pdf='textbook/Numerical_Recipes_in_C.pdf' method='auto' strip='1200': check-poppler
    uv run -m gaussianspec.pdf_pipeline {{pdf}} --pages {{pages}} --method {{method}} --strip-right {{strip}}

# OCR entire PDF in chunks
ocr-all chunk='50' pdf='textbook/Numerical_Recipes_in_C.pdf' method='auto' strip='1200':
    uv run -m gaussianspec.pdf_pipeline {{pdf}} --all --chunk-size {{chunk}} --method {{method}} --strip-right {{strip}}

# Bootstrap toolchain (install Rust/cargo, elan, and uv)
bootstrap rc_file='$HOME/.zshrc':
    #!/usr/bin/env bash
    set -euo pipefail
    
    # 1. Install Rust + cargo
    if ! command -v cargo >/dev/null; then
      curl https://sh.rustup.rs -sSf | sh -s -- -y
      source "$HOME/.cargo/env"
    fi
    cargo --version
    
    # 2. Install elan (Lean toolchain manager)
    if ! command -v elan >/dev/null; then
      curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | bash -s -- --default-toolchain leanprover/lean4:stable --no-modify-path -y
      source "$HOME/.elan/env"
    fi
    elan --version
    
    # 3. Install uv (Python dependency manager)
    if ! command -v uv >/dev/null; then
      curl -Ls https://astral.sh/uv/install.sh | bash
    fi
    uv --version
    
    # 4. Persist PATH additions
    grep -q "# Devin toolchain" "{{rc_file}}" 2>/dev/null || cat >> "{{rc_file}}" <<'EOF'
    # Devin toolchain — cargo / elan / uv
    export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
    EOF
    
    # 5. Final verification
    echo "✔ Installed tools:"
    which cargo
    which elan
    which uv
