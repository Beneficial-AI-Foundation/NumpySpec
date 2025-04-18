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

# OCR pipeline (defaults to project textbook)
ocr pages='1-100' pdf='textbook/Numerical_Recipes_in_C.pdf' method='auto':
    uv run -m gaussianspec.pdf_pipeline {{pdf}} --pages {{pages}} --method {{method}}

# OCR entire PDF in chunks
ocr-all chunk=50 pdf='textbook/Numerical_Recipes_in_C.pdf' method='auto':
    uv run -m gaussianspec.pdf_pipeline {{pdf}} --all --chunk-size {{chunk}} --method {{method}}
