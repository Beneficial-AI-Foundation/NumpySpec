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

# OCR pipeline
ocr pdf:
    uv run -m gaussianspec.pdf_pipeline {{pdf}}
