# Justfile for GaussianSpec project
# Usage: just run

# Ensure dependencies are installed and run the agent
run:
    uv sync
    uv run src/gaussianspec/agent.py 