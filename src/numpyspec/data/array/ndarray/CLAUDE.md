# NDArray Development Guidelines

## Key Principles

- Always use Array instead of List for performance
- Use `just` for build commands (or `./run.sh` if just is not installed)
- Follow the project's Lean 4 naming conventions from the main CLAUDE.md

## Build System

```bash
# Primary build tool: just
just build    # Build the project
just test     # Run all tests
just clean    # Clean build artifacts

# Fallback if just is not installed
./run.sh build
./run.sh test
./run.sh clean
```

## Testing

- LeanArrayLib tests: `just test-lean`
- NDArray tests: `just test-nd`
- Run tests directly without building: `just test-direct`
