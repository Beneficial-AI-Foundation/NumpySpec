# LeanArrayLib

## Build System

This project uses `just` as the primary build system. If `just` is not installed, you can use the `./run.sh` script as a fallback.

### Using Just (Recommended)

```bash
# Build the project
just build

# Run all tests
just test

# Run specific tests
just test-lean   # LeanArrayLib tests only
just test-nd     # NDArray tests only

# Clean build artifacts
just clean

# Show all available commands
just help
```

### Using run.sh (Fallback)

If `just` is not available, use the provided shell script:

```bash
# Build the project
./run.sh build

# Run all tests
./run.sh test

# Run specific tests
./run.sh test-lean   # LeanArrayLib tests only
./run.sh test-nd     # NDArray tests only

# Clean build artifacts
./run.sh clean

# Show all available commands
./run.sh help
```

### Legacy: Using Make

The Makefile is deprecated but still available for backward compatibility.