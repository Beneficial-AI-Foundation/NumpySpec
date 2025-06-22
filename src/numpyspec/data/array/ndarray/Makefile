.PHONY: test test-lean test-nd build clean all

all: build

build:
	lake build

test: build
	@echo "=== Running All Tests ==="
	@echo ""
	@echo "--- LeanArrayLib Tests ---"
	@./.lake/build/bin/testexe
	@echo ""
	@echo "--- NDArray Tests ---"
	@./.lake/build/bin/ndtest

test-lean: build
	@echo "=== Running LeanArrayLib Tests ==="
	@./.lake/build/bin/testexe

test-nd: build
	@echo "=== Running NDArray Tests ==="
	@./.lake/build/bin/ndtest

clean:
	lake clean

# Alternative: run tests directly without building executables
test-direct:
	@echo "=== Running tests directly with Lean ==="
	@echo ""
	@echo "--- LeanArrayLib Tests ---"
	@lake env lean Test.lean
	@echo ""
	@echo "--- NDArray Tests ---"
	@lake env lean NDArrayTest.lean

help:
	@echo "Available targets:"
	@echo "  make build      - Build all executables"
	@echo "  make test       - Run all tests"
	@echo "  make test-lean  - Run only LeanArrayLib tests"
	@echo "  make test-nd    - Run only NDArray tests"
	@echo "  make test-direct - Run tests directly without building executables"
	@echo "  make clean      - Clean build artifacts"
	@echo "  make help       - Show this help message"