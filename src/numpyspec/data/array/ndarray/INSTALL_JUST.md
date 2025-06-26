# Installing Just

`just` is a handy command runner that we use instead of Make. Here are several ways to install it:

## Option 1: Using cargo (if Rust is installed)
```bash
cargo install just
```

## Option 2: Using pre-built binaries
```bash
# For Linux x86_64
curl --proto '=https' --tlsv1.2 -sSf https://just.systems/install.sh | bash -s -- --to ~/.local/bin

# Add to PATH if needed
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

## Option 3: Using package managers

### Ubuntu/Debian
```bash
# If using snap
sudo snap install --edge --classic just

# Or using the prebuilt binary
wget https://github.com/casey/just/releases/download/1.16.0/just-1.16.0-x86_64-unknown-linux-musl.tar.gz
tar xvf just-1.16.0-x86_64-unknown-linux-musl.tar.gz
sudo mv just /usr/local/bin/
```

### macOS
```bash
brew install just
```

### Arch Linux
```bash
pacman -S just
```

## Option 4: Use the fallback script

If you can't install `just`, use the provided `./run.sh` script which provides the same functionality:

```bash
./run.sh help  # Show available commands
./run.sh build # Build the project
./run.sh test  # Run tests
```

## Verification

After installation, verify that just is working:

```bash
just --version
```

Then you can use the justfile in this directory:

```bash
just help  # Show available recipes
```