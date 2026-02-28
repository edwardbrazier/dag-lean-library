#!/usr/bin/env bash
set -euo pipefail

# Setup script for this Lean 4 project (DagLeanLibrary).
# Works from a blank slate (e.g. a fresh cloud container).
#
# Steps performed:
#   1. Install system dependencies (curl, git, tar, zstd)
#   2. Install elan (Lean toolchain manager)
#   3. Install the exact Lean toolchain pinned in lean-toolchain
#   4. Fetch lake package dependencies
#   5. Build the project to verify everything works

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_TOOLCHAIN_FILE="$ROOT_DIR/lean-toolchain"

if [[ ! -f "$LEAN_TOOLCHAIN_FILE" ]]; then
  echo "ERROR: lean-toolchain not found at $LEAN_TOOLCHAIN_FILE" >&2
  exit 1
fi

TOOLCHAIN_ID="$(tr -d '[:space:]' < "$LEAN_TOOLCHAIN_FILE")"

need_cmd() {
  command -v "$1" >/dev/null 2>&1
}

# Use sudo only when not running as root (containers often run as root).
run_privileged() {
  if [[ "$(id -u)" -eq 0 ]]; then
    "$@"
  else
    sudo "$@"
  fi
}

install_base_deps_apt() {
  echo "Installing base dependencies via apt..."
  run_privileged apt-get update -y
  run_privileged apt-get install -y curl git tar zstd xz-utils
}

install_base_deps_brew() {
  echo "Installing base dependencies via Homebrew..."
  brew install curl git zstd
}

ensure_base_deps() {
  local missing=()
  for c in curl git tar; do
    need_cmd "$c" || missing+=("$c")
  done

  if [[ ${#missing[@]} -eq 0 ]]; then
    return 0
  fi

  echo "Missing required commands: ${missing[*]}"

  if need_cmd apt-get; then
    install_base_deps_apt
  elif need_cmd brew; then
    install_base_deps_brew
  else
    cat >&2 <<MSG
Please install these tools manually and re-run:
  - curl
  - git
  - tar
  - zstd (needed for .tar.zst Lean archives)
MSG
    exit 1
  fi
}

ensure_elan() {
  if need_cmd elan; then
    echo "elan already installed: $(elan --version)"
  else
    echo "Installing elan (Lean toolchain manager)..."
    # --default-toolchain none: skip auto-installing a default toolchain;
    # we will install exactly the pinned version below.
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
    echo "elan installed."
  fi

  # Make elan/lean/lake shims available in this shell session.
  if [[ -f "$HOME/.elan/env" ]]; then
    # shellcheck disable=SC1091
    source "$HOME/.elan/env"
  fi
  export PATH="$HOME/.elan/bin:$PATH"

  if ! need_cmd elan; then
    echo "ERROR: elan not found after installation." >&2
    exit 1
  fi
}

install_toolchain() {
  echo "Installing Lean toolchain: $TOOLCHAIN_ID ..."
  elan toolchain install "$TOOLCHAIN_ID"
  # Make it the default so that 'lean' and 'lake' resolve to this version
  # even outside the project directory.
  elan default "$TOOLCHAIN_ID"
  echo "Toolchain ready: $(lean --version)"
}

ensure_lake() {
  if ! need_cmd lake; then
    echo "ERROR: lake not found after toolchain installation." >&2
    exit 1
  fi
  echo "lake: $(lake --version | head -n 1)"
}

main() {
  echo "==> DagLeanLibrary environment setup"
  echo "Project root: $ROOT_DIR"
  echo "Toolchain:    $TOOLCHAIN_ID"
  echo

  ensure_base_deps
  ensure_elan
  install_toolchain
  ensure_lake

  echo "Fetching lake package dependencies..."
  (cd "$ROOT_DIR" && lake update)

  echo "Building project to verify setup..."
  (cd "$ROOT_DIR" && lake build)

  echo
  echo "Setup complete."
}

main "$@"
