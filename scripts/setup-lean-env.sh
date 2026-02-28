#!/usr/bin/env bash
set -euo pipefail

# Setup script for this Lean 4 project (DagLeanLibrary).
# Installs the toolchain manager (elan), Lean/Lake toolchain from lean-toolchain,
# and verifies that the project builds.

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_TOOLCHAIN_FILE="$ROOT_DIR/lean-toolchain"

if [[ ! -f "$LEAN_TOOLCHAIN_FILE" ]]; then
  echo "ERROR: lean-toolchain not found at $LEAN_TOOLCHAIN_FILE" >&2
  exit 1
fi

need_cmd() {
  command -v "$1" >/dev/null 2>&1
}

install_base_deps_apt() {
  echo "Installing base dependencies via apt..."
  sudo apt-get update
  sudo apt-get install -y curl git tar zstd xz-utils
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
  - zstd (recommended, needed for .tar.zst Lean archives)
MSG
    exit 1
  fi
}

ensure_elan() {
  if need_cmd elan; then
    echo "elan already installed: $(command -v elan)"
    return 0
  fi

  echo "Installing elan..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y

  # shellcheck disable=SC1091
  if [[ -f "$HOME/.elan/env" ]]; then
    source "$HOME/.elan/env"
  else
    export PATH="$HOME/.elan/bin:$PATH"
  fi
}

ensure_lake() {
  if ! need_cmd lake; then
    export PATH="$HOME/.elan/bin:$PATH"
  fi

  if ! need_cmd lake; then
    echo "ERROR: lake not found after elan installation." >&2
    exit 1
  fi

  echo "Lake detected: $(lake --version | head -n 1)"
}

main() {
  echo "==> DagLeanLibrary environment setup"
  echo "Project root: $ROOT_DIR"
  echo "Toolchain pin: $(cat "$LEAN_TOOLCHAIN_FILE")"
  echo
  echo "Required tools for this Lean project:"
  echo "  - git"
  echo "  - curl"
  echo "  - tar"
  echo "  - zstd (for Lean .tar.zst archives)"
  echo "  - elan (Lean toolchain manager; installed by this script)"
  echo "  - lean + lake (installed via elan using lean-toolchain)"
  echo

  ensure_base_deps
  ensure_elan
  ensure_lake

  echo "Syncing toolchain from lean-toolchain..."
  (cd "$ROOT_DIR" && lake --version >/dev/null)

  echo "Building project to verify setup..."
  (cd "$ROOT_DIR" && lake build)

  echo
  echo "Setup complete."
}

main "$@"
