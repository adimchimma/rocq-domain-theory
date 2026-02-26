#!/usr/bin/env bash
# build.sh: build the rocq-domain-theory project.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

echo "Building rocq-domain-theory..."
dune build

echo "Running tests..."
dune runtest

echo "Build and tests successful."
