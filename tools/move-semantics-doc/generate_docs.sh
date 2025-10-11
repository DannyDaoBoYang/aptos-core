#!/usr/bin/env bash
# Copyright © Aptos Foundation
# SPDX-License-Identifier: Apache-2.0

# Script to regenerate Move bytecode semantics documentation

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

echo "Extracting Move bytecode semantics..."

python3 "${SCRIPT_DIR}/extract_semantics.py" \
    "${REPO_ROOT}/third_party/move/move-binary-format/src/file_format.rs" \
    > "${REPO_ROOT}/MOVE_BYTECODE_SEMANTICS.md"

echo "Documentation generated at ${REPO_ROOT}/MOVE_BYTECODE_SEMANTICS.md"
echo "Total bytecode instructions documented: $(grep -c '^### `' "${REPO_ROOT}/MOVE_BYTECODE_SEMANTICS.md")"
