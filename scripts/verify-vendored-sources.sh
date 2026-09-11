#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
source_root="$repository_root/ErgodicTheory/MeasureTheory"
upstream_commit=9bd9db36d3d099a32554b34eaf85e2e053a2bf31

verify_file() {
  local expected_hash=$1
  local filename=$2
  local path="$source_root/$filename"

  if [ ! -f "$path" ]; then
    echo "error: missing vendored source $path" >&2
    return 1
  fi

  local actual_hash
  actual_hash=$(sha256sum "$path" | cut -d' ' -f1)
  if [ "$actual_hash" != "$expected_hash" ]; then
    echo "error: $filename does not match upstream commit $upstream_commit" >&2
    echo "expected SHA-256: $expected_hash" >&2
    echo "actual SHA-256:   $actual_hash" >&2
    return 1
  fi
}

verify_file 6f57a8ef0dca1cfb723baba167cc87f0c6ff1bca071a7c61ea6fb1a8e285a694 \
  AnalyticSetLemmas.lean
verify_file b58e4eb4221a83496222626fbdb530b74ec16b2295e6d7aa226dfedc1acf0b19 \
  NovikovSeparation.lean
verify_file 48e27a656923562f21ffee59e23812c39f2170f97e27bf3c127aa2ab98dc795a \
  CoanalyticReduction.lean
verify_file 27fd5e740573e26852fa798ec5b75e763a5ece4089ec83cc3e4fc62b9b09072f \
  KunuguiNovikov.lean
verify_file f81f27c601d45ba56d5a50503dbf4534dd5343695f593f3d6aaf7207d5b3b546 \
  CompactSectionProjection.lean

echo "Vendored sources match upstream commit $upstream_commit"
