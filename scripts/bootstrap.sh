#!/usr/bin/env bash
set -euo pipefail
EC2_PROJECT_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$EC2_PROJECT_ROOT"
# Install elan separately if it is absent. The committed lean-toolchain chooses
# Lean 4.35.0; the committed Lake manifest retains every dependency revision.
lake exe cache get
# Physlib's optional official artifact cache saves a large upstream build.
# Failure of this cache download does not supply any mathematical assumption:
# Lake builds the pinned upstream source in the ordinary way instead.
if ! LAKE_CONFIG="$EC2_PROJECT_ROOT/.lake/packages/Physlib/lake-cache.toml" \
  lake cache get --package=Physlib \
    --scope=physlib-master/leanprover-lean4-v4.35.0/physlib \
    --rev=1eefcc45aa0d864b8c742e72de5d975b3ee3b15e; then
  printf '%s\n' 'Optional Physlib cache unavailable; continuing with a source build.'
fi
python3 scripts/verify.py --clean
