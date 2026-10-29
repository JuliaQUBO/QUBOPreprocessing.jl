#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [ -d "/tmp/lean-theleodynamics-elan" ] && [ -z "${ELAN_HOME:-}" ]; then
  export ELAN_HOME="/tmp/lean-theleodynamics-elan"
  export PATH="/tmp/lean-theleodynamics-elan/bin:${PATH}"
fi
exec python3 verify.py "$@"
