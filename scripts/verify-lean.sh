#!/bin/sh
set -eu

cd "$(dirname "$0")/.."

# Git exports repository-local variables to hooks. Clear them before Lake
# invokes Git for package checks, especially when verifying from a worktree.
for git_variable in $(git rev-parse --local-env-vars); do
    unset "$git_variable"
done

elan_home="${ELAN_HOME:-${HOME}/.elan}"
PATH="${elan_home}/bin:${PATH}"
export PATH

# Keep the semantic module audits exhaustive when a new project module is
# added: every source module except the audit driver itself must be imported
# by the library root.
find DeanK5 -type f -name '*.lean' -print |
  while IFS= read -r source; do
    case "${source}" in
      DeanK5/AxiomAudit.lean) continue ;;
    esac
    module=$(printf '%s\n' "${source%.lean}" | tr '/' '.')
    if ! grep -Fqx "import ${module}" DeanK5.lean; then
      printf '%s\n' \
        "DeanK5.lean must directly import ${module} for complete auditing." >&2
      exit 1
    fi
  done

lake build
# AxiomAudit is intentionally outside the library root. Build its audit-only
# imports explicitly so verification also works from a completely fresh clone.
lake build Batteries.Tactic.Lint Mathlib.Util.AssertNoSorry
# The module scan covers imported proof modules; this also protects the audit
# driver while it is being elaborated.
lake env lean -E hasSorry DeanK5/AxiomAudit.lean
