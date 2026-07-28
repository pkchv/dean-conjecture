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

# The final deduction is the sole proof root. Traverse its project imports and
# reject any source file that has become an orphan. Audit-only modules are
# elaborated separately below.
reached_modules=

visit_module()
{
    module=$1
    case "
${reached_modules}
" in
      *"
${module}
"*) return ;;
    esac
    reached_modules="${reached_modules}
${module}"
    source=$(printf '%s\n' "${module}" | tr '.' '/').lean
    if [ ! -f "${source}" ]; then
        printf '%s\n' \
          "${module} is imported but has no corresponding source file." >&2
        exit 1
    fi
    for dependency in $(sed -n 's/^import \(DeanK5[^ ]*\).*$/\1/p' "${source}"); do
        visit_module "${dependency}"
    done
}

visit_module DeanK5.FinalDeduction

find DeanK5 -type f -name '*.lean' -print |
  while IFS= read -r source; do
    case "${source}" in
      DeanK5/AxiomAudit.lean|\
      DeanK5/FinalDeductionAudit.lean|\
      DeanK5/AxiomCommands.lean) continue ;;
    esac
    module=$(printf '%s\n' "${source%.lean}" | tr '/' '.')
    case "
${reached_modules}
" in
      *"
${module}
"*) ;;
      *)
        printf '%s\n' \
          "${module} is not reachable from DeanK5.FinalDeduction." >&2
        exit 1 ;;
    esac
  done

lake --rehash --wfail build
# The audit modules are intentionally outside the library root. Build their
# support explicitly so verification also works from a completely fresh clone.
lake --rehash --wfail build DeanK5.AxiomCommands Batteries.Tactic.Lint

# Re-elaborate the compact proof spine from source, then run its focused audit
# before the exhaustive scan of every project declaration.
lake env lean -DwarningAsError=true -E hasSorry DeanK5/FinalDeduction.lean
lake env lean -DwarningAsError=true -E hasSorry DeanK5/FinalDeductionAudit.lean
lake env lean -DwarningAsError=true -E hasSorry DeanK5/AxiomAudit.lean
