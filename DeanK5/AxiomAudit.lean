import DeanK5
import DeanK5.AxiomCommands
import Batteries.Tactic.Lint

/-!
# Exhaustive axiom audit

This audit scans every declaration imported by the `DeanK5` library root,
including project declarations outside the principal namespace and
declarations that are not used by the final theorem.  The concise milestone
ledger for the actual proof spine is in `FinalDeductionAudit`.
-/

/-!
Keep public data definitions documented and definition names consistent with
Mathlib conventions.  The theorem-doc linter is intentionally excluded:
major paper-facing theorems are documented, while blanket comments on local
proof-engineering lemmas would add noise.
-/
#lint- only docBlame defsWithUnderscore in DeanK5

assert_axioms DeanK5.dean_conjecture_k5
  propext
  Classical.choice
  Quot.sound

/-!
The module-level check rejects `sorryAx` and every unlisted axiom anywhere in
the project, even when the affected declaration is outside the final
theorem's dependency closure.
-/
assert_module_prefix_axioms DeanK5
  propext
  Classical.choice
  Quot.sound

/-!
Every imported project proof module must contribute a declaration to the
final theorem's kernel dependency closure. `AxiomCommands` is audit
infrastructure rather than part of the mathematical proof.
-/
assert_module_prefix_reachable_from
  DeanK5.dean_conjecture_k5 DeanK5 except
  DeanK5.AxiomCommands
