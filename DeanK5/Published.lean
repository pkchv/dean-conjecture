import DeanK5.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Published results used (paper Section 1.3)

Every theorem declaration in this file is an explicit external dependency
tied to one of the sources below. Any restriction of the published wording is
documented at the declaration. No paper lemma or unnamed standard
graph-theory fact is placed here.

Sources:

* COY: Chiba--Ota--Yamashita, J. Graph Theory 103 (2023), Theorem 3,
  as quoted in BGLP Theorem 2.2.
-/

open scoped Sym2

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

/--
The exact finite-graph model of either `K_{s,t}` or `K_{s,t}` with one
cross-edge deleted.
-/
def IsCompleteBipartiteMinusAtMostOne
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V) : Prop :=
  Disjoint S T ∧ S ∪ T = Finset.univ ∧
    2 ≤ min S.card T.card ∧
    ∃ missing : Option (V × V),
      (∀ p, missing = some p → p.1 ∈ S ∧ p.2 ∈ T) ∧
      (missing.isSome → 3 ≤ max S.card T.card) ∧
      ∀ u v,
        G.Adj u v ↔
          ((u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S)) ∧
          match missing with
          | none => True
          | some p => ¬((u = p.1 ∧ v = p.2) ∨ (u = p.2 ∧ v = p.1))

namespace COY

/--
COY's one-exception rooted theorem, quoted as BGLP Theorem 2.2.
The statement does not require the exceptional vertex `z` to differ from
either root; this intentionally preserves the published quantifiers.
-/
axiom one_exception_rooted_paths
    [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y z : V)
    (hq : 1 ≤ q) (horder : 4 ≤ Fintype.card V) (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y → v ≠ z →
      q + 1 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y q)

end COY

end DeanK5
