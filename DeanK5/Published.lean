import DeanK5.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Published results used (paper Section 1.3)

Every theorem declaration in this file is an explicit external dependency
tied to one of the sources below. Any restriction of the published wording is
documented at the declaration. No paper lemma or unnamed standard
graph-theory fact is placed here.

Sources:

* GHLM: Gao--Huo--Liu--Ma, IMRN 2022, Theorem 3.1.
* COY: Chiba--Ota--Yamashita, J. Graph Theory 103 (2023), Theorem 3,
  as quoted in BGLP Theorem 2.2.
* BGLP: Bai--Grzesik--Li--Prorok, JCTB 180 (2026), Theorem 1.3.
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

namespace GHLM

/--
GHLM Theorem 3.1 (rooted admissible-path theorem).
-/
axiom rooted_admissible_paths
    [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y : V)
    (hq : 1 ≤ q) (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y → q + 1 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y q)

end GHLM

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

namespace BGLP

/-- BGLP Theorem 1.3. -/
axiom two_connected_minimum_degree
    [Fintype V] [DecidableEq V]
    (k : ℕ) (G : SimpleGraph V)
    (hk : 4 ≤ k)
    (hconn : IsTwoConnected G)
    (hdeg : MinDegreeAtLeast G k) :
    Nonempty (AdmissibleCycleFamily G k) ∨
      IsCompleteGraphOfOrder G (k + 1) ∨
      IsCompleteBipartiteOfParts G k (Fintype.card V - k)

end BGLP

end DeanK5
