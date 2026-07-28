import DeanK5.COYInstance
import DeanK5.Graph.Separation
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Protected-edge deletion in a COY minimal counterexample

The proof of COY Claim 3.2 repeatedly deletes an edge whose endpoints
belong to the two roots and the exceptional vertex.  Such a deletion
does not lower the degree of any ordinary vertex.  Minimality therefore
forces the deletion to destroy rooted two-connectivity.
-/

open scoped Sym2

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- A vertex is one of the two roots or the exceptional vertex. -/
def IsProtected (x y z v : V) : Prop :=
  v = x ∨ v = y ∨ v = z

theorem ne_of_not_protected
    {x y z v a : V}
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z)
    (ha : IsProtected x y z a) :
    v ≠ a := by
  intro h
  rcases ha with rfl | rfl | rfl
  · exact hvx h
  · exact hvy h
  · exact hvz h

/-- Deleting a present edge strictly lowers the edge part of the COY measure. -/
theorem edgeSet_sdiff_edge_ncard_lt
    [Finite V]
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    (G \ edge a b).edgeSet.ncard < G.edgeSet.ncard := by
  rw [SimpleGraph.edgeSet_sdiff,
    SimpleGraph.edgeSet_edge_of_ne hab.ne]
  exact Set.ncard_sdiff_singleton_lt_of_mem hab

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z a b : V}

/-- Exchange the two roots of a minimal counterexample. -/
theorem swapRoots
    (M : MinimalCounterexample q G x y z) :
    MinimalCounterexample q G y x z where
  q_pos := M.q_pos
  q_le_four := M.q_le_four
  roots_ne := M.roots_ne.symm
  rooted_two_connected := by
    simpa [edge_comm] using M.rooted_two_connected
  ordinary_nonempty := by
    obtain ⟨v, hvx, hvy, hvz⟩ := M.ordinary_nonempty
    exact ⟨v, hvy, hvx, hvz⟩
  degree_lower := by
    intro v hvy hvx hvz
    exact M.degree_lower v hvx hvy hvz
  no_paths := by
    intro hpaths
    obtain ⟨F⟩ := hpaths
    exact M.no_paths ⟨F.reverse⟩
  smaller_solvable := by
    intro W _ _ q' H r s e I hsmaller
    exact M.smaller_solvable I hsmaller

/--
Deleting a present edge between protected vertices cannot leave a valid
rooted instance.  Otherwise the induction hypothesis solves the smaller
graph and the inclusion maps those paths back into the counterexample.
-/
theorem not_rooted_two_connected_sdiff_protected_edge
    (M : MinimalCounterexample q G x y z)
    (hab : G.Adj a b)
    (ha : IsProtected x y z a)
    (hb : IsProtected x y z b) :
    ¬IsTwoConnected ((G \ edge a b) ⊔ edge x y) := by
  intro hconnected
  let G' := G \ edge a b
  have hdegree :
      ∀ v, v ≠ x → v ≠ y → v ≠ z →
        q + 1 ≤ finiteDegree G' v := by
    intro v hvx hvy hvz
    have hva : v ≠ a :=
      ne_of_not_protected hvx hvy hvz ha
    have hvb : v ≠ b :=
      ne_of_not_protected hvx hvy hvz hb
    rw [finiteDegree_sdiff_edge_of_ne G a b v hva hvb]
    exact M.degree_lower v hvx hvy hvz
  let I : RootedInstance q G' x y z := {
    q_pos := M.q_pos
    q_le_four := M.q_le_four
    roots_ne := M.roots_ne
    rooted_two_connected := hconnected
    ordinary_nonempty := M.ordinary_nonempty
    degree_lower := hdegree
  }
  have hcomplexity : rootedComplexity G' < rootedComplexity G := by
    apply rootedComplexity_lt_of_card_le_of_edgeCount_lt
    · exact le_rfl
    · exact edgeSet_sdiff_edge_ncard_lt G hab
  obtain ⟨F⟩ := M.smaller_solvable I hcomplexity
  let mapped :=
    F.mapInjectiveHom
      (SimpleGraph.Hom.ofLE
        (show G' ≤ G from sdiff_le))
      Function.injective_id
  apply M.no_paths
  exact ⟨by simpa [mapped] using mapped⟩

/-- The two roots of a COY minimal counterexample are nonadjacent. -/
theorem roots_not_adj
    (M : MinimalCounterexample q G x y z) :
    ¬G.Adj x y := by
  intro hxy
  have hedge : edge x y ≤ G :=
    (edge_le_iff G).2 (Or.inr hxy)
  have hGconnected : IsTwoConnected G := by
    simpa [sup_eq_left.mpr hedge] using
      M.rooted_two_connected
  have hdeletedConnected :
      IsTwoConnected ((G \ edge x y) ⊔ edge x y) := by
    simpa [sdiff_sup_cancel hedge] using hGconnected
  exact
    (M.not_rooted_two_connected_sdiff_protected_edge
      hxy (Or.inl rfl) (Or.inr (Or.inl rfl)))
      hdeletedConnected

/--
The underlying graph of a COY minimal counterexample is connected.
Indeed, it is obtained from the rooted 2-connected graph by deleting the
now-known nonedge added between the roots.
-/
theorem underlying_connected
    (M : MinimalCounterexample q G x y z) :
    G.Connected := by
  have hdeleted :=
    M.rooted_two_connected.connected_delete_edge x y
  have hGdelete :
      G.deleteEdges {s(x, y)} = G := by
    apply SimpleGraph.deleteEdges_eq_self.mpr
    simp [M.roots_not_adj]
  simpa [SimpleGraph.deleteEdges_sup, hGdelete] using hdeleted

end MinimalCounterexample

end COY

end DeanK5
