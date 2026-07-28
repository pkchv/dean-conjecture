import DeanK5.COYCutInduction

/-!
# The protected-edge swap in COY Claim 3.2

For a hypothetical edge from the left root to the exceptional vertex,
delete that edge and retain the artificial edge between the two roots.
Minimality makes the resulting rooted graph non-2-connected, while
restoring the deleted edge recovers the original rooted 2-connected
graph.  This file packages the resulting cut decomposition.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- The graph obtained by deleting the edge from the left root to the exception. -/
def leftEdgeDeletedGraph
    (G : SimpleGraph V) (x z : V) : SimpleGraph V :=
  G \ edge x z

/--
The rooted graph after exchanging the left-root--exception edge for the
artificial edge between the roots.
-/
def leftEdgeSwapGraph
    (G : SimpleGraph V) (x y z : V) : SimpleGraph V :=
  leftEdgeDeletedGraph G x z ⊔ edge x y

/--
The complete cut setup forced by a hypothetical edge from the left root
to the exceptional vertex in a minimal COY counterexample.
-/
structure EdgeSwapCutSetup
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y z : V) : Prop where
  /-- Deleting `xz` leaves the underlying graph connected. -/
  deleted_connected : (leftEdgeDeletedGraph G x z).Connected
  /-- Adding the artificial root edge preserves connectedness. -/
  swap_connected : (leftEdgeSwapGraph G x y z).Connected
  /-- The swapped graph is not 2-connected. -/
  swap_not_two_connected :
    ¬IsTwoConnected (leftEdgeSwapGraph G x y z)
  /-- Restoring `xz` recovers a 2-connected graph. -/
  restored_two_connected :
    IsTwoConnected (leftEdgeSwapGraph G x y z ⊔ edge x z)
  /--
  A cut vertex separates `x` and `z` into distinct certified component
  regions of the swapped graph.
  -/
  separating_cut :
    ∃ c : V,
      ∃ Cx Cz :
          (deleteVertices
            (leftEdgeSwapGraph G x y z) {c}).ConnectedComponent,
        Cx ≠ Cz ∧
        x ∈ componentVertices
          (leftEdgeSwapGraph G x y z) {c} Cx ∧
        z ∈ componentVertices
          (leftEdgeSwapGraph G x y z) {c} Cz ∧
        ComponentRegion
          (leftEdgeSwapGraph G x y z) {c}
          (componentVertices
            (leftEdgeSwapGraph G x y z) {c} Cx) ∧
        ComponentRegion
          (leftEdgeSwapGraph G x y z) {c}
          (componentVertices
            (leftEdgeSwapGraph G x y z) {c} Cz) ∧
        Disjoint
          (componentVertices
            (leftEdgeSwapGraph G x y z) {c} Cx)
          (componentVertices
            (leftEdgeSwapGraph G x y z) {c} Cz)

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
A hypothetical edge `xz` in a minimal counterexample yields a connected
but non-2-connected edge-swap graph, together with a cut vertex separating
`x` from `z`.
-/
theorem edgeSwapCutSetup
    (M : MinimalCounterexample q G x y z)
    (hxz : G.Adj x z) :
    EdgeSwapCutSetup G x y z := by
  have hdeleted :
      (leftEdgeDeletedGraph G x z).Connected := by
    exact M.underlying_two_connected.connected_sdiff_edge x z
  have hswap :
      (leftEdgeSwapGraph G x y z).Connected := by
    exact hdeleted.mono le_sup_left
  have hnotTwo :
      ¬IsTwoConnected (leftEdgeSwapGraph G x y z) := by
    exact M.not_rooted_two_connected_sdiff_protected_edge
      hxz (Or.inl rfl) (Or.inr (Or.inr rfl))
  have hxzEdge : edge x z ≤ G :=
    (edge_le_iff G).2 (Or.inr hxz)
  have hrestore :
      leftEdgeSwapGraph G x y z ⊔ edge x z =
        G ⊔ edge x y := by
    simp only [leftEdgeSwapGraph, leftEdgeDeletedGraph]
    calc
      (G \ edge x z ⊔ edge x y) ⊔ edge x z =
          (G \ edge x z ⊔ edge x z) ⊔ edge x y := by
            ac_rfl
      _ = G ⊔ edge x y := by
        rw [sdiff_sup_cancel hxzEdge]
  have hrestored :
      IsTwoConnected
        (leftEdgeSwapGraph G x y z ⊔ edge x z) := by
    rw [hrestore]
    exact M.rooted_two_connected
  obtain ⟨c, Cx, Cz, hCxCz, hx, hz⟩ :=
    ComponentRegion.exists_root_separating_cut_of_sup_edge_two_connected
      (leftEdgeSwapGraph G x y z) x z
      hswap hnotTwo hrestored hrestored.1
  exact {
    deleted_connected := hdeleted
    swap_connected := hswap
    swap_not_two_connected := hnotTwo
    restored_two_connected := hrestored
    separating_cut := ⟨c, Cx, Cz, hCxCz, hx, hz,
      componentRegion_componentVertices
        (leftEdgeSwapGraph G x y z) {c} Cx,
      componentRegion_componentVertices
        (leftEdgeSwapGraph G x y z) {c} Cz,
      componentVertices_disjoint_of_ne
        (leftEdgeSwapGraph G x y z) {c} hCxCz⟩
  }

end MinimalCounterexample

end COY

end DeanK5
