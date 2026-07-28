import DeanK5.COYExteriorClaimThreeThirteenAttachment
import DeanK5.COYExteriorRankOneBoundary

/-!
# Local setup for COY Claim 3.15

Fix an arbitrary feasible exterior block after Claim 3.13.  Under the
negation of Claim 3.15(1), the second block exception is the anchor itself.
Equation (3.2) then says that the only possible working-core neighbours of
`B - b` are the core root and the unique `S`-vertex, while equation (3.3)
bounds their total number at every nonanchor block vertex.

The finite set `sideBlockNeighbors` is the source set
`N_G(s₁) ∩ V(B)`.  The last theorem below gives the exact dichotomy used to
define the two recursive graphs `B'` in the published proof.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s : V}
  {P : PreferredWorkingCoreData G x y z}

/-- The neighbours of a vertex that lie in the selected block. -/
noncomputable def blockNeighbors
    (C : P.ExteriorFeasibleBlockChoice) (v : V) : Finset V := by
  classical
  exact C.ambientCarrier.filter (G.Adj v)

@[simp] theorem mem_blockNeighbors
    (C : P.ExteriorFeasibleBlockChoice) {v d : V} :
    d ∈ C.blockNeighbors v ↔
      d ∈ C.ambientCarrier ∧ G.Adj v d := by
  classical
  simp [blockNeighbors]

/--
The assumption `z' ∉ B-b` forces the second selected exception to coincide
with the anchor.
-/
theorem zPrime_eq_b_of_not_mem_compressionInterior
    (C : P.ExteriorFeasibleBlockChoice)
    (hzPrime : C.zPrime ∉ C.compressionInterior) :
    C.zPrime = C.b := by
  by_contra hne
  exact hzPrime
    (Finset.mem_erase.mpr
      ⟨hne, C.zPrime_mem_ambientCarrier⟩)

/-- Equation (3.2) gives a genuine attachment from `x` into `B-b`. -/
theorem exists_root_attachment_in_compressionInterior
    (C : P.ExteriorFeasibleBlockChoice)
    (hboundary : C.coreAttachments = {x, s}) :
    ∃ d ∈ C.compressionInterior, G.Adj x d := by
  have hxAttachments : x ∈ C.coreAttachments := by
    rw [hboundary]
    simp
  exact (C.mem_coreAttachments.mp hxAttachments).2

/-- Equation (3.2) gives a genuine attachment from `s` into `B-b`. -/
theorem exists_side_attachment_in_compressionInterior
    (C : P.ExteriorFeasibleBlockChoice)
    (hboundary : C.coreAttachments = {x, s}) :
    ∃ d ∈ C.compressionInterior, G.Adj s d := by
  have hsAttachments : s ∈ C.coreAttachments := by
    rw [hboundary]
    simp
  exact (C.mem_coreAttachments.mp hsAttachments).2

/-- The source set `N_G(s) ∩ V(B)` is nonempty. -/
theorem sideBlockNeighbors_nonempty
    (C : P.ExteriorFeasibleBlockChoice)
    (hboundary : C.coreAttachments = {x, s}) :
    (C.blockNeighbors s).Nonempty := by
  obtain ⟨d, hd, hsd⟩ :=
    C.exists_side_attachment_in_compressionInterior hboundary
  exact
    ⟨d, C.mem_blockNeighbors.mpr
      ⟨Finset.mem_of_mem_erase hd, hsd⟩⟩

/--
Every working-core neighbour of a vertex in `B-b` belongs to the pair
`{x,s}` from equation (3.2).
-/
theorem core_neighbor_mem_pair
    (C : P.ExteriorFeasibleBlockChoice)
    (hboundary : C.coreAttachments = {x, s})
    {d v : V}
    (hd : d ∈ C.compressionInterior)
    (hvCore : v ∈ P.working.rooted.core.carrier)
    (hdv : G.Adj d v) :
    v ∈ ({x, s} : Finset V) := by
  have hvAttachments : v ∈ C.coreAttachments :=
    C.mem_coreAttachments.mpr
      ⟨hvCore, ⟨d, hd, hdv.symm⟩⟩
  simpa [hboundary] using hvAttachments

/--
Under `z'=b`, every nonanchor block vertex is a source `V_nc` vertex.
-/
def exteriorOrdinaryOfInterior
    (C : P.ExteriorFeasibleBlockChoice)
    (hzPrime : C.zPrime = C.b)
    {d : V} (hd : d ∈ C.compressionInterior) :
    P.ExteriorOrdinaryVertex := by
  have hdB : d ∈ C.ambientCarrier :=
    Finset.mem_of_mem_erase hd
  have hdb : d ≠ C.b :=
    (Finset.mem_erase.mp hd).1
  exact {
    vertex := C.exteriorVertex hdB
    ne_y := C.ordinary_block_vertex_ne_y
      hdB hdb (by simpa [hzPrime] using hdb)
    ne_z := C.ordinary_block_vertex_ne_z
      hdB hdb (by simpa [hzPrime] using hdb)
    not_cut := C.exteriorVertex_not_cut
      hdB hdb (by simpa [hzPrime] using hdb)
  }

/--
Equation (3.3), specialized to every vertex of `B-b` under the negation of
Claim 3.15(1).
-/
theorem interior_coreNeighbor_ncard_le_one
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    (hzPrime : C.zPrime = C.b)
    {d : V} (hd : d ∈ C.compressionInterior) :
    (G.neighborSet d ∩
      (↑P.working.rooted.core.carrier : Set V)).ncard ≤ 1 :=
  D.coreNeighbor_ncard_le_one M
    (C.exteriorOrdinaryOfInterior hzPrime hd)

/--
If the unique `S`-vertex has exactly one block neighbour `v`, no other
vertex of `B-b` is adjacent to `s`.
-/
theorem not_adj_side_of_blockNeighbors_eq_singleton
    (C : P.ExteriorFeasibleBlockChoice)
    (hside : C.blockNeighbors s = {v})
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdv : d ≠ v) :
    ¬G.Adj d s := by
  intro hds
  have hdSide : d ∈ C.blockNeighbors s :=
    C.mem_blockNeighbors.mpr
      ⟨Finset.mem_of_mem_erase hd, hds.symm⟩
  rw [hside] at hdSide
  simpa using hdv (by simpa using hdSide)

/--
The source split for `N_G(s) ∩ V(B)`: it is either a singleton or has at
least two vertices.
-/
theorem sideBlockNeighbors_eq_singleton_or_two_le
    (C : P.ExteriorFeasibleBlockChoice)
    (hboundary : C.coreAttachments = {x, s}) :
    (∃ v, C.blockNeighbors s = {v}) ∨
      2 ≤ (C.blockNeighbors s).card := by
  have hnonempty :=
    C.sideBlockNeighbors_nonempty hboundary
  by_cases hone : (C.blockNeighbors s).card = 1
  · left
    obtain ⟨v, hv⟩ :=
      Finset.card_eq_one.mp hone
    exact ⟨v, hv⟩
  · right
    have hpositive :
        0 < (C.blockNeighbors s).card :=
      Finset.card_pos.mpr hnonempty
    omega

/--
Claim 3.13 supplies the singleton side and equation (3.2) simultaneously
for every feasible anchored exterior block.
-/
theorem exists_claimThreeFifteen_boundary_data
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice) :
    ∃ s, D.core.S = {s} ∧
      C.coreAttachments = {x, s} := by
  exact C.exists_side_eq_singleton_and_coreAttachments_eq_pair
    M D.core D.core_eq (D.rank_eq_one M)

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
