import DeanK5.COYCoreAttachmentTypeTwo
import DeanK5.COYCoreAttachmentTypeThree
import DeanK5.COYCoreAttachmentModified
import DeanK5.COYWorkingCoreSelection

/-!
# Exterior attachments to the selected COY working core

This file assembles the natural type-1, type-2, type-3, and modified
type-3 cases into the exact source form of COY Claim 3.3.  The selected
excluded vertex is `y` in the natural branch and the removed vertex `t₀`
in the modified branch.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace SelectedWorkingCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}

/--
The vertex denoted `t₀` in Claim 3.3: by convention it is `y` for an
unmodified core, and it is the distinguished removed vertex in the
modified branch.
-/
def excludedVertex
    (W : SelectedWorkingCore (z := z) O) : V :=
  match W with
  | .natural _ => y
  | .modified T _ => T.t₀

@[simp] theorem excludedVertex_natural
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) O)) :
    (SelectedWorkingCore.natural hnot).excludedVertex = y :=
  rfl

@[simp] theorem excludedVertex_modified
    (T : TypeThreeModificationTrigger (z := z) O)
    (K : TypeThreeModificationChoice T) :
    (SelectedWorkingCore.modified T K).excludedVertex = T.t₀ :=
  rfl

/--
COY Claim 3.3: every vertex outside the working core and the two
source-excluded vertices has at most `rank + 1` neighbors in the core.
-/
theorem coreNeighbor_ncard_le
    (W : SelectedWorkingCore (z := z) O)
    {v : V}
    (hvCarrier : v ∉ W.rooted.core.carrier)
    (hvy : v ≠ y)
    (hvExcluded : v ≠ W.excludedVertex) :
    (G.neighborSet v ∩
      (↑W.rooted.core.carrier : Set V)).ncard ≤ W.rank + 1 := by
  cases W with
  | natural hnot =>
      cases hcore : O.rooted.core with
      | typeOne C =>
          simpa [rooted, rank] using
            O.coreNeighbor_ncard_le_of_typeOne
              C hcore hvCarrier hvy
      | typeTwo C =>
          simpa [rooted, rank] using
            O.coreNeighbor_ncard_le_of_typeTwo
              C hcore hvCarrier hvy
      | typeThree C =>
          simpa [rooted, rank] using
            O.coreNeighbor_ncard_le_of_typeThree
              C hcore hvCarrier hvy
  | modified T K =>
      simpa [rooted, rank, excludedVertex] using
        K.coreNeighbor_ncard_le_of_modified
          hvCarrier hvy hvExcluded

/--
The equality case of COY Claim 3.3: an exterior vertex meeting the upper
bound has a neighbor in the working core's `T`-side.
-/
theorem exists_T_neighbor_of_coreNeighbor_ncard_eq
    (W : SelectedWorkingCore (z := z) O)
    {v : V}
    (hvCarrier : v ∉ W.rooted.core.carrier)
    (hvy : v ≠ y)
    (hvExcluded : v ≠ W.excludedVertex)
    (heq :
      (G.neighborSet v ∩
        (↑W.rooted.core.carrier : Set V)).ncard =
        W.rank + 1) :
    ∃ t ∈ W.rooted.core.T, G.Adj v t := by
  cases W with
  | natural hnot =>
      cases hcore : O.rooted.core with
      | typeOne C =>
          simpa [rooted, rank] using
            O.exists_T_neighbor_of_coreNeighbor_ncard_eq_typeOne
              C hcore heq
      | typeTwo C =>
          simpa [rooted, rank] using
            O.exists_T_neighbor_of_coreNeighbor_ncard_eq_typeTwo
              C hcore hvCarrier hvy heq
      | typeThree C =>
          simpa [rooted, rank] using
            O.exists_T_neighbor_of_coreNeighbor_ncard_eq_typeThree
              C hcore hvCarrier hvy heq
  | modified T K =>
      simpa [rooted, rank, excludedVertex] using
        K.exists_T_neighbor_of_coreNeighbor_ncard_eq_modified
          hvCarrier hvy hvExcluded heq

/--
For a selected type-three working core, an exterior vertex with a
`T`-neighbor is not adjacent to the root.
-/
theorem not_adj_root_of_typeThree_of_T_neighbor
    (W : SelectedWorkingCore (z := z) O)
    (C : TypeThreeCore G x W.rank)
    (hcore : W.rooted.core = .typeThree C)
    {v t : V}
    (hvCarrier : v ∉ W.rooted.core.carrier)
    (hvy : v ≠ y)
    (hvExcluded : v ≠ W.excludedVertex)
    (ht : t ∈ W.rooted.core.T)
    (hvt : G.Adj v t) :
    ¬G.Adj x v := by
  cases W with
  | natural hnot =>
      change O.rooted.core = .typeThree C at hcore
      change v ∉ O.rooted.core.carrier at hvCarrier
      have htC : t ∈ C.T := by
        have ht' := ht
        change t ∈ O.rooted.core.T at ht'
        rw [hcore] at ht'
        simpa [Core.T] using ht'
      exact
        O.not_adj_root_of_typeThree_of_T_neighbor
          C hcore hvCarrier hvy htC hvt
  | modified T K =>
      exact
        K.not_adj_root_of_exterior
          hvCarrier hvExcluded

end SelectedWorkingCore

end COY

end DeanK5
