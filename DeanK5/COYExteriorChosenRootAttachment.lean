import DeanK5.COYExteriorClaimThreeFifteenSetup

/-!
# Choosing the root attachment supplied by equation (3.2)

At the rank-one type-three stage, equation (3.2) says that the working-core
vertices attached to the interior of any feasible exterior block are exactly
the root `x` and the unique vertex of the `S`-side.  This file packages the
resulting concrete edge from `x` into the block.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
The singleton `S`-side and a chosen edge from the core root into the
nonanchor part of a feasible exterior block.
-/
structure ChosenRootAttachmentData
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice) where
  /-- The unique vertex on the `S`-side of the type-three core. -/
  side : V
  /-- The rank-one side is the singleton containing `side`. -/
  side_eq : D.core.S = {side}
  /-- Equation (3.2) for the chosen feasible block. -/
  coreAttachments_eq_pair :
    C.coreAttachments = {x, side}
  /-- A block-interior neighbor of the core root. -/
  attachment : V
  /-- The chosen attachment is in the block with its anchor removed. -/
  attachment_mem_interior :
    attachment ∈ C.compressionInterior
  /-- The core root is adjacent to the chosen attachment. -/
  root_adj_attachment :
    G.Adj x attachment

namespace ChosenRootAttachmentData

variable
  {P : PreferredWorkingCoreData G x y z}
  {D : P.TypeThreeStage}
  {C : P.ExteriorFeasibleBlockChoice}

/-- The chosen attachment belongs to the full ambient block carrier. -/
theorem attachment_mem_ambientCarrier
    (A : P.ChosenRootAttachmentData D C) :
    A.attachment ∈ C.ambientCarrier :=
  Finset.mem_of_mem_erase A.attachment_mem_interior

/-- The chosen attachment is distinct from the retained block anchor. -/
theorem attachment_ne_anchor
    (A : P.ChosenRootAttachmentData D C) :
    A.attachment ≠ C.b :=
  (Finset.mem_erase.mp A.attachment_mem_interior).1

/-- The chosen attachment lies in the selected exterior component. -/
theorem attachment_mem_otherRegion
    (A : P.ChosenRootAttachmentData D C) :
    A.attachment ∈ P.working.rooted.otherRegion :=
  C.ambientCarrier_subset_otherRegion
    A.attachment_mem_ambientCarrier

/-- The chosen attachment is outside the selected working-core carrier. -/
theorem attachment_not_mem_core
    (A : P.ChosenRootAttachmentData D C) :
    A.attachment ∉ P.working.rooted.core.carrier := by
  intro haCore
  exact
    Finset.disjoint_left.mp C.compressionInterior_disjoint_core
      A.attachment_mem_interior haCore

/-- In particular, the chosen exterior attachment is not a `T`-vertex. -/
theorem attachment_not_mem_terminal
    (A : P.ChosenRootAttachmentData D C) :
    A.attachment ∉ D.core.T := by
  intro haTerminal
  apply A.attachment_not_mem_core
  rw [D.core_eq]
  exact
    (Core.typeThree D.core).T_subset_carrier
      (by simpa [Core.T] using haTerminal)

end ChosenRootAttachmentData

namespace ExteriorFeasibleBlockChoice

variable {P : PreferredWorkingCoreData G x y z}

/--
Claim 3.13 and equation (3.2) choose a root attachment in the nonanchor
interior of any feasible exterior block.
-/
noncomputable def chosenRootAttachmentData
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice) :
    P.ChosenRootAttachmentData D C := by
  let boundaryData :=
    C.exists_claimThreeFifteen_boundary_data M D
  let s : V :=
    Classical.choose boundaryData
  have hside :
      D.core.S = {s} :=
    (Classical.choose_spec boundaryData).1
  have hboundary :
      C.coreAttachments = {x, s} :=
    (Classical.choose_spec boundaryData).2
  let attachmentData :=
    C.exists_root_attachment_in_compressionInterior
      hboundary
  let a : V :=
    Classical.choose attachmentData
  have haInterior :
      a ∈ C.compressionInterior :=
    (Classical.choose_spec attachmentData).1
  have hxa :
      G.Adj x a :=
    (Classical.choose_spec attachmentData).2
  exact {
    side := s
    side_eq := hside
    coreAttachments_eq_pair := hboundary
    attachment := a
    attachment_mem_interior := haInterior
    root_adj_attachment := hxa
  }

end ExteriorFeasibleBlockChoice

end PreferredWorkingCoreData

end COY

end DeanK5
