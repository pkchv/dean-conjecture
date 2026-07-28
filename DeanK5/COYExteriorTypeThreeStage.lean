import DeanK5.COYExteriorTypeOne
import DeanK5.COYExteriorTypeTwoClose

/-!
# Entering the type-three exterior stage

The type-one and type-two exterior cases have been eliminated.  This file
packages the remaining type-three working core and records the positive-rank
consequence of Claim 3.12(2).
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The working core at the remaining exterior stage is explicitly type 3. -/
structure TypeThreeStage
    (P : PreferredWorkingCoreData G x y z) where
  /-- The source type-3 core. -/
  core : TypeThreeCore G x P.working.rank
  /-- Identification with the selected working core. -/
  core_eq : P.working.rooted.core = .typeThree core

namespace TypeThreeStage

variable {P : PreferredWorkingCoreData G x y z}

/-- Eliminating source types 1 and 2 produces the type-three stage. -/
theorem exists_data
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z) :
    Nonempty P.TypeThreeStage := by
  cases hcore : P.working.rooted.core with
  | typeOne K =>
      exact False.elim
        (P.typeNumber_ne_one M
          (by rw [hcore]; rfl))
  | typeTwo K =>
      exact False.elim
        (P.typeNumber_ne_two M
          (by rw [hcore]; rfl))
  | typeThree K =>
      exact ⟨{
        core := K
        core_eq := hcore
      }⟩

/--
Claim 3.12(2) gives a genuine `S`-attachment, so the type-three side `S`
is nonempty.
-/
theorem side_nonempty
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage) :
    D.core.S.Nonempty := by
  obtain ⟨B⟩ :=
    P.exists_exteriorFeasibleBlockChoice M
      (P.otherRegion_ne_singleton M)
  obtain ⟨s, hs⟩ :=
    B.initialAttachments_nonempty M
  have hsCore :=
    B.initialAttachments_subset_coreS hs
  have hsSide : s ∈ D.core.S := by
    simpa [D.core_eq, Core.S] using hsCore
  exact ⟨s, hsSide⟩

/-- The rank `|S|` at the type-three stage is positive. -/
theorem rank_pos
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage) :
    1 ≤ P.working.rank := by
  have hcardPos :
      0 < D.core.S.card :=
    Finset.card_pos.mpr (D.side_nonempty M)
  rw [D.core.card_S] at hcardPos
  omega

/-- Choose one explicit vertex of the nonempty type-three side. -/
theorem exists_side_vertex
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage) :
    ∃ s, s ∈ D.core.S :=
  D.side_nonempty M

end TypeThreeStage

end PreferredWorkingCoreData

end COY

end DeanK5
