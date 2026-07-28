import DeanK5.COYExteriorClaimThreeTwelveEmptyClose
import DeanK5.COYExteriorClaimThreeTwelveSingletonClose

/-!
# COY Claim 3.12

Claim 3.12(1) excludes terminal-side attachments.  The singleton and empty
alternatives for the remaining initial-side boundary each produce a
forbidden ambient admissible path family.  Therefore at least two vertices
of `{x} ∪ S` meet `B - b`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/--
COY Claim 3.12(2): at least two initial-side core vertices have an edge
to the interior of the selected feasible exterior block.
-/
theorem two_le_initialBoundary_card
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice) :
    2 ≤ C.initialBoundary.card := by
  by_contra hsmall
  have hcases :
      C.initialBoundary.card = 0 ∨
        C.initialBoundary.card = 1 := by
    omega
  rcases hcases with hzero | hone
  · let D : EmptyInitialBoundary C := {
      boundary_eq := Finset.card_eq_zero.mp hzero
    }
    exact D.false_of_empty_initialBoundary M
  · obtain ⟨v, hv⟩ :=
      Finset.card_eq_one.mp hone
    let D : SingletonInitialBoundary C := {
      vertex := v
      boundary_eq := hv
    }
    exact D.false_of_singleton_initialBoundary M

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
