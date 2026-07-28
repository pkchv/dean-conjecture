import DeanK5.COYExteriorClaimThreeFifteenMultiple

/-!
# COY Claim 3.15

For every feasible exterior block with its source anchor data:

1. `B-b` contains the second root `y` or the selected second exception
   `z'`;
2. the selected exterior component is not itself the chosen block.

Both alternatives in the source split on
`|N_G(s₁) ∩ V(B)|` are discharged by the concrete recursive graphs
formalized in the preceding files.
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

/-- COY Claim 3.15(1), for an arbitrary feasible anchored exterior block. -/
theorem claim_three_fifteen_part_one
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice) :
    C.MeetsProtectedInterior := by
  obtain ⟨s, hS, hboundary⟩ :=
    C.exists_claimThreeFifteen_boundary_data M D
  rcases
      C.sideBlockNeighbors_eq_singleton_or_two_le
        hboundary with
    ⟨v, hsingleton⟩ | hmultiple
  · exact
      C.meetsProtectedInterior_of_sideBlockNeighbors_eq_singleton
        M D hS hboundary hsingleton
  · exact
      C.meetsProtectedInterior_of_two_le_sideBlockNeighbors
        M D hS hboundary hmultiple

/-- COY Claim 3.15(2): the selected exterior is not itself the chosen block. -/
theorem claim_three_fifteen_part_two
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice) :
    ¬C.SpansExterior :=
  C.not_spansExterior_of_meetsProtectedInterior
    M D (C.claim_three_fifteen_part_one M D)

/-- The two conclusions of COY Claim 3.15 in one source-shaped theorem. -/
theorem claim_three_fifteen
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice) :
    C.MeetsProtectedInterior ∧
      ¬C.SpansExterior :=
  ⟨C.claim_three_fifteen_part_one M D,
    C.claim_three_fifteen_part_two M D⟩

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
