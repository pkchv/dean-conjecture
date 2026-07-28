import DeanK5.COYExteriorNonsingleton
import DeanK5.COYExteriorClaimThreeTwelve

/-!
# Excluding a type-one core in the nonsingleton exterior

COY Case 2.1 is the immediate consequence of Claim 3.12(2).  A type-one
core has empty `S`, so every initial-side attachment of the chosen feasible
block would have to be the root `x`.  Claim 3.12(2) supplies at least two
distinct such attachments.
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
COY Case 2.1: the selected feasible exterior block is incompatible with a
type-one working core.
-/
theorem false_of_typeNumber_eq_one
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (htype : P.working.rooted.core.typeNumber = 1) :
    False := by
  classical
  cases hcore : P.working.rooted.core with
  | typeOne K =>
      have hsubset : C.initialBoundary ⊆ {x} := by
        intro v hv
        have hvRootS :=
          (C.mem_initialBoundary.mp hv).1
        have hvx : v = x := by
          simpa [hcore, Core.S] using hvRootS
        simp [hvx]
      have hcard :
          C.initialBoundary.card ≤ 1 := by
        have :=
          Finset.card_le_card hsubset
        simpa using this
      have htwo :=
        C.two_le_initialBoundary_card M
      omega
  | typeTwo K =>
      simp [hcore, Core.typeNumber] at htype
  | typeThree K =>
      simp [hcore, Core.typeNumber] at htype

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The selected working core in a minimal counterexample is not type one. -/
theorem typeNumber_ne_one
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z) :
    P.working.rooted.core.typeNumber ≠ 1 := by
  classical
  intro htype
  obtain ⟨C⟩ :=
    P.exists_exteriorFeasibleBlockChoice M
      (P.otherRegion_ne_singleton M)
  exact C.false_of_typeNumber_eq_one M htype

end PreferredWorkingCoreData

end COY

end DeanK5
