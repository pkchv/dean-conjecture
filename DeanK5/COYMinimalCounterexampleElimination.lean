import DeanK5.COYExteriorFinalBlockAnalysis

/-!
# Eliminating the COY minimal counterexample

The exterior analysis eliminates a minimal counterexample once a preferred
working core has been selected.  The root-orientation theorem supplies such
a core either in the original orientation or after exchanging the two
roots, so no minimal counterexample exists.
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
Any preferred working-core selection inside a minimal counterexample leads
to the completed final block contradiction.
-/
theorem impossible
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z) :
    False := by
  have hregion :
      P.working.rooted.otherRegion ≠ {y} :=
    P.otherRegion_ne_singleton M
  obtain ⟨D⟩ :=
    TypeThreeStage.exists_data M P
  let hall :
      P.AllFeasibleBlocksMeetProtectedInterior :=
    allFeasibleBlocksMeetProtectedInterior M P D
  let O :
      P.ExteriorOrderedBlockChain :=
    exteriorOrderedBlockChain M P D hregion hall
  exact
    O.false_of_lastFeasible_analysis
      M D hregion hall

end PreferredWorkingCoreData

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
No bounded COY minimal counterexample exists.  The reverse-orientation
branch is discharged by the root-swapped minimal counterexample.
-/
theorem impossible
  (M : MinimalCounterexample q G x y z) :
    False := by
  rcases M.preferredWorkingCoreData_or_swap with
    hforward | hreverse
  · obtain ⟨P⟩ := hforward
    exact P.impossible M
  · obtain ⟨P⟩ := hreverse
    exact P.impossible M.swapRoots

end MinimalCounterexample

end COY

end DeanK5
