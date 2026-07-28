import DeanK5.COYExteriorZEndBlock

/-!
# The degree equalities in COY Claim 3.9

Once the strict rank bound `ℓ ≤ q - 2` is available, the lower degree
hypothesis at the cut vertex `b_z`, its exact exterior degree two, and
Claim 3.3 force equality throughout:

`ℓ = q - 2` and `|N_G(b_z) ∩ V(H)| = ℓ + 1`.

This file isolates that numerical implication from the path argument that
proves the strict rank bound.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

namespace ExteriorZEndBlock

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/-- The exterior cut vertex is not the root of the working core. -/
theorem bz_ne_core_root
    (E : P.ExteriorZEndBlock) :
    E.bz ≠ x := by
  intro hbx
  have hbCarrier :
      E.bz ∈ P.working.rooted.core.carrier := by
    rw [hbx]
    exact P.working.rooted.core.root_mem_carrier
  exact
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      E.bz_mem_otherRegion hbCarrier

/--
The strict rank bound forces both equality conclusions in
COY Claim 3.9(1)--(2).

The side condition needed to apply Claim 3.3 is discharged by the exterior
adapter from the protected nonedge `xz`.
-/
theorem rank_eq_sub_two_and_coreNeighbor_ncard_eq
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hRank : P.working.rank ≤ q - 2) :
    P.working.rank = q - 2 ∧
      (G.neighborSet E.bz ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard =
          P.working.rank + 1 := by
  have hdegreeLower :
      q + 1 ≤ finiteDegree G E.bz :=
    M.degree_lower E.bz E.bz_ne_core_root
      E.bz_ne_y E.bz_ne_z
  have hdegreeLedger :=
    E.finiteDegree_bz_eq_two_add_coreNeighbors
  have hbzNotCarrier :
      E.bz ∉ P.working.rooted.core.carrier :=
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      E.bz_mem_otherRegion
  have hExcluded :
      E.bz ≠ P.working.excludedVertex :=
    E.bz_ne_excludedVertex
      M.left_root_not_adj_exception
  have hdegreeUpper :=
    P.working.coreNeighbor_ncard_le
      hbzNotCarrier E.bz_ne_y hExcluded
  have hqTwo := M.two_le_q
  constructor <;> omega

/--
In the same equality case, Claim 3.3 supplies a neighbour of `b_z` in
the working core's `T`-side.
-/
theorem rank_degree_equalities_and_exists_T_neighbor
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hRank : P.working.rank ≤ q - 2) :
    P.working.rank = q - 2 ∧
      (G.neighborSet E.bz ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard =
          P.working.rank + 1 ∧
      ∃ t ∈ P.working.rooted.core.T, G.Adj E.bz t := by
  obtain ⟨hRankEq, hDegreeEq⟩ :=
    E.rank_eq_sub_two_and_coreNeighbor_ncard_eq
      M hRank
  have hbzNotCarrier :
      E.bz ∉ P.working.rooted.core.carrier :=
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      E.bz_mem_otherRegion
  have hExcluded :
      E.bz ≠ P.working.excludedVertex :=
    E.bz_ne_excludedVertex
      M.left_root_not_adj_exception
  obtain ⟨t, htT, hbt⟩ :=
    P.working.exists_T_neighbor_of_coreNeighbor_ncard_eq
      hbzNotCarrier E.bz_ne_y hExcluded hDegreeEq
  exact ⟨hRankEq, hDegreeEq, t, htT, hbt⟩

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
