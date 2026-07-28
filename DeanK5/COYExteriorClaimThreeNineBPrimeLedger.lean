import DeanK5.COYExteriorClaimThreeNineNoT
import DeanK5.COYExteriorClaimThreeNineRank

/-!
# The final degree ledger in COY Claim 3.9

This file isolates the numerical part of Claim 3.9(4).  Once the second
exterior neighbour `b'_z` is known not to be the vertex excluded by
Claim 3.3, the no-`T` conclusion from Claim 3.9(3) sharpens the core
attachment bound from `rank + 1` to `rank`.  The exact component-degree
decomposition then forces the exterior degree of `b'_z` to be at least
three.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

namespace ExteriorZEndBlock

/--
The ambient degree of `b'_z` splits exactly into its degree in the selected
exterior component and its number of neighbours in the working core.
-/
theorem finiteDegree_bPrime_eq_exterior_add_coreNeighbors
    (E : P.ExteriorZEndBlock) :
    finiteDegree G E.bPrime =
      finiteDegree P.exteriorGraph E.certificate.bPrime +
        (G.neighborSet E.bPrime ∩
          (↑P.working.rooted.core.carrier : Set V)).ncard := by
  have hdegree :=
    ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
      P.working.rooted.otherRegion_componentRegion
      E.bPrime_mem_otherRegion
  have hPrimeSubtype :
      (⟨E.bPrime, E.bPrime_mem_otherRegion⟩ :
        P.ExteriorVertex) =
          E.certificate.bPrime :=
    Subtype.ext (by rfl)
  rw [hPrimeSubtype] at hdegree
  exact hdegree

/--
If Claim 3.3 applies at `b'_z`, then Claim 3.9(3) rules out its equality
case and leaves at most `rank` neighbours in the working core.
-/
theorem coreNeighbor_ncard_bPrime_le_rank
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hPrimeY : E.bPrime ≠ y)
    (hExcluded :
      E.bPrime ≠ P.working.excludedVertex) :
    (G.neighborSet E.bPrime ∩
      (↑P.working.rooted.core.carrier : Set V)).ncard ≤
        P.working.rank := by
  have hNotCarrier :
      E.bPrime ∉ P.working.rooted.core.carrier :=
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      E.bPrime_mem_otherRegion
  have hupper :=
    P.working.coreNeighbor_ncard_le
      hNotCarrier hPrimeY hExcluded
  by_contra hnot
  have heq :
      (G.neighborSet E.bPrime ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard =
          P.working.rank + 1 := by
    omega
  obtain ⟨t, htT, hPrimeT⟩ :=
    P.working.exists_T_neighbor_of_coreNeighbor_ncard_eq
      hNotCarrier hPrimeY hExcluded heq
  have hno :=
    E.no_T_neighbor_of_z_or_bPrime M
      (E.rank_le_sub_two M)
  have ht :
      t ∈
        (G.neighborSet z ∪ G.neighborSet E.bPrime) ∩
          (↑P.working.rooted.core.T : Set V) := by
    exact ⟨Or.inr hPrimeT, htT⟩
  rw [hno] at ht
  exact ht

/--
The numerical conclusion of Claim 3.9(4), conditional only on excluding
the special vertex omitted from Claim 3.3.
-/
theorem three_le_exterior_degree_bPrime_of_ne_excluded
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hPrimeY : E.bPrime ≠ y)
    (hExcluded :
      E.bPrime ≠ P.working.excludedVertex) :
    3 ≤ finiteDegree P.exteriorGraph E.certificate.bPrime := by
  have hPrimeX : E.bPrime ≠ x := by
    intro h
    have hPrimeCarrier :
        E.bPrime ∈ P.working.rooted.core.carrier := by
      simpa only [h] using
        P.working.rooted.core.root_mem_carrier
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        E.bPrime_mem_otherRegion
        hPrimeCarrier
  have hdegreeLower :
      q + 1 ≤ finiteDegree G E.bPrime :=
    M.degree_lower E.bPrime hPrimeX hPrimeY E.bPrime_ne_z
  have hdegreeSplit :=
    E.finiteDegree_bPrime_eq_exterior_add_coreNeighbors
  have hcoreUpper :=
    E.coreNeighbor_ncard_bPrime_le_rank
      M hPrimeY hExcluded
  have hRankEq :=
    (E.claim_three_nine_rank_and_core_neighbor_count M).1
  have hqTwo := M.two_le_q
  omega

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
