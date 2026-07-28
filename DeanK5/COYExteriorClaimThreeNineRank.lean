import DeanK5.COYClaimThreeNineOuter
import DeanK5.COYExteriorClaimThreeEight
import DeanK5.COYExteriorClaimThreeNineDegree

/-!
# The rank contradiction in COY Claim 3.9

This file proves the strict rank bound in Claim 3.9(1).  If the selected
working rank were `q - 1`, Fact 3 would exclude every attachment from the
working `T`-side.  Connectivity then forces an `S`-attachment at `z`, while
the two consecutive outer paths exclude an `S`-attachment at the cut vertex
`b_z`.

Consequently every working-core neighbour of `b_z` is the root `x`.  The
exact exterior degree two and the ambient degree lower bound force `q = 2`
and working rank one.  The three possible core types are then impossible:
type 1 has empty `S`, type 2 has rank at least two, and a rank-one type-3
core has singleton `S`, so Claim 3.8 supplies the forbidden `T`-attachment.

The final theorem feeds this strict bound into the separate degree ledger,
yielding both numerical conclusions of Claim 3.9(1)--(2).
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

/--
COY Claim 3.9(1), in its inequality form: the selected working rank is at
most `q - 2`.
-/
theorem rank_le_sub_two
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock) :
    P.working.rank ≤ q - 2 := by
  have hfact :=
    M.rootedCore_factThree P.working.rooted
  have hRankLt :
      P.working.rank < q :=
    hfact.1
  by_contra hnotRank
  have hRankEq :
      P.working.rank = q - 1 := by
    have hq := M.two_le_q
    omega
  have hnoT :
      ¬P.working.rooted.core.HasTAttachment
        P.working.rooted.otherRegion := by
    intro hT
    have hstrong := hfact.2 hT
    omega
  obtain ⟨sZ, hsZS, _hsZz⟩ :=
    E.exists_S_attachment_of_no_T M hnoT
  have hnoSAtBz :
      ∀ s ∈ P.working.rooted.core.S,
        ¬G.Adj s E.bz :=
    E.no_S_attachment_of_no_T_of_rank_add_one_eq
      M (by omega) hnoT
  have hcoreNeighborSubset :
      G.neighborSet E.bz ∩
          (↑P.working.rooted.core.carrier : Set V) ⊆
        ({x} : Set V) := by
    intro v hv
    have hvAdj : G.Adj E.bz v :=
      hv.1
    have hvCarrier :
        v ∈ P.working.rooted.core.carrier :=
      hv.2
    by_cases hvx : v = x
    · simp [hvx]
    rcases
        P.working.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
          hvCarrier hvx with
      hvS | hvT
    · exact False.elim
        ((hnoSAtBz v hvS) hvAdj.symm)
    · exact False.elim (hnoT
        ⟨E.bz, E.bz_mem_otherRegion, v, hvT, hvAdj.symm⟩)
  have hcoreNeighborUpper :
      (G.neighborSet E.bz ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard ≤ 1 := by
    calc
      (G.neighborSet E.bz ∩
          (↑P.working.rooted.core.carrier : Set V)).ncard ≤
          ({x} : Set V).ncard :=
        Set.ncard_le_ncard hcoreNeighborSubset
      _ = 1 := by simp
  have hdegreeLower :
      q + 1 ≤ finiteDegree G E.bz :=
    M.degree_lower E.bz E.bz_ne_core_root
      E.bz_ne_y E.bz_ne_z
  have hdegreeLedger :=
    E.finiteDegree_bz_eq_two_add_coreNeighbors
  have hqTwo : 2 ≤ q :=
    M.two_le_q
  have hqEq : q = 2 := by
    omega
  have hRankOne :
      P.working.rank = 1 := by
    omega
  cases hcore : P.working.rooted.core with
  | typeOne C =>
      simp [hcore, Core.S] at hsZS
  | typeTwo C =>
      have hrankTwo := C.rank_ge_two
      omega
  | typeThree C =>
      have hcardS : C.S.card = 1 := by
        rw [C.card_S, hRankOne]
      have hregion :
          P.working.rooted.otherRegion ≠ {y} := by
        intro hsingleton
        have hzSingleton :
            z ∈ ({y} : Finset V) := by
          simpa [hsingleton] using E.z_mem_otherRegion
        have hzy : z = y := by
          simpa using hzSingleton
        exact E.y_ne_z hzy.symm
      have hT :
          (Core.typeThree C).HasTAttachment
            P.working.rooted.otherRegion :=
        hasTAttachment_of_typeThree_card_S_one
          M P C hcore hcardS hregion
      apply hnoT
      simpa [hcore] using hT

/--
The complete numerical conclusion of COY Claim 3.9(1)--(2): the working
rank is exactly `q - 2`, and `b_z` has exactly `rank + 1` neighbours in
the working core.
-/
theorem claim_three_nine_rank_and_core_neighbor_count
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock) :
    P.working.rank = q - 2 ∧
      (G.neighborSet E.bz ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard =
          P.working.rank + 1 :=
  E.rank_eq_sub_two_and_coreNeighbor_ncard_eq
    M (E.rank_le_sub_two M)

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
