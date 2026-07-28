import DeanK5.COYExteriorClaimThreeNineNoT
import DeanK5.COYExteriorClaimThreeNineRank
import DeanK5.COYPathOperations
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Excluding the three-vertex exterior in COY Claim 3.10

Under the degree-two `z`-end-block setup of Claim 3.9, an exterior
`(y,z)`-path of order three has vertex set exactly `{z, b_z, y}`.  This
file formalizes the two source contradictions:

* a type-2 working core supplies the four forbidden path lengths directly;
* a type-3 working core contradicts the degree and distance tie-breaks
  (XY2)--(XY3).
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
In the Claim 3.9 setup, saying that the exterior is a `(y,z)`-path of
order three is equivalent to saying that its vertex set is
`{z, b_z, y}`: the certificate already supplies the edges
`z-b_z-b'_z`, the unique exterior neighbour of `z`, and degree two at
`b_z`.
-/
def IsOrderThreePath
    (E : P.ExteriorZEndBlock) : Prop :=
  P.working.rooted.otherRegion = {z, E.bz, y}

/-- In an order-three exterior, the second neighbour `b'_z` is `y`. -/
theorem bPrime_eq_y_of_isOrderThreePath
    (E : P.ExteriorZEndBlock)
    (hthree : E.IsOrderThreePath) :
    E.bPrime = y := by
  have hmem :
      E.bPrime ∈ ({z, E.bz, y} : Finset V) := by
    rw [← hthree]
    exact E.bPrime_mem_otherRegion
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hpz | hpb | hpy
  · exact False.elim (E.bPrime_ne_z hpz)
  · exact False.elim (E.bPrime_ne_bz hpb)
  · exact hpy

/--
Claim 3.9(3) excludes every edge from `z` to the working core's `T`-side.
-/
theorem no_T_neighbor_of_z
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock) :
    ∀ t ∈ P.working.rooted.core.T, ¬G.Adj t z := by
  have hno :=
    E.no_T_neighbor_of_z_or_bPrime M
      (E.rank_le_sub_two M)
  intro t htT htz
  have ht :
      t ∈
        (G.neighborSet z ∪ G.neighborSet E.bPrime) ∩
          (↑P.working.rooted.core.T : Set V) := by
    exact ⟨Or.inl htz.symm, htT⟩
  rw [hno] at ht
  exact ht

/--
Claim 3.9(3) also excludes every edge from `b'_z` to the working
core's `T`-side.
-/
theorem no_T_neighbor_of_bPrime
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock) :
    ∀ t ∈ P.working.rooted.core.T,
      ¬G.Adj t E.bPrime := by
  have hno :=
    E.no_T_neighbor_of_z_or_bPrime M
      (E.rank_le_sub_two M)
  intro t htT htPrime
  have ht :
      t ∈
        (G.neighborSet z ∪ G.neighborSet E.bPrime) ∩
          (↑P.working.rooted.core.T : Set V) := by
    exact ⟨Or.inr htPrime.symm, htT⟩
  rw [hno] at ht
  exact ht

/--
Deleting `b_z` and following a path from `z` to the core root yields an
`S`-attachment at `z`.  This is the local form of the connectivity
argument used in Claims 3.9 and 3.10; only the no-`T` conclusion at `z`
is required.
-/
theorem exists_S_neighbor_of_z
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock) :
    ∃ s ∈ P.working.rooted.core.S, G.Adj s z := by
  classical
  let Q := P.working.rooted.otherRegion
  let C := P.working.rooted.core
  have hQ : ComponentRegion G C.carrier Q :=
    P.working.rooted.otherRegion_componentRegion
  have hxCarrier : x ∈ C.carrier :=
    C.root_mem_carrier
  have hzx : z ≠ x := by
    intro hzx
    exact hQ.not_mem_separator E.z_mem_otherRegion
      (hzx ▸ hxCarrier)
  have hxbz : x ≠ E.bz := by
    intro hxbz
    exact hQ.not_mem_separator E.bz_mem_otherRegion
      (hxbz ▸ hxCarrier)
  let zDeleted :
      {v : V // v ∉ ({E.bz} : Finset V)} :=
    ⟨z, by simpa using E.z_ne_bz⟩
  let xDeleted :
      {v : V // v ∉ ({E.bz} : Finset V)} :=
    ⟨x, by simpa using hxbz⟩
  have hzxDeleted : zDeleted ≠ xDeleted := by
    intro h
    exact hzx (congrArg Subtype.val h)
  have hdeletedConnected :
      (G.induce
        {v : V | v ∉ ({E.bz} : Finset V)}).Connected :=
    M.underlying_two_connected.2
      {E.bz} (by simp)
  obtain ⟨p, hp⟩ :=
    hdeletedConnected.exists_isPath zDeleted xDeleted
  obtain ⟨v, hzvDeleted, tail, hpEq⟩ :=
    p.exists_eq_cons_of_ne hzxDeleted
  have hzv : G.Adj z v.1 :=
    hzvDeleted
  have hvNotQ : v.1 ∉ Q := by
    intro hvQ
    have hzvExterior :
        P.exteriorGraph.Adj
          (P.exteriorZ E.z_mem_otherRegion) ⟨v.1, hvQ⟩ :=
      hzv
    have hvbzSubtype :=
      (E.certificate.adj_z_iff ⟨v.1, hvQ⟩).mp
        hzvExterior
    have hvbz : v.1 = E.bz :=
      congrArg Subtype.val hvbzSubtype
    exact v.2 (by simpa using hvbz)
  have hvCarrier : v.1 ∈ C.carrier := by
    by_contra hvNotCarrier
    exact hvNotQ
      (hQ.closed E.z_mem_otherRegion hzv hvNotCarrier)
  have hvx : v.1 ≠ x := by
    intro hvx
    apply M.left_root_not_adj_exception
    exact hvx ▸ hzv.symm
  rcases C.mem_S_or_mem_T_of_mem_carrier_of_ne_root
      hvCarrier hvx with
    hvS | hvT
  · exact ⟨v.1, hvS, hzv.symm⟩
  · exact False.elim
      (E.no_T_neighbor_of_z M v.1 hvT hzv.symm)

/-- A core vertex cannot lie in the selected exterior component. -/
private theorem not_mem_otherRegion_of_mem_carrier
    (_E : P.ExteriorZEndBlock)
    {v : V} (hv : v ∈ P.working.rooted.core.carrier) :
    v ∉ P.working.rooted.otherRegion := by
  intro hvQ
  exact
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      hvQ hv

/--
The type-2 branch of Claim 3.10.  Since a type-2 core has rank at least
two and Claim 3.9 gives `rank = q - 2 ≤ 2`, this branch is necessarily
`q = 4`, `rank = 2`.  Fact 2 supplies lengths `3,4,5` through a
`T`-neighbour of `b_z`; its longest path to the `S`-neighbour of `z`,
followed by `s-z-b_z`, supplies length `6`.
-/
private theorem false_of_isOrderThreePath_of_typeTwo
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hthree : E.IsOrderThreePath)
    (C : TypeTwoCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeTwo C) :
    False := by
  classical
  obtain ⟨hRankEq, -, tb, htbT, hbzTb⟩ :=
    E.rank_degree_equalities_and_exists_T_neighbor
      M (E.rank_le_sub_two M)
  have hqFour := M.q_le_four
  have hqEq : q = 4 := by
    have htwo := C.rank_ge_two
    omega
  have hRankEqTwo : P.working.rank = 2 := by
    omega
  have htbTC : tb ∈ C.T := by
    simpa [hcore, Core.T] using htbT
  obtain ⟨sz, hszS, hszAdj⟩ :=
    E.exists_S_neighbor_of_z M
  have hszSC : sz ∈ C.S := by
    simpa [hcore, Core.S] using hszS
  have hPrimeY : E.bPrime = y :=
    E.bPrime_eq_y_of_isOrderThreePath hthree
  have hbzY : G.Adj E.bz y := by
    simpa [hPrimeY] using E.bz_adj_bPrime
  have htbNeBz : tb ≠ E.bz := by
    intro h
    exact E.not_mem_otherRegion_of_mem_carrier
      (P.working.rooted.core.T_subset_carrier htbT)
      (h ▸ E.bz_mem_otherRegion)
  have htbNeY : tb ≠ y := by
    intro h
    exact P.working.rooted.other_root_not_mem
      (h ▸ P.working.rooted.core.T_subset_carrier htbT)
  let tbY : SimplePath G tb y :=
    SimplePath.ofVertexList [E.bz]
      (by simp [hbzTb.symm, hbzY])
      (by simp [htbNeBz, htbNeY, E.bz_ne_y])
  let innerT :
      SemiAdmissiblePathFamily G x tb 3 :=
    C.semiAdmissiblePathsToT tb htbTC 3
      (by omega) (by omega) (by omega)
  let innerTAdmissible :
      AdmissiblePathFamily G x tb 3 :=
    innerT.toAdmissible (by rfl)
  have hdisjointT (i : Fin 3) :
      (innerTAdmissible.path i).walk.support.Disjoint
        tbY.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvInner hvTail
    have hvCore :
        v ∈ P.working.rooted.core.carrier := by
      have hvInner' :
          v ∈ (innerT.path i).walk.support := by
        change v ∈ (innerT.path i).walk.support at hvInner
        exact hvInner
      have hvSmall :=
        C.semiAdmissiblePathsToT_support
          tb htbTC 3 (by omega) (by omega) (by omega)
          i v (by simpa [innerT] using hvInner')
      simpa [hcore, Core.carrier, Core.S, Core.T] using hvSmall
    have hvExterior :
        v ∈ P.working.rooted.otherRegion := by
      have hvPair : v ∈ [E.bz, y] := by
        simpa [tbY] using hvTail
      simp at hvPair
      rcases hvPair with rfl | rfl
      · exact E.bz_mem_otherRegion
      · exact P.working.rooted.other_root_mem_otherRegion
    exact E.not_mem_otherRegion_of_mem_carrier hvCore hvExterior
  let firstThree :
      AdmissiblePathFamily G x y 3 :=
    innerTAdmissible.appendFixed tbY hdisjointT
  let innerS :
      AdmissiblePathFamily G x sz 2 :=
    C.admissiblePathsToS sz hszSC 2
      (by omega) (by omega) (by omega)
  let lastInner : SimplePath G x sz :=
    innerS.path (1 : Fin 2)
  have hszNeZ : sz ≠ z := by
    intro h
    exact E.not_mem_otherRegion_of_mem_carrier
      (P.working.rooted.core.S_subset_carrier hszS)
      (h ▸ E.z_mem_otherRegion)
  have hszNeBz : sz ≠ E.bz := by
    intro h
    exact E.not_mem_otherRegion_of_mem_carrier
      (P.working.rooted.core.S_subset_carrier hszS)
      (h ▸ E.bz_mem_otherRegion)
  have hszNeY : sz ≠ y := by
    intro h
    exact P.working.rooted.other_root_not_mem
      (h ▸ P.working.rooted.core.S_subset_carrier hszS)
  let szY : SimplePath G sz y :=
    SimplePath.ofVertexList [z, E.bz]
      (by simp [hszAdj, E.z_adj_bz, hbzY])
      (by simp [hszNeZ, hszNeBz, hszNeY,
        E.z_ne_bz, E.y_ne_z.symm, E.y_ne_bz.symm])
  have hdisjointS :
      lastInner.walk.support.Disjoint
        szY.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvInner hvTail
    have hvCore :
        v ∈ P.working.rooted.core.carrier := by
      have hvSmall :=
        C.admissiblePathsToS_support
          sz hszSC 2 (by omega) (by omega) (by omega)
          (1 : Fin 2) v
          (by simpa [lastInner, innerS] using hvInner)
      simpa [hcore, Core.carrier, Core.S, Core.T] using hvSmall
    have hvExterior :
        v ∈ P.working.rooted.otherRegion := by
      have hvTriple : v ∈ [z, E.bz, y] := by
        simpa [szY] using hvTail
      simp at hvTriple
      rcases hvTriple with rfl | rfl | rfl
      · exact E.z_mem_otherRegion
      · exact E.bz_mem_otherRegion
      · exact P.working.rooted.other_root_mem_otherRegion
    exact E.not_mem_otherRegion_of_mem_carrier hvCore hvExterior
  let lastPath : SimplePath G x y :=
    lastInner.appendDisjoint szY hdisjointS
  have hfirstLength (i : Fin 3) :
      (firstThree.path i).length = 4 + i.val := by
    rw [AdmissiblePathFamily.appendFixed_path,
      SimplePath.appendDisjoint_length]
    change
      (innerT.path i).length + tbY.length =
        4 + i.val
    rw [innerT.length_path]
    have hstart : innerT.start = 2 := rfl
    have hstep : innerT.step = 1 := rfl
    rw [hstart, hstep]
    have htbYLength : tbY.length = 2 := by
      simp [tbY]
    rw [htbYLength]
    omega
  have hlastLength : lastPath.length = 7 := by
    dsimp only [lastPath]
    rw [SimplePath.appendDisjoint_length]
    have hinner := innerS.length_path (1 : Fin 2)
    change lastInner.length + szY.length = 7
    rw [show lastInner.length = innerS.start + 1 * innerS.step by
      simpa [lastInner] using hinner]
    have hszYLength : szY.length = 3 := by
      simp [szY]
    rw [hszYLength]
    simp [innerS,
      TypeTwoCore.admissiblePathsToS,
      PointedTypeTwoSCore.factTwoTypeTwoBounded]
  let family : AdmissiblePathFamily G x y 4 := {
    start := 4
    step := 1
    admissible_step := Or.inl rfl
    start_ge_two := by omega
    path := ![
      firstThree.path 0,
      firstThree.path 1,
      firstThree.path 2,
      lastPath]
    length_path := by
      intro i
      fin_cases i
      · simpa using hfirstLength 0
      · simpa using hfirstLength 1
      · simpa using hfirstLength 2
      · simpa using hlastLength
  }
  apply M.no_paths
  unfold RootedInstance.Solvable
  rw [hqEq]
  exact ⟨family⟩

/--
The type-3 branch of Claim 3.10.  The order-three hypothesis bounds the
neighbourhood of `y` by `S ∪ {b_z}`.  Together with the type-3 lower
bound on `T` and (XY2), this forces equality throughout the source degree
sandwich and hence `N(x) = T`.  Claim 3.9(3) then makes the `x,z`
distance greater than two, contradicting (XY3) and the two-edge
`y-b_z-z` path.
-/
private theorem false_of_isOrderThreePath_of_typeThree
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hthree : E.IsOrderThreePath)
    (C : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree C) :
    False := by
  classical
  obtain ⟨sz, hszS, hszAdj⟩ :=
    E.exists_S_neighbor_of_z M
  have hszSC : sz ∈ C.S := by
    simpa [hcore, Core.S] using hszS
  have hRankPos : 1 ≤ P.working.rank := by
    have hcardPos : 0 < C.S.card :=
      Finset.card_pos.mpr ⟨sz, hszSC⟩
    rw [C.card_S] at hcardPos
    omega
  have hPrimeY : E.bPrime = y :=
    E.bPrime_eq_y_of_isOrderThreePath hthree
  have hneighborYSubset :
      G.neighborSet y ⊆
        (↑(insert E.bz C.S) : Set V) := by
    intro v hyv
    have hyvAdj : G.Adj y v :=
      hyv
    by_cases hvCarrier :
        v ∈ P.working.rooted.core.carrier
    · by_cases hvx : v = x
      · subst v
        exact False.elim (M.roots_not_adj hyvAdj.symm)
      rcases
          P.working.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
            hvCarrier hvx with
        hvS | hvT
      · have hvSC : v ∈ C.S := by
          simpa [hcore, Core.S] using hvS
        simp [hvSC]
      · exact False.elim
          (E.no_T_neighbor_of_bPrime M v hvT
            (by simpa [hPrimeY] using hyvAdj.symm))
    · have hvQ :
          v ∈ P.working.rooted.otherRegion :=
        P.working.rooted.otherRegion_componentRegion.closed
          P.working.rooted.other_root_mem_otherRegion
          hyvAdj hvCarrier
      have hvTriple :
          v ∈ ({z, E.bz, y} : Finset V) := by
        rw [hthree] at hvQ
        exact hvQ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvTriple
      rcases hvTriple with hvz | hvbz | hvy
      · subst v
        exact False.elim
          (M.right_root_not_adj_exception hyvAdj)
      · subst v
        simp
      · subst v
        exact False.elim (G.loopless.irrefl y hyvAdj)
  have hbzNotS : E.bz ∉ C.S := by
    intro hbzS
    exact E.not_mem_otherRegion_of_mem_carrier
      (P.working.rooted.core.S_subset_carrier
        (by simpa [hcore, Core.S] using hbzS))
      E.bz_mem_otherRegion
  have hdegreeYUpper :
      finiteDegree G y ≤ P.working.rank + 1 := by
    calc
      finiteDegree G y =
          (G.neighborSet y).ncard := rfl
      _ ≤
          (↑(insert E.bz C.S) : Set V).ncard :=
        Set.ncard_le_ncard hneighborYSubset
      _ = (insert E.bz C.S).card :=
        Set.ncard_coe_finset (insert E.bz C.S)
      _ = C.S.card + 1 :=
        Finset.card_insert_of_notMem hbzNotS
      _ = P.working.rank + 1 := by
        rw [C.card_S]
  have hTSubset :
      (↑C.T : Set V) ⊆ G.neighborSet x := by
    intro t ht
    exact C.root_adj_T t ht
  have hTCardDegree :
      C.T.card ≤ finiteDegree G x := by
    calc
      C.T.card = (↑C.T : Set V).ncard := by simp
      _ ≤ (G.neighborSet x).ncard :=
        Set.ncard_le_ncard hTSubset
      _ = finiteDegree G x := rfl
  have hTLower :
      P.working.rank + 1 ≤ C.T.card := by
    have hlower := C.card_T_lower
    omega
  have hWorkingType :
      P.working.rooted.core.typeNumber = 3 := by
    rw [hcore]
    rfl
  have hChosenType :
      P.orientation.chosen.rooted.core.typeNumber = 3 := by
    rw [← P.working.typeNumber_eq_optimal]
    exact hWorkingType
  have hReverseUpper :
      P.orientation.reverse.rooted.core.typeNumber ≤ 3 := by
    cases P.orientation.reverse.rooted.core <;>
      simp [Core.typeNumber]
  have hReverseLower :
      3 ≤ P.orientation.reverse.rooted.core.typeNumber := by
    simpa [hChosenType] using P.orientation.preferred.type_le
  have hReverseType :
      P.orientation.reverse.rooted.core.typeNumber = 3 :=
    Nat.le_antisymm hReverseUpper hReverseLower
  have hAttains :
      P.orientation.OtherRootAttainsChosenType := by
    exact
      ⟨P.orientation.reverse.rank,
        P.orientation.reverse.rooted,
        hReverseType.trans hChosenType.symm⟩
  have hDegreeXY :
      finiteDegree G x ≤ finiteDegree G y :=
    P.orientation.chosen_degree_le_other_of_otherRootAttainsChosenType
      hAttains
  have hDegreeEq :
      finiteDegree G x = finiteDegree G y := by
    omega
  have hTCardEq :
      C.T.card = finiteDegree G x := by
    omega
  have hNeighborXEqT :
      G.neighborSet x = (↑C.T : Set V) := by
    have hNcard :
        (G.neighborSet x).ncard ≤
          (↑C.T : Set V).ncard := by
      have heq :
          (G.neighborSet x).ncard =
            (↑C.T : Set V).ncard := by
        simpa [finiteDegree] using hTCardEq.symm
      exact heq.le
    exact
      (Set.eq_of_subset_of_ncard_le hTSubset hNcard).symm
  have hxNeZ : x ≠ z := by
    intro hxz
    exact E.not_mem_otherRegion_of_mem_carrier
      P.working.rooted.core.root_mem_carrier
      (hxz ▸ E.z_mem_otherRegion)
  have hCommonEmpty :
      G.commonNeighbors x z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rw [G.mem_commonNeighbors] at hv
    have hvT : v ∈ P.working.rooted.core.T := by
      have hvTC : v ∈ C.T := by
        have hvNx : v ∈ G.neighborSet x :=
          hv.1
        rw [hNeighborXEqT] at hvNx
        exact hvNx
      simpa [hcore, Core.T] using hvTC
    exact E.no_T_neighbor_of_z M v hvT hv.2.symm
  have hTwoLtEdist :
      (2 : ℕ∞) < G.edist x z := by
    exact G.two_lt_edist_iff.mpr
      ⟨hxNeZ, M.left_root_not_adj_exception, hCommonEmpty⟩
  have hTwoLtDist :
      2 < G.dist x z := by
    have hReach : G.Reachable x z :=
      M.underlying_connected x z
    rw [← hReach.coe_dist_eq_edist] at hTwoLtEdist
    exact_mod_cast hTwoLtEdist
  have hDistYZ :
      G.dist y z ≤ 2 := by
    let yzPath : SimplePath G y z :=
      (E.stem.castEnd hPrimeY).reverse
    have hdist := SimpleGraph.dist_le yzPath.walk
    change G.dist y z ≤ yzPath.length at hdist
    have hyzLength : yzPath.length = 2 := by
      simp [yzPath]
    omega
  have hDistXY :
      G.dist x z ≤ G.dist y z :=
    P.orientation.chosen_dist_le_other_of_otherRootAttainsChosenType_of_degree_eq
      hAttains hDegreeEq
  omega

/--
COY Claim 3.10: the selected exterior component is not a `(y,z)`-path
of order exactly three.
-/
theorem not_isOrderThreePath
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock) :
    ¬E.IsOrderThreePath := by
  intro hthree
  cases hcore : P.working.rooted.core with
  | typeOne C =>
      obtain ⟨s, hs, -⟩ :=
        E.exists_S_neighbor_of_z M
      simp [hcore, Core.S] at hs
  | typeTwo C =>
      exact E.false_of_isOrderThreePath_of_typeTwo
        M hthree C hcore
  | typeThree C =>
      exact E.false_of_isOrderThreePath_of_typeThree
        M hthree C hcore

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
