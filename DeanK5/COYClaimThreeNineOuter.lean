import DeanK5.COYExteriorZEndBlock
import DeanK5.COYCoreAdapters
import DeanK5.COYConcatenation
import DeanK5.COYProtectedIndependence

/-!
# The first outer-path contradiction in COY Claim 3.9

Suppose that both the exceptional vertex `z` and the cut vertex `b_z`
have neighbours in the `S`-side of the selected working core.  The fixed
`b_z`--`y` path in the exterior then gives two `(S,y)`-paths:

* one enters the exterior directly through `b_z`;
* the other enters through the two-edge stem `z-b_z`.

Their lengths differ by one.  This file constructs those paths as
`SimplePath`s, proves that each meets `S` only at its designated endpoint,
and packages them as the two-member outer family used by COY Fact 1.
The final two theorems combine this family with the bounded type-2 and
type-3 core catalogues.
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

/-- A vertex of the selected core cannot lie in its exterior component. -/
private theorem not_mem_otherRegion_of_mem_carrier
    (P : PreferredWorkingCoreData G x y z)
    {v : V} (hv : v ∈ P.working.rooted.core.carrier) :
    v ∉ P.working.rooted.otherRegion := by
  intro hvQ
  exact
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      hvQ hv

/--
If the working core has no `T`-attachment to the selected exterior, then
`z` has an attachment in the core's `S`-side.

This is the connectivity argument from Claim 3.9(1), not a degree
argument at `z`.  Delete `b_z`, take a path from `z` to the core root, and
inspect its first edge.  The exterior end-block certificate excludes a
second exterior neighbour of `z`; component closure therefore puts that
first neighbour in the core.  It is not the root (because `xz` is a
protected nonedge), and the no-`T` hypothesis leaves only `S`.
-/
theorem exists_S_attachment_of_no_T
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hnoT :
      ¬P.working.rooted.core.HasTAttachment
        P.working.rooted.otherRegion) :
    ∃ s ∈ P.working.rooted.core.S, G.Adj s z := by
  classical
  let Q := P.working.rooted.otherRegion
  let C := P.working.rooted.core
  have hQ : ComponentRegion G C.carrier Q := by
    exact P.working.rooted.otherRegion_componentRegion
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
  · exact False.elim (hnoT
      ⟨z, E.z_mem_otherRegion, v.1, hvT, hzv.symm⟩)

/--
The short outer path: enter the exterior through an edge `s-b_z` and
then follow the fixed `b_z`--`y` path.
-/
noncomputable def shortOuterPath
    (E : P.ExteriorZEndBlock)
    (s : V) (hs : s ∈ P.working.rooted.core.S)
    (hsbz : G.Adj s E.bz) :
    SimplePath G s y where
  walk := .cons hsbz E.pathToY.walk
  isPath := E.pathToY.isPath.cons (by
    intro hsPath
    exact not_mem_otherRegion_of_mem_carrier P
      (P.working.rooted.core.S_subset_carrier hs)
      (E.pathToY_support_mem_otherRegion hsPath))

/-- The short outer path has one edge more than the fixed exterior path. -/
@[simp] theorem shortOuterPath_length
    (E : P.ExteriorZEndBlock)
    (s : V) (hs : s ∈ P.working.rooted.core.S)
    (hsbz : G.Adj s E.bz) :
    (E.shortOuterPath s hs hsbz).length =
      E.pathToY.length + 1 := by
  simp [shortOuterPath, SimplePath.length]

/--
Every vertex of the short outer path is either its `S`-endpoint or lies
in the selected exterior component.
-/
theorem shortOuterPath_support_class
    (E : P.ExteriorZEndBlock)
    (s : V) (hs : s ∈ P.working.rooted.core.S)
    (hsbz : G.Adj s E.bz)
    {v : V}
    (hv : v ∈ (E.shortOuterPath s hs hsbz).walk.support) :
    v = s ∨ v ∈ P.working.rooted.otherRegion := by
  change
    v ∈ (SimpleGraph.Walk.cons hsbz E.pathToY.walk).support at hv
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (E.pathToY_support_mem_otherRegion hv)

/--
The long outer path: enter through `s-z`, traverse `z-b_z`, and then
follow the same fixed `b_z`--`y` path.
-/
noncomputable def longOuterPath
    (E : P.ExteriorZEndBlock)
    (s : V) (hs : s ∈ P.working.rooted.core.S)
    (hsz : G.Adj s z) :
    SimplePath G s y where
  walk := .cons hsz (.cons E.z_adj_bz E.pathToY.walk)
  isPath :=
    (E.pathToY.isPath.cons E.z_not_mem_pathToY_support).cons (by
      intro hsPath
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hsPath
      rcases hsPath with hsz' | hsPath
      · subst s
        exact not_mem_otherRegion_of_mem_carrier P
          (P.working.rooted.core.S_subset_carrier hs)
          E.z_mem_otherRegion
      · exact not_mem_otherRegion_of_mem_carrier P
          (P.working.rooted.core.S_subset_carrier hs)
          (E.pathToY_support_mem_otherRegion hsPath))

/-- The long outer path has two edges more than the fixed exterior path. -/
@[simp] theorem longOuterPath_length
    (E : P.ExteriorZEndBlock)
    (s : V) (hs : s ∈ P.working.rooted.core.S)
    (hsz : G.Adj s z) :
    (E.longOuterPath s hs hsz).length =
      E.pathToY.length + 2 := by
  simp [longOuterPath, SimplePath.length]

/--
Every vertex of the long outer path is either its `S`-endpoint or lies
in the selected exterior component.
-/
theorem longOuterPath_support_class
    (E : P.ExteriorZEndBlock)
    (s : V) (hs : s ∈ P.working.rooted.core.S)
    (hsz : G.Adj s z)
    {v : V}
    (hv : v ∈ (E.longOuterPath s hs hsz).walk.support) :
    v = s ∨ v ∈ P.working.rooted.otherRegion := by
  change
    v ∈
      (SimpleGraph.Walk.cons hsz
        (.cons E.z_adj_bz E.pathToY.walk)).support at hv
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
  rcases hv with rfl | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr E.z_mem_otherRegion
  · exact Or.inr (E.pathToY_support_mem_otherRegion hv)

/-- The two chosen `S`-endpoints, in increasing outer-path length order. -/
def consecutiveOuterEndpoint
    (shortEndpoint longEndpoint : V) :
    Fin 2 → V :=
  fun i =>
    if i.val = 0 then shortEndpoint else longEndpoint

/-- The two outer paths, indexed in increasing length order. -/
noncomputable def consecutiveOuterPath
    (E : P.ExteriorZEndBlock)
    (shortEndpoint longEndpoint : V)
    (hshortS : shortEndpoint ∈ P.working.rooted.core.S)
    (hlongS : longEndpoint ∈ P.working.rooted.core.S)
    (hshort : G.Adj shortEndpoint E.bz)
    (hlong : G.Adj longEndpoint z)
    (i : Fin 2) :
    SimplePath G
      (consecutiveOuterEndpoint shortEndpoint longEndpoint i) y := by
  by_cases hi : i.val = 0
  · exact
      (E.shortOuterPath shortEndpoint hshortS hshort).castStart
        (by simp [consecutiveOuterEndpoint, hi])
  · exact
      (E.longOuterPath longEndpoint hlongS hlong).castStart
        (by simp [consecutiveOuterEndpoint, hi])

/-- The indexed outer paths have consecutive lengths. -/
@[simp] theorem consecutiveOuterPath_length
    (E : P.ExteriorZEndBlock)
    (shortEndpoint longEndpoint : V)
    (hshortS : shortEndpoint ∈ P.working.rooted.core.S)
    (hlongS : longEndpoint ∈ P.working.rooted.core.S)
    (hshort : G.Adj shortEndpoint E.bz)
    (hlong : G.Adj longEndpoint z)
    (i : Fin 2) :
    (E.consecutiveOuterPath shortEndpoint longEndpoint
      hshortS hlongS hshort hlong i).length =
        E.pathToY.length + 1 + i.val := by
  by_cases hi : i.val = 0
  · simp only [consecutiveOuterPath, dif_pos hi,
      SimplePath.castStart_length]
    rw [E.shortOuterPath_length]
    omega
  · have hiOne : i.val = 1 := by
      have := i.isLt
      omega
    simp only [consecutiveOuterPath, dif_neg hi,
      SimplePath.castStart_length]
    rw [E.longOuterPath_length]
    omega

/--
The support of each indexed outer path consists of its designated
`S`-endpoint and vertices of the exterior component.
-/
theorem consecutiveOuterPath_support_class
    (E : P.ExteriorZEndBlock)
    (shortEndpoint longEndpoint : V)
    (hshortS : shortEndpoint ∈ P.working.rooted.core.S)
    (hlongS : longEndpoint ∈ P.working.rooted.core.S)
    (hshort : G.Adj shortEndpoint E.bz)
    (hlong : G.Adj longEndpoint z)
    (i : Fin 2) {v : V}
    (hv : v ∈
      (E.consecutiveOuterPath shortEndpoint longEndpoint
        hshortS hlongS hshort hlong i).walk.support) :
    v = consecutiveOuterEndpoint shortEndpoint longEndpoint i ∨
      v ∈ P.working.rooted.otherRegion := by
  by_cases hi : i.val = 0
  · have hv' :
        v ∈ (E.shortOuterPath shortEndpoint hshortS hshort).walk.support := by
      simpa [consecutiveOuterPath, hi] using hv
    rcases
        E.shortOuterPath_support_class
          shortEndpoint hshortS hshort hv' with
      rfl | hvQ
    · exact Or.inl (by simp [consecutiveOuterEndpoint, hi])
    · exact Or.inr hvQ
  · have hv' :
        v ∈ (E.longOuterPath longEndpoint hlongS hlong).walk.support := by
      simpa [consecutiveOuterPath, hi] using hv
    rcases
        E.longOuterPath_support_class
          longEndpoint hlongS hlong hv' with
      rfl | hvQ
    · exact Or.inl (by simp [consecutiveOuterEndpoint, hi])
    · exact Or.inr hvQ

/--
The two consecutive outer paths, together with the support classification
used to verify every later concatenation.
-/
structure ConsecutiveOuterData
    (E : P.ExteriorZEndBlock) where
  /-- The two-member semi-admissible family from the core `S`-side to `y`. -/
  family :
    SemiAdmissibleSetPathFamily G
      (↑P.working.rooted.core.S : Set V) y 2
  /-- Away from its designated endpoint, each path lies in the exterior. -/
  support_class :
    ∀ i v, v ∈ (family.path i).walk.support →
      v = family.endpoint i ∨
        v ∈ P.working.rooted.otherRegion

/-- Package the short and long paths as a two-member outer family. -/
noncomputable def consecutiveOuterData
    (E : P.ExteriorZEndBlock)
    (shortEndpoint longEndpoint : V)
    (hshortS : shortEndpoint ∈ P.working.rooted.core.S)
    (hlongS : longEndpoint ∈ P.working.rooted.core.S)
    (hshort : G.Adj shortEndpoint E.bz)
    (hlong : G.Adj longEndpoint z) :
    E.ConsecutiveOuterData := by
  let endpoint :=
    consecutiveOuterEndpoint shortEndpoint longEndpoint
  let path := E.consecutiveOuterPath shortEndpoint longEndpoint
    hshortS hlongS hshort hlong
  let family :
      SemiAdmissibleSetPathFamily G
        (↑P.working.rooted.core.S : Set V) y 2 := {
    start := E.pathToY.length + 1
    step := 1
    admissible_step := Or.inl rfl
    start_ge_one := by omega
    endpoint := endpoint
    endpoint_mem := by
      intro i
      fin_cases i
      · exact hshortS
      · exact hlongS
    path := path
    length_path := by
      intro i
      have hlength :=
        E.consecutiveOuterPath_length shortEndpoint longEndpoint
          hshortS hlongS hshort hlong i
      change
        (E.consecutiveOuterPath shortEndpoint longEndpoint
          hshortS hlongS hshort hlong i).length =
            E.pathToY.length + 1 + i.val * 1
      omega
    unique_endpoint := by
      intro i v hvPath hvS
      rcases
          E.consecutiveOuterPath_support_class
            shortEndpoint longEndpoint hshortS hlongS
            hshort hlong i hvPath with
        hv | hvQ
      · exact hv
      · exact False.elim
          (not_mem_otherRegion_of_mem_carrier P
            (P.working.rooted.core.S_subset_carrier hvS) hvQ)
  }
  exact {
    family := family
    support_class := by
      intro i v hv
      exact
        E.consecutiveOuterPath_support_class
          shortEndpoint longEndpoint hshortS hlongS
          hshort hlong i hv
  }

/--
An inner path supported on the working-core carrier is disjoint from the
tail of the corresponding outer path.
-/
theorem ConsecutiveOuterData.inner_support_disjoint_outer_tail
    (E : P.ExteriorZEndBlock)
    (D : E.ConsecutiveOuterData)
    {a : V} (i : Fin 2)
    (inner : SimplePath G a (D.family.endpoint i))
    (hsupport :
      ∀ v, v ∈ inner.walk.support →
        v ∈ P.working.rooted.core.carrier) :
    inner.walk.support.Disjoint
      (D.family.path i).walk.support.tail := by
  apply List.disjoint_left.mpr
  intro v hvInner hvOuterTail
  rcases D.support_class i v
      (List.mem_of_mem_tail hvOuterTail) with
    hvEndpoint | hvQ
  · subst v
    exact (D.family.path i).start_not_mem_tail hvOuterTail
  · exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        hvQ (hsupport v hvInner)

omit [Fintype V] in
private theorem typeTwo_catalog_length
    {ℓ r : ℕ}
    (C : TypeTwoCore G x ℓ)
    (target : V) (htarget : target ∈ C.S)
    (hrOne : 1 ≤ r) (hrFour : r ≤ 4)
    (hrCore : r ≤ ℓ)
    (i : Fin r) :
    ((C.admissiblePathsToS target htarget r
      hrOne hrFour hrCore).path i).length =
        3 + i.val := by
  interval_cases r <;> fin_cases i <;>
    simp [TypeTwoCore.admissiblePathsToS,
      PointedTypeTwoSCore.factTwoTypeTwoBounded]

omit [Fintype V] in
private theorem typeThree_catalog_length
    {ℓ r : ℕ}
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.S)
    (hdeleted : deleted ∈ C.T)
    (hrOne : 1 ≤ r) (hrFour : r ≤ 4)
    (hrCore : r ≤ ℓ)
    (i : Fin r) :
    ((C.admissiblePathsToSAfterDeleting
      target deleted htarget hdeleted r
      hrOne hrFour hrCore).path i).length =
        2 + 2 * i.val := by
  interval_cases r <;> fin_cases i <;>
    simp [TypeThreeCore.admissiblePathsToSAfterDeleting,
      PointedTypeThreeSCore.factTwoTypeThreeBounded]

/--
The first contradiction in COY Claim 3.9(1).

At the extremal value `rank + 1 = q`, the absence of a `T`-attachment
forces an `S`-attachment at `z`.  If `b_z` also had an `S`-attachment,
the two consecutive outer paths constructed above and the full
`rank`-member core catalogue would give `q` admissible root paths by
Fact 1.
-/
theorem false_of_no_T_of_bz_S_attachment_of_rank_add_one_eq
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hRank : P.working.rank + 1 = q)
    (hnoT :
      ¬P.working.rooted.core.HasTAttachment
        P.working.rooted.otherRegion)
    (hbzS :
      ∃ s ∈ P.working.rooted.core.S, G.Adj s E.bz) :
    False := by
  classical
  obtain ⟨shortEndpoint, hshortS, hshort⟩ := hbzS
  obtain ⟨longEndpoint, hlongS, hlong⟩ :=
    E.exists_S_attachment_of_no_T M hnoT
  let outer :=
    E.consecutiveOuterData shortEndpoint longEndpoint
      hshortS hlongS hshort hlong
  have hRankOne : 1 ≤ P.working.rank := by
    have hqTwo := M.two_le_q
    omega
  have hRankFour : P.working.rank ≤ 4 := by
    have hqFour := M.q_le_four
    omega
  cases hcore : P.working.rooted.core with
  | typeOne C =>
      have hmem : shortEndpoint ∈ (Core.typeOne C).S := by
        rw [← hcore]
        exact hshortS
      simp [Core.S] at hmem
  | typeTwo C =>
      have hshortC : shortEndpoint ∈ C.S := by
        have hS :
            P.working.rooted.core.S = C.S := by
          simpa [Core.S] using congrArg Core.S hcore
        rw [← hS]
        exact hshortS
      have hlongC : longEndpoint ∈ C.S := by
        have hS :
            P.working.rooted.core.S = C.S := by
          simpa [Core.S] using congrArg Core.S hcore
        rw [← hS]
        exact hlongS
      have hendpointS (i : Fin 2) :
          outer.family.endpoint i ∈ C.S := by
        change
          consecutiveOuterEndpoint
            shortEndpoint longEndpoint i ∈ C.S
        by_cases hi : i.val = 0
        · simp [consecutiveOuterEndpoint, hi, hshortC]
        · simp [consecutiveOuterEndpoint, hi, hlongC]
      let inner (i : Fin 2) :
          SemiAdmissiblePathFamily G x
            (outer.family.endpoint i) P.working.rank :=
        SemiAdmissiblePathFamily.ofAdmissible
          (C.admissiblePathsToS
            (outer.family.endpoint i) (hendpointS i)
            P.working.rank hRankOne hRankFour le_rfl)
      let certificate :
          FactOneCertificate G x y
            (↑P.working.rooted.core.S : Set V)
            2 P.working.rank := {
        hs := by omega
        ht := hRankOne
        x_ne_y := M.roots_ne
        x_not_mem := P.working.rooted.core.root_not_mem_S
        y_not_mem := by
          intro hyS
          exact P.working.rooted.other_root_not_mem
            (P.working.rooted.core.S_subset_carrier hyS)
        outer := outer.family
        inner := inner
        equal_inner_length := by
          intro i j
          calc
            ((inner i).path j).length = 3 + j.val := by
              exact typeTwo_catalog_length C
                (outer.family.endpoint i) (hendpointS i)
                hRankOne hRankFour le_rfl j
            _ =
                ((inner
                  (firstFin (by omega : 1 ≤ 2))).path j).length := by
              symm
              exact typeTwo_catalog_length C
                (outer.family.endpoint
                  (firstFin (by omega : 1 ≤ 2)))
                (hendpointS (firstFin (by omega : 1 ≤ 2)))
                hRankOne hRankFour le_rfl j
        avoid_outer := by
          intro i j
          apply outer.inner_support_disjoint_outer_tail
          intro v hv
          have hv' :
              v ∈
                ((C.admissiblePathsToS
                  (outer.family.endpoint i) (hendpointS i)
                  P.working.rank hRankOne hRankFour
                  le_rfl).path j).walk.support := by
            exact hv
          have hvCore :=
            C.admissiblePathsToS_support
              (outer.family.endpoint i) (hendpointS i)
              P.working.rank hRankOne hRankFour
              le_rfl j v hv'
          rw [hcore]
          simpa [Core.carrier, Core.S, Core.T] using hvCore
      }
      have hfamily := fact_one certificate
      have hsize : 2 + P.working.rank - 1 = q := by
        omega
      rw [hsize] at hfamily
      exact M.no_paths hfamily
  | typeThree C =>
      have hshortC : shortEndpoint ∈ C.S := by
        have hS :
            P.working.rooted.core.S = C.S := by
          simpa [Core.S] using congrArg Core.S hcore
        rw [← hS]
        exact hshortS
      have hlongC : longEndpoint ∈ C.S := by
        have hS :
            P.working.rooted.core.S = C.S := by
          simpa [Core.S] using congrArg Core.S hcore
        rw [← hS]
        exact hlongS
      have hendpointS (i : Fin 2) :
          outer.family.endpoint i ∈ C.S := by
        change
          consecutiveOuterEndpoint
            shortEndpoint longEndpoint i ∈ C.S
        by_cases hi : i.val = 0
        · simp [consecutiveOuterEndpoint, hi, hshortC]
        · simp [consecutiveOuterEndpoint, hi, hlongC]
      have hTNonempty : C.T.Nonempty := by
        rw [← Finset.card_pos]
        have htwo :
            2 ≤ C.T.card :=
          (Nat.le_max_right (P.working.rank + 1) 2).trans
            C.card_T_lower
        omega
      obtain ⟨deleted, hdeleted⟩ := hTNonempty
      let inner (i : Fin 2) :
          SemiAdmissiblePathFamily G x
            (outer.family.endpoint i) P.working.rank :=
        SemiAdmissiblePathFamily.ofAdmissible
          (C.admissiblePathsToSAfterDeleting
            (outer.family.endpoint i) deleted
            (hendpointS i) hdeleted P.working.rank
            hRankOne hRankFour le_rfl)
      let certificate :
          FactOneCertificate G x y
            (↑P.working.rooted.core.S : Set V)
            2 P.working.rank := {
        hs := by omega
        ht := hRankOne
        x_ne_y := M.roots_ne
        x_not_mem := P.working.rooted.core.root_not_mem_S
        y_not_mem := by
          intro hyS
          exact P.working.rooted.other_root_not_mem
            (P.working.rooted.core.S_subset_carrier hyS)
        outer := outer.family
        inner := inner
        equal_inner_length := by
          intro i j
          calc
            ((inner i).path j).length =
                2 + 2 * j.val := by
              exact typeThree_catalog_length C
                (outer.family.endpoint i) deleted
                (hendpointS i) hdeleted
                hRankOne hRankFour le_rfl j
            _ =
                ((inner
                  (firstFin (by omega : 1 ≤ 2))).path j).length := by
              symm
              exact typeThree_catalog_length C
                (outer.family.endpoint
                  (firstFin (by omega : 1 ≤ 2)))
                deleted
                (hendpointS (firstFin (by omega : 1 ≤ 2)))
                hdeleted hRankOne hRankFour le_rfl j
        avoid_outer := by
          intro i j
          apply outer.inner_support_disjoint_outer_tail
          intro v hv
          have hv' :
              v ∈
                ((C.admissiblePathsToSAfterDeleting
                  (outer.family.endpoint i) deleted
                  (hendpointS i) hdeleted P.working.rank
                  hRankOne hRankFour le_rfl).path j
                    ).walk.support := by
            exact hv
          have hvCore :=
            C.admissiblePathsToSAfterDeleting_support
              (outer.family.endpoint i) deleted
              (hendpointS i) hdeleted P.working.rank
              hRankOne hRankFour le_rfl j v hv'
          rw [hcore]
          simp only [Core.carrier, Core.S, Core.T,
            Finset.mem_insert, Finset.mem_union,
            Finset.mem_erase] at hvCore ⊢
          aesop
      }
      have hfamily := fact_one certificate
      have hsize : 2 + P.working.rank - 1 = q := by
        omega
      rw [hsize] at hfamily
      exact M.no_paths hfamily

/--
At `rank + 1 = q`, no-`T` implies that `b_z` has no neighbour in the
working core's `S`-side.
-/
theorem no_S_attachment_of_no_T_of_rank_add_one_eq
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hRank : P.working.rank + 1 = q)
    (hnoT :
      ¬P.working.rooted.core.HasTAttachment
        P.working.rooted.otherRegion) :
    ∀ s ∈ P.working.rooted.core.S, ¬G.Adj s E.bz := by
  intro s hs hsbz
  exact E.false_of_no_T_of_bz_S_attachment_of_rank_add_one_eq
    M hRank hnoT ⟨s, hs, hsbz⟩

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
