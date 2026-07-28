import DeanK5.COYExteriorClaimThreeNineDegree
import DeanK5.COYConcatenation
import DeanK5.COYCoreAdapters

/-!
# The forbidden `T`-attachments in COY Claim 3.9

After the strict rank bound has forced equality in the degree estimate at
`b_z`, Claim 3.3 supplies a fixed neighbour of `b_z` in the working core's
`T`-side.  A second `T`-attachment at either `z` or `b'_z` would give two
consecutive outer paths to `y`.  Combining those paths with the
`rank + 1` inner catalogue through COY Fact 1 produces the forbidden
`q`-path family.

The two outer paths use the same fixed `b'_z`--`y` tail.  Their simplicity,
support, and endpoint properties are certified explicitly below.
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

/-- A working-core vertex cannot belong to the selected exterior region. -/
private theorem not_mem_otherRegion_of_mem_carrier
    (_E : P.ExteriorZEndBlock)
    {v : V} (hv : v ∈ P.working.rooted.core.carrier) :
    v ∉ P.working.rooted.otherRegion := by
  intro hvQ
  exact
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      hvQ hv

/--
The fixed `b'_z`--`y` tail does not return to `b_z`.

This is inherited from the simple `b_z`--`y` path before its first edge is
removed.
-/
theorem bz_not_mem_bPrimeToY_support
    (E : P.ExteriorZEndBlock) :
    E.bz ∉ E.bPrimeToY.walk.support := by
  intro hbz
  change
    E.bz ∈
      (E.certificate.bPrimeToY.walk.map
        P.exteriorEmbedding.toHom).support at hbz
  rw [SimpleGraph.Walk.support_map] at hbz
  obtain ⟨w, hw, hwVal⟩ := List.mem_map.mp hbz
  have hwEq : w = E.certificate.bz := by
    apply Subtype.ext
    exact hwVal
  subst w
  have hwDrop :
      E.certificate.bz ∈
        (E.certificate.pathToY.drop 1).walk.support := by
    simpa [ZEndBlockCertificate.bPrimeToY,
      SimplePath.castStart_support] using hw
  have hpositive :
      0 < E.certificate.pathToY.walk.length := by
    rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
    exact E.certificate.pathToY.walk.not_nil_of_ne
      E.certificate.y_ne_bz.symm
  have hmin :
      1 ⊓ E.certificate.pathToY.walk.length = 1 := by
    apply Nat.min_eq_left
    omega
  rw [SimplePath.drop,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,
    hmin] at hwDrop
  apply E.certificate.pathToY.start_not_mem_tail
  simpa using hwDrop

/--
The short outer path `t-b'_z-...-y` when a `T`-vertex is adjacent to
`b'_z`.
-/
noncomputable def directPrimeOuterPath
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htPrime : G.Adj t E.bPrime) :
    SimplePath G t y where
  walk := .cons htPrime E.bPrimeToY.walk
  isPath := E.bPrimeToY.isPath.cons (by
    intro htPath
    exact E.not_mem_otherRegion_of_mem_carrier
      (P.working.rooted.core.T_subset_carrier ht)
      (E.bPrimeToY_support_mem_otherRegion htPath))

/-- The direct outer path adds one edge to the common tail. -/
@[simp] theorem directPrimeOuterPath_length
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htPrime : G.Adj t E.bPrime) :
    (E.directPrimeOuterPath t ht htPrime).length =
      E.bPrimeToY.length + 1 := by
  simp [directPrimeOuterPath, SimplePath.length]

/--
Every vertex of the direct outer path is its `T`-endpoint or is in the
selected exterior.
-/
theorem directPrimeOuterPath_support_class
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htPrime : G.Adj t E.bPrime)
    {v : V}
    (hv : v ∈ (E.directPrimeOuterPath t ht htPrime).walk.support) :
    v = t ∨ v ∈ P.working.rooted.otherRegion := by
  change
    v ∈
      (SimpleGraph.Walk.cons htPrime E.bPrimeToY.walk).support at hv
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (E.bPrimeToY_support_mem_otherRegion hv)

/--
The middle outer path `t-b_z-b'_z-...-y` supplied by the fixed
`T`-neighbour of `b_z`.
-/
noncomputable def middlePrimeOuterPath
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htBz : G.Adj t E.bz) :
    SimplePath G t y where
  walk :=
    .cons htBz
      (.cons E.bz_adj_bPrime E.bPrimeToY.walk)
  isPath :=
    (E.bPrimeToY.isPath.cons E.bz_not_mem_bPrimeToY_support).cons
      (by
        intro htPath
        simp only [SimpleGraph.Walk.support_cons,
          List.mem_cons] at htPath
        rcases htPath with htbz | htTail
        · subst t
          exact E.not_mem_otherRegion_of_mem_carrier
            (P.working.rooted.core.T_subset_carrier ht)
            E.bz_mem_otherRegion
        · exact E.not_mem_otherRegion_of_mem_carrier
            (P.working.rooted.core.T_subset_carrier ht)
            (E.bPrimeToY_support_mem_otherRegion htTail))

/-- The middle outer path adds two edges to the common tail. -/
@[simp] theorem middlePrimeOuterPath_length
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htBz : G.Adj t E.bz) :
    (E.middlePrimeOuterPath t ht htBz).length =
      E.bPrimeToY.length + 2 := by
  simp [middlePrimeOuterPath, SimplePath.length]

/--
Every vertex of the middle outer path is its `T`-endpoint or is in the
selected exterior.
-/
theorem middlePrimeOuterPath_support_class
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htBz : G.Adj t E.bz)
    {v : V}
    (hv : v ∈ (E.middlePrimeOuterPath t ht htBz).walk.support) :
    v = t ∨ v ∈ P.working.rooted.otherRegion := by
  change
    v ∈
      (SimpleGraph.Walk.cons htBz
        (.cons E.bz_adj_bPrime E.bPrimeToY.walk)).support at hv
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
  rcases hv with rfl | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr E.bz_mem_otherRegion
  · exact Or.inr (E.bPrimeToY_support_mem_otherRegion hv)

/--
The long outer path `t-z-b_z-b'_z-...-y` when a `T`-vertex is adjacent
to `z`.
-/
noncomputable def longPrimeOuterPath
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htZ : G.Adj t z) :
    SimplePath G t y where
  walk :=
    .cons htZ
      (.cons E.z_adj_bz
        (.cons E.bz_adj_bPrime E.bPrimeToY.walk))
  isPath :=
    ((E.bPrimeToY.isPath.cons
        E.bz_not_mem_bPrimeToY_support).cons
      (by
        intro hzPath
        simp only [SimpleGraph.Walk.support_cons,
          List.mem_cons] at hzPath
        rcases hzPath with hzbz | hzTail
        · exact E.z_ne_bz hzbz
        · exact E.z_not_mem_bPrimeToY_support hzTail)).cons
      (by
        intro htPath
        simp only [SimpleGraph.Walk.support_cons,
          List.mem_cons] at htPath
        rcases htPath with htz | htbz | htTail
        · subst t
          exact E.not_mem_otherRegion_of_mem_carrier
            (P.working.rooted.core.T_subset_carrier ht)
            E.z_mem_otherRegion
        · subst t
          exact E.not_mem_otherRegion_of_mem_carrier
            (P.working.rooted.core.T_subset_carrier ht)
            E.bz_mem_otherRegion
        · exact E.not_mem_otherRegion_of_mem_carrier
            (P.working.rooted.core.T_subset_carrier ht)
            (E.bPrimeToY_support_mem_otherRegion htTail))

/-- The long outer path adds three edges to the common tail. -/
@[simp] theorem longPrimeOuterPath_length
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htZ : G.Adj t z) :
    (E.longPrimeOuterPath t ht htZ).length =
      E.bPrimeToY.length + 3 := by
  simp [longPrimeOuterPath, SimplePath.length]

/--
Every vertex of the long outer path is its `T`-endpoint or is in the
selected exterior.
-/
theorem longPrimeOuterPath_support_class
    (E : P.ExteriorZEndBlock)
    (t : V) (ht : t ∈ P.working.rooted.core.T)
    (htZ : G.Adj t z)
    {v : V}
    (hv : v ∈ (E.longPrimeOuterPath t ht htZ).walk.support) :
    v = t ∨ v ∈ P.working.rooted.otherRegion := by
  change
    v ∈
      (SimpleGraph.Walk.cons htZ
        (.cons E.z_adj_bz
          (.cons E.bz_adj_bPrime E.bPrimeToY.walk))).support at hv
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
  rcases hv with rfl | rfl | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr E.z_mem_otherRegion
  · exact Or.inr E.bz_mem_otherRegion
  · exact Or.inr (E.bPrimeToY_support_mem_otherRegion hv)

/--
Two consecutive outer paths from the working core's `T`-side to `y`,
together with the support classification needed by Fact 1.
-/
structure ConsecutiveTOuterData
    (E : P.ExteriorZEndBlock) where
  /-- The two consecutive paths from the core's `T`-side to `y`. -/
  family :
    SemiAdmissibleSetPathFamily G
      (↑P.working.rooted.core.T : Set V) y 2
  /--
  Apart from its represented `T`-endpoint, each path stays in the selected
  exterior region.
  -/
  support_class :
    ∀ i v, v ∈ (family.path i).walk.support →
      v = family.endpoint i ∨
        v ∈ P.working.rooted.otherRegion

/-- The endpoint of the shorter or longer member of a two-path family. -/
private def twoEndpoint (shortEndpoint longEndpoint : V) :
    Fin 2 → V :=
  fun i =>
    if i.val = 0 then shortEndpoint else longEndpoint

/--
Package any two already-certified consecutive paths as the outer family
required by Fact 1.
-/
private noncomputable def consecutiveTOuterDataOfPaths
    (E : P.ExteriorZEndBlock)
    (shortEndpoint longEndpoint : V)
    (hshortT : shortEndpoint ∈ P.working.rooted.core.T)
    (hlongT : longEndpoint ∈ P.working.rooted.core.T)
    (shortPath : SimplePath G shortEndpoint y)
    (longPath : SimplePath G longEndpoint y)
    (hshortPositive : 1 ≤ shortPath.length)
    (hlength : longPath.length = shortPath.length + 1)
    (hshortSupport :
      ∀ {v}, v ∈ shortPath.walk.support →
        v = shortEndpoint ∨
          v ∈ P.working.rooted.otherRegion)
    (hlongSupport :
      ∀ {v}, v ∈ longPath.walk.support →
        v = longEndpoint ∨
          v ∈ P.working.rooted.otherRegion) :
    E.ConsecutiveTOuterData := by
  let endpoint := twoEndpoint shortEndpoint longEndpoint
  let path :
      ∀ i : Fin 2, SimplePath G (endpoint i) y := fun i => by
    by_cases hi : i = 0
    · exact shortPath.castStart
        (by simp [endpoint, twoEndpoint, hi])
    · have hiOne : i = 1 := by
        apply Fin.ext
        have := i.isLt
        omega
      exact longPath.castStart
        (by simp [endpoint, twoEndpoint, hiOne])
  let family :
      SemiAdmissibleSetPathFamily G
        (↑P.working.rooted.core.T : Set V) y 2 := {
    start := shortPath.length
    step := 1
    admissible_step := Or.inl rfl
    start_ge_one := hshortPositive
    endpoint := endpoint
    endpoint_mem := by
      intro i
      fin_cases i
      · exact hshortT
      · exact hlongT
    path := path
    length_path := by
      intro i
      by_cases hi : i = 0
      · simp [path, hi]
      · have hiVal : i.val = 1 := by
          have := i.isLt
          omega
        simp only [path, dif_neg hi,
          SimplePath.castStart_length]
        omega
    unique_endpoint := by
      intro i v hvPath hvT
      by_cases hi : i = 0
      · have hv :
            v ∈ shortPath.walk.support := by
          simpa [path, hi] using hvPath
        rcases hshortSupport hv with hv | hvQ
        · simpa [endpoint, twoEndpoint, hi] using hv
        · exact False.elim
            (E.not_mem_otherRegion_of_mem_carrier
              (P.working.rooted.core.T_subset_carrier hvT) hvQ)
      · have hv :
            v ∈ longPath.walk.support := by
          simpa [path, hi] using hvPath
        rcases hlongSupport hv with hv | hvQ
        · simpa [endpoint, twoEndpoint, hi] using hv
        · exact False.elim
            (E.not_mem_otherRegion_of_mem_carrier
              (P.working.rooted.core.T_subset_carrier hvT) hvQ)
  }
  exact {
    family := family
    support_class := by
      intro i v hvPath
      by_cases hi : i = 0
      · have hv :
            v ∈ shortPath.walk.support := by
          simpa [family, path, hi] using hvPath
        rcases hshortSupport hv with hv | hvQ
        · exact Or.inl (by
            simpa [family, endpoint, twoEndpoint, hi] using hv)
        · exact Or.inr hvQ
      · have hv :
            v ∈ longPath.walk.support := by
          simpa [family, path, hi] using hvPath
        rcases hlongSupport hv with hv | hvQ
        · exact Or.inl (by
            simpa [family, endpoint, twoEndpoint, hi] using hv)
        · exact Or.inr hvQ
  }

/--
The consecutive outer pair when the extra attachment is at `b'_z`:
`t_v-b'_z-...-y` followed by `t_b-b_z-b'_z-...-y`.
-/
noncomputable def consecutiveTOuterDataOfPrimeAdj
    (E : P.ExteriorZEndBlock)
    (tv tb : V)
    (htv : tv ∈ P.working.rooted.core.T)
    (htb : tb ∈ P.working.rooted.core.T)
    (htvPrime : G.Adj tv E.bPrime)
    (htbBz : G.Adj tb E.bz) :
    E.ConsecutiveTOuterData := by
  let shortPath := E.directPrimeOuterPath tv htv htvPrime
  let longPath := E.middlePrimeOuterPath tb htb htbBz
  apply E.consecutiveTOuterDataOfPaths
    tv tb htv htb shortPath longPath
  · simp [shortPath]
  · simp [shortPath, longPath]
  · intro v hv
    exact E.directPrimeOuterPath_support_class
      tv htv htvPrime hv
  · intro v hv
    exact E.middlePrimeOuterPath_support_class
      tb htb htbBz hv

/--
The consecutive outer pair when the extra attachment is at `z`:
`t_b-b_z-b'_z-...-y` followed by
`t_v-z-b_z-b'_z-...-y`.
-/
noncomputable def consecutiveTOuterDataOfZAdj
    (E : P.ExteriorZEndBlock)
    (tv tb : V)
    (htv : tv ∈ P.working.rooted.core.T)
    (htb : tb ∈ P.working.rooted.core.T)
    (htvZ : G.Adj tv z)
    (htbBz : G.Adj tb E.bz) :
    E.ConsecutiveTOuterData := by
  let shortPath := E.middlePrimeOuterPath tb htb htbBz
  let longPath := E.longPrimeOuterPath tv htv htvZ
  apply E.consecutiveTOuterDataOfPaths
    tb tv htb htv shortPath longPath
  · simp [shortPath]
  · simp [shortPath, longPath]
  · intro v hv
    exact E.middlePrimeOuterPath_support_class
      tb htb htbBz hv
  · intro v hv
    exact E.longPrimeOuterPath_support_class
      tv htv htvZ hv

omit [Fintype V] in
private theorem typeOne_T_catalog_start
    {ℓ n : ℕ} (C : TypeOneCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsTo target htarget n
      hnOne hnFour hnCore).start = 1 := by
  unfold TypeOneCore.semiAdmissiblePathsTo
  unfold PointedTypeOneCore.factTwoTypeOneBounded
  interval_cases n <;> rfl

omit [Fintype V] in
private theorem typeOne_T_catalog_step
    {ℓ n : ℕ} (C : TypeOneCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsTo target htarget n
      hnOne hnFour hnCore).step = 1 := by
  unfold TypeOneCore.semiAdmissiblePathsTo
  unfold PointedTypeOneCore.factTwoTypeOneBounded
  interval_cases n <;> rfl

omit [Fintype V] in
private theorem typeTwo_T_catalog_start
    {ℓ n : ℕ} (C : TypeTwoCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).start = 2 := by
  unfold TypeTwoCore.semiAdmissiblePathsToT
  unfold PointedTypeTwoTCore.factTwoTypeTwoTBounded
  interval_cases n <;> rfl

omit [Fintype V] in
private theorem typeTwo_T_catalog_step
    {ℓ n : ℕ} (C : TypeTwoCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).step = 1 := by
  unfold TypeTwoCore.semiAdmissiblePathsToT
  unfold PointedTypeTwoTCore.factTwoTypeTwoTBounded
  interval_cases n <;> rfl

omit [Fintype V] in
private theorem typeThree_T_catalog_start
    {ℓ n : ℕ} (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).start = 1 := by
  unfold TypeThreeCore.semiAdmissiblePathsToT
  unfold PointedTypeThreeTCore.factTwoTypeThreeTBounded
  interval_cases n <;> rfl

omit [Fintype V] in
private theorem typeThree_T_catalog_step
    {ℓ n : ℕ} (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).step = 2 := by
  unfold TypeThreeCore.semiAdmissiblePathsToT
  unfold PointedTypeThreeTCore.factTwoTypeThreeTBounded
  interval_cases n <;> rfl

/--
Fact 1 applied to a two-member consecutive `T`-outer family and a
uniform `rank + 1` inner catalogue.
-/
private theorem false_of_consecutiveTOuterData_of_inner
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hRankEq : P.working.rank = q - 2)
    (outer : E.ConsecutiveTOuterData)
    (inner :
      ∀ i : Fin 2,
        SemiAdmissiblePathFamily G x
          (outer.family.endpoint i) (P.working.rank + 1))
    (hequal :
      ∀ i j,
        ((inner i).path j).length =
          ((inner (firstFin (by omega : 1 ≤ 2))).path j).length)
    (hsupport :
      ∀ i j v, v ∈ ((inner i).path j).walk.support →
        v ∈ P.working.rooted.core.carrier) :
    False := by
  have hxNotT :
      x ∉ (↑P.working.rooted.core.T : Set V) := by
    exact P.working.rooted.core.root_not_mem_T
  have hyNotT :
      y ∉ (↑P.working.rooted.core.T : Set V) := by
    intro hyT
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        P.working.rooted.other_root_mem_otherRegion
        (P.working.rooted.core.T_subset_carrier hyT)
  let certificate :
      FactOneCertificate G x y
        (↑P.working.rooted.core.T : Set V)
        2 (P.working.rank + 1) := {
    hs := by omega
    ht := by omega
    x_ne_y := M.roots_ne
    x_not_mem := hxNotT
    y_not_mem := hyNotT
    outer := outer.family
    inner := inner
    equal_inner_length := hequal
    avoid_outer := by
      intro i j
      apply List.disjoint_left.mpr
      intro v hvInner hvOuterTail
      have hvOuter :
          v ∈ (outer.family.path i).walk.support :=
        List.mem_of_mem_tail hvOuterTail
      rcases outer.support_class i v hvOuter with
        hvEndpoint | hvQ
      · subst v
        exact (outer.family.path i).start_not_mem_tail
          hvOuterTail
      · exact E.not_mem_otherRegion_of_mem_carrier
          (hsupport i j v hvInner) hvQ
  }
  have hcount :
      2 + (P.working.rank + 1) - 1 = q := by
    have hqTwo := M.two_le_q
    omega
  apply M.no_paths
  unfold RootedInstance.Solvable
  simpa only [hcount] using fact_one certificate

/--
Every source core type supplies the uniform `rank + 1` inner catalogue
needed by the preceding Fact 1 application.
-/
private theorem false_of_consecutiveTOuterData
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hRankEq : P.working.rank = q - 2)
    (outer : E.ConsecutiveTOuterData) :
    False := by
  have hInnerOne : 1 ≤ P.working.rank + 1 := by
    omega
  have hInnerFour : P.working.rank + 1 ≤ 4 := by
    have hqFour := M.q_le_four
    omega
  cases hcore : P.working.rooted.core with
  | typeOne C =>
      have hendpoint (i : Fin 2) :
          outer.family.endpoint i ∈ C.T := by
        simpa [hcore, Core.T] using outer.family.endpoint_mem i
      let inner :
          ∀ i : Fin 2,
            SemiAdmissiblePathFamily G x
              (outer.family.endpoint i) (P.working.rank + 1) :=
        fun i =>
          C.semiAdmissiblePathsTo
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour le_rfl
      apply E.false_of_consecutiveTOuterData_of_inner
        M hRankEq outer inner
      · intro i j
        simp only [inner]
        rw [
          (C.semiAdmissiblePathsTo
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl).length_path j,
          (C.semiAdmissiblePathsTo
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl).length_path j]
        rw [
          typeOne_T_catalog_start C
            (outer.family.endpoint i) (hendpoint i)
            hInnerOne hInnerFour le_rfl,
          typeOne_T_catalog_step C
            (outer.family.endpoint i) (hendpoint i)
            hInnerOne hInnerFour le_rfl,
          typeOne_T_catalog_start C
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            hInnerOne hInnerFour le_rfl,
          typeOne_T_catalog_step C
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            hInnerOne hInnerFour le_rfl]
      · intro i j v hv
        have hvSmall :=
          C.semiAdmissiblePathsTo_support
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl j v (by simpa [inner] using hv)
        simpa [hcore, Core.carrier, Core.S, Core.T] using hvSmall
  | typeTwo C =>
      have hendpoint (i : Fin 2) :
          outer.family.endpoint i ∈ C.T := by
        simpa [hcore, Core.T] using outer.family.endpoint_mem i
      let inner :
          ∀ i : Fin 2,
            SemiAdmissiblePathFamily G x
              (outer.family.endpoint i) (P.working.rank + 1) :=
        fun i =>
          C.semiAdmissiblePathsToT
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour le_rfl
      apply E.false_of_consecutiveTOuterData_of_inner
        M hRankEq outer inner
      · intro i j
        simp only [inner]
        rw [
          (C.semiAdmissiblePathsToT
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl).length_path j,
          (C.semiAdmissiblePathsToT
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl).length_path j]
        rw [
          typeTwo_T_catalog_start C
            (outer.family.endpoint i) (hendpoint i)
            hInnerOne hInnerFour le_rfl,
          typeTwo_T_catalog_step C
            (outer.family.endpoint i) (hendpoint i)
            hInnerOne hInnerFour le_rfl,
          typeTwo_T_catalog_start C
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            hInnerOne hInnerFour le_rfl,
          typeTwo_T_catalog_step C
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            hInnerOne hInnerFour le_rfl]
      · intro i j v hv
        have hvSmall :=
          C.semiAdmissiblePathsToT_support
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl j v (by simpa [inner] using hv)
        simpa [hcore, Core.carrier, Core.S, Core.T] using hvSmall
  | typeThree C =>
      have hendpoint (i : Fin 2) :
          outer.family.endpoint i ∈ C.T := by
        simpa [hcore, Core.T] using outer.family.endpoint_mem i
      let inner :
          ∀ i : Fin 2,
            SemiAdmissiblePathFamily G x
              (outer.family.endpoint i) (P.working.rank + 1) :=
        fun i =>
          C.semiAdmissiblePathsToT
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour le_rfl
      apply E.false_of_consecutiveTOuterData_of_inner
        M hRankEq outer inner
      · intro i j
        simp only [inner]
        rw [
          (C.semiAdmissiblePathsToT
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl).length_path j,
          (C.semiAdmissiblePathsToT
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl).length_path j]
        rw [
          typeThree_T_catalog_start C
            (outer.family.endpoint i) (hendpoint i)
            hInnerOne hInnerFour le_rfl,
          typeThree_T_catalog_step C
            (outer.family.endpoint i) (hendpoint i)
            hInnerOne hInnerFour le_rfl,
          typeThree_T_catalog_start C
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            hInnerOne hInnerFour le_rfl,
          typeThree_T_catalog_step C
            (outer.family.endpoint
              (firstFin (by omega : 1 ≤ 2)))
            (hendpoint (firstFin (by omega : 1 ≤ 2)))
            hInnerOne hInnerFour le_rfl]
      · intro i j v hv
        have hvSmall :=
          C.semiAdmissiblePathsToT_support
            (outer.family.endpoint i) (hendpoint i)
            (P.working.rank + 1) hInnerOne hInnerFour
            le_rfl j v (by simpa [inner] using hv)
        simpa [hcore, Core.carrier, Core.S, Core.T] using hvSmall

/--
COY Claim 3.9(3): neither `z` nor `b'_z` has a neighbour in the working
core's `T`-side.
-/
theorem no_T_neighbor_of_z_or_bPrime
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hRank : P.working.rank ≤ q - 2) :
    (G.neighborSet z ∪ G.neighborSet E.bPrime) ∩
        (↑P.working.rooted.core.T : Set V) =
      ∅ := by
  obtain ⟨hRankEq, -, tb, htbT, hbzTb⟩ :=
    E.rank_degree_equalities_and_exists_T_neighbor M hRank
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro tv htv
  rcases htv with ⟨htvAdj, htvT⟩
  rcases htvAdj with hztv | hPrimeTv
  · let outer :=
      E.consecutiveTOuterDataOfZAdj
        tv tb htvT htbT hztv.symm hbzTb.symm
    exact E.false_of_consecutiveTOuterData
      M hRankEq outer
  · let outer :=
      E.consecutiveTOuterDataOfPrimeAdj
        tv tb htvT htbT hPrimeTv.symm hbzTb.symm
    exact E.false_of_consecutiveTOuterData
      M hRankEq outer

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
