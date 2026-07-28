import DeanK5.COYExteriorClaimThreeSixteenAssemblyChain
import DeanK5.COYExteriorClaimThreeSixteenTerminalGeometry

/-!
# Terminal-block assembly in COY Claim 3.16

When the selected last feasible block is the final block, its recursive
interfaces are the final cut and `y`.  An earlier terminal-side attachment
still supplies the two prefix paths.  The recursive middle paths end at
`y`, so the suffix in the common Claim 3.16 assembly is the stationary path
at `y`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorOrderedBlockChain

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s : V}
  {P : PreferredWorkingCoreData G x y z}

omit [Fintype V] [DecidableEq V] in
private theorem simplePath_support_tail_eq_nil_of_length_eq_zero
    {u v : V}
    (path : SimplePath G u v)
    (hlength : path.length = 0) :
    path.walk.support.tail = [] := by
  have hwalkLength :
      path.walk.length = 0 := by
    exact hlength
  have hnil :
      path.walk.Nil :=
    SimpleGraph.Walk.length_eq_zero_iff.mp hwalkLength
  have hsupport :
      path.walk.support = [u] :=
    SimpleGraph.Walk.nil_iff_support_eq.mp hnil
  rw [hsupport]
  rfl

/--
The terminal selected block needs no genuine suffix: its recursive right
root is already the ambient vertex `y`.
-/
noncomputable def claimThreeSixteenTerminalSuffix
    {M : MinimalCounterexample q G x y z}
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1) :
    SimplePath G
      ((L.claimThreeSixteenTerminalBlockData
        D hall hpositive).recursiveEmbedding
          (L.claimThreeSixteenTerminalBlockData
            D hall hpositive).recursiveRightRoot)
      y := by
  let C :=
    L.claimThreeSixteenTerminalBlockData
      D hall hpositive
  have hright :
      C.recursiveEmbedding C.recursiveRightRoot = y := by
    rw [C.recursiveEmbedding_rightRoot]
    have hrightData :=
      L.claimThreeSixteenTerminalBlockData_right
        D hall hpositive
    change C.right = P.exteriorY at hrightData
    rw [hrightData]
    rfl
  let walk :
      G.Walk
        (C.recursiveEmbedding C.recursiveRightRoot) y :=
    (SimpleGraph.Walk.nil : G.Walk y y).copy
      hright.symm rfl
  exact {
    walk := walk
    isPath := by
      apply
        (SimpleGraph.Walk.isPath_copy
          (SimpleGraph.Walk.nil : G.Walk y y)
          hright.symm rfl).2
      exact SimpleGraph.Walk.IsPath.nil
  }

@[simp] theorem claimThreeSixteenTerminalSuffix_length
    {M : MinimalCounterexample q G x y z}
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1) :
    (O.claimThreeSixteenTerminalSuffix
      D hregion hall L hpositive).length = 0 := by
  unfold claimThreeSixteenTerminalSuffix
  unfold SimplePath.length
  dsimp only
  rw [SimpleGraph.Walk.length_copy]
  rfl

@[simp] theorem claimThreeSixteenTerminalSuffix_support
    {M : MinimalCounterexample q G x y z}
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1) :
    (O.claimThreeSixteenTerminalSuffix
      D hregion hall L hpositive).walk.support = [y] := by
  unfold claimThreeSixteenTerminalSuffix
  dsimp only
  rw [SimpleGraph.Walk.support_copy]
  rfl

/--
Every vertex of a recursively mapped terminal-block path has an exterior
representative in the final block.
-/
theorem exists_exterior_of_mem_mappedTerminalBlockPath_support
    {M : MinimalCounterexample q G x y z}
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    (middle :
      AdmissiblePathFamily
        (L.claimThreeSixteenTerminalBlockData
          D hall hpositive).recursiveGraph
        (L.claimThreeSixteenTerminalBlockData
          D hall hpositive).recursiveLeftRoot
        (L.claimThreeSixteenTerminalBlockData
          D hall hpositive).recursiveRightRoot
        (q - 1))
    (k : Fin (q - 1))
    {v : V}
    (hv :
      v ∈
        ((middle.path k).mapInjectiveHom
          (L.claimThreeSixteenTerminalBlockData
            D hall hpositive).recursiveEmbedding.toHom
          (L.claimThreeSixteenTerminalBlockData
            D hall hpositive).recursiveEmbedding.injective).walk.support) :
    ∃ w : P.ExteriorVertex,
      w.1 = v ∧
        w ∈ (O.chain.blocks O.lastIndex).carrier := by
  let C :=
    L.claimThreeSixteenTerminalBlockData
      D hall hpositive
  have hvRange :
      v ∈ Set.range C.recursiveEmbedding :=
    SimplePath.mem_range_of_mem_mapInjectiveHom_support
      (P := middle.path k)
      (f := C.recursiveEmbedding.toHom)
      (hinj := C.recursiveEmbedding.injective)
      (by simpa [C] using hv)
  obtain ⟨d, hdv⟩ := hvRange
  refine ⟨d.1, ?_, ?_⟩
  · exact C.recursiveEmbedding_apply d ▸ hdv
  · exact d.2

/--
The stationary suffix has empty tail, so every mapped recursive path is
automatically disjoint from it after their common endpoint.
-/
theorem mappedTerminalBlockPath_disjoint_suffix
    {M : MinimalCounterexample q G x y z}
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    (middle :
      AdmissiblePathFamily
        (L.claimThreeSixteenTerminalBlockData
          D hall hpositive).recursiveGraph
        (L.claimThreeSixteenTerminalBlockData
          D hall hpositive).recursiveLeftRoot
        (L.claimThreeSixteenTerminalBlockData
          D hall hpositive).recursiveRightRoot
        (q - 1))
    (k : Fin (q - 1)) :
    ((middle.path k).mapInjectiveHom
      (L.claimThreeSixteenTerminalBlockData
        D hall hpositive).recursiveEmbedding.toHom
      (L.claimThreeSixteenTerminalBlockData
        D hall hpositive).recursiveEmbedding.injective).walk.support.Disjoint
        (O.claimThreeSixteenTerminalSuffix
          D hregion hall L hpositive).walk.support.tail := by
  rw [simplePath_support_tail_eq_nil_of_length_eq_zero
    (O.claimThreeSixteenTerminalSuffix
      D hregion hall L hpositive)
    (O.claimThreeSixteenTerminalSuffix_length
      D hregion hall L hpositive)]
  simp

/--
Any vertex shared by a concrete prefix path and the selected terminal block
is the final cut, the common left endpoint of the recursive middle paths.
-/
theorem claimThreeSixteenPrefix_meets_terminalBlock_only_at_left
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1)
    (j : Fin 2)
    {v : V}
    (hvPrefix :
      v ∈
        ((O.claimThreeSixteenPrefixFamilyFromEarlierAttachment
          M D O.lastIndex
          (by
            change 0 < O.chain.cutCount
            exact O.chain.one_le_cutCount)
          i (by
            simpa [ExteriorOrderedBlockChain.lastIndex,
              L.index_eq_cutCount] using hip)
          a ha htarget hta).path j).walk.support)
    (w : P.ExteriorVertex)
    (hwv : w.1 = v)
    (hwBlock :
      w ∈ (O.chain.blocks O.lastIndex).carrier) :
    v =
      (L.claimThreeSixteenTerminalBlockData
        D hall
          (by
            rw [L.index_eq_cutCount]
            exact O.chain.one_le_cutCount)).recursiveEmbedding
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveLeftRoot := by
  have hpositiveIndex : 0 < L.index.1 := by
    rw [L.index_eq_cutCount]
    exact O.chain.one_le_cutCount
  have hpositiveLast : 0 < O.lastIndex.1 := by
    change 0 < O.chain.cutCount
    exact O.chain.one_le_cutCount
  have hipLast : i.1 < O.lastIndex.1 := by
    simpa [ExteriorOrderedBlockChain.lastIndex,
      L.index_eq_cutCount] using hip
  let C :=
    L.claimThreeSixteenTerminalBlockData
      D hall hpositiveIndex
  have hvClass :=
    O.claimThreeSixteenPrefixFamily_support
      M D O.lastIndex hpositiveLast i hipLast
      a ha htarget hta j hvPrefix
  rcases hvClass with hvCore |
      ⟨wPrefix, hwPrefix, hwPrefixInterval⟩
  · have hwRegion :
        v ∈ P.working.rooted.otherRegion := by
      rw [← hwv]
      exact w.2
    exact False.elim
      (P.working.rooted.otherRegion_componentRegion.not_mem_separator
        hwRegion hvCore)
  · have hwEq : wPrefix = w := by
      apply Subtype.ext
      exact hwPrefix.trans hwv.symm
    have hwPrefixBlock :
        wPrefix ∈
          (O.chain.blocks O.lastIndex).carrier := by
      simpa [hwEq] using hwBlock
    have hmeet :=
      O.chain.intervalCarrier_inter_nextBlock_eq_singleton
        P.exteriorGraph_connected O.incidence_degree_le_two
        (start := 0) (len := O.chain.cutCount - 1)
        (by
          have := O.chain.one_le_cutCount
          omega)
    have hwInter :
        wPrefix ∈
          O.chain.intervalCarrier 0
              (O.chain.cutCount - 1) ∩
            (O.chain.blocks
              ⟨0 + (O.chain.cutCount - 1) + 1,
                by omega⟩).carrier := by
      apply Finset.mem_inter.mpr
      refine ⟨?_, ?_⟩
      · simpa [ExteriorOrderedBlockChain.lastIndex] using
          hwPrefixInterval
      · have hindex :
            (⟨0 + (O.chain.cutCount - 1) + 1,
                by omega⟩ :
              Fin (O.chain.cutCount + 1)) =
              O.lastIndex := by
          apply Fin.ext
          dsimp [ExteriorOrderedBlockChain.lastIndex]
          have := O.chain.one_le_cutCount
          omega
        rw [hindex]
        exact hwPrefixBlock
    rw [hmeet] at hwInter
    have hwLeft :
        wPrefix =
          (O.chain.cuts
            ⟨O.chain.cutCount - 1, by
              omega⟩).1 := by
      simpa using hwInter
    rw [C.recursiveEmbedding_leftRoot]
    calc
      v = wPrefix.1 := hwPrefix.symm
      _ =
          (O.chain.cuts
            ⟨O.chain.cutCount - 1, by
              omega⟩).1.1 :=
        congrArg Subtype.val hwLeft
      _ = C.left.1 := by
        simp [C]

/--
The prefix family is disjoint from the tail of every mapped recursive
middle path in the selected terminal block.
-/
theorem claimThreeSixteenTerminalPrefix_disjoint_mappedMiddle_tail
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1)
    (middle :
      AdmissiblePathFamily
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveGraph
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveLeftRoot
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveRightRoot
        (q - 1))
    (k : Fin (q - 1))
    (j : Fin 2) :
    ((O.claimThreeSixteenPrefixFamilyFromEarlierAttachment
      M D O.lastIndex
      (by
        change 0 < O.chain.cutCount
        exact O.chain.one_le_cutCount)
      i (by
        simpa [ExteriorOrderedBlockChain.lastIndex,
          L.index_eq_cutCount] using hip)
      a ha htarget hta).path j).walk.support.Disjoint
      ((middle.path k).mapInjectiveHom
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveEmbedding.toHom
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveEmbedding.injective).walk.support.tail := by
  let hpositive : 0 < L.index.1 := by
    rw [L.index_eq_cutCount]
    exact O.chain.one_le_cutCount
  let C :=
    L.claimThreeSixteenTerminalBlockData
      D hall hpositive
  let middlePath :=
    (middle.path k).mapInjectiveHom
      C.recursiveEmbedding.toHom C.recursiveEmbedding.injective
  apply List.disjoint_left.mpr
  intro v hvPrefix hvMiddle
  obtain ⟨w, hwv, hwBlock⟩ :=
    O.exists_exterior_of_mem_mappedTerminalBlockPath_support
      D hregion hall L hpositive middle k
      (List.mem_of_mem_tail
        (by simpa [C, middlePath] using hvMiddle))
  have hvStart :
      v =
        C.recursiveEmbedding C.recursiveLeftRoot := by
    exact
      O.claimThreeSixteenPrefix_meets_terminalBlock_only_at_left
        M D hregion hall L i hip a ha htarget hta
          j hvPrefix w hwv hwBlock
  have hvMiddle' :
      v ∈ middlePath.walk.support.tail := by
    simpa [C, middlePath] using hvMiddle
  rw [hvStart] at hvMiddle'
  exact middlePath.start_not_mem_tail hvMiddle'

/--
The terminal prefix avoids the tail of every middle path followed by the
stationary suffix.
-/
theorem claimThreeSixteenTerminalPrefix_disjoint_outer
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1)
    (middle :
      AdmissiblePathFamily
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveGraph
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveLeftRoot
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveRightRoot
        (q - 1))
    (k : Fin (q - 1))
    (j : Fin 2) :
    let hpositive : 0 < L.index.1 := by
      rw [L.index_eq_cutCount]
      exact O.chain.one_le_cutCount
    let C :=
      L.claimThreeSixteenTerminalBlockData
        D hall hpositive
    let suffix :=
      O.claimThreeSixteenTerminalSuffix
        D hregion hall L hpositive
    let hmiddle :=
      O.mappedTerminalBlockPath_disjoint_suffix
        D hregion hall L hpositive middle k
    ((O.claimThreeSixteenPrefixFamilyFromEarlierAttachment
      M D O.lastIndex
      (by
        change 0 < O.chain.cutCount
        exact O.chain.one_le_cutCount)
      i (by
        simpa [ExteriorOrderedBlockChain.lastIndex,
          L.index_eq_cutCount] using hip)
      a ha htarget hta).path j).walk.support.Disjoint
      (((middle.path k).mapInjectiveHom
        C.recursiveEmbedding.toHom
        C.recursiveEmbedding.injective).appendDisjoint
          suffix hmiddle).walk.support.tail := by
  dsimp only
  let hpositive : 0 < L.index.1 := by
    rw [L.index_eq_cutCount]
    exact O.chain.one_le_cutCount
  let C :=
    L.claimThreeSixteenTerminalBlockData
      D hall hpositive
  let middlePath :=
    (middle.path k).mapInjectiveHom
      C.recursiveEmbedding.toHom C.recursiveEmbedding.injective
  let suffix :=
    O.claimThreeSixteenTerminalSuffix
      D hregion hall L hpositive
  apply List.disjoint_left.mpr
  intro v hvPrefix hvOuter
  have hvParts :
      v ∈ middlePath.walk.support.tail ∨
        v ∈ suffix.walk.support.tail := by
    exact
      (SimpleGraph.Walk.mem_tail_support_append_iff
        middlePath.walk suffix.walk).1
        (by
          simpa [C, middlePath, suffix,
            SimplePath.appendDisjoint] using hvOuter)
  rcases hvParts with hvMiddle | hvSuffix
  · exact
      List.disjoint_left.mp
        (O.claimThreeSixteenTerminalPrefix_disjoint_mappedMiddle_tail
          M D hregion hall L i hip a ha htarget hta
            middle k j)
        hvPrefix
        (by simpa [C, middlePath] using hvMiddle)
  · have hsuffixEmpty :
        suffix.walk.support.tail = [] := by
      apply
        simplePath_support_tail_eq_nil_of_length_eq_zero
          suffix
      dsimp only [suffix]
      exact
        O.claimThreeSixteenTerminalSuffix_length
          D hregion hall L hpositive
    rw [hsuffixEmpty] at hvSuffix
    simp at hvSuffix

/--
Assemble the two prefix paths and the recursively obtained terminal-block
family, using the stationary path at `y` as suffix.
-/
noncomputable def claimThreeSixteenTerminalAssemblyFromEarlierAttachment
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hS : D.core.S = {s})
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1)
    (middle :
      AdmissiblePathFamily
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveGraph
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveLeftRoot
        (L.claimThreeSixteenTerminalBlockData
          D hall
            (by
              rw [L.index_eq_cutCount]
              exact O.chain.one_le_cutCount)).recursiveRightRoot
        (q - 1)) :
    let hpositive : 0 < L.index.1 := by
      rw [L.index_eq_cutCount]
      exact O.chain.one_le_cutCount
    let C :=
      L.claimThreeSixteenTerminalBlockData
        D hall hpositive
    ClaimThreeSixteenAssembly G x y
      C.recursiveGraph C.recursiveLeftRoot
      C.recursiveRightRoot middle := by
  dsimp only
  let hpositive : 0 < L.index.1 := by
    rw [L.index_eq_cutCount]
    exact O.chain.one_le_cutCount
  let hpositiveLast : 0 < O.lastIndex.1 := by
    change 0 < O.chain.cutCount
    exact O.chain.one_le_cutCount
  let hipLast : i.1 < O.lastIndex.1 := by
    simpa [ExteriorOrderedBlockChain.lastIndex,
      L.index_eq_cutCount] using hip
  let C :=
    L.claimThreeSixteenTerminalBlockData
      D hall hpositive
  let prefixFamily :=
    O.claimThreeSixteenPrefixFamilyFromEarlierAttachment
      M D O.lastIndex hpositiveLast i hipLast
        a ha htarget hta
  let suffix :=
    O.claimThreeSixteenTerminalSuffix
      D hregion hall L hpositive
  let middleSuffixDisjoint :
      ∀ k,
        ((middle.path k).mapInjectiveHom
          C.recursiveEmbedding.toHom
          C.recursiveEmbedding.injective).walk.support.Disjoint
            suffix.walk.support.tail :=
    O.mappedTerminalBlockPath_disjoint_suffix
      D hregion hall L hpositive middle
  refine {
    embedding := C.recursiveEmbedding
    prefixFamily := prefixFamily
    suffix := suffix
    middle_disjoint_suffix := middleSuffixDisjoint
    prefix_disjoint_outer := ?_
    roots_ne := M.roots_ne
    root_ne_left := ?_
    otherRoot_ne_left := ?_
    pred_pos := ?_
  }
  · intro k j
    exact
      O.claimThreeSixteenTerminalPrefix_disjoint_outer
        M D hregion hall L i hip a ha htarget hta
          middle k j
  · intro hx
    have hleftRegion :
        C.left.1 ∈ P.working.rooted.otherRegion :=
      C.left.2
    have hxCore :
        x ∈ P.working.rooted.core.carrier :=
      P.working.rooted.core.root_mem_carrier
    have hxLeft :
        x = C.left.1 :=
      hx.trans C.recursiveEmbedding_leftRoot
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        hleftRegion (by
          rw [← hxLeft]
          exact hxCore)
  · intro hy
    apply O.y_not_cut
    have hleftY :
        C.left = P.exteriorY := by
      apply Subtype.ext
      exact hy.symm
    exact hleftY ▸ C.left_isCut
  · have hq :=
      P.three_le_q_of_typeThree_singleton_side
        M D.core D.core_eq hS hregion
    omega

/--
Package the selected terminal block and its stationary-suffix assembly as
the recursive stage consumed by minimality.
-/
noncomputable def claimThreeSixteenTerminalRecursiveStageFromEarlierAttachment
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hS : D.core.S = {s})
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1) :
    let hpositive : 0 < L.index.1 := by
      rw [L.index_eq_cutCount]
      exact O.chain.one_le_cutCount
    let C :=
      L.claimThreeSixteenTerminalBlockData
        D hall hpositive
    ClaimThreeSixteenRecursiveStage
      (q := q) G x y C.recursiveGraph
      C.recursiveLeftRoot C.recursiveRightRoot
      C.recursiveException := by
  dsimp only
  let hpositive : 0 < L.index.1 := by
    rw [L.index_eq_cutCount]
    exact O.chain.one_le_cutCount
  let C :=
    L.claimThreeSixteenTerminalBlockData
      D hall hpositive
  exact
    C.recursiveStage M hS hregion fun middle =>
      O.claimThreeSixteenTerminalAssemblyFromEarlierAttachment
        M D hregion hall L hS i hip a ha
          htarget hta middle

/--
An earlier terminal-side attachment contradicts minimality when the selected
last feasible block is terminal.
-/
theorem false_of_terminal_attachment_before_terminalLastFeasible
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hS : D.core.S = {s})
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1) :
    False :=
  (O.claimThreeSixteenTerminalRecursiveStageFromEarlierAttachment
    M D hregion hall L hS i hip a ha
      htarget hta).false_of_recursiveStage M

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
