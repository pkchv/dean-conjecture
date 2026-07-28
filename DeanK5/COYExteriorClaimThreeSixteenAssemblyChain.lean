import DeanK5.COYExteriorClaimThreeSixteenGeometry
import DeanK5.COYExteriorClaimThreeSixteenPrefixChain
import DeanK5.COYExteriorClaimThreeSixteenSuffixChain
import DeanK5.Graph.OrderedBlockChainIntervalMembership

/-!
# Assembling the recursive paths in COY Claim 3.16

An attachment from the terminal side of the working core to a block before
the selected last feasible block supplies two prefix paths.  The selected
block supplies the recursive middle family, and the blocks after it supply
one fixed suffix to `y`.  This file verifies the support separation needed
to concatenate those three pieces into the forbidden ambient family.
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

/--
Every vertex of the mapped prefix path has a unique exterior representative
in the prefix interval.
-/
theorem exists_exterior_of_mem_prefixAmbientPath_support
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {v : V}
    (hv :
      v ∈ (O.prefixAmbientPath p hp i hip a ha).walk.support) :
    ∃ w : P.ExteriorVertex,
      w.1 = v ∧
        w ∈ O.chain.intervalCarrier 0 (p.1 - 1) := by
  have hvMap :
      v ∈
        ((O.prefixExteriorPath p hp i hip a ha).walk.map
          P.exteriorEmbedding.toHom).support := by
    change
      v ∈
        ((O.prefixExteriorPath p hp i hip a ha).walk.map
          P.exteriorEmbedding.toHom).support at hv
    exact hv
  rw [SimpleGraph.Walk.support_map] at hvMap
  obtain ⟨w, hw, hwv⟩ := List.mem_map.mp hvMap
  refine ⟨w, ?_, O.prefixExteriorPath_support
    p hp i hip a ha w hw⟩
  exact hwv

/--
After its initial core vertex, the fixed prefix connector is supported in
the blocks strictly before the selected block.
-/
theorem exists_exterior_of_mem_claimThreeSixteenPrefixConnector_tail
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1)
    {v : V}
    (hv :
      v ∈
        (O.claimThreeSixteenPrefixConnector
          D p hp i hip a ha htarget hta).walk.support.tail) :
    ∃ w : P.ExteriorVertex,
      w.1 = v ∧
        w ∈ O.chain.intervalCarrier 0 (p.1 - 1) := by
  have hvParts :
      v ∈ (SimplePath.ofAdj hta).walk.support.tail ∨
        v ∈
          (O.prefixAmbientPath p hp i hip a ha).walk.support.tail := by
    exact
      (SimpleGraph.Walk.mem_tail_support_append_iff
        (SimplePath.ofAdj hta).walk
        (O.prefixAmbientPath p hp i hip a ha).walk).1
        (by
          simpa [claimThreeSixteenPrefixConnector,
            SimplePath.appendDisjoint] using hv)
  rcases hvParts with hvEdge | hvPath
  · have hva : v = a.1 := by
      simpa using hvEdge
    refine ⟨a, hva.symm, ?_⟩
    have hbound :
        0 + (p.1 - 1) ≤ O.chain.cutCount := by
      omega
    have hiOffset :
        i.1 ≤ p.1 - 1 := by
      omega
    exact
      O.chain.block_subset_intervalCarrier
        (start := 0) (len := p.1 - 1) (k := i.1)
        hiOffset hbound (by simpa using ha)
  · exact
      O.exists_exterior_of_mem_prefixAmbientPath_support
        p hp i hip a ha (List.mem_of_mem_tail hvPath)

/--
The concrete two-path prefix family is supported either in the selected core
or in the chain interval strictly before the selected block.
-/
theorem claimThreeSixteenPrefixFamily_support
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1)
    (j : Fin 2)
    {v : V}
    (hv :
      v ∈
        ((O.claimThreeSixteenPrefixFamilyFromEarlierAttachment
          M D p hp i hip a ha htarget hta).path j).walk.support) :
    v ∈ P.working.rooted.core.carrier ∨
      ∃ w : P.ExteriorVertex,
        w.1 = v ∧
          w ∈ O.chain.intervalCarrier 0 (p.1 - 1) := by
  let connector :=
    O.claimThreeSixteenPrefixConnector
      D p hp i hip a ha htarget hta
  have hcapacity :
      2 ≤ P.working.rank + 1 := by
    have hrank := D.rank_eq_one M
    omega
  let htailOutside :
      ∀ v ∈ connector.walk.support.tail,
        v ∉ insert x (D.core.S ∪ D.core.T) :=
    fun v hv =>
      O.claimThreeSixteenPrefixConnector_tail_outside
        D p hp i hip a ha htarget hta hv
  let hdisjoint :
      ∀ k : Fin 2,
        ((D.core.semiAdmissiblePathsToT target htarget 2
          (by omega) (by omega) hcapacity).path k).walk.support.Disjoint
            connector.walk.support.tail :=
    D.core.claimThreeSixteenPrefix_disjoint_of_tail_outside
      htarget connector hcapacity htailOutside
  have hvParts :
      v ∈
          ((D.core.semiAdmissiblePathsToT target htarget 2
            (by omega) (by omega) hcapacity).path j).walk.support ∨
        v ∈ connector.walk.support.tail := by
    change
      v ∈
        (((D.core.semiAdmissiblePathsToT target htarget 2
          (by omega) (by omega) hcapacity).path j).appendDisjoint
            connector (hdisjoint j)).walk.support at hv
    rw [SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hv
    exact List.mem_append.mp hv
  rcases hvParts with hvCore | hvConnector
  · left
    have hvCarrier :=
      D.core.semiAdmissiblePathsToT_support
        target htarget 2 (by omega) (by omega)
        hcapacity j v hvCore
    rw [D.core_eq]
    simpa [Core.carrier, Core.S, Core.T] using hvCarrier
  · right
    exact
      O.exists_exterior_of_mem_claimThreeSixteenPrefixConnector_tail
        D p hp i hip a ha htarget hta hvConnector

/--
Every vertex of a recursively mapped selected-block path has an exterior
representative in that selected block.
-/
theorem exists_exterior_of_mem_mappedSelectedBlockPath_support
    {M : MinimalCounterexample q G x y z}
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    (middle :
      AdmissiblePathFamily
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveGraph
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveLeftRoot
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveRightRoot
        (q - 1))
    (k : Fin (q - 1))
    {v : V}
    (hv :
      v ∈
        ((middle.path k).mapInjectiveHom
          (L.claimThreeSixteenBlockData D hall hpositive).recursiveEmbedding.toHom
          (L.claimThreeSixteenBlockData D hall hpositive).recursiveEmbedding.injective).walk.support) :
    ∃ w : P.ExteriorVertex,
      w.1 = v ∧
        w ∈ (O.chain.blocks L.index).carrier := by
  let C :=
    L.claimThreeSixteenBlockData D hall hpositive
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
The two chain intervals separated by the selected block are disjoint.
-/
theorem prefixInterval_disjoint_suffixInterval
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (hpBefore : p.1 < O.chain.cutCount) :
    Disjoint
      (O.chain.intervalCarrier 0 (p.1 - 1))
      (O.chain.intervalCarrier
        (p.1 + 1)
        (O.chain.cutCount - (p.1 + 1))) := by
  apply Finset.disjoint_left.mpr
  intro v hvPrefix hvSuffix
  have hprefixBound :
      0 + (p.1 - 1) ≤ O.chain.cutCount := by
    omega
  have hsuffixBound :
      p.1 + 1 +
          (O.chain.cutCount - (p.1 + 1)) ≤
        O.chain.cutCount := by
    omega
  obtain ⟨k, hk, hvBlock⟩ :=
    O.chain.exists_blockAt_add_of_mem_intervalCarrier
      hsuffixBound hvSuffix
  let j : Fin (O.chain.cutCount + 1) :=
    ⟨p.1 + 1 + k, by omega⟩
  have hfar :
      0 + (p.1 - 1) + 1 < j.1 := by
    dsimp [j]
    omega
  have hinter :=
    O.chain.intervalCarrier_inter_block_eq_empty
      P.exteriorGraph_connected O.incidence_degree_le_two
      hprefixBound j (Or.inr hfar)
  have hvInter :
      v ∈ O.chain.intervalCarrier 0 (p.1 - 1) ∩
        (O.chain.blocks j).carrier :=
    Finset.mem_inter.mpr
      ⟨hvPrefix, by simpa [j, Nat.add_assoc] using hvBlock⟩
  rw [hinter] at hvInter
  simp at hvInter

/--
Every vertex of the mapped suffix has an exterior representative in the
chain interval strictly after the selected block.
-/
theorem exists_exterior_of_mem_suffixAmbientPath_support
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hpBefore : p.1 < O.chain.cutCount)
    {v : V}
    (hv : v ∈ (O.suffixAmbientPath p hpBefore).walk.support) :
    ∃ w : P.ExteriorVertex,
      w.1 = v ∧
        w ∈ O.chain.intervalCarrier
          (p.1 + 1)
          (O.chain.cutCount - (p.1 + 1)) := by
  have hvMap :
      v ∈
        ((O.suffixExteriorPath p hpBefore).walk.map
          P.exteriorEmbedding.toHom).support := by
    change
      v ∈
        ((O.suffixExteriorPath p hpBefore).walk.map
          P.exteriorEmbedding.toHom).support at hv
    exact hv
  rw [SimpleGraph.Walk.support_map] at hvMap
  obtain ⟨w, hw, hwv⟩ := List.mem_map.mp hvMap
  refine ⟨w, hwv, ?_⟩
  exact O.suffixExteriorPath_support p hpBefore w hw

/--
A recursively mapped path in the selected block meets the fixed suffix only
at their common right cut.
-/
theorem mappedSelectedBlockPath_disjoint_suffix
    {M : MinimalCounterexample q G x y z}
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    (middle :
      AdmissiblePathFamily
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveGraph
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveLeftRoot
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveRightRoot
        (q - 1))
    (k : Fin (q - 1)) :
    ((middle.path k).mapInjectiveHom
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveEmbedding.toHom
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveEmbedding.injective).walk.support.Disjoint
        (O.suffixAmbientPath
          L.index L.index_lt_cutCount).walk.support.tail := by
  let C :=
    L.claimThreeSixteenBlockData D hall hpositive
  let Q :=
    (middle.path k).mapInjectiveHom
      C.recursiveEmbedding.toHom
      C.recursiveEmbedding.injective
  have hQ :
      ∀ v ∈ Q.walk.support,
        ∃ w ∈ (O.chain.blocks L.index).carrier,
          w.1 = v := by
    intro v hv
    obtain ⟨w, hwv, hwBlock⟩ :=
      O.exists_exterior_of_mem_mappedSelectedBlockPath_support
        D hregion hall L hpositive middle k
        (by simpa [C, Q] using hv)
    exact ⟨w, hwBlock, hwv⟩
  have h :=
    O.pathInSelectedBlock_disjoint_suffix_tail
      L.index L.index_lt_cutCount Q hQ
  exact h

/--
The concrete prefix family avoids the tail of every middle-plus-suffix path.
This is the final geometric premise required by COY Fact 1.
-/
theorem claimThreeSixteenPrefix_disjoint_outer
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1)
    (middle :
      AdmissiblePathFamily
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveGraph
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveLeftRoot
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveRightRoot
        (q - 1))
    (k : Fin (q - 1))
    (j : Fin 2) :
    ((O.claimThreeSixteenPrefixFamilyFromEarlierAttachment
      M D L.index hpositive i hip a ha htarget hta).path j).walk.support.Disjoint
      (((middle.path k).mapInjectiveHom
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveEmbedding.toHom
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveEmbedding.injective).appendDisjoint
          (O.suffixAmbientPath L.index L.index_lt_cutCount)
          (O.mappedSelectedBlockPath_disjoint_suffix
            D hregion hall L hpositive middle k)).walk.support.tail := by
  let C :=
    L.claimThreeSixteenBlockData D hall hpositive
  let middlePath :=
    (middle.path k).mapInjectiveHom
      C.recursiveEmbedding.toHom C.recursiveEmbedding.injective
  let suffix :=
    O.suffixAmbientPath L.index L.index_lt_cutCount
  apply List.disjoint_left.mpr
  intro v hvPrefix hvOuter
  have hvPrefixClass :=
    O.claimThreeSixteenPrefixFamily_support
      M D L.index hpositive i hip a ha htarget hta j hvPrefix
  have hvOuterParts :
      v ∈ middlePath.walk.support.tail ∨
        v ∈ suffix.walk.support.tail := by
    exact
      (SimpleGraph.Walk.mem_tail_support_append_iff
        middlePath.walk suffix.walk).1
        (by
          simpa [C, middlePath, suffix,
            SimplePath.appendDisjoint] using hvOuter)
  rcases hvPrefixClass with hvCore | ⟨wPrefix, hwPrefix, hwPrefixInterval⟩
  · rcases hvOuterParts with hvMiddle | hvSuffix
    · obtain ⟨wMiddle, hwMiddle, -⟩ :=
        O.exists_exterior_of_mem_mappedSelectedBlockPath_support
          D hregion hall L hpositive middle k
          (List.mem_of_mem_tail
            (by simpa [C, middlePath] using hvMiddle))
      have hvRegion :
          v ∈ P.working.rooted.otherRegion := by
        rw [← hwMiddle]
        exact wMiddle.2
      exact
        P.working.rooted.otherRegion_componentRegion.not_mem_separator
          hvRegion hvCore
    · have hvRegion :
          v ∈ P.working.rooted.otherRegion :=
        O.suffixAmbientPath_support_mem_otherRegion
          L.index L.index_lt_cutCount
          (List.mem_of_mem_tail
            (by simpa [suffix] using hvSuffix))
      exact
        P.working.rooted.otherRegion_componentRegion.not_mem_separator
          hvRegion hvCore
  · rcases hvOuterParts with hvMiddle | hvSuffix
    · obtain ⟨wMiddle, hwMiddle, hwMiddleBlock⟩ :=
        O.exists_exterior_of_mem_mappedSelectedBlockPath_support
          D hregion hall L hpositive middle k
          (List.mem_of_mem_tail
            (by simpa [C, middlePath] using hvMiddle))
      have hwEq : wPrefix = wMiddle := by
        apply Subtype.ext
        exact hwPrefix.trans hwMiddle.symm
      have hwPrefixBlock :
          wPrefix ∈ (O.chain.blocks L.index).carrier := by
        simpa [hwEq] using hwMiddleBlock
      have hmeet :=
        O.chain.intervalCarrier_inter_nextBlock_eq_singleton
          P.exteriorGraph_connected O.incidence_degree_le_two
          (start := 0) (len := L.index.1 - 1)
          (by omega : 0 + (L.index.1 - 1) < O.chain.cutCount)
      have hwInter :
          wPrefix ∈
            O.chain.intervalCarrier 0 (L.index.1 - 1) ∩
              (O.chain.blocks
                ⟨0 + (L.index.1 - 1) + 1, by omega⟩).carrier := by
        apply Finset.mem_inter.mpr
        refine ⟨hwPrefixInterval, ?_⟩
        have hindex :
            (⟨0 + (L.index.1 - 1) + 1, by omega⟩ :
              Fin (O.chain.cutCount + 1)) =
              L.index := by
          apply Fin.ext
          change 0 + (L.index.1 - 1) + 1 = L.index.1
          omega
        rw [hindex]
        exact hwPrefixBlock
      rw [hmeet] at hwInter
      have hwLeft :
          wPrefix =
            (O.chain.cuts
              ⟨L.index.1 - 1, by omega⟩).1 := by
        simpa using hwInter
      have hvStart :
          v = C.recursiveEmbedding C.recursiveLeftRoot := by
        rw [C.recursiveEmbedding_leftRoot]
        simpa [C] using
          hwPrefix.symm.trans
            (congrArg Subtype.val hwLeft)
      have hvMiddle' :
          v ∈ middlePath.walk.support.tail := by
        simpa [C, middlePath] using hvMiddle
      rw [hvStart] at hvMiddle'
      exact middlePath.start_not_mem_tail hvMiddle'
    · obtain ⟨wSuffix, hwSuffix, hwSuffixInterval⟩ :=
        O.exists_exterior_of_mem_suffixAmbientPath_support
          L.index L.index_lt_cutCount
          (List.mem_of_mem_tail
            (by simpa [suffix] using hvSuffix))
      have hwEq : wPrefix = wSuffix := by
        apply Subtype.ext
        exact hwPrefix.trans hwSuffix.symm
      have hwPrefixInSuffix :
          wPrefix ∈
            O.chain.intervalCarrier
              (L.index.1 + 1)
              (O.chain.cutCount - (L.index.1 + 1)) := by
        simpa [hwEq] using hwSuffixInterval
      exact
        Finset.disjoint_left.mp
          (O.prefixInterval_disjoint_suffixInterval
            L.index hpositive L.index_lt_cutCount)
          hwPrefixInterval hwPrefixInSuffix

/--
Assemble the two core-prefix paths, the recursively obtained selected-block
family, and the fixed suffix path.
-/
noncomputable def claimThreeSixteenAssemblyFromEarlierAttachment
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
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
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveGraph
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveLeftRoot
        (L.claimThreeSixteenBlockData D hall hpositive).recursiveRightRoot
        (q - 1)) :
    ClaimThreeSixteenAssembly G x y
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveGraph
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveLeftRoot
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveRightRoot
      middle := by
  let C :=
    L.claimThreeSixteenBlockData D hall hpositive
  let prefixFamily :=
    O.claimThreeSixteenPrefixFamilyFromEarlierAttachment
      M D L.index hpositive i hip a ha htarget hta
  let suffix :=
    O.suffixAmbientPath L.index L.index_lt_cutCount
  let middleSuffixDisjoint :
      ∀ k,
        ((middle.path k).mapInjectiveHom
          C.recursiveEmbedding.toHom
          C.recursiveEmbedding.injective).walk.support.Disjoint
            suffix.walk.support.tail :=
    O.mappedSelectedBlockPath_disjoint_suffix
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
      O.claimThreeSixteenPrefix_disjoint_outer
        M D hregion hall L hpositive i hip a ha
          htarget hta middle k j
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
Package the selected block and its concrete path assembly as the recursive
stage consumed by minimality.
-/
noncomputable def claimThreeSixteenRecursiveStageFromEarlierAttachment
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    (hS : D.core.S = {s})
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1) :
    ClaimThreeSixteenRecursiveStage
      (q := q) G x y
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveGraph
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveLeftRoot
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveRightRoot
      (L.claimThreeSixteenBlockData D hall hpositive).recursiveException := by
  let C :=
    L.claimThreeSixteenBlockData D hall hpositive
  exact
    C.recursiveStage M hS hregion fun middle =>
      O.claimThreeSixteenAssemblyFromEarlierAttachment
        M D hregion hall L hpositive hS i hip a ha
          htarget hta middle

/--
Consequently, no terminal-side attachment can occur in a block strictly
before a positive, nonfinal selected last feasible block.
-/
theorem false_of_terminal_attachment_before_lastFeasible
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    (hS : D.core.S = {s})
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1) :
    False :=
  (O.claimThreeSixteenRecursiveStageFromEarlierAttachment
    M D hregion hall L hpositive hS i hip a ha
      htarget hta).false_of_recursiveStage M

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
