import DeanK5.COYExteriorBlockTree
import DeanK5.Graph.BlockCutChain

/-!
# The endpoint blocks of the selected COY exterior

After Claim 3.15, the block--cut incidence tree of the selected exterior has
exactly two leaves.  The marked-leaf map injects those leaves into the
protected exterior vertices.  Since there are at most two protected vertices,
the map is a bijection: one leaf block contains `z` as a non-cut vertex and
the other contains `y` as a non-cut vertex.

The final theorem records the unique Hamiltonian incidence path between these
two endpoint blocks.  This is the precise block-chain interface needed by the
remaining part of the COY argument.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- Finiteness of exterior block--cut nodes used to identify the endpoint blocks. -/
noncomputable local instance exteriorEndpointNodeFintype
    (P : PreferredWorkingCoreData G x y z) :
    Fintype (BlockCutNode P.exteriorGraph) :=
  Fintype.ofFinite _

/-- Decidable equality for exterior block--cut nodes in the endpoint argument. -/
noncomputable local instance exteriorEndpointNodeDecidableEq
    (P : PreferredWorkingCoreData G x y z) :
    DecidableEq (BlockCutNode P.exteriorGraph) :=
  Classical.decEq _

/-- Decidable exterior incidence adjacency used in the endpoint argument. -/
noncomputable local instance exteriorEndpointAdjDecidable
    (P : PreferredWorkingCoreData G x y z) :
    DecidableRel (blockCutIncidence P.exteriorGraph).Adj :=
  Classical.decRel _

/--
After Claim 3.15, both possible protected exterior vertices occur: the
protected set has cardinality exactly two.
-/
theorem exteriorProtected_card_eq_two
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    P.exteriorProtected.card = 2 := by
  have hleaves :=
    P.exteriorBlockCutIncidence_leafVertices_card_eq_two
      M D hregion hall
  have hle :=
    BlockCutIncidence.leafVertices_card_le_marked
      P.exteriorGraph_connected
      P.exteriorProtected P.exteriorY
      P.exteriorY_mem_exteriorProtected
      (P.anchoredBlockMeetsExceptions_of_allFeasibleBlocks hall)
  rw [hleaves] at hle
  exact Nat.le_antisymm P.exteriorProtected_card_le_two hle

/-- Claim 3.15 forces the exceptional vertex `z` into the selected exterior. -/
theorem exception_mem_otherRegion_of_allFeasibleBlocks
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    z ∈ P.working.rooted.otherRegion := by
  by_contra hz
  have hcard :=
    P.exteriorProtected_card_eq_two M D hregion hall
  rw [P.exteriorProtected_eq_singleton_of_exception_not_mem hz] at hcard
  simp at hcard

/-- The two protected vertices in the selected exterior are distinct. -/
theorem right_root_ne_exception_of_allFeasibleBlocks
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    y ≠ z := by
  let hz :=
    P.exception_mem_otherRegion_of_allFeasibleBlocks
      M D hregion hall
  intro hyz
  have hcard :=
    P.exteriorProtected_card_eq_two M D hregion hall
  rw [P.exteriorProtected_eq_pair hz] at hcard
  have hvertices :
      P.exteriorY = P.exteriorZ hz := by
    apply Subtype.ext
    exact hyz
  rw [hvertices] at hcard
  simp at hcard

/--
The two endpoint leaf blocks of the selected exterior block--cut tree.

The membership and non-cut fields state exactly that `z` and `y` are the
non-cut marked vertices selected at the two leaves.
-/
structure ExteriorBlockEndpoints
    (P : PreferredWorkingCoreData G x y z) where
  /-- The exceptional vertex lies in the selected exterior. -/
  z_mem_otherRegion : z ∈ P.working.rooted.otherRegion
  /-- The protected ambient vertices are distinct. -/
  y_ne_z : y ≠ z
  /-- The incidence leaf whose block contains `z`. -/
  zLeaf : BlockCutIncidence.IncidenceLeaf P.exteriorGraph
  /-- The incidence leaf whose block contains `y`. -/
  yLeaf : BlockCutIncidence.IncidenceLeaf P.exteriorGraph
  /-- The two endpoint leaves are distinct. -/
  zLeaf_ne_yLeaf : zLeaf ≠ yLeaf
  /-- The exterior copy of `z` belongs to the `z`-leaf block. -/
  z_mem_block :
    P.exteriorZ z_mem_otherRegion ∈
      (BlockCutIncidence.blockOfLeaf
        P.exteriorGraph_connected zLeaf).carrier
  /-- The exterior copy of `y` belongs to the `y`-leaf block. -/
  y_mem_block :
    P.exteriorY ∈
      (BlockCutIncidence.blockOfLeaf
        P.exteriorGraph_connected yLeaf).carrier
  /-- The exterior copy of `z` is not a cut vertex. -/
  z_not_cut :
    ¬IsCutVertex P.exteriorGraph
      (P.exteriorZ z_mem_otherRegion)
  /-- The exterior copy of `y` is not a cut vertex. -/
  y_not_cut :
    ¬IsCutVertex P.exteriorGraph P.exteriorY

namespace ExteriorBlockEndpoints

variable {P : PreferredWorkingCoreData G x y z}

/-- The leaf block containing the exceptional vertex. -/
noncomputable abbrev zBlock
    (E : P.ExteriorBlockEndpoints) :
    GraphBlock P.exteriorGraph :=
  BlockCutIncidence.blockOfLeaf
    P.exteriorGraph_connected E.zLeaf

/-- The leaf block containing the second root. -/
noncomputable abbrev yBlock
    (E : P.ExteriorBlockEndpoints) :
    GraphBlock P.exteriorGraph :=
  BlockCutIncidence.blockOfLeaf
    P.exteriorGraph_connected E.yLeaf

/-- The `z`-endpoint block is a degree-one incidence node. -/
theorem zBlock_degree_eq_one
    (E : P.ExteriorBlockEndpoints) :
    (blockCutIncidence P.exteriorGraph).degree
      (.inl E.zBlock) = 1 :=
  BlockCutIncidence.blockOfLeaf_degree_eq_one
    P.exteriorGraph_connected E.zLeaf

/-- The `y`-endpoint block is a degree-one incidence node. -/
theorem yBlock_degree_eq_one
    (E : P.ExteriorBlockEndpoints) :
    (blockCutIncidence P.exteriorGraph).degree
      (.inl E.yBlock) = 1 :=
  BlockCutIncidence.blockOfLeaf_degree_eq_one
    P.exteriorGraph_connected E.yLeaf

/-- The two endpoint blocks are distinct. -/
theorem zBlock_ne_yBlock
    (E : P.ExteriorBlockEndpoints) :
    E.zBlock ≠ E.yBlock := by
  intro hblocks
  apply E.zLeaf_ne_yLeaf
  apply Subtype.ext
  calc
    E.zLeaf.1 =
        .inl E.zBlock :=
      BlockCutIncidence.leaf_eq_inl_blockOfLeaf
        P.exteriorGraph_connected E.zLeaf
    _ = .inl E.yBlock := by rw [hblocks]
    _ = E.yLeaf.1 :=
      (BlockCutIncidence.leaf_eq_inl_blockOfLeaf
        P.exteriorGraph_connected E.yLeaf).symm

end ExteriorBlockEndpoints

/--
Choose the two endpoint leaves by inverting the marked-leaf bijection.
-/
noncomputable def exteriorBlockEndpoints
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    P.ExteriorBlockEndpoints := by
  classical
  let hanchored :=
    P.anchoredBlockMeetsExceptions_of_allFeasibleBlocks hall
  let f :
      BlockCutIncidence.IncidenceLeaf P.exteriorGraph →
        {r : P.ExteriorVertex // r ∈ P.exteriorProtected} :=
    BlockCutIncidence.markedVertexOfLeaf
      P.exteriorGraph_connected
      P.exteriorProtected P.exteriorY
      P.exteriorY_mem_exteriorProtected hanchored
  have hinjective : Function.Injective f :=
    BlockCutIncidence.markedVertexOfLeaf_injective
      P.exteriorGraph_connected
      P.exteriorProtected P.exteriorY
      P.exteriorY_mem_exteriorProtected hanchored
  have hleafCard :
      (TreePath.leafVertices
        (blockCutIncidence P.exteriorGraph)).card = 2 :=
    P.exteriorBlockCutIncidence_leafVertices_card_eq_two
      M D hregion hall
  have hprotectedCard :
      P.exteriorProtected.card = 2 :=
    P.exteriorProtected_card_eq_two M D hregion hall
  have htypeCard :
      Fintype.card
          (BlockCutIncidence.IncidenceLeaf P.exteriorGraph) =
        Fintype.card
          {r : P.ExteriorVertex // r ∈ P.exteriorProtected} := by
    calc
      Fintype.card
          (BlockCutIncidence.IncidenceLeaf P.exteriorGraph) =
          (TreePath.leafVertices
            (blockCutIncidence P.exteriorGraph)).card := by
        rw [Fintype.card_subtype]
        rfl
      _ = 2 := hleafCard
      _ = P.exteriorProtected.card :=
        hprotectedCard.symm
      _ = Fintype.card
          {r : P.ExteriorVertex //
            r ∈ P.exteriorProtected} := by
        exact (Fintype.card_coe P.exteriorProtected).symm
  have hbijective : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hinjective, htypeCard⟩
  let hz :=
    P.exception_mem_otherRegion_of_allFeasibleBlocks
      M D hregion hall
  let hyz :=
    P.right_root_ne_exception_of_allFeasibleBlocks
      M D hregion hall
  let zMarked :
      {r : P.ExteriorVertex // r ∈ P.exteriorProtected} :=
    ⟨P.exteriorZ hz, P.exteriorZ_mem_exteriorProtected hz⟩
  let yMarked :
      {r : P.ExteriorVertex // r ∈ P.exteriorProtected} :=
    ⟨P.exteriorY, P.exteriorY_mem_exteriorProtected⟩
  let zLeaf :=
    Classical.choose (hbijective.2 zMarked)
  have hzLeaf :
      f zLeaf = zMarked :=
    Classical.choose_spec (hbijective.2 zMarked)
  let yLeaf :=
    Classical.choose (hbijective.2 yMarked)
  have hyLeaf :
      f yLeaf = yMarked :=
    Classical.choose_spec (hbijective.2 yMarked)
  have hleavesNe : zLeaf ≠ yLeaf := by
    intro hleaves
    have hmarked :
        zMarked = yMarked :=
      hzLeaf.symm.trans
        ((congrArg f hleaves).trans hyLeaf)
    apply hyz
    have hzy :
        P.exteriorZ hz = P.exteriorY :=
      congrArg Subtype.val hmarked
    exact (congrArg Subtype.val hzy).symm
  have hzValue :
      (f zLeaf).1 = P.exteriorZ hz :=
    congrArg Subtype.val hzLeaf
  have hyValue :
      (f yLeaf).1 = P.exteriorY :=
    congrArg Subtype.val hyLeaf
  refine {
    z_mem_otherRegion := hz
    y_ne_z := hyz
    zLeaf := zLeaf
    yLeaf := yLeaf
    zLeaf_ne_yLeaf := hleavesNe
    z_mem_block := ?_
    y_mem_block := ?_
    z_not_cut := ?_
    y_not_cut := ?_
  }
  · rw [← hzValue]
    exact
      BlockCutIncidence.markedVertexOfLeaf_mem_block
        P.exteriorGraph_connected
        P.exteriorProtected P.exteriorY
        P.exteriorY_mem_exteriorProtected hanchored zLeaf
  · rw [← hyValue]
    exact
      BlockCutIncidence.markedVertexOfLeaf_mem_block
        P.exteriorGraph_connected
        P.exteriorProtected P.exteriorY
        P.exteriorY_mem_exteriorProtected hanchored yLeaf
  · rw [← hzValue]
    exact
      BlockCutIncidence.markedVertexOfLeaf_not_cut
        P.exteriorGraph_connected
        P.exteriorProtected P.exteriorY
        P.exteriorY_mem_exteriorProtected hanchored zLeaf
  · rw [← hyValue]
    exact
      BlockCutIncidence.markedVertexOfLeaf_not_cut
        P.exteriorGraph_connected
        P.exteriorProtected P.exteriorY
        P.exteriorY_mem_exteriorProtected hanchored yLeaf

namespace ExteriorBlockEndpoints

/--
The unique incidence path from the `z`-leaf to the `y`-leaf contains every
block and cut node.
-/
theorem existsUnique_incidencePath_containing_every_node
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (E : P.ExteriorBlockEndpoints) :
    ∃! p :
        (blockCutIncidence P.exteriorGraph).Walk
          E.zLeaf.1 E.yLeaf.1,
      p.IsPath ∧
        ∀ n : BlockCutNode P.exteriorGraph,
          n ∈ p.support := by
  letI : Nontrivial (BlockCutNode P.exteriorGraph) :=
    P.exteriorBlockCutNode_nontrivial M D hregion hall
  have hLeafNodes :
      E.zLeaf.1 ≠ E.yLeaf.1 := by
    intro h
    exact E.zLeaf_ne_yLeaf (Subtype.ext h)
  exact
    BlockCutIncidence.existsUnique_leafPath_containing_every_node
      (P.exteriorBlockCutIncidence_isTree hregion)
      (P.exteriorBlockCutIncidence_degree_le_two
        M D hregion hall)
      hLeafNodes E.zLeaf.2 E.yLeaf.2

end ExteriorBlockEndpoints

end PreferredWorkingCoreData

end COY

end DeanK5
