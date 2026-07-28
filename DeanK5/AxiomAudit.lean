import DeanK5
import Batteries.Tactic.Lint
import Mathlib.Util.AssertNoSorry

/-!
# Axiom audit (paper Section 1.3)

Compile this module directly to display the axioms used by the main theorem
and its supporting declarations.
-/

/-!
Keep public data definitions documented and definition names consistent with
Mathlib conventions.  The theorem-doc linter is intentionally excluded:
major paper-facing theorems are documented, while blanket comments on local
proof-engineering lemmas would add noise.
-/
#lint- only docBlame defsWithUnderscore in DeanK5

open Lean Elab Command

/--
Fail unless a declaration's complete axiom set is exactly the supplied
allowlist. Unlike `#print axioms`, this turns axiom-set drift into a
verification failure.
-/
elab "assert_axioms " decl:ident
    allowed:(ppSpace colGt ident)* : command => do
  let declName ←
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let actual ← Lean.collectAxioms declName
  let allowedNames ← allowed.mapM fun id =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let expected := NameSet.ofArray allowedNames
  let mut unexpected : Array Name := #[]
  let mut missing : Array Name := #[]
  for name in actual do
    unless expected.contains name do
      unexpected := unexpected.push name
  for name in expected do
    unless actual.contains name do
      missing := missing.push name
  unless unexpected.isEmpty && missing.isEmpty do
    throwError
      "axiom allowlist mismatch for {declName}\n\
       unexpected: {unexpected}\nmissing: {missing}"

/-!
`assert_no_sorry` below protects the final theorem's dependency closure.
The module-level companion also rejects `sorryAx` and any unlisted axiom in
project declarations that are built but not used by the final theorem.
Selecting declarations by their source module includes private declarations
and project helpers intentionally defined outside the `DeanK5` namespace.
-/
elab "assert_module_prefix_axioms " module:ident
    allowed:(ppSpace colGt ident)* : command => do
  let modulePrefix := module.getId
  let env ← getEnv
  let mut actual : NameSet := {}
  let mut sorryOffenders : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some moduleIdx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[moduleIdx.toNat]!
      if modulePrefix.isPrefixOf moduleName then
        let axioms ← Lean.collectAxioms name
        if axioms.contains ``sorryAx then
          sorryOffenders := sorryOffenders.push (privateToUserName name)
        for axiomName in axioms do
          actual := actual.insert axiomName
  unless sorryOffenders.isEmpty do
    throwError
      "declarations containing sorry in modules under {modulePrefix}: \
       {sorryOffenders.qsort Name.lt}"
  let allowedNames ← allowed.mapM fun id =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let expected := NameSet.ofArray allowedNames
  let mut unexpected : Array Name := #[]
  let mut missing : Array Name := #[]
  for name in actual do
    unless expected.contains name do
      unexpected := unexpected.push name
  for name in expected do
    unless actual.contains name do
      missing := missing.push name
  unless unexpected.isEmpty && missing.isEmpty do
    throwError
      "axiom allowlist mismatch for modules under {modulePrefix}\n\
       unexpected: {unexpected}\nmissing: {missing}"

assert_no_sorry DeanK5.dean_conjecture_k5

assert_axioms DeanK5.dean_conjecture_k5
  propext
  Classical.choice
  Quot.sound

assert_module_prefix_axioms DeanK5
  propext
  Classical.choice
  Quot.sound

#print axioms DeanK5.GHLM.rooted_admissible_paths_one
#print axioms DeanK5.GHLM.rooted_admissible_paths_one_of_two_connected
#print axioms DeanK5.COY.one_exception_rooted_paths_one
#print axioms DeanK5.COY.one_exception_rooted_paths_of_card_eq_four
#print axioms DeanK5.COY.one_exception_rooted_paths_internal
#print axioms DeanK5.COY.fact_one
#print axioms DeanK5.COY.fact_one_single_outer
#print axioms DeanK5.COY.PointedTypeOneCore.factTwoTypeOneBounded
#print axioms DeanK5.COY.PointedTypeTwoSCore.factTwoTypeTwoBounded
#print axioms DeanK5.COY.PointedTypeTwoTCore.factTwoTypeTwoTBounded
#print axioms DeanK5.COY.PointedTypeThreeSCore.factTwoTypeThreeBounded
#print axioms DeanK5.COY.PointedTypeThreeTCore.factTwoTypeThreeTBounded
#print axioms DeanK5.COY.exists_typeOne_or_typeThree_rootedCore
#print axioms DeanK5.COY.TypeOneCore.semiAdmissiblePathsTo
#print axioms DeanK5.COY.TypeTwoCore.admissiblePathsToS
#print axioms DeanK5.COY.TypeTwoCore.semiAdmissiblePathsToT
#print axioms DeanK5.COY.TypeThreeCore.admissiblePathsToSAfterDeleting
#print axioms DeanK5.COY.TypeThreeCore.semiAdmissiblePathsToTAfterDeleting
#print axioms DeanK5.COY.TypeThreeCore.UniformSCatalogue.equal_length
#print axioms DeanK5.COY.catalog_capacity_lt_of_no_paths
#print axioms DeanK5.COY.TypeThreeCore.rank_add_one_lt_of_no_paths_to_t
#print axioms DeanK5.ComponentRegion.boundaryPath_tail_subset
#print axioms DeanK5.COY.RootedCore.factThree
#print axioms DeanK5.COY.RootedCore.factThree_on_otherRegion
#print axioms DeanK5.COY.RootedInstance.five_le_card
#print axioms DeanK5.COY.RootedInstance.ofNoExtraException
#print axioms DeanK5.COY.MinimalCounterexample.roots_not_adj
#print axioms DeanK5.COY.MinimalCounterexample.underlying_connected
#print axioms DeanK5.COY.MinimalCounterexample.exists_root_separating_cut
#print axioms DeanK5.COY.CutSide.graph_sup_root_cut_two_connected
#print axioms DeanK5.COY.MinimalCounterexample.recursive_family_on_cut_side
#print axioms DeanK5.COY.MinimalCounterexample.underlying_two_connected
#print axioms DeanK5.COY.MinimalCounterexample.left_root_not_adj_exception
#print axioms DeanK5.COY.MinimalCounterexample.right_root_not_adj_exception
#print axioms DeanK5.COY.MinimalCounterexample.protected_vertices_pairwise_nonadjacent
#print axioms DeanK5.COY.MinimalCounterexample.exists_left_rootedCore
#print axioms DeanK5.COY.MinimalCounterexample.exists_right_rootedCore
#print axioms DeanK5.COY.MinimalCounterexample.rootedCore_factThree
#print axioms DeanK5.COY.exists_optimalRootedCore
#print axioms DeanK5.COY.MinimalCounterexample.exists_optimalRootedCore
#print axioms DeanK5.COY.MinimalCounterexample.optimalRootedCore_factThree
#print axioms DeanK5.COY.preferredOrientation_or_reverse
#print axioms DeanK5.COY.MinimalCounterexample.preferredOrientationData_or_swap
#print axioms DeanK5.COY.TypeOneCore.insertTerminal
#print axioms DeanK5.COY.TypeTwoCore.insertTerminal
#print axioms DeanK5.COY.TypeThreeCore.insertTerminal
#print axioms DeanK5.COY.TypeThreeCore.insertInitial
#print axioms DeanK5.COY.TypeThreeCore.eraseBalanced
#print axioms DeanK5.COY.TypeThreeCore.eraseTerminal
#print axioms DeanK5.COY.TypeThreeModificationChoice.exists_choice
#print axioms DeanK5.COY.TypeThreeModificationChoice.rooted
#print axioms DeanK5.COY.TypeThreeModificationChoice.two_le_otherRegion_sdiff_protected
#print axioms DeanK5.COY.SelectedWorkingCore.exists_selection
#print axioms DeanK5.COY.MinimalCounterexample.preferredWorkingCoreData_or_swap
#print axioms DeanK5.COY.OptimalRootedCore.coreNeighbor_ncard_le_of_typeOne
#print axioms DeanK5.COY.OptimalRootedCore.exists_T_neighbor_of_coreNeighbor_ncard_eq_typeOne
#print axioms DeanK5.COY.OptimalRootedCore.coreNeighbor_ncard_le_of_typeTwo
#print axioms DeanK5.COY.OptimalRootedCore.exists_T_neighbor_of_coreNeighbor_ncard_eq_typeTwo
#print axioms DeanK5.COY.OptimalRootedCore.coreNeighbor_ncard_le_of_typeThree
#print axioms DeanK5.COY.OptimalRootedCore.exists_T_neighbor_of_coreNeighbor_ncard_eq_typeThree
#print axioms DeanK5.COY.TypeThreeModificationChoice.coreNeighbor_ncard_le_of_modified
#print axioms DeanK5.COY.TypeThreeModificationChoice.exists_T_neighbor_of_coreNeighbor_ncard_eq_modified
#print axioms DeanK5.COY.SelectedWorkingCore.coreNeighbor_ncard_le
#print axioms DeanK5.COY.SelectedWorkingCore.exists_T_neighbor_of_coreNeighbor_ncard_eq
#print axioms DeanK5.COY.SelectedWorkingCore.eq_natural_of_otherRegion_eq_singleton
#print axioms DeanK5.COY.PreferredOrientationData.neighborSets_eq_T_of_natural_singleton
#print axioms DeanK5.COY.PreferredOrientationData.neighborSets_eq_S_of_natural_singleton
#print axioms DeanK5.COY.TypeOneSingletonRigidity.admissiblePaths
#print axioms DeanK5.COY.OptimalRootedCore.typeOne_singleton_rigidity
#print axioms DeanK5.COY.OptimalRootedCore.contradiction_of_natural_singleton_typeOne
#print axioms DeanK5.COY.SingletonTypeTwoDeletion.graph_two_connected
#print axioms DeanK5.COY.SingletonTypeTwoDeletion.contradiction
#print axioms DeanK5.COY.MinimalCounterexample.false_of_natural_singleton_typeTwo
#print axioms DeanK5.COY.PreferredOrientationData.attachment_to_S_of_natural_singleton
#print axioms DeanK5.COY.PreferredOrientationData.no_ordinary_other_component_of_natural_singleton_typeOne
#print axioms DeanK5.COY.SingletonTwinDeletion.finiteDegree_le_graph
#print axioms DeanK5.COY.SingletonTwinDeletion.sup_edge_two_connected
#print axioms DeanK5.COY.SingletonTwinDeletion.sup_edge_two_connected_of_five_le_card
#print axioms DeanK5.COY.PreferredOrientationData.exception_not_mem_typeThreeSComponent
#print axioms DeanK5.COY.PreferredOrientationData.exists_typeThreeOtherComponentWitness_of_natural_singleton
#print axioms DeanK5.COY.PreferredOrientationData.typeThree_singleton_cardinalities
#print axioms DeanK5.COY.SingletonTwinDeletion.contradiction
#print axioms DeanK5.COY.MinimalCounterexample.false_of_natural_singleton_typeThree
#print axioms DeanK5.ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
#print axioms DeanK5.ComponentPruning.rooted_two_connected
#print axioms DeanK5.COY.TypeThreeCore.carrierGraph_sup_root_side_two_connected
#print axioms DeanK5.COY.PreferredWorkingCoreData.hasTAttachment_of_typeThree_card_S_one
#print axioms DeanK5.COY.ZEndBlockCertificate.neighborSet_z_eq_singleton
#print axioms DeanK5.COY.ZEndBlockCertificate.neighborSet_bz_eq_pair
#print axioms DeanK5.COY.ZEndBlockCertificate.withoutZ_connected
#print axioms DeanK5.COY.ZEndBlockCertificate.pathToY_snd_eq_bPrime
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.bz_ne_excludedVertex
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.exists_S_attachment_of_no_T
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.no_S_attachment_of_no_T_of_rank_add_one_eq
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.rank_degree_equalities_and_exists_T_neighbor
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.rank_le_sub_two
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.claim_three_nine_rank_and_core_neighbor_count
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.no_T_neighbor_of_z_or_bPrime
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.three_le_exterior_degree_bPrime
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.not_isOrderThreePath
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorZEndBlock.bPrime_ne_y_of_no_feasibleBlock
#print axioms DeanK5.COY.PreferredWorkingCoreData.exists_feasible_exterior_block
#print axioms DeanK5.GraphBlock.isCutVertex_of_adj_outside
#print axioms DeanK5.GraphBlock.isCutVertex_of_mem_inter
#print axioms DeanK5.GraphBlock.exists_two_distinct_of_isCutVertex
#print axioms DeanK5.GraphBlock.exists_of_vertex
#print axioms DeanK5.BlockCutIncidence.reachable_blocks_of_walk
#print axioms DeanK5.BlockCutIncidence.connected
#print axioms DeanK5.GraphBlock.path_subset_of_meets_only_at_ends
#print axioms DeanK5.BlockCutIncidence.isAcyclic
#print axioms DeanK5.BlockCutIncidence.isTree
#print axioms DeanK5.BlockCutIncidence.two_le_degree_cut
#print axioms DeanK5.BlockCutIncidence.exists_marked_noncut_of_block_degree_eq_one
#print axioms DeanK5.BlockCutIncidence.leafVertices_card_le_marked
#print axioms DeanK5.BlockCutIncidence.incidence_degree_le_two
#print axioms DeanK5.TreePath.isHamiltonian_of_isPath_between_leaves
#print axioms DeanK5.BlockCutIncidence.existsUnique_leafPath_containing_every_node
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.ofTwoLeafBlocks
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.nonconsecutive_inter_eq_empty
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.intervalCarrier_connected
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.exists_prefix_path_to_cut
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.exists_cut_to_lastBlock_path
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.intervalCarrier_inter_nextBlock_eq_singleton
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.previousBlock_inter_intervalCarrier_eq_singleton
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.blocksBeforeCarrier_eq_intervalCarrier
#print axioms DeanK5.GraphBlock.neighbor_mem_carrier_of_not_cut
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.lastBlock_neighborSet_subset_lastCut
#print axioms DeanK5.BlockCutIncidence.OrderedBlockChain.penultimateCut_neighborSet_subset
#print axioms DeanK5.BlockCutIncidence.walk_getVert_alternates
#print axioms DeanK5.COY.SemiAdmissiblePathFamily.appendFixedToAdmissible
#print axioms DeanK5.COY.SemiAdmissiblePathFamily.prependFixedToAdmissible
#print axioms DeanK5.COY.TypeThreeCore.claimThreeSixteenPrefixFamilyOfTailOutside
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.claimThreeSixteenPrefixFamilyFromEarlierAttachment
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.pathInSelectedBlock_disjoint_suffix_tail
#print axioms DeanK5.GraphBlock.exists_anchor_path_to
#print axioms DeanK5.GraphBlock.exists_feasibleBlockAnchor
#print axioms DeanK5.COY.PreferredWorkingCoreData.exists_exteriorFeasibleBlockChoice
#print axioms DeanK5.IsNonseparableCarrier.map_embedding
#print axioms DeanK5.GraphBlock.image_nonseparable
#print axioms DeanK5.IsNonseparableCarrier.isTwoConnected_adjoinRoot
#print axioms DeanK5.COY.Core.three_le_card_carrier
#print axioms DeanK5.COY.TypeThreeModificationChoice.t₀_isCutVertex_in_otherRegion
#print axioms DeanK5.COY.SelectedWorkingCore.excludedVertex_eq_otherRoot_or_exteriorCut
#print axioms DeanK5.COY.BoundaryCompression.rootedGraph_twoConnected_of_nonseparable
#print axioms DeanK5.COY.BoundaryCompression.selectedNeighbors_card_le_finiteDegree
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.compressionRootedGraph_twoConnected
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.compressionComplexity_lt
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.finiteDegree_le_compression_add_rank
#print axioms DeanK5.COY.Core.UniformTCatalogue.equal_length
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exists_liftedTerminalToYData
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exists_compression_recursive_family
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.false_of_hasTerminalAttachment
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.terminalAttachments_eq_empty
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.SingletonInitialBoundary.false_of_singleton_initialBoundary
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.EmptyInitialBoundary.exists_offRegion_core_attachment
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.EmptyInitialBoundary.exists_connectorPathData
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.EmptyInitialBoundary.false_of_empty_initialBoundary
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.two_le_initialBoundary_card
#print axioms DeanK5.COY.MinimalCounterexample.selectedWorkingCore_otherRegion_ne_singleton
#print axioms DeanK5.COY.PreferredWorkingCoreData.otherRegion_ne_singleton
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.false_of_typeNumber_eq_one
#print axioms DeanK5.COY.PreferredWorkingCoreData.typeNumber_ne_one
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.initialAttachments_nonempty
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.initialCompressionRootedGraph_twoConnected
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.initialCompressionComplexity_lt
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.not_root_adj_and_typeTwo_S_neighbor
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exterior_degree_le_initialCompression_degree
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exterior_degree_add_one_le_initialCompression_degree_of_S_neighbor
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.finiteDegree_le_initialCompression_add_one_of_typeTwo
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.coreNeighbor_ncard_le_rank
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.finiteDegree_le_initialCompression_add_rankLoss
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exists_initialCompression_recursive_family_of_rankLoss
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exists_typeTwo_initialCompression_recursive_family
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exists_liftedInitialToYData
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.false_of_typeTwo
#print axioms DeanK5.COY.PreferredWorkingCoreData.typeNumber_ne_two
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.exists_data
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.side_nonempty
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.rank_pos
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.rank_eq_one
#print axioms DeanK5.GraphBlock.exists_feasibleBlockAnchor_avoiding
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exists_reanchored_avoiding
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.LiftedInitialToYData.avoids_of_not_mem_block_and_connector
#print axioms DeanK5.COY.TypeThreeCore.UniformAugmentedTwoCatalogue.equal_length
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.claim_three_thirteen
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.coreNeighbor_ncard_le_one
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.coreAttachments_eq_initialBoundary
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exists_side_eq_singleton_and_coreAttachments_eq_pair
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.chosenRootAttachmentData
#print axioms DeanK5.COY.TypeThreeCore.carrierGraph_two_connected
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeExteriorDeletion.rootedGraph_two_connected
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeExteriorDeletion.finiteDegree_graph_eq
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeExteriorDeletion.false_of_data
#print axioms DeanK5.COY.PreferredWorkingCoreData.three_le_q_of_typeThree_singleton_side
#print axioms DeanK5.COY.PreferredWorkingCoreData.hasTAttachmentAwayFromY_of_exception_mem
#print axioms DeanK5.COY.PreferredWorkingCoreData.claim_three_fourteen
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.exists_claimThreeFifteen_boundary_data
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.singleBPrime_rooted_twoConnected
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.singleBPrime_recursiveInstance
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.meetsProtectedInterior_of_sideBlockNeighbors_eq_singleton
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.doubleBPrime_recursiveInstance
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.meetsProtectedInterior_of_two_le_sideBlockNeighbors
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.false_of_claimThreeFifteen_recursiveInstance
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.not_spansExterior_of_meetsProtectedInterior
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFeasibleBlockChoice.claim_three_fifteen
#print axioms DeanK5.COY.PreferredWorkingCoreData.allFeasibleBlocksMeetProtectedInterior
#print axioms DeanK5.COY.PreferredWorkingCoreData.anchoredBlockMeetsExceptions_of_allFeasibleBlocks
#print axioms DeanK5.COY.PreferredWorkingCoreData.exteriorBlockCutIncidence_leafVertices_card_eq_two
#print axioms DeanK5.COY.PreferredWorkingCoreData.exteriorBlockCutIncidence_degree_le_two
#print axioms DeanK5.COY.PreferredWorkingCoreData.exteriorProtected_card_eq_two
#print axioms DeanK5.COY.PreferredWorkingCoreData.exception_mem_otherRegion_of_allFeasibleBlocks
#print axioms DeanK5.COY.PreferredWorkingCoreData.exteriorBlockEndpoints
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorBlockEndpoints.existsUnique_incidencePath_containing_every_node
#print axioms DeanK5.COY.PreferredWorkingCoreData.exteriorOrderedBlockChain
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.nonconsecutive_inter_eq_empty
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.not_hasExteriorAttachmentAwayFrom_of_selected_last
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.not_hasExteriorAttachmentAwayFrom_of_selected_penultimate
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.finalCut_not_mem_selected_of_add_one_lt
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorCandidateChain.feasible_iff_three_le_card
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorCandidateChain.later_block_card_eq_two
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.lastFeasibleAnchor
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.terminalFeasibleAnchor
#print axioms DeanK5.COY.PreferredWorkingCoreData.ClaimThreeSixteenBlockData.recursiveInstance
#print axioms DeanK5.COY.PreferredWorkingCoreData.ClaimThreeSixteenBlockData.recursiveStage
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorLastFeasibleAnchor.claimThreeSixteenBlockData
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorTerminalFeasibleAnchor.claimThreeSixteenTerminalBlockData
#print axioms DeanK5.COY.ClaimThreeSixteenAssembly.false_of_assembly
#print axioms DeanK5.COY.ClaimThreeSixteenRecursiveStage.false_of_recursiveStage
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.claimThreeSixteenAssemblyFromEarlierAttachment
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_terminal_attachment_before_lastFeasible
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.claimThreeSixteenTerminalAssemblyFromEarlierAttachment
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_terminal_attachment_before_terminalLastFeasible
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.claim_three_sixteen_blockwise
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.claim_three_sixteen_blocksBeforeCarrier
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.root_degree_sandwich
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.otherRoot_coreNeighbors_eq_terminal
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.root_degree_sandwich_of_core_envelope
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.chosenRoot_neighborSet_eq_insert_terminal
#print axioms DeanK5.COY.PreferredWorkingCoreData.TypeThreeStage.terminal_not_adj_last_of_otherRoot_neighborSet
#print axioms DeanK5.COY.ExteriorFinalDegreeCertificate.false_of_typeThree_singleton_side
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.ambient_neighbor_eq_terminalCut_of_not_mem_core
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.root_degree_sandwich_of_lastFeasible_before
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.terminalCut_neighborSet_subset_three
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_lastFeasible_before_preterminal
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorLastFeasibleAnchor.finalRootData
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorFinalRootData.terminalCut_not_adj_root_of_ne_attachment
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_nonterminal_lastFeasible
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_terminal_lastFeasible
#print axioms DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_lastFeasible_analysis
#print axioms DeanK5.COY.PreferredWorkingCoreData.impossible
#print axioms DeanK5.COY.MinimalCounterexample.impossible
#print axioms DeanK5.COY.all_solvable_of_minimal_counterexample_false
#print axioms DeanK5.GHLM.rooted_admissible_paths_internal
#print axioms DeanK5.isTwoConnected_adjoinRoot
#print axioms DeanK5.BGLP.three_connected_of_two_connected_minDegree_four
#print axioms DeanK5.root_deletion_is_three_connected
#print axioms DeanK5.one_component_two_separator_roots
#print axioms DeanK5.StandingSetup.separator_side_admissible_paths
#print axioms DeanK5.StandingSetup.three_separator_structure
#print axioms DeanK5.StandingSetup.four_connected
#print axioms DeanK5.root_lifting
#print axioms DeanK5.disjoint_three_by_three_forces_cycle_divisible_by_five
#print axioms DeanK5.StandingSetup.no_k4minus
#print axioms DeanK5.isThreeConnected_contractPair
#print axioms DeanK5.StandingSetup.triangle_contraction_admissible_paths
#print axioms DeanK5.StandingSetup.triangle_contraction_admissible_paths_no_deficient
#print axioms DeanK5.StandingSetup.no_triangle
#print axioms DeanK5.Theta.minimumOrder_isInduced
#print axioms DeanK5.Theta.minimumOrder_attachment_induces_oneSubdivisionK4
#print axioms DeanK5.GHLM.minimum_theta_structure_internal
#print axioms DeanK5.no_divisible_cycle_adjoinRoot_empty
#print axioms DeanK5.standingSetupOfTwoConnected
#print axioms DeanK5.divisible_cycle_of_two_connected_min_degree_five_internal
#print axioms DeanK5.isTwoConnected_of_connected_delete_one
#print axioms DeanK5.boundaryAuxGraph_add_roots_two_connected
#print axioms DeanK5.finiteDegree_le_induced_region_add_boundary
#print axioms DeanK5.boundaryAux_degree_bound_missing_endpoint
#print axioms DeanK5.boundaryAuxConnectivityDataOfDeletedConnected
#print axioms DeanK5.ComponentRegion.exists_independent_boundary_edges
#print axioms DeanK5.ComponentRegion.connectivity_le_separator_card
#print axioms DeanK5.boundary_root_lifting_artificial_detailed
#print axioms DeanK5.BipartiteCore.complete_or_missing
#print axioms DeanK5.BipartiteCore.MissingEdgeData.swap
#print axioms DeanK5.BipartiteCore.MissingEdgeData.exists_smaller_complete_core_of_left_card_two
#print axioms DeanK5.BipartiteCore.MissingEdgeData.exists_smaller_bounded_core_of_rank_two
#print axioms DeanK5.BipartiteCore.rank_two_complete_of_minimal
#print axioms DeanK5.BipartiteCore.exists_minimal_bounded_core
#print axioms DeanK5.BGLP.complete_bipartite_core_opposite_part_paths
#print axioms DeanK5.BGLP.complete_bipartite_core_same_part_paths
#print axioms DeanK5.six_path_grid_forces_divisible_cycle
#print axioms DeanK5.StandingSetup.opposite_core_sequence_forces_divisible_cycle
#print axioms DeanK5.StandingSetup.same_core_sequence_forces_divisible_cycle
#print axioms DeanK5.StandingSetup.same_larger_core_sequence_forces_divisible_cycle
#print axioms DeanK5.StandingSetup.opposite_boundary_core_case
#print axioms DeanK5.StandingSetup.same_boundary_core_case
#print axioms DeanK5.StandingSetup.same_larger_boundary_core_case
#print axioms DeanK5.StandingSetup.BoundaryCoreModel.opposite_case_contradiction
#print axioms DeanK5.StandingSetup.BoundaryCoreModel.same_case_contradiction
#print axioms DeanK5.StandingSetup.BoundaryCoreModel.same_larger_case_contradiction
#print axioms DeanK5.StandingSetup.complete_core_component_both_parts_contradiction
#print axioms DeanK5.StandingSetup.missing_edge_core_component_both_parts_contradiction
#print axioms DeanK5.StandingSetup.same_part_component_contradiction
#print axioms DeanK5.StandingSetup.rank_two_same_part_component_contradiction
#print axioms DeanK5.StandingSetup.same_part_component_contradiction_of_connectivity
#print axioms DeanK5.StandingSetup.complete_core_component_contradiction
#print axioms DeanK5.StandingSetup.missing_core_component_contradiction
#print axioms DeanK5.StandingSetup.core_rank_five_contradiction
#print axioms DeanK5.StandingSetup.core_carrier_ne_univ
#print axioms DeanK5.StandingSetup.minimal_bounded_core_contradiction
#print axioms DeanK5.StandingSetup.lifted_core_contradiction
#print axioms DeanK5.StandingSetup.complete_pair_adj_iff
#print axioms DeanK5.StandingSetup.almost_pair_adj_iff
#print axioms DeanK5.BipartiteCore.ofMissingRaw
#print axioms DeanK5.four_cycle_has_complete_pair_size_two
#print axioms DeanK5.exists_maximal_complete_pair_size
#print axioms DeanK5.exists_maximal_complete_right_side
#print axioms DeanK5.StandingSetup.balanced_complete_pair_contradiction_of_no_unbalanced_pair
#print axioms DeanK5.StandingSetup.unbalanced_complete_pair_contradiction_of_side_bounds
#print axioms DeanK5.StandingSetup.unbalanced_complete_pair_contradiction_of_maximal_large_side
#print axioms DeanK5.StandingSetup.large_side_degree_bound_of_no_almost_balanced
#print axioms DeanK5.StandingSetup.almost_balanced_pair_contradiction_of_no_complete
#print axioms DeanK5.StandingSetup.unbalanced_complete_pair_contradiction_of_maximal_and_no_almost
#print axioms DeanK5.StandingSetup.no_four_cycle
#print axioms DeanK5.theta_three_distinct_residue_paths_of_girth_six
#print axioms DeanK5.GHLM.outside_vertex_on_subdivided_K4
#print axioms DeanK5.GHLM.multiNeighborSet_subsingleton_of_induces
#print axioms DeanK5.ClassicalGraphTheory.induced_theta_core_properties
#print axioms DeanK5.ClassicalGraphTheory.exists_theta_of_two_connected
#print axioms DeanK5.ClassicalGraphTheory.two_end_lobes_with_root_attachments
#print axioms DeanK5.ClassicalGraphTheory.two_end_lobes_of_non_two_component
#print axioms DeanK5.final_residue_argument_of_attachments
#print axioms DeanK5.StandingSetup.outside_component_two_connected
#print axioms DeanK5.StandingSetup.two_component_contradiction_of_heavy
#print axioms DeanK5.StandingSetup.two_component_contradiction_of_light
#print axioms DeanK5.StandingSetup.outside_envelope_connected
#print axioms DeanK5.StandingSetup.outside_envelope_two_connected
#print axioms DeanK5.StandingSetup.final_residue_contradiction_of_envelope
#print axioms DeanK5.StandingSetup.exists_thetaEnvelope
#print axioms DeanK5.StandingSetup.girth_six_case_contradiction
#print axioms DeanK5.RootedBlockSetup.root_degree_upper
#print axioms DeanK5.RootedBlockSetup.root_deletion_two_connected
#print axioms DeanK5.RootedBlockSetup.toStandingSetup
#print axioms DeanK5.RootedBlockSetup.contradiction
#print axioms DeanK5.EndLobe.toRootedBlockSetup
#print axioms DeanK5.divisible_cycle_of_two_connected_min_degree_five
#print axioms DeanK5.dean_conjecture_k5
