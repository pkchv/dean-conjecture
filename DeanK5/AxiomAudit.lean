import DeanK5
import Batteries.Tactic.Lint
import Mathlib.Util.AssertNoSorry

/-!
# Trust-boundary audit (paper Section 1.3)

Compile this module directly to display the trusted assumptions of the main
conditional deductions.
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
allowlist. Unlike `#print axioms`, this turns trust-boundary drift into a
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
  DeanK5.BGLP.two_connected_minimum_degree
  DeanK5.COY.one_exception_rooted_paths
  DeanK5.GHLM.rooted_admissible_paths

assert_module_prefix_axioms DeanK5
  propext
  Classical.choice
  Quot.sound
  DeanK5.BGLP.two_connected_minimum_degree
  DeanK5.COY.one_exception_rooted_paths
  DeanK5.GHLM.rooted_admissible_paths

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
#print axioms DeanK5.StandingSetup.no_triangle
#print axioms DeanK5.Theta.minimumOrder_isInduced
#print axioms DeanK5.Theta.minimumOrder_attachment_induces_oneSubdivisionK4
#print axioms DeanK5.GHLM.minimum_theta_structure_internal
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
