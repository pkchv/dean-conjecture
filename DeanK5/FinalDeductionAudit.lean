import DeanK5.FinalDeduction
import DeanK5.AxiomCommands

/-!
# Focused audit of the final deduction

This module is the concise reviewer-facing verification ledger.  It imports
only the final proof spine, checks the exact transitive axiom set of each
major milestone, and confirms that the milestones occur in the final
theorem's kernel dependency closure. `AxiomAudit` separately scans every
declaration in every project module.
-/

assert_axioms DeanK5.COY.one_exception_rooted_paths_internal
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.GHLM.rooted_admissible_paths_internal
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.BGLP.three_connected_of_two_connected_minDegree_four
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.StandingSetup.four_connected
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.StandingSetup.no_triangle
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.StandingSetup.no_four_cycle
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.GHLM.minimum_theta_structure_internal
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.StandingSetup.girth_six_case_contradiction
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.divisible_cycle_of_two_connected_min_degree_five
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.RootedBlockSetup.contradiction
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.divisible_cycle_of_connected_min_degree_five
  propext
  Classical.choice
  Quot.sound

assert_axioms DeanK5.dean_conjecture_k5
  propext
  Classical.choice
  Quot.sound

/-!
The reachability ledger makes the architectural claims above enforceable:
the terminal and nonterminal COY branches and every displayed milestone must
occur in the final theorem's kernel dependency closure.
-/
assert_reachable_from DeanK5.dean_conjecture_k5
  DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_terminal_lastFeasible
  DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_nonterminal_lastFeasible
  DeanK5.COY.PreferredWorkingCoreData.ExteriorOrderedBlockChain.false_of_lastFeasible_analysis
  DeanK5.COY.MinimalCounterexample.impossible
  DeanK5.COY.one_exception_rooted_paths_internal
  DeanK5.GHLM.rooted_admissible_paths_internal
  DeanK5.BGLP.three_connected_of_two_connected_minDegree_four
  DeanK5.StandingSetup.four_connected
  DeanK5.StandingSetup.no_triangle
  DeanK5.StandingSetup.no_four_cycle
  DeanK5.GHLM.minimum_theta_structure_internal
  DeanK5.StandingSetup.girth_six_case_contradiction
  DeanK5.divisible_cycle_of_two_connected_min_degree_five
  DeanK5.RootedBlockSetup.contradiction
  DeanK5.divisible_cycle_of_connected_min_degree_five
