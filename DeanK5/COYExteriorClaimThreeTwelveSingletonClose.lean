import DeanK5.COYCoreInitialPath
import DeanK5.COYExteriorClaimThreeTwelveSingletonRecursive
import DeanK5.COYPathOperations

/-!
# Closing the singleton-boundary branch of COY Claim 3.12

The recursive family in the graph induced by the selected block and its
unique core attachment is joined first to a fixed path in the core and then
to the fixed block-to-`y` connector.  Both joins use explicit support
separation, so the resulting objects are simple paths rather than walks.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

namespace SingletonInitialBoundary

variable {C : P.ExteriorFeasibleBlockChoice}

/--
A singleton initial boundary yields a forbidden ambient admissible family
from `x` to `y`.
-/
theorem false_of_singleton_initialBoundary
    (M : MinimalCounterexample q G x y z)
    (D : SingletonInitialBoundary C) :
    False := by
  classical
  obtain ⟨recursiveFamily⟩ :=
    D.exists_recursive_family M
  let mapped :
      AdmissiblePathFamily G D.vertex C.b q :=
    recursiveFamily.mapEmbedding D.recursiveEmbedding
  let corePath :=
    P.working.rooted.core.initialPathData
      D.vertex D.vertex_mem_root_insert_S
  have hcoreDisjoint :
      ∀ i, corePath.path.walk.support.Disjoint
        (mapped.path i).walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvCorePath hvMappedTail
    have hvCore :
        v ∈ P.working.rooted.core.carrier :=
      corePath.support_subset hvCorePath
    have hvMapped :
        v ∈ (mapped.path i).walk.support :=
      List.mem_of_mem_tail hvMappedTail
    have hvRange :
        v ∈ Set.range D.recursiveEmbedding := by
      change
        v ∈
          ((recursiveFamily.path i).mapInjectiveHom
            D.recursiveEmbedding.toHom
            D.recursiveEmbedding.injective).walk.support at hvMapped
      exact
        SimplePath.mem_range_of_mem_mapInjectiveHom_support
          (P := recursiveFamily.path i)
          (f := D.recursiveEmbedding.toHom)
          (hinj := D.recursiveEmbedding.injective)
          hvMapped
    obtain ⟨w, hw⟩ := hvRange
    cases w with
    | none =>
        have hvVertex : v = D.vertex :=
          hw.symm.trans D.recursiveEmbedding_none
        exact
          (mapped.path i).start_not_mem_tail
            (by simpa [hvVertex] using hvMappedTail)
    | some d =>
        have hdVal : d.1 = v :=
          (D.recursiveEmbedding_some d).symm.trans hw
        have hvBlock : v ∈ C.ambientCarrier := by
          exact hdVal ▸ d.2
        exact
          Finset.disjoint_left.mp
            C.ambientCarrier_disjoint_core
            hvBlock hvCore
  let prep :
      AdmissiblePathFamily G x C.b q :=
    mapped.prependFixed corePath.path hcoreDisjoint
  have hconnectorDisjoint :
      ∀ i, (prep.path i).walk.support.Disjoint
        C.pathToY.walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvPrep hvConnectorTail
    have hvConnector :
        v ∈ C.pathToY.walk.support :=
      List.mem_of_mem_tail hvConnectorTail
    have hvParts :
        v ∈ corePath.path.walk.support ∨
          v ∈ (mapped.path i).walk.support := by
      change
        v ∈
          ((corePath.path.appendDisjoint
            (mapped.path i)
            (hcoreDisjoint i)).walk.support) at hvPrep
      rw [SimplePath.appendDisjoint,
        SimpleGraph.Walk.support_append] at hvPrep
      rcases List.mem_append.mp hvPrep with
        hvCore | hvMappedTail
      · exact Or.inl hvCore
      · exact Or.inr
          (List.mem_of_mem_tail hvMappedTail)
    rcases hvParts with hvCorePath | hvMapped
    · exact
        P.working.rooted.otherRegion_componentRegion.not_mem_separator
          (C.pathToY_support_mem_otherRegion hvConnector)
          (corePath.support_subset hvCorePath)
    · have hvRange :
          v ∈ Set.range D.recursiveEmbedding := by
        change
          v ∈
            ((recursiveFamily.path i).mapInjectiveHom
              D.recursiveEmbedding.toHom
              D.recursiveEmbedding.injective).walk.support at hvMapped
        exact
          SimplePath.mem_range_of_mem_mapInjectiveHom_support
            (P := recursiveFamily.path i)
            (f := D.recursiveEmbedding.toHom)
            (hinj := D.recursiveEmbedding.injective)
            hvMapped
      obtain ⟨w, hw⟩ := hvRange
      cases w with
      | none =>
          have hvVertex : v = D.vertex :=
            hw.symm.trans D.recursiveEmbedding_none
          exact
            P.working.rooted.otherRegion_componentRegion.not_mem_separator
              (C.pathToY_support_mem_otherRegion hvConnector)
              (hvVertex ▸ D.vertex_mem_core)
      | some d =>
          have hdVal : d.1 = v :=
            (D.recursiveEmbedding_some d).symm.trans hw
          have hvBlock : v ∈ C.ambientCarrier := by
            exact hdVal ▸ d.2
          have hvb : v = C.b :=
            C.pathToY_meets_block_only_at_b
              hvConnector
              (by
                rw [C.mem_ambientCarrier] at hvBlock
                obtain ⟨w, hwBlock, hwVal⟩ := hvBlock
                exact ⟨w, hwBlock, hwVal⟩)
          exact
            C.pathToY.start_not_mem_tail
              (by simpa [hvb] using hvConnectorTail)
  exact
    M.no_paths
      ⟨prep.appendFixed C.pathToY
        hconnectorDisjoint⟩

end SingletonInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
