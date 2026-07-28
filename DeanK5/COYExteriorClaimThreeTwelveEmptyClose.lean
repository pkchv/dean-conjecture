import DeanK5.COYExteriorClaimThreeTwelveEmptyFamily
import DeanK5.COYExteriorClaimThreeTwelveEmptyPath
import DeanK5.COYPathOperations

/-!
# Closing the empty-boundary branch of COY Claim 3.12

The recursive `zPrime`--`b` family is joined to the fixed connector from
the original root and then to the fixed path from the block anchor to `y`.
The support theorems proved for those pieces certify both concatenations
as simple paths.
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

namespace EmptyInitialBoundary

variable {C : P.ExteriorFeasibleBlockChoice}

/--
An empty initial boundary yields a forbidden ambient admissible family
from `x` to `y`.
-/
theorem false_of_empty_initialBoundary
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    False := by
  classical
  obtain ⟨recursiveFamily⟩ :=
    D.exists_recursive_family M
  let mapped :
      AdmissiblePathFamily G C.zPrime C.b q :=
    recursiveFamily.mapEmbedding D.recursiveEmbedding
  obtain ⟨connector⟩ :=
    D.exists_connectorPathData M
  have hconnectorDisjoint :
      ∀ i, connector.path.walk.support.Disjoint
        (mapped.path i).walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvConnector hvMappedTail
    have hvMapped :
        v ∈
          ((recursiveFamily.path i).mapEmbedding
            D.recursiveEmbedding).walk.support := by
      exact List.mem_of_mem_tail hvMappedTail
    have hvBlock :
        v ∈ C.ambientCarrier :=
      D.mappedPath_support_mem_ambientCarrier
        recursiveFamily hvMapped
    have hvz :
        v = C.zPrime :=
      connector.meets_ambientCarrier_only_at_zPrime
        hvConnector hvBlock
    exact
      (mapped.path i).start_not_mem_tail
        (by simpa [hvz] using hvMappedTail)
  let prep :
      AdmissiblePathFamily G x C.b q :=
    mapped.prependFixed connector.path
      hconnectorDisjoint
  have hpathToYDisjoint :
      ∀ i, (prep.path i).walk.support.Disjoint
        C.pathToY.walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvPrep hvPathToYTail
    have hvParts :
        v ∈ connector.path.walk.support ∨
          v ∈ (mapped.path i).walk.support.tail := by
      change
        v ∈
          ((connector.path.appendDisjoint
            (mapped.path i)
            (hconnectorDisjoint i)).walk.support) at hvPrep
      rw [SimplePath.appendDisjoint,
        SimpleGraph.Walk.support_append] at hvPrep
      exact List.mem_append.mp hvPrep
    rcases hvParts with hvConnector | hvMappedTail
    · exact
        List.disjoint_left.mp
          connector.disjoint_pathToY_tail
          hvConnector hvPathToYTail
    · have hvMapped :
          v ∈
            ((recursiveFamily.path i).mapEmbedding
              D.recursiveEmbedding).walk.support :=
        List.mem_of_mem_tail hvMappedTail
      exact
        List.disjoint_left.mp
          (D.mappedPath_disjoint_pathToY_tail
            recursiveFamily i)
          hvMapped hvPathToYTail
  exact
    M.no_paths
      ⟨prep.appendFixed C.pathToY
        hpathToYDisjoint⟩

end EmptyInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
