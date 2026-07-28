import DeanK5.COYExteriorClaimThreeTwelveEmptyRecursive

/-!
# Support of the empty-boundary recursive family

The recursive graph in the empty-boundary branch is the graph induced by
the selected block.  Consequently its mapped paths remain in that block
and are disjoint from the tail of the fixed block-to-`y` connector.
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

/-- Every vertex of a recursively mapped path belongs to the selected block. -/
theorem mappedPath_support_mem_ambientCarrier
    (D : EmptyInitialBoundary C)
    (F : AdmissiblePathFamily D.recursiveGraph
      D.recursiveLeftRoot D.recursiveBlockRoot q)
    {i : Fin q} {v : V}
    (hv :
      v ∈
        ((F.path i).mapEmbedding
          D.recursiveEmbedding).walk.support) :
    v ∈ C.ambientCarrier := by
  have hvRange :
      v ∈ Set.range D.recursiveEmbedding := by
    change
      v ∈
        ((F.path i).mapInjectiveHom
          D.recursiveEmbedding.toHom
          D.recursiveEmbedding.injective).walk.support at hv
    exact
      SimplePath.mem_range_of_mem_mapInjectiveHom_support
        (P := F.path i)
        (f := D.recursiveEmbedding.toHom)
        (hinj := D.recursiveEmbedding.injective)
        hv
  obtain ⟨w, hw⟩ := hvRange
  have hwVal : w.1 = v := by
    exact hw
  exact hwVal ▸ w.2

/--
Every recursively mapped path is disjoint from the noninitial part of the
fixed block-to-`y` connector.
-/
theorem mappedPath_disjoint_pathToY_tail
    (D : EmptyInitialBoundary C)
    (F : AdmissiblePathFamily D.recursiveGraph
      D.recursiveLeftRoot D.recursiveBlockRoot q)
    (i : Fin q) :
    ((F.path i).mapEmbedding
        D.recursiveEmbedding).walk.support.Disjoint
      C.pathToY.walk.support.tail := by
  apply List.disjoint_left.mpr
  intro v hvMapped hvConnectorTail
  have hvBlock :
      v ∈ C.ambientCarrier :=
    D.mappedPath_support_mem_ambientCarrier
      F hvMapped
  have hvConnector :
      v ∈ C.pathToY.walk.support :=
    List.mem_of_mem_tail hvConnectorTail
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

end EmptyInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
