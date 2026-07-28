import DeanK5.COYExteriorZEndBlock
import DeanK5.Graph.CutVertices

/-!
# The removed type-3 vertex separates the modified exterior

In a modified COY working core, the removed vertex `t₀` is the only
neighbour of the second root inside the new exterior.  The former second
deletion component supplies another exterior vertex, so deleting `t₀`
disconnects the induced exterior graph.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace TypeThreeModificationChoice

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}
  {T : TypeThreeModificationTrigger (z := z) O}

/--
The copy of the removed vertex `t₀` is a cut vertex of the exterior induced
by a modified working core.

Indeed, the second root `y` has no other neighbour in that exterior, while
the ordinary vertex from the trigger component is a distinct surviving
vertex.
-/
theorem t₀_isCutVertex_in_otherRegion
    (K : TypeThreeModificationChoice T) :
    IsCutVertex
      (G.induce (↑K.rooted.otherRegion : Set V))
      (⟨T.t₀, K.t₀_mem_otherRegion⟩ :
        {v : V // v ∈ K.rooted.otherRegion}) := by
  let D : SimpleGraph {v : V // v ∈ K.rooted.otherRegion} :=
    G.induce (↑K.rooted.otherRegion : Set V)
  let tD : {v : V // v ∈ K.rooted.otherRegion} :=
    ⟨T.t₀, K.t₀_mem_otherRegion⟩
  let yD : {v : V // v ∈ K.rooted.otherRegion} :=
    ⟨y, K.rooted.other_root_mem_otherRegion⟩
  let dD : {v : V // v ∈ K.rooted.otherRegion} :=
    ⟨T.ordinary, K.ordinary_mem_otherRegion⟩
  have hyt : yD ≠ tD := by
    intro h
    exact T.other_root_adj_t₀.ne (congrArg Subtype.val h)
  have htOldCarrier :
      T.t₀ ∈ O.rooted.core.carrier := by
    rw [T.core_eq]
    exact
      (Core.typeThree T.core).T_subset_carrier
        (by simpa [Core.T] using T.t₀_mem)
  have hdt : dD ≠ tD := by
    intro h
    apply ordinary_not_mem_original_carrier (T := T)
    have hval : T.ordinary = T.t₀ :=
      congrArg Subtype.val h
    exact hval ▸ htOldCarrier
  have hyd : D.Reachable yD dD :=
    K.rooted.otherRegion_componentRegion.connected.preconnected yD dD
  refine ⟨yD, dD, hyt, hdt, hyd, ?_⟩
  let yDel : {v : {v : V // v ∈ K.rooted.otherRegion} // v ∉ ({tD} : Finset _)} :=
    ⟨yD, by simpa using hyt⟩
  let dDel : {v : {v : V // v ∈ K.rooted.otherRegion} // v ∉ ({tD} : Finset _)} :=
    ⟨dD, by simpa using hdt⟩
  change ¬(deleteVertices D {tD}).Reachable yDel dDel
  apply not_reachable_of_neighborSet_left_eq_empty
  · intro h
    apply TypeThreeModificationChoice.ordinary_ne_other_root (T := T)
    exact congrArg (fun v => v.1.1) h.symm
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hyv : D.Adj yD v.1 := hv
    have hvT :
        v.1.1 = T.t₀ :=
      (K.other_root_adj_iff_t₀_in_otherRegion v.1).1 hyv
    have hvt : v.1 ≠ tD := by
      simpa using v.2
    apply hvt
    apply Subtype.ext
    exact hvT

end TypeThreeModificationChoice

namespace SelectedWorkingCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}

/--
The extra vertex excluded by the working-core attachment bound is either the
second root itself or a cut vertex of the selected exterior.  Thus every
nonexceptional vertex of a feasible block automatically avoids it.
-/
theorem excludedVertex_eq_otherRoot_or_exteriorCut
    (W : SelectedWorkingCore (z := z) O) :
    W.excludedVertex = y ∨
      ∃ hmem : W.excludedVertex ∈ W.rooted.otherRegion,
        IsCutVertex
          (G.induce (↑W.rooted.otherRegion : Set V))
          (⟨W.excludedVertex, hmem⟩ :
            {v : V // v ∈ W.rooted.otherRegion}) := by
  cases W with
  | natural hnot =>
      exact Or.inl rfl
  | modified T K =>
      exact Or.inr
        ⟨K.t₀_mem_otherRegion,
          K.t₀_isCutVertex_in_otherRegion⟩

end SelectedWorkingCore

end COY

end DeanK5
