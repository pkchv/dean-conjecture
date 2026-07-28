import DeanK5.COYExteriorClaimThreeTwelveTerminal
import DeanK5.Graph.AvoidingBlockAnchor

/-!
# Re-anchoring the exterior block away from one vertex

The temporary Type I and Type II configurations in COY Claim 3.13 use an
exterior vertex inside the core-side path catalogue.  The block-to-root
connector must therefore avoid that vertex.  A terminal attachment first
shows that the vertex is outside the selected feasible block; because it is
not a cut vertex, the generic avoiding-anchor construction then supplies a
new valid anchor and connector.
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

/--
An exterior non-cut vertex with a working-core `T`-neighbor lies outside
the selected feasible block.
-/
theorem not_mem_ambientCarrier_of_T_neighbor
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    {v t : V}
    (hvRegion : v ∈ P.working.rooted.otherRegion)
    (hvy : v ≠ y) (hvz : v ≠ z)
    (hvNotCut :
      ¬IsCutVertex P.exteriorGraph
        (⟨v, hvRegion⟩ : P.ExteriorVertex))
    (ht : t ∈ P.working.rooted.core.T)
    (hvt : G.Adj v t) :
    v ∉ C.ambientCarrier := by
  classical
  let v' : P.ExteriorVertex := ⟨v, hvRegion⟩
  have hvNotProtected :
      v' ∉ P.exteriorProtected := by
    rw [P.mem_exteriorProtected]
    push Not
    exact ⟨hvy, hvz⟩
  have hvNotSpecial :
      v' ∉ cutVertices P.exteriorGraph ∪
        P.exteriorProtected := by
    intro hvSpecial
    rcases Finset.mem_union.mp hvSpecial with
      hvCut | hvProtected
    · exact hvNotCut
        ((mem_cutVertices_iff _ _).1 hvCut)
    · exact hvNotProtected hvProtected
  intro hvCarrier
  have hvBlock :
      v' ∈ C.block.carrier := by
    rw [C.mem_ambientCarrier] at hvCarrier
    obtain ⟨w, hwBlock, hwv⟩ := hvCarrier
    have hwEq : w = v' := by
      apply Subtype.ext
      exact hwv
    simpa [hwEq] using hwBlock
  have hvb : v ≠ C.b := by
    intro hvb
    apply hvNotSpecial
    have hvEq : v' = C.anchor.b := by
      apply Subtype.ext
      exact hvb
    exact hvEq ▸ C.anchor.b_special
  have hvzPrime : v ≠ C.zPrime := by
    intro hvzPrime
    apply hvNotSpecial
    have hvEq : v' = C.anchor.zPrime := by
      apply Subtype.ext
      exact hvzPrime
    exact hvEq ▸ C.anchor.zPrime_special
  have hvInterior :
      v ∈ C.compressionInterior := by
    simp [compressionInterior, hvCarrier, hvb]
  have htAttachment :
      t ∈ C.terminalAttachments := by
    change
      t ∈ P.working.rooted.core.T.filter
        (fun t =>
          ∃ d ∈ C.compressionInterior, G.Adj t d)
    exact Finset.mem_filter.mpr
      ⟨ht, ⟨v, hvInterior, hvt.symm⟩⟩
  rw [C.terminalAttachments_eq_empty M] at htAttachment
  simp at htAttachment

/--
Re-anchor the same feasible block so that its connector to `y` avoids the
specified exterior non-cut vertex.
-/
theorem exists_reanchored_avoiding
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    {v t : V}
    (hvRegion : v ∈ P.working.rooted.otherRegion)
    (hvy : v ≠ y) (hvz : v ≠ z)
    (hvNotCut :
      ¬IsCutVertex P.exteriorGraph
        (⟨v, hvRegion⟩ : P.ExteriorVertex))
    (ht : t ∈ P.working.rooted.core.T)
    (hvt : G.Adj v t) :
    ∃ C' : P.ExteriorFeasibleBlockChoice,
      v ∉ C'.pathToY.walk.support := by
  classical
  let v' : P.ExteriorVertex := ⟨v, hvRegion⟩
  have hvAmbient :
      v ∉ C.ambientCarrier :=
    C.not_mem_ambientCarrier_of_T_neighbor
      M hvRegion hvy hvz hvNotCut ht hvt
  have hvBlock :
      v' ∉ C.block.carrier := by
    intro hvB
    apply hvAmbient
    rw [C.mem_ambientCarrier]
    exact ⟨v', hvB, rfl⟩
  have hvTarget :
      v' ≠ P.exteriorY := by
    intro h
    exact hvy (congrArg Subtype.val h)
  obtain ⟨A, havoidA⟩ :=
    C.block.exists_feasibleBlockAnchor_avoiding
      P.exteriorGraph_connected
      P.exteriorProtected P.exteriorY v'
      P.exteriorY_mem_exteriorProtected C.feasible
      hvBlock hvTarget hvNotCut
  let C' : P.ExteriorFeasibleBlockChoice := {
    block := C.block
    feasible := C.feasible
    anchor := A
  }
  refine ⟨C', ?_⟩
  intro hvPath
  change
    v ∈
      (A.pathToTarget.walk.map
        P.exteriorEmbedding.toHom).support at hvPath
  rw [SimpleGraph.Walk.support_map] at hvPath
  obtain ⟨w, hwSupport, hwv⟩ :=
    List.mem_map.mp hvPath
  have hwEq : w = v' := by
    apply Subtype.ext
    exact hwv
  exact havoidA (hwEq ▸ hwSupport)

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
