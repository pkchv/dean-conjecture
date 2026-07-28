import DeanK5.COYComponentConnector
import DeanK5.COYCoreInitialPath
import DeanK5.COYExteriorClaimThreeTwelveEmptyConnector

/-!
# The fixed path in the empty-boundary branch of COY Claim 3.12

The off component at `zPrime` has an edge to the working core.  A path
inside that component, the attachment edge, and a path inside the core
therefore form a fixed ambient path from `x` to `zPrime`.  This file also
records the two support-separation statements used in the recursive
concatenation: the fixed path meets the selected block only at `zPrime`,
and it is disjoint from the tail of the fixed block-to-`y` path.
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

omit [Fintype V] in
/--
If a walk starts in a component region and avoids its separator, then its
whole support remains in that component region.
-/
private theorem walk_support_subset_componentRegion
    {S Q : Finset V}
    (hQ : ComponentRegion G S Q)
    {a t : V} (W : G.Walk a t)
    (ha : a ∈ Q)
    (havoid : ∀ v ∈ W.support, v ∉ S) :
    ∀ v ∈ W.support, v ∈ Q := by
  let rec go {a t : V}
      (W : G.Walk a t)
      (ha : a ∈ Q)
      (havoid : ∀ v ∈ W.support, v ∉ S) :
      ∀ v ∈ W.support, v ∈ Q := by
    cases W with
    | nil =>
        intro v hv
        have hvStart : v = a := by
          simpa using hv
        exact hvStart ▸ ha
    | @cons a b t hab W =>
        have hbNotS : b ∉ S := by
          intro hbS
          exact havoid b (by simp) hbS
        have hbQ : b ∈ Q :=
          hQ.closed ha hab hbNotS
        have htailAvoid :
            ∀ v ∈ W.support, v ∉ S := by
          intro v hv
          exact havoid v
            (W.support_subset_support_cons hab hv)
        intro v hv
        have hvClass : v = a ∨ v ∈ W.support := by
          simpa using hv
        rcases hvClass with rfl | hvTail
        · exact ha
        · exact go W hbQ htailAvoid v hvTail
  exact go W ha havoid

/--
Every vertex of the anchor-to-`y` path avoids the second block vertex
`zPrime`.
-/
theorem zPrime_not_mem_pathToY_support
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    C.zPrime ∉ C.pathToY.walk.support := by
  intro hz
  have hzBlock :
      ∃ w ∈ C.block.carrier, w.1 = C.zPrime :=
    ⟨C.exteriorVertex C.zPrime_mem_ambientCarrier,
      C.exteriorVertex_mem_block
        C.zPrime_mem_ambientCarrier,
      rfl⟩
  have hzb :
      C.zPrime = C.b :=
    C.pathToY_meets_block_only_at_b hz hzBlock
  exact D.zPrime_ne_b M hzb

set_option maxHeartbeats 500000 in
/--
The exterior anchor path lies in the main deletion component of the
selected block at `zPrime`.
-/
theorem anchor_path_support_mem_mainDeletionRegion
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {w : P.ExteriorVertex}
    (hw : w ∈ C.anchor.pathToTarget.walk.support) :
    w ∈ componentVertices P.exteriorGraph
      {D.zPrimeExterior}
      (C.block.mainDeletionComponent
        D.zPrimeExterior
        (C.exteriorVertex_mem_block
          C.zPrime_mem_ambientCarrier)) := by
  let mainRegion :=
    componentVertices P.exteriorGraph
      {D.zPrimeExterior}
      (C.block.mainDeletionComponent
        D.zPrimeExterior
        (C.exteriorVertex_mem_block
          C.zPrime_mem_ambientCarrier))
  have hMain :
      ComponentRegion P.exteriorGraph
        {D.zPrimeExterior} mainRegion :=
    componentRegion_componentVertices
      P.exteriorGraph {D.zPrimeExterior}
      (C.block.mainDeletionComponent
        D.zPrimeExterior
        (C.exteriorVertex_mem_block
          C.zPrime_mem_ambientCarrier))
  have hbNeZ :
      C.anchor.b ≠ D.zPrimeExterior := by
    intro h
    exact D.zPrime_ne_b M
      (by
        simpa using congrArg Subtype.val h.symm)
  have hbMain :
      C.anchor.b ∈ mainRegion := by
    exact C.block.mem_mainDeletionComponent
      (C.exteriorVertex_mem_block
        C.zPrime_mem_ambientCarrier)
      C.anchor.b_mem hbNeZ
  have hAvoid :
      ∀ v ∈ C.anchor.pathToTarget.walk.support,
        v ∉ ({D.zPrimeExterior} :
          Finset P.ExteriorVertex) := by
    intro v hv
    simp only [Finset.mem_singleton]
    intro hvz
    have hvBlock :
        v ∈ C.block.carrier := by
      simpa [hvz] using
        C.exteriorVertex_mem_block
          C.zPrime_mem_ambientCarrier
    have hvb :
        v = C.anchor.b :=
      C.anchor.path_meets_carrier_only_at_b
        hv hvBlock
    exact hbNeZ (hvb.symm.trans hvz)
  exact
    walk_support_subset_componentRegion
      hMain C.anchor.pathToTarget.walk
      hbMain hAvoid w hw

set_option maxHeartbeats 500000 in
/--
The selected off component is disjoint from every exterior vertex on the
fixed anchor-to-`y` path.
-/
theorem offRegion_disjoint_anchor_path_support
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {w : P.ExteriorVertex}
    (hwOff : w ∈ D.offRegion M)
    (hwPath : w ∈ C.anchor.pathToTarget.walk.support) :
    False := by
  have hwMain :=
    D.anchor_path_support_mem_mainDeletionRegion M hwPath
  exact
    Finset.disjoint_left.mp
      (componentVertices_disjoint_of_ne
        P.exteriorGraph {D.zPrimeExterior}
        (D.offComponent_isOff M))
      hwOff hwMain

set_option maxHeartbeats 500000 in
/--
The selected off component is disjoint from the ambient support of the
fixed block-to-`y` path.
-/
theorem offRegion_disjoint_pathToY_support
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {w : P.ExteriorVertex}
    (hwOff : w ∈ D.offRegion M)
    (hwPath : w.1 ∈ C.pathToY.walk.support) :
    False := by
  change
    w.1 ∈
      (C.anchor.pathToTarget.walk.map
        P.exteriorEmbedding.toHom).support at hwPath
  rw [SimpleGraph.Walk.support_map] at hwPath
  obtain ⟨v, hvPath, hvVal⟩ :=
    List.mem_map.mp hwPath
  have hvw : v = w := by
    apply Subtype.ext
    exact hvVal
  exact D.offRegion_disjoint_anchor_path_support
    M hwOff (hvw ▸ hvPath)

/--
The fixed `x`--`zPrime` path in the empty-boundary branch, together with
the exact support classification used by both later concatenations.
-/
structure ConnectorPathData
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) where
  /-- The fixed path from the original root to the recursive left root. -/
  path : SimplePath G x C.zPrime
  /--
  Every path vertex lies in the working core, is `zPrime`, or is represented
  by a vertex of the selected off component.
  -/
  support_class :
    ∀ ⦃v : V⦄, v ∈ path.walk.support →
      v ∈ P.working.rooted.core.carrier ∨
        v = C.zPrime ∨
          ∃ w : P.ExteriorVertex,
            w ∈ D.offRegion M ∧ w.1 = v

namespace ConnectorPathData

/--
The fixed connector meets the selected block only at its endpoint
`zPrime`.
-/
theorem meets_ambientCarrier_only_at_zPrime
    {D : EmptyInitialBoundary C}
    {M : MinimalCounterexample q G x y z}
    (E : ConnectorPathData D M)
    {v : V} (hvPath : v ∈ E.path.walk.support)
    (hvBlock : v ∈ C.ambientCarrier) :
    v = C.zPrime := by
  rcases E.support_class hvPath with
    hvCore | rfl | ⟨w, hwOff, hwVal⟩
  · exact False.elim
      (Finset.disjoint_left.mp
        C.ambientCarrier_disjoint_core
        hvBlock hvCore)
  · rfl
  · have hwBlock :
        w ∈ C.block.carrier := by
      have hwEq :
          w = C.exteriorVertex hvBlock := by
        apply Subtype.ext
        exact hwVal
      rw [hwEq]
      exact C.exteriorVertex_mem_block hvBlock
    exact False.elim
      (Finset.disjoint_left.mp
        (D.offRegion_disjoint_block M)
        hwOff hwBlock)

/--
The fixed connector is disjoint from the tail of the fixed block-to-`y`
path.
-/
theorem disjoint_pathToY_tail
    {D : EmptyInitialBoundary C}
    {M : MinimalCounterexample q G x y z}
    (E : ConnectorPathData D M) :
    E.path.walk.support.Disjoint
      C.pathToY.walk.support.tail := by
  apply List.disjoint_left.mpr
  intro v hvE hvTail
  have hvPath :
      v ∈ C.pathToY.walk.support :=
    List.mem_of_mem_tail hvTail
  rcases E.support_class hvE with
    hvCore | hvZ | ⟨w, hwOff, hwVal⟩
  · exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        (C.pathToY_support_mem_otherRegion hvPath)
        hvCore
  · subst v
    exact D.zPrime_not_mem_pathToY_support M hvPath
  · exact D.offRegion_disjoint_pathToY_support
      M hwOff (hwVal ▸ hvPath)

end ConnectorPathData

set_option maxHeartbeats 500000 in
/--
Construct the source-faithful fixed path from `x` to `zPrime`.
-/
theorem exists_connectorPathData
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    Nonempty (ConnectorPathData D M) := by
  classical
  obtain ⟨u, huOff, s, hsCore, hsu⟩ :=
    D.exists_offRegion_core_attachment M
  let corePath :=
    P.working.rooted.core.carrierPathData s hsCore
  obtain ⟨outsideExterior, houtsideTail⟩ :=
    (D.offRegion_componentRegion M
      ).exists_path_from_singleton_boundary
        P.exteriorGraph_connected huOff
  let outside :
      SimplePath G C.zPrime u.1 :=
    outsideExterior.mapInjectiveHom
      P.exteriorEmbedding.toHom Subtype.val_injective
  let outsideReverse :
      SimplePath G u.1 C.zPrime :=
    outside.reverse
  have houtsideSupportClass :
      ∀ ⦃v : V⦄,
        v ∈ outsideReverse.walk.support →
          v = C.zPrime ∨
            ∃ w : P.ExteriorVertex,
              w ∈ D.offRegion M ∧ w.1 = v := by
    intro v hv
    have hvForward :
        v ∈ outside.walk.support := by
      simpa [outsideReverse, SimplePath.reverse,
        SimpleGraph.Walk.support_reverse] using hv
    change
      v ∈
        (outsideExterior.walk.map
          P.exteriorEmbedding.toHom).support at hvForward
    rw [SimpleGraph.Walk.support_map] at hvForward
    obtain ⟨w, hwSupport, hwVal⟩ :=
      List.mem_map.mp hvForward
    rcases
        (outsideExterior.walk.mem_support_iff).1
          hwSupport with hwStart | hwTail
    · left
      have hwRoot : w.1 = C.zPrime := by
        simp [hwStart]
      exact hwVal.symm.trans hwRoot
    · exact Or.inr ⟨w, houtsideTail w hwTail, hwVal⟩
  have hbridgeDisjoint :
      (SimplePath.ofAdj hsu).walk.support.Disjoint
        outsideReverse.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvBridge hvOutsideTail
    have hvOutside :
        v ∈ outsideReverse.walk.support :=
      List.mem_of_mem_tail hvOutsideTail
    have hvClass : v = s ∨ v = u.1 := by
      simpa using hvBridge
    rcases hvClass with hvS | hvU
    · have hsOutside :
          s ∈ outsideReverse.walk.support := by
        simpa [hvS] using hvOutside
      rcases houtsideSupportClass hsOutside with
        hsZ | ⟨w, -, hwVal⟩
      · have hsOther :
            s ∈ P.working.rooted.otherRegion := by
          rw [hsZ]
          exact C.ambientCarrier_subset_otherRegion
            C.zPrime_mem_ambientCarrier
        exact
          P.working.rooted.otherRegion_componentRegion.not_mem_separator
            hsOther hsCore
      · have hsOther :
            s ∈ P.working.rooted.otherRegion := by
          rw [← hwVal]
          exact w.2
        exact
          P.working.rooted.otherRegion_componentRegion.not_mem_separator
            hsOther hsCore
    · exact outsideReverse.start_not_mem_tail
        (by simpa [hvU] using hvOutsideTail)
  let exteriorPart :
      SimplePath G s C.zPrime :=
    (SimplePath.ofAdj hsu).appendDisjoint
      outsideReverse hbridgeDisjoint
  have hexteriorPartTailClass :
      ∀ ⦃v : V⦄,
        v ∈ exteriorPart.walk.support.tail →
          v = C.zPrime ∨
            ∃ w : P.ExteriorVertex,
              w ∈ D.offRegion M ∧ w.1 = v := by
    intro v hv
    have hvParts :
        v ∈ (SimplePath.ofAdj hsu).walk.support.tail ∨
          v ∈ outsideReverse.walk.support.tail := by
      exact
        (SimpleGraph.Walk.mem_tail_support_append_iff
          (SimplePath.ofAdj hsu).walk
          outsideReverse.walk).1
          (by
            simpa [exteriorPart,
              SimplePath.appendDisjoint] using hv)
    rcases hvParts with hvBridge | hvOutside
    · have hvu : v = u.1 := by
        simpa using hvBridge
      exact Or.inr ⟨u, huOff, hvu.symm⟩
    · exact houtsideSupportClass
        (List.mem_of_mem_tail hvOutside)
  have hcoreDisjoint :
      corePath.path.walk.support.Disjoint
        exteriorPart.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvCorePath hvExterior
    have hvCore :
        v ∈ P.working.rooted.core.carrier :=
      corePath.support_subset hvCorePath
    rcases hexteriorPartTailClass hvExterior with
      hvZ | ⟨w, -, hwVal⟩
    · have hvOther :
          v ∈ P.working.rooted.otherRegion := by
        rw [hvZ]
        exact C.ambientCarrier_subset_otherRegion
          C.zPrime_mem_ambientCarrier
      exact
        P.working.rooted.otherRegion_componentRegion.not_mem_separator
          hvOther hvCore
    · have hvOther :
          v ∈ P.working.rooted.otherRegion := by
        rw [← hwVal]
        exact w.2
      exact
        P.working.rooted.otherRegion_componentRegion.not_mem_separator
          hvOther hvCore
  let connector :
      SimplePath G x C.zPrime :=
    corePath.path.appendDisjoint
      exteriorPart hcoreDisjoint
  refine ⟨{
    path := connector
    support_class := ?_
  }⟩
  intro v hv
  have hvParts :
      v ∈ corePath.path.walk.support ∨
        v ∈ exteriorPart.walk.support.tail := by
    change
      v ∈
        ((corePath.path.appendDisjoint
          exteriorPart hcoreDisjoint).walk.support) at hv
    rw [SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hv
    exact List.mem_append.mp hv
  rcases hvParts with hvCore | hvExterior
  · exact Or.inl (corePath.support_subset hvCore)
  · rcases hexteriorPartTailClass hvExterior with
      hvZ | hvOff
    · exact Or.inr (Or.inl hvZ)
    · exact Or.inr (Or.inr hvOff)

end EmptyInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
