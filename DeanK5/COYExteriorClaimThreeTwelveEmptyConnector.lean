import DeanK5.COYExteriorClaimThreeTwelveEmptyRecursive

/-!
# The exterior connector in the empty-boundary branch

The second special block vertex is a genuine cut vertex of the exterior.
An off component at that cut vertex is disjoint from the selected block.
Two-connectivity of the ambient graph forces that off component to attach
to the working core, producing the source path from `x` to `zPrime`.
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

/-- The exterior copy of `zPrime`. -/
abbrev zPrimeExterior
    (_D : EmptyInitialBoundary C) :
    P.ExteriorVertex :=
  C.exteriorVertex C.zPrime_mem_ambientCarrier

/-- A deletion component at `zPrime` away from the selected block. -/
noncomputable def offComponent
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    (deleteVertices P.exteriorGraph
      {D.zPrimeExterior}).ConnectedComponent :=
  C.block.offDeletionComponent
    P.exteriorGraph_connected
    D.zPrimeExterior
    (C.exteriorVertex_mem_block
      C.zPrime_mem_ambientCarrier)
    (D.zPrime_isCutVertex M)

/-- The vertices in the selected off component at `zPrime`. -/
noncomputable def offRegion
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    Finset P.ExteriorVertex :=
  componentVertices P.exteriorGraph
    {D.zPrimeExterior} (D.offComponent M)

/-- The selected off side is a component region of the exterior deletion. -/
theorem offRegion_componentRegion
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    ComponentRegion P.exteriorGraph
      {D.zPrimeExterior} (D.offRegion M) :=
  componentRegion_componentVertices
    P.exteriorGraph {D.zPrimeExterior}
      (D.offComponent M)

/-- No vertex of the off side is the deleted cut vertex. -/
theorem offRegion_ne_zPrime
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {u : P.ExteriorVertex}
    (hu : u ∈ D.offRegion M) :
    u ≠ D.zPrimeExterior := by
  intro h
  have huSeparator :
      u ∈ ({D.zPrimeExterior} :
        Finset P.ExteriorVertex) :=
    Finset.mem_singleton.mpr h
  exact
    (D.offRegion_componentRegion M).not_mem_separator
      hu huSeparator

set_option maxHeartbeats 500000 in
/-- The off side is closed under exterior edges that avoid `zPrime`. -/
theorem offRegion_closed
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {u v : P.ExteriorVertex}
    (hu : u ∈ D.offRegion M)
    (huv : P.exteriorGraph.Adj u v)
    (hv : v ≠ D.zPrimeExterior) :
    v ∈ D.offRegion M := by
  have hvSeparator :
      v ∉ ({D.zPrimeExterior} :
        Finset P.ExteriorVertex) := by
    simpa only [Finset.mem_singleton] using hv
  change
    u ∈ componentVertices P.exteriorGraph
      {D.zPrimeExterior} (D.offComponent M) at hu
  obtain ⟨huSeparator, huComponent⟩ :=
    (mem_componentVertices_iff
      P.exteriorGraph {D.zPrimeExterior}
        (D.offComponent M) u).1 hu
  have huvDeleted :
      (deleteVertices P.exteriorGraph
        {D.zPrimeExterior}).Adj
        ⟨u, huSeparator⟩ ⟨v, hvSeparator⟩ :=
    huv
  have hvComponent :
      (⟨v, hvSeparator⟩ :
        {w : P.ExteriorVertex //
          w ∉ ({D.zPrimeExterior} :
            Finset P.ExteriorVertex)}) ∈
        (D.offComponent M).supp :=
    (D.offComponent M).mem_supp_of_adj_mem_supp
      huComponent huvDeleted
  change
    v ∈ componentVertices P.exteriorGraph
      {D.zPrimeExterior} (D.offComponent M)
  exact
    (mem_componentVertices_iff
      P.exteriorGraph {D.zPrimeExterior}
        (D.offComponent M) v).2
      ⟨hvSeparator, hvComponent⟩

set_option maxHeartbeats 500000 in
/--
An ambient edge from the off side remains on the off side whenever its
other end is neither in the core nor the deleted cut vertex.
-/
theorem exists_offRegion_neighbor
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {a : P.ExteriorVertex} {b : V}
    (ha : a ∈ D.offRegion M)
    (hab : G.Adj a.1 b)
    (hbCore :
      b ∉ P.working.rooted.core.carrier)
    (hbZ : b ≠ C.zPrime) :
    ∃ bE : P.ExteriorVertex,
      bE ∈ D.offRegion M ∧ bE.1 = b := by
  have hbRegion :
      b ∈ P.working.rooted.otherRegion :=
    P.working.rooted.otherRegion_componentRegion.closed
      a.2 hab hbCore
  let bE : P.ExteriorVertex := ⟨b, hbRegion⟩
  have habExterior :
      P.exteriorGraph.Adj a bE := hab
  have hbENeZ : bE ≠ D.zPrimeExterior := by
    intro h
    exact hbZ (congrArg Subtype.val h)
  exact
    ⟨bE,
      D.offRegion_closed M ha
        habExterior hbENeZ,
      rfl⟩

/-- The selected component is not the block's main deletion component. -/
theorem offComponent_isOff
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    C.block.IsOffDeletionComponent
      (C.exteriorVertex_mem_block
        C.zPrime_mem_ambientCarrier)
      (D.offComponent M) :=
  C.block.offDeletionComponent_isOff
    P.exteriorGraph_connected
    D.zPrimeExterior
    (C.exteriorVertex_mem_block
      C.zPrime_mem_ambientCarrier)
    (D.zPrime_isCutVertex M)

/-- The off component contains no vertex of the selected block. -/
theorem offRegion_disjoint_block
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    Disjoint (D.offRegion M) C.block.carrier :=
  C.block.componentVertices_disjoint_carrier_of_isOff
    (C.exteriorVertex_mem_block
      C.zPrime_mem_ambientCarrier)
    (D.offComponent_isOff M)

omit [Fintype V] [DecidableEq V] in
private theorem exists_boundary_edge_of_walk_predicate
    {S : Finset V} {A : V → Prop}
    {a t forbidden : V}
    (ha : A a) (ht : t ∈ S)
    (hdisjoint : ∀ ⦃v : V⦄, A v → v ∉ S)
    (hclosed :
      ∀ ⦃u v : V⦄, A u → G.Adj u v →
        v ∉ S → v ≠ forbidden → A v)
    (W : G.Walk a t)
    (havoid : forbidden ∉ W.support) :
    ∃ u, A u ∧ u ∈ W.support ∧
      ∃ s ∈ S, s ∈ W.support ∧ G.Adj u s := by
  let rec go {a : V} (ha : A a)
      (W : G.Walk a t)
      (havoid : forbidden ∉ W.support) :
      ∃ u, A u ∧ u ∈ W.support ∧
        ∃ s ∈ S, s ∈ W.support ∧ G.Adj u s := by
    cases W with
    | nil =>
        exact False.elim (hdisjoint ha ht)
    | @cons a b c hab W =>
        by_cases hb : A b
        · have htailAvoid :
              forbidden ∉ W.support := by
            intro h
            apply havoid
            exact
              W.support_subset_support_cons hab h
          obtain
              ⟨u, hu, huSupport, s, hs,
                hsSupport, hus⟩ :=
            go hb W htailAvoid
          exact
            ⟨u, hu, by simp [huSupport],
              s, hs, by simp [hsSupport], hus⟩
        · have hbS : b ∈ S := by
            by_contra hbNotS
            have hbNeForbidden :
                b ≠ forbidden := by
              intro h
              apply havoid
              exact
                W.support_subset_support_cons hab
                  (h ▸ W.start_mem_support)
            exact hb
              (hclosed ha hab hbNotS
                hbNeForbidden)
          exact ⟨a, ha, by simp,
            b, hbS, by simp, hab⟩
  exact go ha W havoid

set_option maxHeartbeats 500000 in
/--
Two-connectivity forces an edge from the selected off component to the
working-core carrier.  A walk in `G - zPrime` cannot leave the off
component through another exterior vertex.
-/
theorem exists_offRegion_core_attachment
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    ∃ u : P.ExteriorVertex, u ∈ D.offRegion M ∧
      ∃ s ∈ P.working.rooted.core.carrier,
        G.Adj s u.1 := by
  classical
  have hOff :
      ComponentRegion P.exteriorGraph
        {D.zPrimeExterior} (D.offRegion M) :=
    D.offRegion_componentRegion M
  obtain ⟨u, huOff⟩ := hOff.nonempty
  have huNeZ : u.1 ≠ C.zPrime := by
    intro h
    apply hOff.not_mem_separator huOff
    have huEq : u = D.zPrimeExterior := by
      apply Subtype.ext
      exact h
    simp [huEq]
  have hxNeZ : x ≠ C.zPrime := by
    intro h
    have hzCore :
        C.zPrime ∈
          P.working.rooted.core.carrier := by
      rw [← h]
      exact P.working.rooted.core.root_mem_carrier
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        (C.ambientCarrier_subset_otherRegion
          C.zPrime_mem_ambientCarrier)
        hzCore
  let uDeleted :
      {v : V // v ∉ ({C.zPrime} : Finset V)} :=
    ⟨u.1, by simpa using huNeZ⟩
  let xDeleted :
      {v : V // v ∉ ({C.zPrime} : Finset V)} :=
    ⟨x, by simpa using hxNeZ⟩
  have hdeletedConnected :
      (G.induce
        {v : V | v ∉ ({C.zPrime} : Finset V)}).Connected :=
    M.underlying_two_connected.2
      {C.zPrime} (by simp)
  obtain ⟨p⟩ :=
    hdeletedConnected.preconnected
      uDeleted xDeleted
  let pG : G.Walk u.1 x :=
    p.map
      (Embedding.induce
        {v : V | v ∉
          ({C.zPrime} : Finset V)}).toHom
  have hpAvoid :
      C.zPrime ∉ pG.support := by
    intro hz
    change
      C.zPrime ∈
        (p.map
          (Embedding.induce
            {v : V | v ∉
              ({C.zPrime} : Finset V)}).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨v, hv, hvz⟩ := List.mem_map.mp hz
    apply v.2
    simpa [hvz]
  let A : V → Prop := fun v =>
    ∃ w : P.ExteriorVertex,
      w ∈ D.offRegion M ∧ w.1 = v
  have huA : A u.1 :=
    ⟨u, huOff, rfl⟩
  have hxSeparator :
      x ∈ P.working.rooted.core.carrier :=
    P.working.rooted.core.root_mem_carrier
  have hdisjoint :
      ∀ ⦃v : V⦄, A v →
        v ∉ P.working.rooted.core.carrier := by
    rintro v ⟨w, -, rfl⟩ hwCore
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        w.2 hwCore
  have hclosed :
      ∀ ⦃a b : V⦄, A a → G.Adj a b →
        b ∉ P.working.rooted.core.carrier →
        b ≠ C.zPrime →
        A b := by
    rintro a b ⟨aE, haEOff, rfl⟩ hab
      hbNotCore hbNotZ
    exact
      D.exists_offRegion_neighbor M
        haEOff hab hbNotCore hbNotZ
  obtain
      ⟨a, haA, -, s, hsSeparator,
        hsSupport, has⟩ :=
    exists_boundary_edge_of_walk_predicate
      huA hxSeparator hdisjoint hclosed
        pG hpAvoid
  obtain ⟨aE, haEOff, haEVal⟩ := haA
  refine ⟨aE, haEOff, s, hsSeparator, ?_⟩
  simpa [haEVal] using has.symm

end EmptyInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
