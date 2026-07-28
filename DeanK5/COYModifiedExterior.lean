import DeanK5.COYWorkingCore

/-!
# The exterior region after the special type-3 modification

Removing the distinguished vertex `t₀` joins the former second component
to the singleton component containing the other root.  This is the precise
mechanism behind COY Claim 3.4.
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

/-- The distinguished vertex is outside the modified core carrier. -/
theorem t₀_not_mem_carrier
    (K : TypeThreeModificationChoice T) :
    T.t₀ ∉ K.rooted.core.carrier := by
  have htRoot : T.t₀ ≠ x :=
    T.root_adj_t₀.ne.symm
  have htS : T.t₀ ∉ T.core.S := by
    intro ht
    exact Finset.disjoint_left.mp T.core.disjoint
      ht T.t₀_mem
  cases K with
  | balanced s₀ hs₀ hbalance =>
      simp [rooted, core, rank, Core.carrier,
        Core.S, Core.T, TypeThreeCore.eraseBalanced,
        htRoot, htS]
  | terminal hlarge =>
      simp [rooted, core, rank, Core.carrier,
        Core.S, Core.T, TypeThreeCore.eraseTerminal,
        htRoot, htS]

/-- The selected ordinary vertex lies outside the original core carrier. -/
theorem ordinary_not_mem_original_carrier :
    T.ordinary ∉ O.rooted.core.carrier := by
  exact
    (componentRegion_componentVertices
      G O.rooted.core.carrier T.component).not_mem_separator
      T.ordinary_mem

/-- The selected ordinary vertex also lies outside the modified carrier. -/
theorem ordinary_not_mem_carrier
    (K : TypeThreeModificationChoice T) :
    T.ordinary ∉ K.rooted.core.carrier := by
  intro hordinary
  exact ordinary_not_mem_original_carrier
    (K.carrier_subset_original hordinary)

/-- The selected attachment lies outside the original core carrier. -/
theorem attachment_not_mem_original_carrier :
    T.attachment ∉ O.rooted.core.carrier := by
  exact
    (componentRegion_componentVertices
      G O.rooted.core.carrier T.component).not_mem_separator
      T.attachment_mem

/-- The selected attachment also lies outside the modified carrier. -/
theorem attachment_not_mem_carrier
    (K : TypeThreeModificationChoice T) :
    T.attachment ∉ K.rooted.core.carrier := by
  intro hattachment
  exact attachment_not_mem_original_carrier
    (K.carrier_subset_original hattachment)

/-- The ordinary vertex in the second old component is not the other root. -/
theorem ordinary_ne_other_root :
    T.ordinary ≠ y := by
  intro h
  have hyOld : y ∈ O.rooted.otherRegion :=
    O.rooted.other_root_mem_otherRegion
  have hordinaryOld :
      T.ordinary ∈ O.rooted.otherRegion := by
    simpa only [h] using hyOld
  exact Finset.disjoint_left.mp
    (componentVertices_disjoint_of_ne
      G O.rooted.core.carrier T.component_ne_other)
    T.ordinary_mem hordinaryOld

/-- The distinguished vertex belongs to the new exterior component. -/
theorem t₀_mem_otherRegion
    (K : TypeThreeModificationChoice T) :
    T.t₀ ∈ K.rooted.otherRegion := by
  let yD :
      {v : V // v ∉ K.rooted.core.carrier} :=
    ⟨y, K.rooted.other_root_not_mem⟩
  let tD :
      {v : V // v ∉ K.rooted.core.carrier} :=
    ⟨T.t₀, K.t₀_not_mem_carrier⟩
  have hyt :
      (deleteVertices G K.rooted.core.carrier).Adj yD tD :=
    T.other_root_adj_t₀
  have hySupp :
      yD ∈ K.rooted.otherComponent.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have htSupp :
      tD ∈ K.rooted.otherComponent.supp :=
    K.rooted.otherComponent.mem_supp_of_adj_mem_supp
      hySupp hyt
  apply (mem_componentVertices_iff
    G K.rooted.core.carrier
    K.rooted.otherComponent T.t₀).2
  exact ⟨K.t₀_not_mem_carrier, by simpa [tD] using htSupp⟩

/-- The ordinary vertex of the former second component joins the new exterior. -/
theorem ordinary_mem_otherRegion
    (K : TypeThreeModificationChoice T) :
    T.ordinary ∈ K.rooted.otherRegion := by
  let oldToNew :
      deleteVertices G O.rooted.core.carrier →g
        deleteVertices G K.rooted.core.carrier := {
    toFun := fun v =>
      ⟨v.1, fun hv =>
        v.2 (K.carrier_subset_original hv)⟩
    map_rel' := by
      intro a b hab
      exact hab
  }
  let tD :
      {v : V // v ∉ K.rooted.core.carrier} :=
    ⟨T.t₀, K.t₀_not_mem_carrier⟩
  let aD :
      {v : V // v ∉ K.rooted.core.carrier} :=
    ⟨T.attachment, K.attachment_not_mem_carrier⟩
  let dD :
      {v : V // v ∉ K.rooted.core.carrier} :=
    ⟨T.ordinary, K.ordinary_not_mem_carrier⟩
  have htRegion := K.t₀_mem_otherRegion
  obtain ⟨htNot, htSupp⟩ :=
    (mem_componentVertices_iff
      G K.rooted.core.carrier
      K.rooted.otherComponent T.t₀).1 htRegion
  have htSupp' :
      tD ∈ K.rooted.otherComponent.supp := by
    simpa [tD] using htSupp
  have hta :
      (deleteVertices G K.rooted.core.carrier).Adj tD aD :=
    T.t₀_adj_attachment
  have haSupp :
      aD ∈ K.rooted.otherComponent.supp :=
    K.rooted.otherComponent.mem_supp_of_adj_mem_supp
      htSupp' hta
  obtain ⟨haOld, haOldSupp⟩ :=
    (mem_componentVertices_iff
      G O.rooted.core.carrier
      T.component T.attachment).1 T.attachment_mem
  obtain ⟨hdOld, hdOldSupp⟩ :=
    (mem_componentVertices_iff
      G O.rooted.core.carrier
      T.component T.ordinary).1 T.ordinary_mem
  have hadOld :
      (deleteVertices G O.rooted.core.carrier).Reachable
        ⟨T.attachment, haOld⟩ ⟨T.ordinary, hdOld⟩ :=
    T.component.reachable_of_mem_supp haOldSupp hdOldSupp
  have hadNew :
      (deleteVertices G K.rooted.core.carrier).Reachable aD dD := by
    simpa [oldToNew, aD, dD] using hadOld.map oldToNew
  have hdSupp :
      dD ∈ K.rooted.otherComponent.supp := by
    change
      (deleteVertices G K.rooted.core.carrier).connectedComponentMk dD =
        K.rooted.otherComponent
    change
      (deleteVertices G K.rooted.core.carrier).connectedComponentMk aD =
        K.rooted.otherComponent at haSupp
    exact
      (SimpleGraph.ConnectedComponent.sound hadNew).symm.trans haSupp
  apply (mem_componentVertices_iff
    G K.rooted.core.carrier
    K.rooted.otherComponent T.ordinary).2
  exact ⟨K.ordinary_not_mem_carrier,
    by simpa [dD] using hdSupp⟩

/--
COY Claim 3.4: under protected independence, the new exterior component has
at least two vertices other than the second root and the exception.
-/
theorem two_le_otherRegion_sdiff_protected
    (K : TypeThreeModificationChoice T)
    (hxz : ¬G.Adj x z) :
    2 ≤ (K.rooted.otherRegion \ {y, z}).card := by
  have htY : T.t₀ ≠ y :=
    T.other_root_adj_t₀.symm.ne
  have htZ : T.t₀ ≠ z := by
    intro h
    exact hxz (h ▸ T.root_adj_t₀)
  have hdY : T.ordinary ≠ y :=
    ordinary_ne_other_root
  have hdZ : T.ordinary ≠ z :=
    T.ordinary_ne_exception
  have htd : T.t₀ ≠ T.ordinary :=
    fun h => ordinary_not_mem_original_carrier
      (by
        rw [← h, T.core_eq]
        exact (Core.typeThree T.core).T_subset_carrier
          (by simpa [Core.T] using T.t₀_mem))
  have hsubset :
      ({T.t₀, T.ordinary} : Finset V) ⊆
        K.rooted.otherRegion \ {y, z} := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [K.t₀_mem_otherRegion, htY, htZ]
    · simp [K.ordinary_mem_otherRegion, hdY, hdZ]
  have hcard :=
    Finset.card_le_card hsubset
  simpa [htd] using hcard

end TypeThreeModificationChoice

end COY

end DeanK5
