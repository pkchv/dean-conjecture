import DeanK5.COYExteriorAvoidingAnchor
import DeanK5.COYExteriorClaimThreeThirteenCatalogues

/-!
# Eliminating Types I and II in COY Claim 3.13

A Type I or Type II witness augments the old type-three core by one exterior
vertex and supplies two endpoint-uniform paths.  Re-anchoring the feasible
block makes its connector avoid that vertex.  The rank-loss compression
then yields `q - 1` exterior paths, and COY Fact 1 produces the forbidden
family of `q` root paths.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.TypeThreeStage

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/--
The common closing argument for the rank-one Type I and Type II
two-path catalogues.
-/
theorem false_of_uniformAugmentedTwoCatalogue
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (ordinary : P.ExteriorOrdinaryVertex)
    {t : V}
    (ht : t ∈ D.core.T)
    (hvt : G.Adj ordinary.vertex.1 t)
    (catalogue :
      D.core.UniformAugmentedTwoCatalogue
        ordinary.vertex.1) :
    False := by
  classical
  have hrank : P.working.rank = 1 :=
    D.rank_eq_one M
  have htWorking :
      t ∈ P.working.rooted.core.T := by
    simpa [D.core_eq, Core.T] using ht
  have hattachment :
      P.working.rooted.core.HasTAttachment
        P.working.rooted.otherRegion := by
    exact
      ⟨ordinary.vertex.1, ordinary.vertex.2,
        t, htWorking, hvt.symm⟩
  have htwoLtQ : 2 < q := by
    have hstrong :
        P.working.rank + 1 < q :=
      (M.rootedCore_factThree P.working.rooted).2
        hattachment
    omega
  obtain ⟨C⟩ :=
    P.exists_exteriorFeasibleBlockChoice M
      (P.otherRegion_ne_singleton M)
  obtain ⟨C', hconnectorAvoids⟩ :=
    C.exists_reanchored_avoiding
      M ordinary.vertex.2 ordinary.ne_y ordinary.ne_z
      ordinary.not_cut htWorking hvt
  have hvBlock :
      ordinary.vertex.1 ∉ C'.ambientCarrier :=
    C'.not_mem_ambientCarrier_of_T_neighbor
      M ordinary.vertex.2 ordinary.ne_y ordinary.ne_z
      ordinary.not_cut htWorking hvt
  obtain ⟨recursive⟩ :=
    C'.exists_initialCompression_recursive_family_of_rankLoss
      M 2 (by omega) (by omega) htwoLtQ
  obtain ⟨outer⟩ :=
    C'.exists_liftedInitialToYData recursive
  have houterPos :
      1 ≤ q - 2 + 1 := by
    omega
  have hendpointS (i : Fin (q - 2 + 1)) :
      outer.family.endpoint i ∈ D.core.S := by
    have hcoreS :=
      C'.initialAttachments_subset_coreS
        (outer.family.endpoint_mem i)
    simpa [D.core_eq, Core.S] using hcoreS
  let innerAdmissible (i : Fin (q - 2 + 1)) :
      AdmissiblePathFamily G x
        (outer.family.endpoint i) 2 :=
    catalogue.family
      (outer.family.endpoint i) (hendpointS i)
  let inner (i : Fin (q - 2 + 1)) :
      SemiAdmissiblePathFamily G x
        (outer.family.endpoint i) 2 :=
    SemiAdmissiblePathFamily.ofAdmissible
      (innerAdmissible i)
  have hxNotAttachments :
      x ∉ (↑C'.initialAttachments : Set V) := by
    intro hx
    exact P.working.rooted.core.root_not_mem_S
      (C'.initialAttachments_subset_coreS hx)
  have hyNotAttachments :
      y ∉ (↑C'.initialAttachments : Set V) := by
    intro hy
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        P.working.rooted.other_root_mem_otherRegion
        (P.working.rooted.core.S_subset_carrier
          (C'.initialAttachments_subset_coreS hy))
  let certificate :
      FactOneCertificate G x y
        (↑C'.initialAttachments : Set V)
        (q - 2 + 1) 2 := {
    hs := houterPos
    ht := by omega
    x_ne_y := M.roots_ne
    x_not_mem := hxNotAttachments
    y_not_mem := hyNotAttachments
    outer := outer.family
    inner := inner
    equal_inner_length := by
      intro i j
      simpa [inner, innerAdmissible,
        SemiAdmissiblePathFamily.ofAdmissible] using
        catalogue.equal_length
          (outer.family.endpoint i)
          (outer.family.endpoint (firstFin houterPos))
          (hendpointS i)
          (hendpointS (firstFin houterPos))
          j
    avoid_outer := by
      intro i j
      apply List.disjoint_left.mpr
      intro v hvInner hvOuterTail
      have hvAugmented :=
        catalogue.support
          (outer.family.endpoint i) (hendpointS i)
          j v (by
            simpa [inner, innerAdmissible,
              SemiAdmissiblePathFamily.ofAdmissible] using
              hvInner)
      rcases Finset.mem_insert.mp hvAugmented with
        hvWitness | hvCoreRaw
      · subst v
        exact
          (outer.avoids_of_not_mem_block_and_connector
            ordinary.vertex.2 hvBlock hconnectorAvoids i)
            (List.mem_of_mem_tail hvOuterTail)
      · have hvCore :
            v ∈ P.working.rooted.core.carrier := by
          simpa [D.core_eq] using hvCoreRaw
        have hvOuter :
            v ∈ (outer.family.path i).walk.support :=
          List.mem_of_mem_tail hvOuterTail
        rcases outer.support_class i v hvOuter with
          hvEndpoint | hvExterior
        · subst v
          exact (outer.family.path i).start_not_mem_tail
            hvOuterTail
        · exact
            P.working.rooted.otherRegion_componentRegion.not_mem_separator
              hvExterior hvCore
  }
  have hcount :
      (q - 2 + 1) + 2 - 1 = q := by
    omega
  apply M.no_paths
  unfold RootedInstance.Solvable
  simpa only [hcount] using fact_one certificate

/-- The source Type I alternative is impossible. -/
theorem false_of_typeI
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (W : D.TypeIWitness) :
    False := by
  obtain ⟨t, ht, hvt⟩ :=
    W.exists_terminal_neighbor (D.rank_eq_one M)
  exact D.false_of_uniformAugmentedTwoCatalogue
    M W.ordinary ht hvt
      (W.uniformAugmentedTwoCatalogue (D.rank_eq_one M))

/-- The source Type II alternative is impossible. -/
theorem false_of_typeII
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (W : D.TypeIIWitness) :
    False := by
  obtain ⟨t, ht, hvt⟩ :=
    W.exists_terminal_neighbor
  exact D.false_of_uniformAugmentedTwoCatalogue
    M W.ordinary ht hvt
      W.uniformAugmentedTwoCatalogue

/-- COY Claim 3.13 in source classification form. -/
theorem claim_three_thirteen
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage) :
    P.working.rank = 1 ∧ D.IsTypeIII := by
  refine ⟨D.rank_eq_one M, ?_, ?_⟩
  · intro h
    obtain ⟨W⟩ := h
    exact D.false_of_typeI M W
  · intro h
    obtain ⟨W⟩ := h
    exact D.false_of_typeII M W

end PreferredWorkingCoreData.TypeThreeStage

end COY

end DeanK5
