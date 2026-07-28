import DeanK5.COYCoreSCatalogue
import DeanK5.COYExteriorInitialPathLift
import DeanK5.COYExteriorInitialRecursive
import DeanK5.COYExteriorTypeThreeStage

/-!
# The rank conclusion in COY Claim 3.13

The source proof introduces an augmented side before Claim 3.13.  Its first
consequence can be obtained more directly: if the selected type-three core
had rank at least two, the initial compression would give
`q - rank + 1` exterior paths, while the core gives `rank` paths of lengths
`2, 4, ..., 2 rank` to every possible exterior endpoint.  COY Fact 1 then
produces the forbidden `q` root paths.

This direct argument isolates the rank-one conclusion from the later
Type I/II/III classification.
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

/-- The selected type-three core in a minimal counterexample has rank one. -/
theorem rank_eq_one
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage) :
    P.working.rank = 1 := by
  classical
  have hrankPos : 1 ≤ P.working.rank :=
    D.rank_pos M
  by_contra hrankNe
  have hrankTwo : 2 ≤ P.working.rank := by
    omega
  have hrankLtQ : P.working.rank < q :=
    (M.rootedCore_factThree P.working.rooted).1
  have hrankFour : P.working.rank ≤ 4 :=
    (Nat.le_of_lt hrankLtQ).trans M.q_le_four
  obtain ⟨C⟩ :=
    P.exists_exteriorFeasibleBlockChoice M
      (P.otherRegion_ne_singleton M)
  obtain ⟨recursive⟩ :=
    C.exists_initialCompression_recursive_family_of_rankLoss
      M P.working.rank hrankTwo le_rfl hrankLtQ
  obtain ⟨outer⟩ :=
    C.exists_liftedInitialToYData recursive
  have houterPos :
      1 ≤ q - P.working.rank + 1 := by
    omega
  let catalogue :=
    D.core.uniformSCatalogue
      P.working.rank hrankPos hrankFour le_rfl
  have hendpointS (i : Fin (q - P.working.rank + 1)) :
      outer.family.endpoint i ∈ D.core.S := by
    have hcoreS :=
      C.initialAttachments_subset_coreS
        (outer.family.endpoint_mem i)
    simpa [D.core_eq, Core.S] using hcoreS
  let innerAdmissible
      (i : Fin (q - P.working.rank + 1)) :
      AdmissiblePathFamily G x
        (outer.family.endpoint i) P.working.rank :=
    catalogue.family
      (outer.family.endpoint i) (hendpointS i)
  let inner
      (i : Fin (q - P.working.rank + 1)) :
      SemiAdmissiblePathFamily G x
        (outer.family.endpoint i) P.working.rank :=
    SemiAdmissiblePathFamily.ofAdmissible
      (innerAdmissible i)
  have hxNotAttachments :
      x ∉ (↑C.initialAttachments : Set V) := by
    intro hx
    exact P.working.rooted.core.root_not_mem_S
      (C.initialAttachments_subset_coreS hx)
  have hyNotAttachments :
      y ∉ (↑C.initialAttachments : Set V) := by
    intro hy
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        P.working.rooted.other_root_mem_otherRegion
        (P.working.rooted.core.S_subset_carrier
          (C.initialAttachments_subset_coreS hy))
  let certificate :
      FactOneCertificate G x y
        (↑C.initialAttachments : Set V)
        (q - P.working.rank + 1)
        P.working.rank := {
    hs := houterPos
    ht := hrankPos
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
      have hvCoreRaw :=
        catalogue.support
          (outer.family.endpoint i) (hendpointS i)
          j v (by
            simpa [inner, innerAdmissible,
              SemiAdmissiblePathFamily.ofAdmissible] using
              hvInner)
      have hvCore :
          v ∈ P.working.rooted.core.carrier := by
        rw [D.core_eq]
        simpa [Core.carrier, Core.S, Core.T] using
          hvCoreRaw
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
      (q - P.working.rank + 1) +
          P.working.rank - 1 = q := by
    omega
  apply M.no_paths
  unfold RootedInstance.Solvable
  simpa only [hcount] using fact_one certificate

end PreferredWorkingCoreData.TypeThreeStage

end COY

end DeanK5
