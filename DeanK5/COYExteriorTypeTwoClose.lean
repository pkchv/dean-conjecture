import DeanK5.COYExteriorInitialPathLift
import DeanK5.COYExteriorNonsingleton
import DeanK5.COYExteriorTypeTwoRecursive

/-!
# Closing COY Case 2.2

The recursive compression contributes `q - 1` admissible paths from
`S` to `y`.  A type-two core contributes two endpoint-uniform admissible
paths from `x` to each selected `S`-vertex.  Fact 1 combines them into the
forbidden family of `q` root paths.
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

private theorem typeTwo_sCatalogue_start
    (K : TypeTwoCore G x P.working.rank)
    (target : V) (htarget : target ∈ K.S) :
    (K.admissiblePathsToS target htarget 2
      (by omega) (by omega) K.rank_ge_two).start = 3 := by
  unfold TypeTwoCore.admissiblePathsToS
  unfold PointedTypeTwoSCore.factTwoTypeTwoBounded
  rfl

private theorem typeTwo_sCatalogue_step
    (K : TypeTwoCore G x P.working.rank)
    (target : V) (htarget : target ∈ K.S) :
    (K.admissiblePathsToS target htarget 2
      (by omega) (by omega) K.rank_ge_two).step = 1 := by
  unfold TypeTwoCore.admissiblePathsToS
  unfold PointedTypeTwoSCore.factTwoTypeTwoBounded
  rfl

/-- COY Case 2.2: a type-two working core is impossible. -/
theorem false_of_typeTwo
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (K : TypeTwoCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeTwo K) :
    False := by
  classical
  have hqSub : 1 ≤ q - 1 := by
    have hqTwo := M.two_le_q
    omega
  obtain ⟨recursive⟩ :=
    C.exists_typeTwo_initialCompression_recursive_family
      M K hcore
  obtain ⟨outer⟩ :=
    C.exists_liftedInitialToYData recursive
  have hendpointS (i : Fin (q - 1)) :
      outer.family.endpoint i ∈ K.S := by
    have hcoreS :=
      C.initialAttachments_subset_coreS
        (outer.family.endpoint_mem i)
    simpa [hcore, Core.S] using hcoreS
  let innerAdmissible (i : Fin (q - 1)) :
      AdmissiblePathFamily G x
        (outer.family.endpoint i) 2 :=
    K.admissiblePathsToS
      (outer.family.endpoint i) (hendpointS i)
      2 (by omega) (by omega) K.rank_ge_two
  let inner (i : Fin (q - 1)) :
      SemiAdmissiblePathFamily G x
        (outer.family.endpoint i) 2 :=
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
        (q - 1) 2 := {
    hs := hqSub
    ht := by omega
    x_ne_y := M.roots_ne
    x_not_mem := hxNotAttachments
    y_not_mem := hyNotAttachments
    outer := outer.family
    inner := inner
    equal_inner_length := by
      intro i j
      rw [(inner i).length_path j,
        (inner (firstFin hqSub)).length_path j]
      change
        (innerAdmissible i).start +
            j.val * (innerAdmissible i).step =
          (innerAdmissible (firstFin hqSub)).start +
            j.val *
              (innerAdmissible (firstFin hqSub)).step
      rw [typeTwo_sCatalogue_start K
          (outer.family.endpoint i) (hendpointS i),
        typeTwo_sCatalogue_step K
          (outer.family.endpoint i) (hendpointS i),
        typeTwo_sCatalogue_start K
          (outer.family.endpoint (firstFin hqSub))
          (hendpointS (firstFin hqSub)),
        typeTwo_sCatalogue_step K
          (outer.family.endpoint (firstFin hqSub))
          (hendpointS (firstFin hqSub))]
    avoid_outer := by
      intro i j
      apply List.disjoint_left.mpr
      intro v hvInner hvOuterTail
      have hvCoreRaw :=
        K.admissiblePathsToS_support
          (outer.family.endpoint i) (hendpointS i)
          2 (by omega) (by omega) K.rank_ge_two
          j v (by
            simpa [inner, innerAdmissible,
              SemiAdmissiblePathFamily.ofAdmissible] using
              hvInner)
      have hvCore :
          v ∈ P.working.rooted.core.carrier := by
        rw [hcore]
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
      (q - 1) + 2 - 1 = q := by
    omega
  apply M.no_paths
  unfold RootedInstance.Solvable
  simpa only [hcount] using fact_one certificate

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The selected working core in a minimal counterexample is not type two. -/
theorem typeNumber_ne_two
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z) :
    P.working.rooted.core.typeNumber ≠ 2 := by
  classical
  intro htype
  obtain ⟨C⟩ :=
    P.exists_exteriorFeasibleBlockChoice M
      (P.otherRegion_ne_singleton M)
  cases hcore : P.working.rooted.core with
  | typeOne K =>
      simp [hcore, Core.typeNumber] at htype
  | typeTwo K =>
      exact C.false_of_typeTwo M K hcore
  | typeThree K =>
      simp [hcore, Core.typeNumber] at htype

end PreferredWorkingCoreData

end COY

end DeanK5
