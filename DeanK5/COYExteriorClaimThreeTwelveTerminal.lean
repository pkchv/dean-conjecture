import DeanK5.COYCoreTCatalogue
import DeanK5.COYExteriorFeasibleBlockPathLift
import DeanK5.COYExteriorFeasibleBlockRecursive

/-!
# COY Claim 3.12(1): excluding a `T`-attachment

If the nonanchor part of the feasible block met the working core's `T`-side,
the block compression would provide `q - rank` recursive paths.  Lifting
them to `y` and combining them with the uniform `rank + 1` core catalogues
through Fact 1 would give the forbidden `q` root paths.
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

/-- The `T`-attachment alternative in Claim 3.12 is impossible. -/
theorem false_of_hasTerminalAttachment
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (hA : C.HasTerminalAttachment) :
    False := by
  classical
  have hrankStrong :
      P.working.rank + 1 < q :=
    C.rank_add_one_lt M hA
  obtain ⟨recursive⟩ :=
    C.exists_compression_recursive_family M hA
  obtain ⟨outer⟩ :=
    C.exists_liftedTerminalToYData recursive
  have hinnerOne :
      1 ≤ P.working.rank + 1 := by
    omega
  have hinnerFour :
      P.working.rank + 1 ≤ 4 := by
    have hqFour := M.q_le_four
    omega
  let catalogue :=
    P.working.rooted.core.uniformTCatalogue
      (P.working.rank + 1)
      hinnerOne hinnerFour le_rfl
  have hendpointT (i : Fin (q - P.working.rank)) :
      outer.family.endpoint i ∈
        P.working.rooted.core.T :=
    C.terminalAttachments_subset_coreT
      (outer.family.endpoint_mem i)
  let inner (i : Fin (q - P.working.rank)) :
      SemiAdmissiblePathFamily G x
        (outer.family.endpoint i)
        (P.working.rank + 1) :=
    catalogue.family
      (outer.family.endpoint i) (hendpointT i)
  have hxNotAttachments :
      x ∉ (↑C.terminalAttachments : Set V) := by
    intro hx
    exact P.working.rooted.core.root_not_mem_T
      (C.terminalAttachments_subset_coreT hx)
  have hyNotAttachments :
      y ∉ (↑C.terminalAttachments : Set V) := by
    intro hy
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        P.working.rooted.other_root_mem_otherRegion
        (P.working.rooted.core.T_subset_carrier
          (C.terminalAttachments_subset_coreT hy))
  let certificate :
      FactOneCertificate G x y
        (↑C.terminalAttachments : Set V)
        (q - P.working.rank)
        (P.working.rank + 1) := {
    hs := by omega
    ht := hinnerOne
    x_ne_y := M.roots_ne
    x_not_mem := hxNotAttachments
    y_not_mem := hyNotAttachments
    outer := outer.family
    inner := inner
    equal_inner_length := by
      intro i j
      exact catalogue.equal_length
        (outer.family.endpoint i)
        (outer.family.endpoint
          (firstFin (by omega :
            1 ≤ q - P.working.rank)))
        (hendpointT i)
        (hendpointT
          (firstFin (by omega :
            1 ≤ q - P.working.rank)))
        j
    avoid_outer := by
      intro i j
      apply List.disjoint_left.mpr
      intro v hvInner hvOuterTail
      have hvCore :
          v ∈ P.working.rooted.core.carrier :=
        catalogue.support
          (outer.family.endpoint i)
          (hendpointT i) j v
          (by simpa [inner] using hvInner)
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
      (q - P.working.rank) +
          (P.working.rank + 1) - 1 = q := by
    omega
  apply M.no_paths
  unfold RootedInstance.Solvable
  simpa only [hcount] using fact_one certificate

/-- COY Claim 3.12(1): no working-core `T`-vertex meets `B - b`. -/
theorem terminalAttachments_eq_empty
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice) :
    C.terminalAttachments = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hA
  exact C.false_of_hasTerminalAttachment M hA

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
