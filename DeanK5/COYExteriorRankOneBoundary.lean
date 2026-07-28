import DeanK5.COYExteriorTypeThreeStage

/-!
# The rank-one exterior boundary

At the post-Claim-3.13 stage, the type-three side `S` has one vertex.
Claim 3.12 then identifies the entire working-core attachment set of
`B - b` with the pair `{x,s}`.  This is equation (3.2) in COY.
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

/-- All working-core vertices adjacent to the interior `B - b`. -/
noncomputable def coreAttachments
    (C : P.ExteriorFeasibleBlockChoice) : Finset V :=
  by
    classical
    exact P.working.rooted.core.carrier.filter fun v =>
      ∃ d ∈ C.compressionInterior, G.Adj v d

@[simp] theorem mem_coreAttachments
    (C : P.ExteriorFeasibleBlockChoice) {v : V} :
    v ∈ C.coreAttachments ↔
      v ∈ P.working.rooted.core.carrier ∧
        ∃ d ∈ C.compressionInterior, G.Adj v d := by
  classical
  simp [coreAttachments]

/--
After Claim 3.12(1), the full core attachment set equals the initial-side
boundary.
-/
theorem coreAttachments_eq_initialBoundary
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice) :
    C.coreAttachments = C.initialBoundary := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨hvCore, d, hd, hvd⟩ :=
      C.mem_coreAttachments.mp hv
    exact C.core_attachment_mem_initialBoundary
      M hvCore hd hvd
  · intro v hv
    obtain ⟨hvRootS, d, hd, hvd⟩ :=
      C.mem_initialBoundary.mp hv
    have hvCore :
        v ∈ P.working.rooted.core.carrier := by
      rcases Finset.mem_insert.mp hvRootS with rfl | hvS
      · exact P.working.rooted.core.root_mem_carrier
      · exact P.working.rooted.core.S_subset_carrier hvS
    exact C.mem_coreAttachments.mpr
      ⟨hvCore, ⟨d, hd, hvd⟩⟩

/--
For a rank-one type-three working core, `S = {s}` and the initial boundary
is exactly `{x,s}`.
-/
theorem exists_side_eq_singleton_and_initialBoundary_eq_pair
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (K : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree K)
    (hrank : P.working.rank = 1) :
    ∃ s, K.S = {s} ∧ C.initialBoundary = {x, s} := by
  classical
  have hScard : K.S.card = 1 := by
    rw [K.card_S, hrank]
  obtain ⟨s, hS⟩ :=
    Finset.card_eq_one.mp hScard
  have hsubset :
      C.initialBoundary ⊆ {x, s} := by
    intro v hv
    have hvRootS :=
      (C.mem_initialBoundary.mp hv).1
    simpa [hcore, Core.S, hS] using hvRootS
  have hpairCard :
      ({x, s} : Finset V).card = 2 := by
    have hxs : x ≠ s := by
      intro h
      apply K.root_not_mem_S
      rw [hS]
      simp [h]
    simp [hxs]
  have hpairLe :
      ({x, s} : Finset V).card ≤
        C.initialBoundary.card := by
    rw [hpairCard]
    exact C.two_le_initialBoundary_card M
  have hboundary :
      C.initialBoundary = {x, s} :=
    Finset.eq_of_subset_of_card_le hsubset hpairLe
  exact ⟨s, hS, hboundary⟩

/--
Equation (3.2): every core endpoint of an edge into `B - b`, and no other
core vertex, belongs to `{x,s}`.
-/
theorem exists_side_eq_singleton_and_coreAttachments_eq_pair
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (K : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree K)
    (hrank : P.working.rank = 1) :
    ∃ s, K.S = {s} ∧ C.coreAttachments = {x, s} := by
  obtain ⟨s, hS, hboundary⟩ :=
    C.exists_side_eq_singleton_and_initialBoundary_eq_pair
      M K hcore hrank
  exact ⟨s, hS,
    (C.coreAttachments_eq_initialBoundary M).trans hboundary⟩

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
