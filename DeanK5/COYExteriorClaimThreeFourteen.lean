import DeanK5.COYExteriorClaimThreeFourteenDeletion

/-!
# COY Claim 3.14

At the post-Claim-3.13 stage the working core is type 3 with singleton
`S`.  Claim 3.8 supplies a `T`-attachment to the nonsingleton exterior.
The stronger part of COY Fact 3 (itself proved from Fact 2(2)) then forces
`q ≥ 3`.

If the exception lies in the selected exterior, that attachment cannot
occur only at `y`.  Otherwise deleting the rest of the exterior gives the
strictly smaller rooted instance formalized in
`COYExteriorClaimThreeFourteenDeletion`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s : V}
  {P : PreferredWorkingCoreData G x y z}

/--
COY Claim 3.14(1): the singleton-side type-3 stage lies in the range
`q ≥ 3`.

The strict inequality is exactly the `T`-attachment clause of Fact 3,
whose proof applies the type-3 Fact 2(2) catalogue to a fixed exterior
connector.
-/
theorem three_le_q_of_typeThree_singleton_side
    (M : MinimalCounterexample q G x y z)
    (C : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree C)
    (hS : C.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    3 ≤ q := by
  have hScard : C.S.card = 1 := by
    rw [hS]
    simp
  have hattach :
      P.working.rooted.core.HasTAttachment
        P.working.rooted.otherRegion := by
    have hattach' :
        (Core.typeThree C).HasTAttachment
          P.working.rooted.otherRegion :=
      hasTAttachment_of_typeThree_card_S_one
        M P C hcore hScard hregion
    simpa [hcore] using hattach'
  have hstrong :
      P.working.rank + 1 < q :=
    (M.rootedCore_factThree P.working.rooted).2 hattach
  have hrank : P.working.rank = 1 := by
    have hcard := C.card_S
    rw [hS] at hcard
    simp at hcard
    omega
  omega

/--
COY Claim 3.14(2): when `z` lies in the selected exterior, some
`T`-vertex is adjacent to an exterior vertex other than `y`.
-/
theorem hasTAttachmentAwayFromY_of_exception_mem
    (M : MinimalCounterexample q G x y z)
    (C : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree C)
    (hS : C.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hz : z ∈ P.working.rooted.otherRegion) :
    P.HasTAttachmentAwayFromY C := by
  by_contra hno
  obtain ⟨D⟩ :=
    TypeThreeExteriorDeletion.exists_data
      M C hcore s hS hregion hz hno
  exact D.false_of_data M

/-- Claim 3.14(2) in the literal deleted-component form `C-y`. -/
theorem exists_T_attachment_in_otherRegion_erase_y
    (M : MinimalCounterexample q G x y z)
    (C : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree C)
    (hS : C.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hz : z ∈ P.working.rooted.otherRegion) :
    ∃ a ∈ P.working.rooted.otherRegion.erase y,
      ∃ t ∈ C.T, G.Adj t a := by
  obtain ⟨a, haQ, hay, t, htT, hta⟩ :=
    hasTAttachmentAwayFromY_of_exception_mem
      M C hcore hS hregion hz
  exact ⟨a, Finset.mem_erase.mpr ⟨hay, haQ⟩,
    t, htT, hta⟩

/-- The two conclusions of COY Claim 3.14 in one source-shaped theorem. -/
theorem claim_three_fourteen
    (M : MinimalCounterexample q G x y z)
    (C : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree C)
    (hS : C.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    3 ≤ q ∧
      (z ∈ P.working.rooted.otherRegion →
        P.HasTAttachmentAwayFromY C) :=
  ⟨three_le_q_of_typeThree_singleton_side
      M C hcore hS hregion,
    hasTAttachmentAwayFromY_of_exception_mem
      M C hcore hS hregion⟩

end PreferredWorkingCoreData

end COY

end DeanK5
