import DeanK5.COYExteriorZEndBlock
import DeanK5.COYProtectedIndependence

/-!
# Protected vertices in the selected COY exterior

The protected set in the exterior graph is the intersection of that
component with the two ambient vertices `y` and `z`.  This file records the
corresponding subtype finset and the elementary cardinality facts used in
the block argument for COY Claim 3.11.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
The protected vertices that actually occur in the selected exterior
component.
-/
noncomputable def exteriorProtected
    (P : PreferredWorkingCoreData G x y z) :
    Finset P.ExteriorVertex :=
  Finset.univ.filter fun v => v.1 = y ∨ v.1 = z

/-- Membership in the exterior protected set is ambient membership in
`{y, z}`. -/
@[simp] theorem mem_exteriorProtected
    (P : PreferredWorkingCoreData G x y z)
    {v : P.ExteriorVertex} :
    v ∈ P.exteriorProtected ↔ v.1 = y ∨ v.1 = z := by
  classical
  simp [exteriorProtected]

/-- The second root is always protected in the selected exterior. -/
@[simp] theorem exteriorY_mem_exteriorProtected
    (P : PreferredWorkingCoreData G x y z) :
    P.exteriorY ∈ P.exteriorProtected := by
  simp [exteriorY]

/-- If the exceptional vertex lies in the exterior, its subtype copy is
protected. -/
@[simp] theorem exteriorZ_mem_exteriorProtected
    (P : PreferredWorkingCoreData G x y z)
    (hz : z ∈ P.working.rooted.otherRegion) :
    P.exteriorZ hz ∈ P.exteriorProtected := by
  simp [exteriorZ]

/-- When `z` lies in the exterior, the protected set is represented by the
two canonical subtype vertices. -/
theorem exteriorProtected_eq_pair
    (P : PreferredWorkingCoreData G x y z)
    (hz : z ∈ P.working.rooted.otherRegion) :
    P.exteriorProtected = {P.exteriorY, P.exteriorZ hz} := by
  classical
  ext v
  simp only [mem_exteriorProtected, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (hvy | hvz)
    · exact Or.inl (Subtype.ext hvy)
    · exact Or.inr (Subtype.ext hvz)
  · rintro (hvy | hvz)
    · exact Or.inl (congrArg Subtype.val hvy)
    · exact Or.inr (congrArg Subtype.val hvz)

/-- When `z` does not lie in the exterior, only the second root is
protected there. -/
theorem exteriorProtected_eq_singleton_of_exception_not_mem
    (P : PreferredWorkingCoreData G x y z)
    (hz : z ∉ P.working.rooted.otherRegion) :
    P.exteriorProtected = {P.exteriorY} := by
  classical
  ext v
  simp only [mem_exteriorProtected, Finset.mem_singleton]
  constructor
  · rintro (hvy | hvz)
    · exact Subtype.ext hvy
    · exact False.elim (hz (by simpa [hvz] using v.2))
  · intro hvy
    exact Or.inl (congrArg Subtype.val hvy)

/-- At most two vertices of the exterior graph are protected. -/
theorem exteriorProtected_card_le_two
    (P : PreferredWorkingCoreData G x y z) :
    P.exteriorProtected.card ≤ 2 := by
  classical
  by_cases hz : z ∈ P.working.rooted.otherRegion
  · rw [P.exteriorProtected_eq_pair hz]
    simpa using
      (Finset.card_insert_le P.exteriorY
        ({P.exteriorZ hz} : Finset P.ExteriorVertex))
  · rw [P.exteriorProtected_eq_singleton_of_exception_not_mem hz]
    simp

/-- The selected exterior graph is connected. -/
theorem exteriorGraph_connected
    (P : PreferredWorkingCoreData G x y z) :
    P.exteriorGraph.Connected :=
  P.working.rooted.otherRegion_componentRegion.connected

/-- A nonsingleton exterior has a nontrivial subtype of vertices. -/
theorem exteriorVertex_nontrivial_of_otherRegion_ne_singleton
    (P : PreferredWorkingCoreData G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    Nontrivial P.ExteriorVertex := by
  classical
  have hother :
      ∃ v ∈ P.working.rooted.otherRegion, v ≠ y := by
    by_contra h
    push Not at h
    apply hregion
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨P.working.rooted.other_root_mem_otherRegion,
      fun v hv => h v hv⟩
  obtain ⟨v, hvRegion, hvy⟩ := hother
  refine ⟨⟨⟨v, hvRegion⟩, P.exteriorY, ?_⟩⟩
  intro h
  exact hvy (congrArg Subtype.val h)

/-- A nonsingleton exterior contains at least two vertices. -/
theorem one_lt_exteriorVertex_card
    (P : PreferredWorkingCoreData G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    1 < Fintype.card P.ExteriorVertex := by
  letI : Nontrivial P.ExteriorVertex :=
    P.exteriorVertex_nontrivial_of_otherRegion_ne_singleton hregion
  exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance

/--
In a minimal counterexample, a nonsingleton exterior has an unprotected
vertex.  Indeed, connectedness gives a neighbor of `y`; looplessness keeps
it distinct from `y`, and Claim 3.2(2) keeps it distinct from `z`.
-/
theorem exists_exteriorVertex_not_mem_exteriorProtected
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    ∃ v : P.ExteriorVertex, v ∉ P.exteriorProtected := by
  classical
  letI : Nontrivial P.ExteriorVertex :=
    P.exteriorVertex_nontrivial_of_otherRegion_ne_singleton hregion
  obtain ⟨v, hyv⟩ :=
    P.exteriorGraph_connected.preconnected.exists_adj_of_nontrivial
      P.exteriorY
  have hyvAmbient : G.Adj y v.1 := by
    exact hyv
  refine ⟨v, ?_⟩
  simp only [mem_exteriorProtected]
  push Not
  constructor
  · exact hyvAmbient.ne'
  · intro hvz
    apply M.right_root_not_adj_exception
    simpa [hvz] using hyvAmbient

/-- In a nonsingleton exterior of a minimal counterexample, the protected
set is a proper subset of the full vertex set. -/
theorem exteriorProtected_card_lt_exteriorVertex_card
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    P.exteriorProtected.card < Fintype.card P.ExteriorVertex := by
  classical
  obtain ⟨v, hv⟩ :=
    P.exists_exteriorVertex_not_mem_exteriorProtected M hregion
  rw [← Finset.card_univ]
  exact Finset.card_lt_card
    (Finset.ssubset_iff.mpr
      ⟨v, hv, Finset.subset_univ (insert v P.exteriorProtected)⟩)

end PreferredWorkingCoreData

end COY

end DeanK5
