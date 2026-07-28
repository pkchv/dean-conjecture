import DeanK5.COYExteriorClaimThreeTen
import DeanK5.COYExteriorProtected
import DeanK5.Graph.NoFeasibleDegree

/-!
# The terminal endpoint in COY Claim 3.11

In the degree-two end-block branch, Claim 3.9 applies only after proving
that the second neighbor `b'_z` is not the other root `y`.  Under the
no-feasible-block hypothesis, `y` has exterior degree at most one.  Thus,
if `b'_z = y`, the three vertices `z`, `b_z`, and `y` are closed under
exterior adjacency.  Connectedness would make them the entire exterior,
contrary to Claim 3.10.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

namespace ExteriorZEndBlock

/--
If no exterior block is feasible, the second neighbor of a degree-two
`z`-end block is not the other root.
-/
theorem bPrime_ne_y_of_no_feasibleBlock
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hnoFeasible :
      ∀ B : GraphBlock P.exteriorGraph,
        ¬IsFeasibleBlock
          P.exteriorGraph P.exteriorProtected B) :
    E.bPrime ≠ y := by
  intro hPrimeY
  have hPrimeYSub :
      E.certificate.bPrime = P.exteriorY := by
    apply Subtype.ext
    exact hPrimeY
  have hyzSub :
      P.exteriorY ≠
        P.exteriorZ E.z_mem_otherRegion := by
    intro h
    apply E.y_ne_z
    exact congrArg Subtype.val h
  have hyDegreeLe :
      finiteDegree P.exteriorGraph P.exteriorY ≤ 1 := by
    have hbound :=
      finiteDegree_le_card_erase_of_no_feasibleBlock
        P.exteriorGraph_connected P.exteriorProtected
          P.exteriorProtected_card_le_two
          hnoFeasible P.exteriorY
    rw [P.exteriorProtected_eq_pair
      E.z_mem_otherRegion] at hbound
    simpa [hyzSub] using hbound
  have hyAdjBz :
      P.exteriorGraph.Adj
        P.exteriorY E.certificate.bz := by
    simpa only [hPrimeYSub] using
      E.certificate.bz_adj_bPrime.symm
  have hyNeighborSet :
      P.exteriorGraph.neighborSet P.exteriorY =
        {E.certificate.bz} := by
    apply
      (Set.eq_of_subset_of_ncard_le
        (s := ({E.certificate.bz} :
          Set P.ExteriorVertex))
        (t := P.exteriorGraph.neighborSet
          P.exteriorY) ?_ ?_).symm
    · intro v hv
      have hvbz : v = E.certificate.bz := by
        simpa only [Set.mem_singleton_iff] using hv
      subst v
      exact hyAdjBz
    · unfold finiteDegree at hyDegreeLe
      simpa only [Set.ncard_singleton] using
        hyDegreeLe
  let A : P.ExteriorVertex → Prop := fun v =>
    v = P.exteriorZ E.z_mem_otherRegion ∨
      v = E.certificate.bz ∨
        v = P.exteriorY
  have hclosed :
      ∀ ⦃u v : P.ExteriorVertex⦄,
        A u → P.exteriorGraph.Adj u v → A v := by
    intro u v hu huv
    rcases hu with huz | hub | huy
    · subst u
      exact
        Or.inr (Or.inl
          ((E.certificate.adj_z_iff v).mp huv))
    · subst u
      rcases
          (E.certificate.adj_bz_iff v).mp huv with
        hvz | hvPrime
      · exact Or.inl hvz
      · exact
          Or.inr (Or.inr
            (hvPrime.trans hPrimeYSub))
    · subst u
      have hv :
          v ∈ P.exteriorGraph.neighborSet
            P.exteriorY := huv
      rw [hyNeighborSet] at hv
      exact
        Or.inr (Or.inl (by simpa using hv))
  have hpropOfWalk :
      ∀ {u v : P.ExteriorVertex},
        P.exteriorGraph.Walk u v → A u → A v := by
    intro u v p hu
    induction p with
    | nil => exact hu
    | @cons a b c hab p ih =>
        exact ih (hclosed hu hab)
  have hall : ∀ v : P.ExteriorVertex, A v := by
    intro v
    obtain ⟨p⟩ :=
      P.exteriorGraph_connected.preconnected
        (P.exteriorZ E.z_mem_otherRegion) v
    exact hpropOfWalk p (Or.inl rfl)
  apply E.not_isOrderThreePath M
  ext v
  constructor
  · intro hv
    rcases hall ⟨v, hv⟩ with hvz | hvb | hvy
    · exact
        Finset.mem_insert.mpr
          (Or.inl (congrArg Subtype.val hvz))
    · exact
        Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr
            (Or.inl (congrArg Subtype.val hvb))))
    · exact
        Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr
              (congrArg Subtype.val hvy)))))
  · intro hv
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact E.z_mem_otherRegion
    · exact E.bz_mem_otherRegion
    · exact
        P.working.rooted.other_root_mem_otherRegion

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
