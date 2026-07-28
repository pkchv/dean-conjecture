import DeanK5.COYExteriorClaimThreeThirteenTypes

/-!
# The two-path catalogues in COY Claim 3.13

At rank one, each temporary Type I or Type II exterior witness supplies two
admissible paths from the root to every vertex of the old `S`-side.  The
paths have lengths `2,4` in Type I and `2,3` in Type II.  Their supports are
certified to lie in the old core together with the one exterior witness.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace TypeThreeCore

variable [DecidableEq V]
  {G : SimpleGraph V} {x target v₀ : V} {ℓ : ℕ}

/-- Two paths to one `S`-endpoint, with their common augmented support. -/
structure AugmentedTwoPathData
    (K : TypeThreeCore G x ℓ)
    (v₀ target : V) (step : ℕ) where
  /-- The two admissible paths. -/
  family : AdmissiblePathFamily G x target 2
  /-- The first path has length two. -/
  family_start : family.start = 2
  /-- The packaged common difference is exact. -/
  family_step : family.step = step
  /-- Both paths stay in the old core together with `v₀`. -/
  support :
    ∀ i v, v ∈ (family.path i).walk.support →
      v ∈ insert v₀ (Core.typeThree K).carrier

/--
Endpoint-uniform two-path catalogues supported in a type-three core
together with one exterior vertex.
-/
structure UniformAugmentedTwoCatalogue
    (K : TypeThreeCore G x ℓ) (v₀ : V) where
  /-- The endpoint-independent common difference. -/
  step : ℕ
  /-- The catalogue to each old `S`-vertex. -/
  family :
    ∀ target : V, target ∈ K.S →
      AdmissiblePathFamily G x target 2
  /-- Every catalogue starts at length two. -/
  family_start :
    ∀ target htarget, (family target htarget).start = 2
  /-- Every catalogue has the packaged common difference. -/
  family_step :
    ∀ target htarget, (family target htarget).step = step
  /-- Every path stays in the common augmented carrier. -/
  support :
    ∀ target htarget i v,
      v ∈ ((family target htarget).path i).walk.support →
        v ∈ insert v₀ (Core.typeThree K).carrier

namespace UniformAugmentedTwoCatalogue

variable {K : TypeThreeCore G x ℓ}

/-- Corresponding paths to different `S`-endpoints have equal lengths. -/
theorem equal_length
    (U : K.UniformAugmentedTwoCatalogue v₀)
    (target₁ target₂ : V)
    (htarget₁ : target₁ ∈ K.S)
    (htarget₂ : target₂ ∈ K.S)
    (i : Fin 2) :
    ((U.family target₁ htarget₁).path i).length =
      ((U.family target₂ htarget₂).path i).length := by
  rw [
    (U.family target₁ htarget₁).length_path i,
    (U.family target₂ htarget₂).length_path i,
    U.family_start target₁ htarget₁,
    U.family_start target₂ htarget₂,
    U.family_step target₁ htarget₁,
    U.family_step target₂ htarget₂]

end UniformAugmentedTwoCatalogue

end TypeThreeCore

namespace PreferredWorkingCoreData.TypeThreeStage

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}
  {D : P.TypeThreeStage}

namespace TypeIWitness

/-- The explicit length-`2,4` paths supplied by a Type I witness. -/
noncomputable def augmentedTwoPathData
    (W : D.TypeIWitness)
    (hrank : P.working.rank = 1)
    (target : V) (htarget : target ∈ D.core.S) :
    D.core.AugmentedTwoPathData
      W.ordinary.vertex.1 target 2 := by
  classical
  have hcard :
      (D.terminalNeighborFinset
        W.ordinary.vertex.1).card = 2 :=
    W.terminal_neighbors_card_eq_two hrank
  let terminal : Fin 2 ↪ V :=
    finsetEmbeddingOfCardEq
      (D.terminalNeighborFinset
        W.ordinary.vertex.1) hcard
  let t₀ : V := terminal 0
  let t₁ : V := terminal 1
  have htne : t₀ ≠ t₁ :=
    terminal.injective.ne (by decide)
  have ht₀N :
      t₀ ∈ D.terminalNeighborFinset
        W.ordinary.vertex.1 := by
    exact finsetEmbeddingOfCardEq_mem
      (D.terminalNeighborFinset
        W.ordinary.vertex.1) hcard 0
  have ht₁N :
      t₁ ∈ D.terminalNeighborFinset
        W.ordinary.vertex.1 := by
    exact finsetEmbeddingOfCardEq_mem
      (D.terminalNeighborFinset
        W.ordinary.vertex.1) hcard 1
  have ht₀ :=
    (D.mem_terminalNeighborFinset.mp ht₀N)
  have ht₁ :=
    (D.mem_terminalNeighborFinset.mp ht₁N)
  have hvOutside :
      W.ordinary.vertex.1 ∉
        (Core.typeThree D.core).carrier := by
    have hv :=
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        W.mem_otherRegion
    simpa [D.core_eq] using hv
  have hxt₀ : G.Adj x t₀ :=
    D.core.root_adj_T t₀ ht₀.1
  have hxt₁ : G.Adj x t₁ :=
    D.core.root_adj_T t₁ ht₁.1
  have ht₀Target : G.Adj t₀ target :=
    D.core.cross_adj t₀ ht₀.1 target htarget
  have ht₁Target : G.Adj t₁ target :=
    D.core.cross_adj t₁ ht₁.1 target htarget
  have hxTarget : x ≠ target := by
    intro h
    exact D.core.root_not_mem_S (h ▸ htarget)
  have hvx : W.ordinary.vertex.1 ≠ x := by
    intro h
    apply hvOutside
    rw [h]
    exact (Core.typeThree D.core).root_mem_carrier
  have hvTarget : W.ordinary.vertex.1 ≠ target := by
    intro h
    apply hvOutside
    rw [h]
    exact (Core.typeThree D.core).S_subset_carrier
      (by simpa [Core.S] using htarget)
  let p₂ : SimplePath G x target :=
    SimplePath.ofVertexList [t₀]
      (by simp [hxt₀, ht₀Target])
      (by simp [hxTarget, hxt₀.ne, ht₀Target.ne])
  let p₄ : SimplePath G x target :=
    SimplePath.ofVertexList
      [t₀, W.ordinary.vertex.1, t₁]
      (by
        simp [hxt₀, ht₀.2.symm, ht₁.2,
          ht₁Target])
      (by
        simp [hxTarget, hxt₀.ne, hvx.symm,
          hxt₁.ne, ht₀.2.ne.symm, htne,
          ht₀Target.ne, ht₁.2.ne,
          hvTarget, ht₁Target.ne])
  have hp₂Support (v : V)
      (hv : v ∈ p₂.walk.support) :
      v = x ∨ v = t₀ ∨ v = target := by
    simpa [p₂, SimplePath.ofVertexList_support] using hv
  have hp₄Support (v : V)
      (hv : v ∈ p₄.walk.support) :
      v = x ∨ v = t₀ ∨
        v = W.ordinary.vertex.1 ∨
          v = t₁ ∨ v = target := by
    simpa [p₄, SimplePath.ofVertexList_support] using hv
  have hxAugmented :
      x ∈ insert W.ordinary.vertex.1
        (Core.typeThree D.core).carrier :=
    Finset.mem_insert_of_mem
      (Core.typeThree D.core).root_mem_carrier
  have ht₀Augmented :
      t₀ ∈ insert W.ordinary.vertex.1
        (Core.typeThree D.core).carrier :=
    Finset.mem_insert_of_mem
      ((Core.typeThree D.core).T_subset_carrier
        (by simpa [Core.T] using ht₀.1))
  have ht₁Augmented :
      t₁ ∈ insert W.ordinary.vertex.1
        (Core.typeThree D.core).carrier :=
    Finset.mem_insert_of_mem
      ((Core.typeThree D.core).T_subset_carrier
        (by simpa [Core.T] using ht₁.1))
  have htargetAugmented :
      target ∈ insert W.ordinary.vertex.1
        (Core.typeThree D.core).carrier :=
    Finset.mem_insert_of_mem
      ((Core.typeThree D.core).S_subset_carrier
        (by simpa [Core.S] using htarget))
  have hvAugmented :
      W.ordinary.vertex.1 ∈
        insert W.ordinary.vertex.1
          (Core.typeThree D.core).carrier :=
    Finset.mem_insert_self _ _
  let family : AdmissiblePathFamily G x target 2 := {
    start := 2
    step := 2
    admissible_step := Or.inr rfl
    start_ge_two := le_rfl
    path := ![p₂, p₄]
    length_path := by
      intro i
      fin_cases i <;> simp [p₂, p₄]
  }
  exact {
    family := family
    family_start := rfl
    family_step := rfl
    support := by
      intro i v hv
      change v ∈ (![p₂, p₄] i).walk.support at hv
      fin_cases i
      · have hv' := hp₂Support v hv
        rcases hv' with rfl | rfl | rfl
        · exact hxAugmented
        · exact ht₀Augmented
        · exact htargetAugmented
      · have hv' := hp₄Support v hv
        rcases hv' with rfl | rfl | rfl | rfl | rfl
        · exact hxAugmented
        · exact ht₀Augmented
        · exact hvAugmented
        · exact ht₁Augmented
        · exact htargetAugmented
  }

/-- The endpoint-uniform Type I catalogue. -/
noncomputable def uniformAugmentedTwoCatalogue
    (W : D.TypeIWitness)
    (hrank : P.working.rank = 1) :
    D.core.UniformAugmentedTwoCatalogue
      W.ordinary.vertex.1 where
  step := 2
  family target htarget :=
    (W.augmentedTwoPathData hrank target htarget).family
  family_start target htarget :=
    (W.augmentedTwoPathData hrank target htarget).family_start
  family_step target htarget :=
    (W.augmentedTwoPathData hrank target htarget).family_step
  support target htarget :=
    (W.augmentedTwoPathData hrank target htarget).support

end TypeIWitness

namespace TypeIIWitness

/-- The explicit length-`2,3` paths supplied by a Type II witness. -/
noncomputable def augmentedTwoPathData
    (W : D.TypeIIWitness)
    (target : V) (htarget : target ∈ D.core.S) :
    D.core.AugmentedTwoPathData
      W.ordinary.vertex.1 target 1 := by
  classical
  let initial : Fin 1 ↪ V :=
    finsetEmbeddingOfCardEq
      (D.initialNeighborFinset
        W.ordinary.vertex.1)
      W.initial_neighbor_card
  let terminal : Fin 1 ↪ V :=
    finsetEmbeddingOfCardEq
      (D.terminalNeighborFinset
        W.ordinary.vertex.1)
      W.terminal_neighbor_card
  let s₀ : V := initial 0
  let t : V := terminal 0
  have hs₀N :
      s₀ ∈ D.initialNeighborFinset
        W.ordinary.vertex.1 := by
    exact finsetEmbeddingOfCardEq_mem
      (D.initialNeighborFinset
        W.ordinary.vertex.1)
      W.initial_neighbor_card 0
  have htN :
      t ∈ D.terminalNeighborFinset
        W.ordinary.vertex.1 := by
    exact finsetEmbeddingOfCardEq_mem
      (D.terminalNeighborFinset
        W.ordinary.vertex.1)
      W.terminal_neighbor_card 0
  have hs₀ :=
    D.mem_initialNeighborFinset.mp hs₀N
  have ht :=
    D.mem_terminalNeighborFinset.mp htN
  have hScard : D.core.S.card = 1 := by
    rw [D.core.card_S, W.rank_eq_one]
  have htargetEq : target = s₀ := by
    exact
      Finset.card_le_one.mp (by omega)
        target htarget s₀ hs₀.1
  have hvTarget :
      G.Adj W.ordinary.vertex.1 target := by
    simpa [htargetEq] using hs₀.2
  have hvOutside :
      W.ordinary.vertex.1 ∉
        (Core.typeThree D.core).carrier := by
    have hv :=
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        W.mem_otherRegion
    simpa [D.core_eq] using hv
  have hxt : G.Adj x t :=
    D.core.root_adj_T t ht.1
  have htTarget : G.Adj t target :=
    D.core.cross_adj t ht.1 target htarget
  have hxTarget : x ≠ target := by
    intro h
    exact D.core.root_not_mem_S (h ▸ htarget)
  have hvx : W.ordinary.vertex.1 ≠ x := by
    intro h
    apply hvOutside
    rw [h]
    exact (Core.typeThree D.core).root_mem_carrier
  let p₂ : SimplePath G x target :=
    SimplePath.ofVertexList [t]
      (by simp [hxt, htTarget])
      (by simp [hxTarget, hxt.ne, htTarget.ne])
  let p₃ : SimplePath G x target :=
    SimplePath.ofVertexList
      [t, W.ordinary.vertex.1]
      (by simp [hxt, ht.2.symm, hvTarget])
      (by
        simp [hxTarget, hxt.ne, hvx.symm,
          ht.2.ne.symm, htTarget.ne,
          hvTarget.ne])
  have hp₂Support (v : V)
      (hv : v ∈ p₂.walk.support) :
      v = x ∨ v = t ∨ v = target := by
    simpa [p₂, SimplePath.ofVertexList_support] using hv
  have hp₃Support (v : V)
      (hv : v ∈ p₃.walk.support) :
      v = x ∨ v = t ∨
        v = W.ordinary.vertex.1 ∨
          v = target := by
    simpa [p₃, SimplePath.ofVertexList_support] using hv
  have hxAugmented :
      x ∈ insert W.ordinary.vertex.1
        (Core.typeThree D.core).carrier :=
    Finset.mem_insert_of_mem
      (Core.typeThree D.core).root_mem_carrier
  have htAugmented :
      t ∈ insert W.ordinary.vertex.1
        (Core.typeThree D.core).carrier :=
    Finset.mem_insert_of_mem
      ((Core.typeThree D.core).T_subset_carrier
        (by simpa [Core.T] using ht.1))
  have htargetAugmented :
      target ∈ insert W.ordinary.vertex.1
        (Core.typeThree D.core).carrier :=
    Finset.mem_insert_of_mem
      ((Core.typeThree D.core).S_subset_carrier
        (by simpa [Core.S] using htarget))
  have hvAugmented :
      W.ordinary.vertex.1 ∈
        insert W.ordinary.vertex.1
          (Core.typeThree D.core).carrier :=
    Finset.mem_insert_self _ _
  let family : AdmissiblePathFamily G x target 2 := {
    start := 2
    step := 1
    admissible_step := Or.inl rfl
    start_ge_two := le_rfl
    path := ![p₂, p₃]
    length_path := by
      intro i
      fin_cases i <;> simp [p₂, p₃]
  }
  exact {
    family := family
    family_start := rfl
    family_step := rfl
    support := by
      intro i v hv
      change v ∈ (![p₂, p₃] i).walk.support at hv
      fin_cases i
      · have hv' := hp₂Support v hv
        rcases hv' with rfl | rfl | rfl
        · exact hxAugmented
        · exact htAugmented
        · exact htargetAugmented
      · have hv' := hp₃Support v hv
        rcases hv' with rfl | rfl | rfl | rfl
        · exact hxAugmented
        · exact htAugmented
        · exact hvAugmented
        · exact htargetAugmented
  }

/-- The endpoint-uniform Type II catalogue. -/
noncomputable def uniformAugmentedTwoCatalogue
    (W : D.TypeIIWitness) :
    D.core.UniformAugmentedTwoCatalogue
      W.ordinary.vertex.1 where
  step := 1
  family target htarget :=
    (W.augmentedTwoPathData target htarget).family
  family_start target htarget :=
    (W.augmentedTwoPathData target htarget).family_start
  family_step target htarget :=
    (W.augmentedTwoPathData target htarget).family_step
  support target htarget :=
    (W.augmentedTwoPathData target htarget).support

end TypeIIWitness

end PreferredWorkingCoreData.TypeThreeStage

end COY

end DeanK5
