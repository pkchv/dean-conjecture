import DeanK5.COYExteriorFinalDegree

/-!
# The terminal core neighbourhood at the second root

The final COY degree argument first shows that the second root has at
least `|T|` neighbours in the selected type-3 core.  When the `S`-side is
a singleton, those neighbours must be exactly `T`.  Otherwise the
singleton `S`-vertex and a further core neighbour form a triangle at the
second root, producing a reverse type-1 core and contradicting (XY1).

This file isolates that source argument from the later block-chain
bookkeeping.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.TypeThreeStage

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s : V}
  {P : PreferredWorkingCoreData G x y z}

/-- The neighbours of `v` that belong to the selected working core. -/
noncomputable def selectedCoreNeighborFinset
    (P : PreferredWorkingCoreData G x y z)
    (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w =>
    G.Adj v w ∧ w ∈ P.working.rooted.core.carrier

@[simp] theorem mem_selectedCoreNeighborFinset
    (P : PreferredWorkingCoreData G x y z)
    {v w : V} :
    w ∈ selectedCoreNeighborFinset P v ↔
      G.Adj v w ∧
        w ∈ P.working.rooted.core.carrier := by
  classical
  simp [selectedCoreNeighborFinset]

/--
At the type-three stage, two distinct neighbours of the second root cannot
be adjacent.  Such an edge would give a reverse type-one core, contradicting
the globally minimal type choice (XY1).
-/
theorem not_adj_of_otherRoot_neighbors
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    {u v : V}
    (hyu : G.Adj y u)
    (hyv : G.Adj y v) :
    ¬G.Adj u v := by
  intro huv
  have hxu : x ≠ u := by
    intro h
    subst u
    exact M.roots_not_adj hyu.symm
  have hxv : x ≠ v := by
    intro h
    subst v
    exact M.roots_not_adj hyv.symm
  let reverseTypeOne : TypeOneCore G y 1 := {
    T := {u, v}
    rank_pos := le_rfl
    card_T := by simp [huv.ne]
    root_not_mem := by
      simp [hyu.ne, hyv.ne]
    root_adj := by
      intro w hw
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hyu
      · exact hyv
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show u ≠ v → G.Adj u v from fun _ => huv)
  }
  let reverseRooted : RootedCore G y x 1 := {
    core := .typeOne reverseTypeOne
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T,
        reverseTypeOne, M.roots_ne, hxu, hxv]
  }
  have hWorkingType :
      P.working.rooted.core.typeNumber = 3 := by
    rw [D.core_eq]
    rfl
  have hChosenType :
      P.orientation.chosen.rooted.core.typeNumber = 3 := by
    rw [← P.working.typeNumber_eq_optimal]
    exact hWorkingType
  have hminimal :=
    P.orientation.type_le_core_at_other_root reverseRooted
  rw [hChosenType] at hminimal
  change 3 ≤ 1 at hminimal
  omega

/--
If the second root has at least `|T|` neighbours in the selected core,
then its core neighbourhood is exactly the terminal side `T`.

The statement is the core-neighbour calculation in the last paragraph of
the proof of COY Theorem 3.  Its only use of optimality is the exclusion
of a reverse type-1 core.
-/
theorem otherRoot_coreNeighborFinset_eq_terminal
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (hS : D.core.S = {s})
    (hcard :
      D.core.T.card ≤
        (selectedCoreNeighborFinset P y).card) :
    selectedCoreNeighborFinset P y =
        D.core.T := by
  classical
  let N : Finset V := selectedCoreNeighborFinset P y
  have hmemN (v : V) :
      v ∈ N ↔
        G.Adj y v ∧
          v ∈ P.working.rooted.core.carrier := by
    simp [N]
  have hNsubset :
      N ⊆ insert s D.core.T := by
    intro v hv
    have hvData := (hmemN v).1 hv
    have hvx : v ≠ x := by
      intro hvx
      subst v
      exact M.roots_not_adj hvData.1.symm
    have hvParts :=
      P.working.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
        hvData.2 hvx
    rcases hvParts with hvS | hvT
    · have hvSC : v ∈ D.core.S := by
        rw [D.core_eq] at hvS
        simpa only [Core.S] using hvS
      rw [hS] at hvSC
      have hvs : v = s := by
        simpa using hvSC
      simp [hvs]
    · have hvTC : v ∈ D.core.T := by
        simpa [D.core_eq, Core.T] using hvT
      simp [hvTC]
  have hNcard :
      D.core.T.card ≤ N.card := by
    simpa [N] using hcard
  by_contra hne
  have hsN : s ∈ N := by
    by_contra hs
    have hNsubsetT : N ⊆ D.core.T := by
      intro v hv
      rcases Finset.mem_insert.mp (hNsubset hv) with
        rfl | hvT
      · exact False.elim (hs hv)
      · exact hvT
    exact hne
      (Finset.eq_of_subset_of_card_le
        hNsubsetT hNcard)
  have hTtwo : 2 ≤ D.core.T.card :=
    D.two_le_terminal_card
  have hNtwo : 1 < N.card := by
    omega
  obtain ⟨t, htN, hts⟩ :=
    N.exists_mem_ne hNtwo s
  have htT : t ∈ D.core.T := by
    rcases Finset.mem_insert.mp (hNsubset htN) with
      hts' | htT
    · exact False.elim (hts hts')
    · exact htT
  have hsCore : s ∈ D.core.S := by
    rw [hS]
    simp
  have hyS : G.Adj y s :=
    ((hmemN s).1 hsN).1
  have hyT : G.Adj y t :=
    ((hmemN t).1 htN).1
  have hst : G.Adj s t :=
    (D.core.cross_adj t htT s hsCore).symm
  have hxs : x ≠ s := by
    intro h
    exact D.core.root_not_mem_S (h ▸ hsCore)
  have hxt : x ≠ t := by
    intro h
    exact D.core.root_not_mem_T (h ▸ htT)
  let reverseTypeOne : TypeOneCore G y 1 := {
    T := {s, t}
    rank_pos := le_rfl
    card_T := by simp [hts.symm]
    root_not_mem := by
      simp [hyS.ne, hyT.ne]
    root_adj := by
      intro v hv
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hyS
      · exact hyT
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show s ≠ t → G.Adj s t from fun _ => hst)
  }
  let reverseRooted : RootedCore G y x 1 := {
    core := .typeOne reverseTypeOne
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T,
        reverseTypeOne, M.roots_ne, hxs, hxt]
  }
  have hWorkingType :
      P.working.rooted.core.typeNumber = 3 := by
    rw [D.core_eq]
    rfl
  have hChosenType :
      P.orientation.chosen.rooted.core.typeNumber = 3 := by
    rw [← P.working.typeNumber_eq_optimal]
    exact hWorkingType
  have hminimal :=
    P.orientation.type_le_core_at_other_root reverseRooted
  rw [hChosenType] at hminimal
  change 3 ≤ 1 at hminimal
  omega

/-- Set-valued form of `otherRoot_coreNeighborFinset_eq_terminal`. -/
theorem otherRoot_coreNeighbors_eq_terminal
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (hS : D.core.S = {s})
    (hcard :
      D.core.T.card ≤
        (G.neighborSet y ∩
          (↑P.working.rooted.core.carrier : Set V)).ncard) :
    G.neighborSet y ∩
      (↑P.working.rooted.core.carrier : Set V) =
        (↑D.core.T : Set V) := by
  classical
  have hfinset :=
    D.otherRoot_coreNeighborFinset_eq_terminal
      M hS (by
        have hset :
            (↑(selectedCoreNeighborFinset P y) : Set V) =
              G.neighborSet y ∩
                (↑P.working.rooted.core.carrier : Set V) := by
          ext v
          simp [SimpleGraph.mem_neighborSet]
        rw [← hset, Set.ncard_coe_finset] at hcard
        exact hcard)
  ext v
  have hmem :
      v ∈ selectedCoreNeighborFinset P y ↔
        v ∈ D.core.T :=
    Iff.of_eq
      (congrArg (fun A : Finset V => v ∈ A) hfinset)
  simpa [SimpleGraph.mem_neighborSet] using hmem

/--
The final root-degree sandwich from a one-vertex exterior envelope.

The hypothesis `hyOutside` says that every neighbour of `y` outside the
selected core is the last cut vertex of the exterior block chain.  The
degree lower bound at `x` and (XY2) then force at least `|T|` core
neighbours at `y`; the preceding theorem identifies them with `T`.
-/
theorem root_degree_sandwich_of_core_envelope
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (hS : D.core.S = {s})
    {a last : V}
    (hxa : G.Adj x a)
    (haT : a ∉ D.core.T)
    (hyOutside :
      ∀ ⦃v : V⦄, G.Adj y v →
        v ∉ P.working.rooted.core.carrier →
          v = last) :
    finiteDegree G x = D.core.T.card + 1 ∧
      finiteDegree G y = D.core.T.card + 1 ∧
      G.neighborSet y =
        (↑(insert last D.core.T) : Set V) := by
  have hxLower :
      D.core.T.card + 1 ≤ finiteDegree G x :=
    D.terminal_card_add_one_le_chosenRoot_degree
      hxa haT
  have hxy :
      finiteDegree G x ≤ finiteDegree G y :=
    D.chosenRoot_degree_le_otherRoot
  let coreNeighbors : Set V :=
    G.neighborSet y ∩
      (↑P.working.rooted.core.carrier : Set V)
  have hyCover :
      G.neighborSet y ⊆
        coreNeighbors ∪ ({last} : Set V) := by
    intro v hv
    by_cases hvCore :
        v ∈ P.working.rooted.core.carrier
    · exact Or.inl ⟨hv, hvCore⟩
    · exact Or.inr (by
        simpa using hyOutside hv hvCore)
  have hyCoreUpper :
      finiteDegree G y ≤ coreNeighbors.ncard + 1 := by
    calc
      finiteDegree G y =
          (G.neighborSet y).ncard := rfl
      _ ≤
          (coreNeighbors ∪ ({last} : Set V)).ncard :=
        Set.ncard_le_ncard hyCover
      _ ≤
          coreNeighbors.ncard +
            ({last} : Set V).ncard :=
        Set.ncard_union_le _ _
      _ = coreNeighbors.ncard + 1 := by
        simp
  have hcoreCard :
      D.core.T.card ≤ coreNeighbors.ncard := by
    omega
  have hcoreEq :
      coreNeighbors = (↑D.core.T : Set V) := by
    exact D.otherRoot_coreNeighbors_eq_terminal
      M hS (by simpa [coreNeighbors] using hcoreCard)
  have hySubset :
      G.neighborSet y ⊆
        (↑(insert last D.core.T) : Set V) := by
    intro v hv
    by_cases hvCore :
        v ∈ P.working.rooted.core.carrier
    · have hvT : v ∈ D.core.T := by
        have hvIntersection :
            v ∈ coreNeighbors := ⟨hv, hvCore⟩
        rw [hcoreEq] at hvIntersection
        exact hvIntersection
      simp [hvT]
    · have hlast : v = last :=
        hyOutside hv hvCore
      simp [hlast]
  exact D.root_degree_sandwich
    hxa haT hySubset

/--
Equality in the chosen-root degree bound identifies its whole
neighbourhood with `T` and the one displayed exterior neighbour.
-/
theorem chosenRoot_neighborSet_eq_insert_terminal
    (D : P.TypeThreeStage)
    {a : V}
    (hxa : G.Adj x a)
    (haT : a ∉ D.core.T)
    (hdegree :
      finiteDegree G x = D.core.T.card + 1) :
    G.neighborSet x =
      (↑(insert a D.core.T) : Set V) := by
  have hsubset :
      (↑(insert a D.core.T) : Set V) ⊆
        G.neighborSet x := by
    intro v hv
    change v ∈ insert a D.core.T at hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hvT
    · exact hxa
    · exact D.core.root_adj_T v hvT
  have hcard :
      (G.neighborSet x).ncard ≤
        (↑(insert a D.core.T) : Set V).ncard := by
    rw [show (G.neighborSet x).ncard =
        finiteDegree G x by rfl,
      hdegree, Set.ncard_coe_finset,
      Finset.card_insert_of_notMem haT]
  exact
    (Set.eq_of_subset_of_ncard_le hsubset hcard).symm

/--
Once `N(y)=T∪{last}`, the final exterior cut has no neighbour in `T`.
Otherwise it and a terminal vertex would be adjacent neighbours of `y`,
contradicting the reverse type-one exclusion.
-/
theorem terminal_not_adj_last_of_otherRoot_neighborSet
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    {last : V}
    (hlastCore :
      last ∉ P.working.rooted.core.carrier)
    (hneighbor :
      G.neighborSet y =
        (↑(insert last D.core.T) : Set V)) :
    ∀ t ∈ D.core.T, ¬G.Adj last t := by
  intro t htT
  have hlastT : last ∉ D.core.T := by
    intro h
    apply hlastCore
    rw [D.core_eq]
    exact
      (Core.typeThree D.core).T_subset_carrier
        (by simpa [Core.T] using h)
  have hylast : G.Adj y last := by
    have : last ∈ G.neighborSet y := by
      rw [hneighbor]
      simp
    exact this
  have hyt : G.Adj y t := by
    have : t ∈ G.neighborSet y := by
      rw [hneighbor]
      simp [htT]
    exact this
  exact D.not_adj_of_otherRoot_neighbors
    M hylast hyt

end PreferredWorkingCoreData.TypeThreeStage

end COY

end DeanK5
