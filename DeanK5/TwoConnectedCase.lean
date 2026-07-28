import DeanK5.GirthSixCase
import DeanK5.BGLPConnectivityInternal

/-!
# The two-connected minimum-degree-five case

The machinery of Sections 4--7 applies directly to a two-connected graph
whose minimum degree is already five: the deficient set is empty.  To reuse
the common `StandingSetup` interface, this file adjoins an isolated
bookkeeping root.  A separate triangle-contraction branch in
`SmallSubgraphs` handles exactly this deficiency-free situation without
using that root.

This proves the only specialization of BGLP Theorem 1.3 needed by the final
argument, without invoking that theorem.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

private noncomputable def oldRootRangeValue
    (z : Set.range (some : V → Option V)) : V :=
  Classical.choose z.2

private theorem some_oldRootRangeValue
    (z : Set.range (some : V → Option V)) :
    some (oldRootRangeValue z) = z.1 :=
  Classical.choose_spec z.2

/--
The graph induced by the old vertices of an empty root extension embeds
back into the original graph.
-/
private noncomputable def oldRootRangeEmbedding
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ((adjoinRoot G ∅).induce
      (Set.range (some : V → Option V))) ↪g G where
  toFun := oldRootRangeValue
  inj' := by
    intro a b hab
    apply Subtype.ext
    rw [← some_oldRootRangeValue a,
      ← some_oldRootRangeValue b, hab]
  map_rel_iff' := by
    intro a b
    change G.Adj (oldRootRangeValue a)
        (oldRootRangeValue b) ↔
      (adjoinRoot G ∅).Adj a.1 b.1
    rw [← some_oldRootRangeValue a,
      ← some_oldRootRangeValue b]
    rfl

/--
Adjoining an isolated root cannot create a cycle whose length is divisible
by five.
-/
theorem no_divisible_cycle_adjoinRoot_empty
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hno : ¬ HasCycleDivisibleBy G 5) :
    ¬ HasCycleDivisibleBy (adjoinRoot G ∅) 5 := by
  rintro ⟨C, hC⟩
  let B := adjoinRoot G ∅
  let old : Set (Option V) :=
    Set.range (some : V → Option V)
  have hsupport :
      ∀ z ∈ C.walk.support, z ∈ old := by
    intro z hz
    have hnotIsolated : ¬B.IsIsolated z := by
      obtain ⟨e, he, hze⟩ :=
        (C.walk.mem_support_iff_exists_mem_edges_of_not_nil
          C.isCycle.not_nil).1 hz
      have hinc : e ∈ B.incidenceSet z :=
        ⟨C.walk.edges_subset_edgeSet he, hze⟩
      have hnbr := B.incidence_other_prop hinc
      intro hisolated
      exact hisolated _
        ((B.mem_neighborSet z _).1 hnbr)
    cases z with
    | none =>
        exact False.elim (hnotIsolated (by
          intro w
          cases w <;> simp [B, adjoinRoot]))
    | some z => exact ⟨z, rfl⟩
  let walkOld := C.walk.induce old hsupport
  have hcycleOld : walkOld.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
      (f := (Embedding.induce old).toHom)
    rw [SimpleGraph.Walk.map_induce]
    exact C.isCycle
  let COld : SimpleCycle (B.induce old) := {
    base :=
      ⟨C.base, hsupport C.base
        C.walk.start_mem_support⟩
    walk := walkOld
    isCycle := hcycleOld
  }
  let f : B.induce old ↪g G := by
    simpa [B, old] using oldRootRangeEmbedding G
  let CG : SimpleCycle G :=
    SimpleCycle.mapInjectiveHom COld f f.injective
  apply hno
  refine ⟨CG, ?_⟩
  have hlengthOld :
      walkOld.length = C.walk.length := by
    rw [← SimpleGraph.Walk.length_map
      (Embedding.induce old).toHom walkOld]
    exact congrArg SimpleGraph.Walk.length
      (SimpleGraph.Walk.map_induce C.walk hsupport)
  change CG.length % 5 = 0
  rw [SimpleCycle.mapInjectiveHom_length]
  change walkOld.length % 5 = 0
  rw [hlengthOld]
  exact hC

/--
A two-connected minimum-degree-five counterexample supplies the common
standing setup with empty deficiency and an isolated ambient root.
-/
noncomputable def standingSetupOfTwoConnected
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hconnected : IsTwoConnected G)
    (hdegree : MinDegreeAtLeast G 5)
    (hno : ¬ HasCycleDivisibleBy G 5) :
    StandingSetup G (adjoinRoot G ∅) none ∅ := by
  classical
  exact {
    inclusion := someEmbedding G ∅
    c_not_old := by
      rintro ⟨w, hw⟩
      simp [someEmbedding] at hw
    vertex_decomposition := by
      intro z
      cases z with
      | none => exact Or.inl rfl
      | some w => exact Or.inr ⟨w, rfl⟩
    degree_c_lower := by
      intro h
      simp at h
    deficient_adjacent_to_c := by
      intro d hd
      simp at hd
    degree_deficient := by
      intro d hd
      simp at hd
    degree_regular := by
      intro w _
      exact hdegree w
    deficient_card := by simp
    three_connected :=
      BGLP.three_connected_of_two_connected_minDegree_four
        G hconnected (fun w => (hdegree w).trans' (by omega))
          hno
    no_divisible_cycle :=
      no_divisible_cycle_adjoinRoot_empty G hno
  }

/--
Every finite two-connected graph of minimum degree at least five contains a
cycle whose length is divisible by five.
-/
theorem divisible_cycle_of_two_connected_min_degree_five
    [Fintype V]
    (G : SimpleGraph V)
    (hconnected : IsTwoConnected G)
    (hdegree : MinDegreeAtLeast G 5) :
    HasCycleDivisibleBy G 5 := by
  classical
  by_contra hno
  exact
    (standingSetupOfTwoConnected
      G hconnected hdegree hno).girth_six_case_contradiction

end DeanK5
