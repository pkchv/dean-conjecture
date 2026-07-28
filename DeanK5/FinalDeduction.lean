import DeanK5.Reduction

/-!
# Final deduction (paper Section 8)

This is the canonical human-review entry point for the final theorem.  The
substantive graph-theoretic routines are proved in the modules imported by
`Reduction`; this file only assembles their terminal interfaces.

The connected case has two branches:

* a two-connected graph is closed by the internally proved
  minimum-degree-five theorem;
* a graph that is not two-connected supplies an end lobe, whose rooted
  setup is closed by the common Sections 3--7 contradiction.

The final theorem then restricts the ambient graph to one connected component
and transports the resulting cycle back along the component inclusion.
-/

open SimpleGraph

namespace DeanK5

namespace ConnectedComponent

/-- Restrict a minimum-degree bound to a connected component. -/
theorem minDegreeAtLeast
    {X : Type*} [Fintype X]
    {G : SimpleGraph X}
    (C : G.ConnectedComponent) [Fintype C]
    {d : ℕ}
    (hdegree : MinDegreeAtLeast G d) :
    MinDegreeAtLeast C.toSimpleGraph d := by
  intro w
  have hinside :
      ∀ y, G.Adj w.1 y → y ∈ C.supp := by
    intro y hwy
    exact C.mem_supp_of_adj_mem_supp w.2 hwy
  have hle :=
    finiteDegree_le_induce G C.supp w hinside
  exact (hdegree w.1).trans hle

end ConnectedComponent

namespace RootedBlockSetup

/--
All of Sections 3--7 assembled for an extracted rooted end block.
-/
theorem contradiction
    {W V : Type*}
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V} {c : V}
    (R : RootedBlockSetup J B c) :
    False :=
  R.toStandingSetup.girth_six_case_contradiction

end RootedBlockSetup

/--
Every finite connected graph of minimum degree at least five contains a
cycle whose length is divisible by five.
-/
theorem divisible_cycle_of_connected_min_degree_five
    {X : Type*} [Fintype X]
    (G : SimpleGraph X)
    (hconnected : G.Connected)
    (hdegree : MinDegreeAtLeast G 5) :
    HasCycleDivisibleBy G 5 := by
  classical
  by_cases htwo : IsTwoConnected G
  · exact
      divisible_cycle_of_two_connected_min_degree_five
        G htwo hdegree
  · by_contra hno
    have hdegreeThree : MinDegreeAtLeast G 3 := by
      intro v
      exact (hdegree v).trans' (by omega)
    obtain ⟨P⟩ :=
      ClassicalGraphTheory.two_end_lobes
        G hconnected htwo hdegreeThree
    exact
      (P.left.toRootedBlockSetup hdegree hno).contradiction

/--
The paper's final theorem.

`Nonempty X` is explicit because the pointwise predicate
`MinDegreeAtLeast G 5` is vacuously true on an empty carrier.  This is the
formal counterpart of the conventional graph-theoretic assumption that a
graph with a stated minimum degree has a vertex.
-/
theorem dean_conjecture_k5
    {X : Type*} [Fintype X]
    [Nonempty X]
    (G : SimpleGraph X)
    (hdegree : MinDegreeAtLeast G 5) :
    HasCycleDivisibleBy G 5 := by
  classical
  let C :=
    G.connectedComponentMk
      (Classical.choice (inferInstance : Nonempty X))
  letI : Fintype C := Fintype.ofFinite C
  exact
    (divisible_cycle_of_connected_min_degree_five
      C.toSimpleGraph
      C.connected_toSimpleGraph
      (ConnectedComponent.minDegreeAtLeast C hdegree)).mapInjectiveHom
        C.toSimpleGraph_hom Subtype.val_injective

end DeanK5
