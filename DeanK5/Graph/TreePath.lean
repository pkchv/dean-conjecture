import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Finite trees with at most two leaves

A finite nontrivial tree whose degree-one vertices lie in a set of at
most two vertices is a path-like chain: that set is exactly the two leaves,
and every other vertex has degree two.

The results below state this conclusion as a degree classification rather
than as an isomorphism with `SimpleGraph.pathGraph`.  This is the form needed
for the block-tree bookkeeping in the proof of Claim 3.11.
-/

namespace DeanK5

open SimpleGraph
open scoped BigOperators

universe u

variable {V : Type u}

namespace TreePath

/-- The degree-one vertices of a finite simple graph. -/
def leafVertices
    [Fintype V]
    (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ.filter fun v => G.degree v = 1

/-- Membership in `leafVertices` is exactly the degree-one condition. -/
@[simp] theorem mem_leafVertices
    [Fintype V]
    (G : SimpleGraph V)
    [DecidableRel G.Adj]
    {v : V} :
    v ∈ leafVertices G ↔ G.degree v = 1 := by
  simp [leafVertices]

/--
If a finite nontrivial tree has at most two leaves, then every vertex has
degree at most two.

The proof compares the degree sum with the baseline sum that assigns degree
one to leaves and degree two to all other vertices.  Any vertex of degree at
least three would make the actual sum strictly larger, contradicting the
tree identity `|E| + 1 = |V|`.
-/
theorem degree_le_two_of_leafVertices_card_le_two
    [Fintype V] [Nontrivial V]
    {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (hG : G.IsTree)
    (hLeaves : (leafVertices G).card ≤ 2)
    (v : V) :
    G.degree v ≤ 2 := by
  by_contra hnot
  have hvThree : 3 ≤ G.degree v := by
    omega
  have hpositive (w : V) : 0 < G.degree w :=
    hG.preconnected.degree_pos_of_nontrivial w
  let baseline : V → ℕ := fun w =>
    if G.degree w = 1 then 1 else 2
  have hbaseline_le :
      ∀ w : V, baseline w ≤ G.degree w := by
    intro w
    by_cases hw : G.degree w = 1
    · simp [baseline, hw]
    · simp only [baseline, hw, ↓reduceIte]
      have := hpositive w
      omega
  have hbaseline_lt :
      baseline v < G.degree v := by
    have hvNotOne : G.degree v ≠ 1 := by
      omega
    simp [baseline, hvNotOne]
    omega
  have hsumStrict :
      (∑ w : V, baseline w) <
        ∑ w : V, G.degree w := by
    apply Finset.sum_lt_sum
    · intro w _
      exact hbaseline_le w
    · exact ⟨v, Finset.mem_univ v, hbaseline_lt⟩
  have hbaselineSum :
      (∑ w : V, baseline w) =
        (leafVertices G).card +
          2 *
            (Finset.univ.filter fun w =>
              G.degree w ≠ 1).card := by
    simp only [baseline]
    rw [Finset.sum_ite]
    simp [leafVertices, mul_comm]
  have hpartition :
      (leafVertices G).card +
          (Finset.univ.filter fun w =>
            G.degree w ≠ 1).card =
        Fintype.card V := by
    simpa [leafVertices] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.univ)
        (fun w : V => G.degree w = 1))
  have hdegreeSum :=
    G.sum_degrees_eq_twice_card_edges
  have hedgeCount :=
    hG.card_edgeFinset
  omega

/--
A finite nontrivial tree with at most two leaves has exactly two leaves.

The nontriviality hypothesis is essential: a one-vertex tree has no
degree-one vertices.
-/
theorem leafVertices_card_eq_two_of_card_le_two
    [Fintype V] [Nontrivial V]
    {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (hG : G.IsTree)
    (hLeaves : (leafVertices G).card ≤ 2) :
    (leafVertices G).card = 2 := by
  have hdegreeUpper :
      ∀ w : V, G.degree w ≤ 2 :=
    degree_le_two_of_leafVertices_card_le_two
      hG hLeaves
  have hpositive (w : V) : 0 < G.degree w :=
    hG.preconnected.degree_pos_of_nontrivial w
  have hdegreeClass (w : V) :
      G.degree w =
        if G.degree w = 1 then 1 else 2 := by
    by_cases hw : G.degree w = 1
    · simp [hw]
    · simp [hw]
      have := hpositive w
      have := hdegreeUpper w
      omega
  have hdegreeSumClass :
      (∑ w : V, G.degree w) =
        (leafVertices G).card +
          2 *
            (Finset.univ.filter fun w =>
              G.degree w ≠ 1).card := by
    calc
      (∑ w : V, G.degree w) =
          ∑ w : V,
            if G.degree w = 1 then 1 else 2 := by
        apply Finset.sum_congr rfl
        intro w _
        exact hdegreeClass w
      _ =
          (leafVertices G).card +
            2 *
              (Finset.univ.filter fun w =>
                G.degree w ≠ 1).card := by
        rw [Finset.sum_ite]
        simp [leafVertices, mul_comm]
  have hpartition :
      (leafVertices G).card +
          (Finset.univ.filter fun w =>
            G.degree w ≠ 1).card =
        Fintype.card V := by
    simpa [leafVertices] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.univ)
        (fun w : V => G.degree w = 1))
  have hdegreeSum :=
    G.sum_degrees_eq_twice_card_edges
  have hedgeCount :=
    hG.card_edgeFinset
  omega

/--
Every non-leaf vertex of a finite nontrivial tree with at most two leaves
has degree exactly two.
-/
theorem degree_eq_two_of_not_mem_leafVertices
    [Fintype V] [Nontrivial V]
    {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (hG : G.IsTree)
    (hLeaves : (leafVertices G).card ≤ 2)
    {v : V}
    (hv : v ∉ leafVertices G) :
    G.degree v = 2 := by
  have hpositive :
      0 < G.degree v :=
    hG.preconnected.degree_pos_of_nontrivial v
  have hupper :
      G.degree v ≤ 2 :=
    degree_le_two_of_leafVertices_card_le_two
      hG hLeaves v
  have hnotOne :
      G.degree v ≠ 1 := by
    intro hdegree
    exact hv ((mem_leafVertices G).2 hdegree)
  omega

/--
Specified-endpoint form of the two-leaf tree lemma.

If every leaf lies in `endpoints` and `endpoints` has at most two vertices,
then `endpoints` is exactly the two-leaf set.  The remaining conjunction is
the path-like degree classification: endpoints have degree one and every
other vertex has degree two.
-/
theorem chain_degree_classification_of_leaves_subset
    [Fintype V] [Nontrivial V]
    {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (hG : G.IsTree)
    (endpoints : Finset V)
    (hLeaf :
      ∀ v : V, G.degree v = 1 → v ∈ endpoints)
    (hEndpoints : endpoints.card ≤ 2) :
    leafVertices G = endpoints ∧
      ∀ v : V,
        (v ∈ endpoints → G.degree v = 1) ∧
          (v ∉ endpoints → G.degree v = 2) := by
  have hsubset :
      leafVertices G ⊆ endpoints := by
    intro v hv
    exact hLeaf v ((mem_leafVertices G).1 hv)
  have hLeaves :
      (leafVertices G).card ≤ 2 :=
    (Finset.card_le_card hsubset).trans hEndpoints
  have hLeafCard :
      (leafVertices G).card = 2 :=
    leafVertices_card_eq_two_of_card_le_two
      hG hLeaves
  have hEndpointsCard :
      endpoints.card ≤ (leafVertices G).card := by
    omega
  have hLeafEq :
      leafVertices G = endpoints :=
    Finset.eq_of_subset_of_card_le
      hsubset hEndpointsCard
  refine ⟨hLeafEq, ?_⟩
  intro v
  constructor
  · intro hv
    apply (mem_leafVertices G).1
    rw [hLeafEq]
    exact hv
  · intro hv
    apply degree_eq_two_of_not_mem_leafVertices
      hG hLeaves
    intro hvLeaf
    apply hv
    rw [← hLeafEq]
    exact hvLeaf

end TreePath

end DeanK5
