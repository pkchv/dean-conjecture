import DeanK5.Graph.Connectivity
import DeanK5.GHLMRootedBase

/-!
# The four-vertex case of the COY rooted theorem

The source proof of COY Theorem 3 begins by excluding counterexamples of
order four.  In the bounded range needed by this project, the degree
hypothesis forces `q = 2`; a vertex outside the roots and exception is
universal, and rooted two-connectivity supplies an endpoint edge at the
remaining nonroot.  The two resulting paths have lengths two and three.
-/

open scoped Sym2

namespace DeanK5

open SimpleGraph

universe u

namespace COY

/-- Four vertices leave one vertex outside any three specified vertices. -/
theorem exists_avoiding_three_of_four_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (x y z : V) (hcard : 4 ≤ Fintype.card V) :
    ∃ v : V, v ≠ x ∧ v ≠ y ∧ v ≠ z := by
  by_contra h
  push Not at h
  have huniv :
      Finset.univ ⊆ ({x, y, z} : Finset V) := by
    intro v _
    by_cases hvx : v = x
    · simp [hvx]
    by_cases hvy : v = y
    · simp [hvy]
    simp [h v hvx hvy]
  have hcardUpper : Fintype.card V ≤ 3 := by
    rw [← Finset.card_univ]
    calc
      Finset.univ.card ≤ ({x, y, z} : Finset V).card :=
        Finset.card_le_card huniv
      _ ≤ ({y, z} : Finset V).card + 1 :=
        Finset.card_insert_le x {y, z}
      _ ≤ 2 + 1 := by
        rcases Finset.card_pair_eq_one_or_two
            (a := y) (b := z) with h | h <;> omega
      _ = 3 := rfl
  omega

/--
The order-four case of the bounded one-exception rooted theorem, proved
directly.
-/
theorem one_exception_rooted_paths_of_card_eq_four
    {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y z : V)
    (hqTwo : 2 ≤ q)
    (hcard : Fintype.card V = 4)
    (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y → v ≠ z →
      q + 1 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y q) := by
  classical
  have hfourth :
      ∃ u : V, u ≠ x ∧ u ≠ y ∧ u ≠ z :=
    exists_avoiding_three_of_four_le x y z (by omega)
  obtain ⟨u, hux, huy, huz⟩ := hfourth
  have hsecond :
      ∃ v : V, v ≠ x ∧ v ≠ y ∧ v ≠ u :=
    exists_avoiding_three_of_four_le x y u (by omega)
  obtain ⟨v, hvx, hvy, hvu⟩ := hsecond
  let S : Finset V := {x, y, u, v}
  have hScard : S.card = 4 := by
    apply Finset.card_eq_four.mpr
    exact ⟨x, y, u, v, hxy, hux.symm, hvx.symm,
      huy.symm, hvy.symm, hvu.symm, rfl⟩
  have hSuniv : S = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [hcard] using hScard
  have classify (w : V) :
      w = x ∨ w = y ∨ w = u ∨ w = v := by
    have hw : w ∈ S := by
      rw [hSuniv]
      simp
    simpa [S] using hw
  have hfiniteDegree :
      finiteDegree G u = G.degree u := by
    unfold finiteDegree SimpleGraph.degree SimpleGraph.neighborFinset
    rw [Set.ncard_eq_toFinset_card']
  have hdegreeLower :
      q + 1 ≤ G.degree u := by
    rw [← hfiniteDegree]
    exact hdeg u hux huy huz
  have hdegreeUpper :
      G.degree u < 4 := by
    simpa [hcard] using G.degree_lt_card_verts u
  have hq : q = 2 := by
    omega
  have huDegree : G.degree u = 3 := by
    omega
  have huUniversal : G.IsUniversal u := by
    apply (G.degree_eq_card_sub_one u).1
    simpa [hcard] using huDegree
  have huxAdj : G.Adj u x := huUniversal hux
  have huyAdj : G.Adj u y := huUniversal huy
  have huvAdj : G.Adj u v := huUniversal hvu.symm
  let H := G ⊔ edge x y
  have hvEndpoint : G.Adj v x ∨ G.Adj v y := by
    by_contra h
    push Not at h
    have hneighborSubset :
        H.neighborSet v ⊆ ({u} : Set V) := by
      intro w hvw
      change G.Adj v w ∨ (edge x y).Adj v w at hvw
      rcases hvw with hvw | hvw
      · rcases classify w with rfl | rfl | rfl | rfl
        · exact False.elim (h.1 hvw)
        · exact False.elim (h.2 hvw)
        · simp
        · exact False.elim (hvw.ne rfl)
      · exfalso
        simp [SimpleGraph.edge_adj, hvx, hvy] at hvw
    have hdegreeH :
        2 ≤ finiteDegree H v :=
      ClassicalGraphTheory.degree_at_least_connectivity
        H 2 hconn v
    have hcardNeighbor :
        (H.neighborSet v).ncard ≤ 1 := by
      calc
        (H.neighborSet v).ncard ≤ ({u} : Set V).ncard :=
          Set.ncard_le_ncard hneighborSubset
        _ = 1 := by simp
    exact (by
      unfold finiteDegree at hdegreeH
      omega)
  have hxu : G.Adj x u := huxAdj.symm
  have huv : G.Adj u v := huvAdj
  have hvuAdj : G.Adj v u := huvAdj.symm
  let short : SimplePath G x y := {
    walk := .cons hxu (.cons huyAdj .nil)
    isPath := by
      simpa using And.intro huy
        (And.intro hux.symm hxy)
  }
  have hshortLength : short.length = 2 := by
    simp [short, SimplePath.length]
  subst q
  rcases hvEndpoint with hvxAdj | hvyAdj
  · let long : SimplePath G x y := {
      walk := .cons hvxAdj.symm (.cons hvuAdj (.cons huyAdj .nil))
      isPath := by
        simpa using And.intro
          (And.intro huy
            (And.intro hvu hvy))
          (And.intro hvx.symm
            (And.intro hux.symm hxy))
    }
    have hlongLength : long.length = 3 := by
      simp [long, SimplePath.length]
    exact ⟨{
      start := 2
      step := 1
      admissible_step := Or.inl rfl
      start_ge_two := le_rfl
      path := ![short, long]
      length_path := by
        intro i
        fin_cases i <;>
          simp [hshortLength, hlongLength]
    }⟩
  · let long : SimplePath G x y := {
      walk := .cons hxu (.cons huv (.cons hvyAdj .nil))
      isPath := by
        simpa using And.intro
          (And.intro hvy
            (And.intro hvu.symm huy))
          (And.intro hux.symm
            (And.intro hvx.symm hxy))
    }
    have hlongLength : long.length = 3 := by
      simp [long, SimplePath.length]
    exact ⟨{
      start := 2
      step := 1
      admissible_step := Or.inl rfl
      start_ge_two := le_rfl
      path := ![short, long]
      length_path := by
        intro i
        fin_cases i <;>
          simp [hshortLength, hlongLength]
    }⟩

/--
A counterexample to the bounded one-exception theorem has at least five
vertices.  This is COY Claim 3.1(2) in the present finite-graph interface.
-/
theorem five_le_card_of_no_one_exception_rooted_paths
    {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y z : V)
    (hqTwo : 2 ≤ q)
    (horder : 4 ≤ Fintype.card V)
    (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y → v ≠ z →
      q + 1 ≤ finiteDegree G v)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    5 ≤ Fintype.card V := by
  by_contra h
  have hcard : Fintype.card V = 4 := by
    omega
  exact hno
    (one_exception_rooted_paths_of_card_eq_four
      q G x y z hqTwo hcard hxy hconn hdeg)

end COY

end DeanK5
