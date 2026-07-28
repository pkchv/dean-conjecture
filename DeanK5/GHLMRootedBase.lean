import DeanK5.Graph.Basic

/-!
# The first rooted admissible-path base case

This file proves the `q = 1` specialization of the rooted
admissible-path theorem internally.  The artificial root edge is used only
to express the connectivity hypothesis: two-connectivity supplies a route
between the roots that avoids that edge, and hence lies in the original
graph.
-/

open scoped Sym2

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace GHLM

/--
Two-connectivity after adjoining the root edge supplies an `x`--`y` path
of length at least two in the original graph.

This is the degree-free content of the `q = 1` rooted-path theorem and the
base case needed by a source-faithful COY induction.
-/
theorem rooted_admissible_paths_one_of_two_connected
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y)) :
    Nonempty (AdmissiblePathFamily G x y 1) := by
  classical
  let H := G ⊔ edge x y
  have hthird : ∃ z : V, z ≠ x ∧ z ≠ y := by
    by_contra h
    push Not at h
    have huniv : Finset.univ ⊆ ({x, y} : Finset V) := by
      intro z hz
      by_cases hzx' : z = x
      · simp [hzx']
      · simp [h z hzx']
    have hcard : Fintype.card V ≤ 2 := by
      rw [← Finset.card_univ]
      calc
        Finset.univ.card ≤ ({x, y} : Finset V).card :=
          Finset.card_le_card huniv
        _ ≤ 2 := by simp [hxy]
    have horder := hconn.1
    omega
  obtain ⟨z, hzx, hzy⟩ := hthird
  have hyCard : ({y} : Finset V).card < 2 := by simp
  have hxCard : ({x} : Finset V).card < 2 := by simp
  have hxNotY : x ∉ ({y} : Finset V) := by simpa using hxy
  have hzNotY : z ∉ ({y} : Finset V) := by simpa using hzy
  have hzNotX : z ∉ ({x} : Finset V) := by simpa using hzx
  have hyNotX : y ∉ ({x} : Finset V) := by simpa using hxy.symm
  obtain ⟨p₁⟩ :=
    (hconn.2 ({y} : Finset V) hyCard).preconnected
      ⟨x, hxNotY⟩ ⟨z, hzNotY⟩
  obtain ⟨p₂⟩ :=
    (hconn.2 ({x} : Finset V) hxCard).preconnected
      ⟨z, hzNotX⟩ ⟨y, hyNotX⟩
  let p₁H : H.Walk x z :=
    p₁.map
      (Embedding.induce
        {v | v ∉ ({y} : Finset V)}).toHom
  let p₂H : H.Walk z y :=
    p₂.map
      (Embedding.induce
        {v | v ∉ ({x} : Finset V)}).toHom
  have hyNotSupport : y ∉ p₁H.support := by
    intro hy
    change y ∈
      (p₁.map
        (Embedding.induce
          {v | v ∉ ({y} : Finset V)}).toHom).support at hy
    rw [SimpleGraph.Walk.support_map] at hy
    obtain ⟨v, hv, hvy⟩ := List.mem_map.mp hy
    apply v.2
    change v.1 = y at hvy
    simp [hvy]
  have hxNotSupport : x ∉ p₂H.support := by
    intro hx
    change x ∈
      (p₂.map
        (Embedding.induce
          {v | v ∉ ({x} : Finset V)}).toHom).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hx
    apply v.2
    change v.1 = x at hvx
    simp [hvx]
  have hp₁Avoid : s(x, y) ∉ p₁H.edges := by
    intro he
    exact hyNotSupport (p₁H.snd_mem_support_of_mem_edges he)
  have hp₂Avoid : s(x, y) ∉ p₂H.edges := by
    intro he
    exact hxNotSupport (p₂H.fst_mem_support_of_mem_edges he)
  have hHAvoid :
      s(x, y) ∉ (p₁H.append p₂H).edges := by
    simp [hp₁Avoid, hp₂Avoid]
  have hHDeleteReach :
      (H.deleteEdges {s(x, y)}).Reachable x y :=
    reachable_deleteEdges_iff_exists_walk.mpr
      ⟨p₁H.append p₂H, hHAvoid⟩
  have hHNotBridge : ¬H.IsBridge s(x, y) := by
    rw [isBridge_iff]
    exact not_not_intro hHDeleteReach
  have hGNotBridge : ¬G.IsBridge s(x, y) := by
    simpa [H] using hHNotBridge
  have hGDeleteReach :
      (G.deleteEdges {s(x, y)}).Reachable x y := by
    simpa [isBridge_iff] using hGNotBridge
  obtain ⟨p, hp⟩ := hGDeleteReach.exists_isPath
  let pG : G.Walk x y :=
    p.mapLe (G.deleteEdges_le {s(x, y)})
  have hpG : pG.IsPath := by
    exact hp.mapLe (G.deleteEdges_le {s(x, y)})
  let P : SimplePath G x y := ⟨pG, hpG⟩
  have hlength : 2 ≤ P.length := by
    have hzero : p.length ≠ 0 := by
      intro hpzero
      exact hxy (p.eq_of_length_eq_zero hpzero)
    have hone : p.length ≠ 1 := by
      intro hpone
      have hadj :
          (G.deleteEdges {s(x, y)}).Adj x y :=
        p.adj_of_length_eq_one hpone
      have hnotAdj :
          ¬(G.deleteEdges {s(x, y)}).Adj x y := by
        simp
      exact hnotAdj hadj
    have hlengthEq : P.length = p.length := by
      change (p.mapLe (G.deleteEdges_le {s(x, y)})).length =
        p.length
      unfold SimpleGraph.Walk.mapLe
      exact SimpleGraph.Walk.length_map
        (.ofLE (G.deleteEdges_le {s(x, y)})) p
    rw [hlengthEq]
    omega
  exact ⟨{
    start := P.length
    step := 1
    admissible_step := Or.inl rfl
    start_ge_two := hlength
    path := fun _ => P
    length_path := by
      intro i
      simp
  }⟩

/--
The `q = 1` specialization of GHLM's rooted admissible-path theorem.
Its degree hypothesis is retained for a statement-level comparison with
the published theorem, but the proof uses only rooted two-connectivity.
-/
theorem rooted_admissible_paths_one
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (_hdeg : ∀ v, v ≠ x → v ≠ y → 2 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y 1) :=
  rooted_admissible_paths_one_of_two_connected G x y hxy hconn

end GHLM

namespace COY

/--
The `q = 1` case of COY's one-exception rooted theorem.  The exceptional
vertex and all degree information are immaterial in this base case.
-/
theorem one_exception_rooted_paths_one
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y z : V)
    (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (_hdeg : ∀ v, v ≠ x → v ≠ y → v ≠ z →
      2 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y 1) :=
  GHLM.rooted_admissible_paths_one_of_two_connected
    G x y hxy hconn

end COY

end DeanK5
