import DeanK5.COYRootedInternal

/-!
# Internal reduction of the needed GHLM fragment to COY

The one-exception theorem of Chiba--Ota--Yamashita contains the fragment of
the GHLM rooted theorem needed here.  A third vertex is chosen as the
exception; the stronger GHLM degree hypothesis also supplies its degree
bound.  COY's order bound follows from that degree bound and the elementary
fact that a vertex has fewer neighbors than the order of a finite simple
graph.
-/

open SimpleGraph

namespace DeanK5

universe u

namespace GHLM

/-- The `2 ≤ q ≤ 4` fragment of GHLM Theorem 3.1 needed by this project. -/
theorem rooted_admissible_paths_internal
    {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y : V)
    (hqTwo : 2 ≤ q) (hqFour : q ≤ 4) (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y →
      q + 1 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y q) := by
  have hthird : ∃ z : V, z ≠ x ∧ z ≠ y := by
    by_contra h
    push Not at h
    have huniv :
        Finset.univ ⊆ ({x, y} : Finset V) := by
      intro z _
      by_cases hzx : z = x
      · simp [hzx]
      · simp [h z hzx]
    have hcard : Fintype.card V ≤ 2 := by
      rw [← Finset.card_univ]
      calc
        Finset.univ.card ≤ ({x, y} : Finset V).card :=
          Finset.card_le_card huniv
        _ ≤ 2 := (Finset.card_pair hxy).le
    have horder := hconn.1
    omega
  obtain ⟨z, hzx, hzy⟩ := hthird
  have hneighborProper :
      G.neighborSet z ≠ Set.univ := by
    intro h
    have hz :
        z ∈ G.neighborSet z := by
      rw [h]
      simp
    exact G.loopless.irrefl z hz
  have hdegreeUpper :
      finiteDegree G z < Fintype.card V := by
    unfold finiteDegree
    simpa [Nat.card_eq_fintype_card] using
      Set.ncard_lt_card hneighborProper
  have horder : 4 ≤ Fintype.card V := by
    have hdegreeLower := hdeg z hzx hzy
    omega
  exact COY.one_exception_rooted_paths_internal
    q G x y z hqTwo hqFour horder hxy hzx hzy hconn
    (fun v hvx hvy _ => hdeg v hvx hvy)

end GHLM

end DeanK5
