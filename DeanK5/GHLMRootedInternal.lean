import DeanK5.GHLMRootedBase
import DeanK5.Published

/-!
# Internal reduction of the GHLM rooted theorem to COY

The one-exception theorem of Chiba--Ota--Yamashita contains the GHLM rooted
theorem whenever `q ≥ 2`: choose one root itself as the exceptional vertex.
COY additionally assumes that the graph has at least four vertices.  That
order bound follows here from the degree hypothesis and the elementary fact
that a vertex has fewer neighbors than the order of a finite simple graph.

The remaining `q = 1` case is proved directly in `GHLMRootedBase`.
-/

open SimpleGraph

namespace DeanK5

universe u

namespace GHLM

/--
GHLM Theorem 3.1, derived from the stronger COY one-exception theorem and
the internally proved first base case.
-/
theorem rooted_admissible_paths_internal
    {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y : V)
    (hq : 1 ≤ q) (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y →
      q + 1 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y q) := by
  by_cases hqOne : q = 1
  · subst q
    exact rooted_admissible_paths_one
      G x y hxy hconn (by simpa using hdeg)
  · have hqTwo : 2 ≤ q := by omega
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
    exact COY.one_exception_rooted_paths
      q G x y x hq horder hxy hconn
      (fun v hvx hvy _ => hdeg v hvx hvy)

end GHLM

end DeanK5
