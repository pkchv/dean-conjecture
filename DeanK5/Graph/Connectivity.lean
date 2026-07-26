import DeanK5.Graph.Basic

/-!
# Connectivity transport

The paper moves repeatedly between finite graphs on equivalent
carriers.  This file records that the project's explicit vertex-connectivity
predicate is invariant under graph isomorphism.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {V : Type u} {W : Type v}

/-- Vertex `k`-connectivity is preserved by a graph isomorphism. -/
theorem IsKConnected.map_iso
    [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {k : ℕ} (hG : IsKConnected G k)
    (e : G ≃g H) :
    IsKConnected H k := by
  classical
  constructor
  · rw [← Fintype.card_congr e.toEquiv]
    exact hG.1
  · intro S hScard
    let S' : Finset V :=
      S.map e.symm.toEquiv.toEmbedding
    have hS'card : S'.card < k := by
      simpa [S'] using hScard
    have hsource :
        (G.induce {v : V | v ∉ S'}).Connected :=
      hG.2 S' hS'card
    have hmem (x : V) :
        x ∈ S' ↔ e x ∈ S := by
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ :=
          Finset.mem_map.mp hx
        have hyeq : y = e x := by
          apply e.symm.injective
          simpa using hyx
        simpa [hyeq] using hy
      · intro hx
        apply Finset.mem_map.mpr
        exact ⟨e x, hx, by simp⟩
    have hbij :
        Set.BijOn e
          {v : V | v ∉ S'}
          {w : W | w ∉ S} := by
      refine ⟨?_, e.injective.injOn, ?_⟩
      · intro x hx
        exact fun hex => hx ((hmem x).2 hex)
      · intro y hy
        refine ⟨e.symm y, ?_, by simp⟩
        intro hmem'
        apply hy
        have := (hmem (e.symm y)).1 hmem'
        simpa using this
    exact
      (SimpleGraph.Iso.connected_iff
        (e.induce hbij)).mp hsource

end DeanK5
