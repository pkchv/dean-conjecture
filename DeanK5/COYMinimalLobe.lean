import DeanK5.EndLobeExistence

/-!
# A minimum rooted lobe for the COY protected-edge argument

If adding one edge `xz` restores 2-connectivity to a connected graph,
the two endpoints lie on opposite sides of every relevant cut.  Starting
from the `x`-side and minimizing its lobe interior produces a certified
lobe that still contains `x` and whose whole closure excludes `z`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- The minimum rooted lobe selected on one side of a restored edge. -/
structure MinimalRootLobeData
    [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (x z : V) where
  /-- The initial component lobe on the `x`-side of a cut. -/
  initial : LobeRegion K
  /-- A lobe of minimum interior cardinality inside `initial`. -/
  lobe : LobeRegion K
  /-- The selected lobe stays inside the initial side. -/
  within : lobe.Within initial.inner initial.cut
  /-- Interior-cardinality minimality among lobes on the initial side. -/
  minimal :
    ∀ L : LobeRegion K,
      L.Within initial.inner initial.cut →
        lobe.inner.card ≤ L.inner.card
  /-- The retained endpoint belongs to the lobe interior. -/
  root_mem : x ∈ lobe.inner
  /-- The opposite endpoint lies outside the entire lobe closure. -/
  other_not_carrier : z ∉ lobe.carrier

/--
Select a minimum `x`-side lobe when `K` is connected but not
2-connected and adjoining `xz` restores 2-connectivity.
-/
theorem exists_minimalRootLobeData
    [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (x z : V)
    (hconnected : K.Connected)
    (hnotTwo : ¬IsTwoConnected K)
    (hrestored : IsTwoConnected (K ⊔ edge x z))
    (horder : 3 ≤ Fintype.card V) :
    Nonempty (MinimalRootLobeData K x z) := by
  obtain ⟨c, Cx, Cz, hCxCz, hxQx, hzQz⟩ :=
    ComponentRegion.exists_root_separating_cut_of_sup_edge_two_connected
      K x z hconnected hnotTwo hrestored horder
  let Qx := componentVertices K {c} Cx
  let Qz := componentVertices K {c} Cz
  have hQx : ComponentRegion K {c} Qx :=
    componentRegion_componentVertices K {c} Cx
  have hQz : ComponentRegion K {c} Qz :=
    componentRegion_componentVertices K {c} Cz
  have hdisjoint : Disjoint Qx Qz :=
    componentVertices_disjoint_of_ne K {c} hCxCz
  obtain ⟨L₀, hL₀inner, hL₀cut⟩ :=
    LobeRegion.exists_ofComponent hconnected c Cx
  obtain ⟨L, hwithin, hminimal⟩ :=
    L₀.exists_minimal_within
  have hinnerQx : L.inner ⊆ Qx := by
    intro v hv
    simpa [Qx, hL₀inner] using hwithin.1 hv
  have hcutLocation : L.cut ∈ insert c Qx := by
    simpa [Qx, hL₀inner, hL₀cut] using hwithin.2
  have hzNotCarrier : z ∉ L.carrier := by
    intro hzCarrier
    rcases Finset.mem_insert.mp hzCarrier with hzCut | hzInner
    · have hzCutLocation : z ∈ insert c Qx := by
        simpa [hzCut] using hcutLocation
      rcases Finset.mem_insert.mp hzCutLocation with hzc | hzQx
      · exact hQz.not_mem_separator hzQz (by simp [hzc])
      · exact Finset.disjoint_left.mp hdisjoint hzQx hzQz
    · exact Finset.disjoint_left.mp hdisjoint
        (hinnerQx hzInner) hzQz
  have hzNotInner : z ∉ L.inner := by
    intro hz
    exact hzNotCarrier
      (Finset.mem_insert.mpr (Or.inr hz))
  have hzNotCut : z ≠ L.cut := by
    intro h
    exact hzNotCarrier
      (Finset.mem_insert.mpr (Or.inl h))
  have hxInner : x ∈ L.inner := by
    by_contra hxNotInner
    obtain ⟨u, huInner⟩ := L.inner_nonempty
    have huCut : u ≠ L.cut := by
      intro h
      exact L.cut_not_inner (h ▸ huInner)
    have hdeleted :=
      hrestored.2 ({L.cut} : Finset V) (by simp)
    let uD :
        {v : V // v ∉ ({L.cut} : Finset V)} :=
      ⟨u, by simpa using huCut⟩
    let zD :
        {v : V // v ∉ ({L.cut} : Finset V)} :=
      ⟨z, by simpa using hzNotCut⟩
    obtain ⟨p⟩ :=
      hdeleted.preconnected uD zD
    let pK : (K ⊔ edge x z).Walk u z :=
      p.map (Embedding.induce
        {v : V | v ∉ ({L.cut} : Finset V)}).toHom
    have havoid :
        ∀ v ∈ pK.support,
          v ∉ ({L.cut} : Finset V) := by
      intro v hv
      change v ∈
        (p.map (Embedding.induce
          {v : V | v ∉ ({L.cut} : Finset V)}).toHom).support at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨w, -, hwv⟩ := List.mem_map.mp hv
      change w.1 = v at hwv
      exact hwv ▸ w.2
    have hsame :
        x ∈ L.inner ↔ z ∈ L.inner := by
      constructor
      · exact fun hx => False.elim (hxNotInner hx)
      · exact fun hz => False.elim (hzNotInner hz)
    exact hzNotInner
      (L.componentRegion.endpoint_mem_of_sup_edge_walk
        huInner pK havoid hsame)
  exact ⟨{
    initial := L₀
    lobe := L
    within := hwithin
    minimal := hminimal
    root_mem := hxInner
    other_not_carrier := hzNotCarrier
  }⟩

end COY

end DeanK5
