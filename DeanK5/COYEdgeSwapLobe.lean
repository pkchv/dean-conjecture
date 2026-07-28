import DeanK5.COYEdgeSwapSetup
import DeanK5.COYMinimalLobe

/-!
# The minimum lobe in the COY protected-edge swap

Assume that the exceptional vertex is adjacent to the left root of a
minimal COY counterexample.  Deleting that edge and adding the artificial
root edge produces the connected non-2-connected graph from
`COYEdgeSwapSetup`.  This file selects the minimum lobe on the left-root
side and records the elementary order facts needed for the subsequent
core argument.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace MinimalRootLobeData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
The artificial edge `xy` forces the other root into every selected
`x`-side lobe of the edge-swap graph.
-/
theorem other_root_mem_of_edgeSwap
    (M : MinimalCounterexample q G x y z)
    (D : MinimalRootLobeData
      (leftEdgeSwapGraph G x y z) x z) :
    y ∈ D.lobe.carrier := by
  have hxy :
      (leftEdgeSwapGraph G x y z).Adj x y := by
    rw [leftEdgeSwapGraph, SimpleGraph.sup_adj]
    exact Or.inr
      ((SimpleGraph.edge_adj x y x y).2
        ⟨Or.inl ⟨rfl, rfl⟩, M.roots_ne⟩)
  rcases D.lobe.closed D.root_mem hxy with hyInner | hyCut
  · exact Finset.mem_insert.mpr (Or.inr hyInner)
  · exact Finset.mem_insert.mpr (Or.inl hyCut)

/--
A walk in the genuinely deleted graph reaches the cut of the selected
lobe through an edge of that deleted graph, rather than merely through
the artificial root edge.
-/
theorem exists_deleted_boundary_edge
    (M : MinimalCounterexample q G x y z)
    (hxz : G.Adj x z)
    (D : MinimalRootLobeData
      (leftEdgeSwapGraph G x y z) x z) :
    ∃ v ∈ D.lobe.inner,
      (leftEdgeDeletedGraph G x z).Adj v D.lobe.cut := by
  obtain ⟨p⟩ :=
    (M.edgeSwapCutSetup hxz).deleted_connected.preconnected
      x D.lobe.cut
  let pSwap :
      (leftEdgeSwapGraph G x y z).Walk x D.lobe.cut :=
    p.mapLe (show
      leftEdgeDeletedGraph G x z ≤
        leftEdgeSwapGraph G x y z from le_sup_left)
  obtain ⟨v, hvInner, c, hc, hvcEdge, -⟩ :=
    D.lobe.componentRegion.exists_boundary_edge_mem_edges_of_walk
      D.root_mem (by simp) pSwap
  have hcEq : c = D.lobe.cut := by
    simpa using hc
  subst c
  change s(v, D.lobe.cut) ∈
    (p.mapLe (show
      leftEdgeDeletedGraph G x z ≤
        leftEdgeSwapGraph G x y z from le_sup_left)).edges at hvcEdge
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hvcEdge
  exact ⟨v, hvInner, p.adj_of_mem_edges hvcEdge⟩

/--
The selected lobe contains a vertex other than the two roots and its cut
vertex.  If the other root is the cut, a boundary edge in the genuinely
deleted graph supplies such a vertex.  Otherwise the other root is in the
lobe interior, and 2-connectivity of the original graph supplies a first
neighbor on a path avoiding the cut.
-/
theorem exists_ordinary_carrier_of_edgeSwap
    (M : MinimalCounterexample q G x y z)
    (hxz : G.Adj x z)
    (D : MinimalRootLobeData
      (leftEdgeSwapGraph G x y z) x z) :
    ∃ v ∈ D.lobe.carrier,
      v ≠ x ∧ v ≠ y ∧ v ≠ z ∧ v ≠ D.lobe.cut := by
  have hyCarrier :=
    D.other_root_mem_of_edgeSwap M
  by_cases hyCut : y = D.lobe.cut
  · obtain ⟨v, hvInner, hvCutAdj⟩ :=
      D.exists_deleted_boundary_edge M hxz
    have hvCut : v ≠ D.lobe.cut := by
      intro hv
      exact D.lobe.cut_not_inner (hv ▸ hvInner)
    have hvx : v ≠ x := by
      intro hv
      have hxyDeleted :
          (leftEdgeDeletedGraph G x z).Adj x y := by
        simpa [hv, hyCut] using hvCutAdj
      exact M.roots_not_adj
        ((show leftEdgeDeletedGraph G x z ≤ G from sdiff_le)
          hxyDeleted)
    have hvy : v ≠ y := by
      simpa [hyCut] using hvCut
    have hvCarrier :
        v ∈ D.lobe.carrier :=
      Finset.mem_insert.mpr (Or.inr hvInner)
    have hvz : v ≠ z := by
      intro h
      have hvNotCarrier : v ∉ D.lobe.carrier := by
        simpa only [h] using D.other_not_carrier
      exact hvNotCarrier hvCarrier
    exact ⟨v, hvCarrier, hvx, hvy, hvz, hvCut⟩
  · have hyInner : y ∈ D.lobe.inner := by
      rcases Finset.mem_insert.mp hyCarrier with hyCut' | hyInner
      · exact False.elim (hyCut hyCut')
      · exact hyInner
    have hxCut : x ≠ D.lobe.cut := by
      intro h
      exact D.lobe.cut_not_inner (h ▸ D.root_mem)
    have hyz : y ≠ z := by
      intro h
      exact D.other_not_carrier (h ▸ hyCarrier)
    let yD :
        {v : V // v ∉ ({D.lobe.cut} : Finset V)} :=
      ⟨y, by simpa using hyCut⟩
    let xD :
        {v : V // v ∉ ({D.lobe.cut} : Finset V)} :=
      ⟨x, by simpa using hxCut⟩
    obtain ⟨p⟩ :=
      (M.underlying_two_connected.2
        ({D.lobe.cut} : Finset V) (by simp)).preconnected yD xD
    have hyDxD : yD ≠ xD := by
      intro h
      exact M.roots_ne
        (congrArg Subtype.val h).symm
    have hpNotNil : ¬p.Nil :=
      p.not_nil_of_ne hyDxD
    let v := p.snd.1
    have hyv : G.Adj y v := by
      exact p.adj_snd hpNotNil
    have hvCut : v ≠ D.lobe.cut := by
      have hvNotMem :
          v ∉ ({D.lobe.cut} : Finset V) :=
        p.snd.2
      simpa using hvNotMem
    have hvx : v ≠ x := by
      intro h
      apply M.roots_not_adj
      simpa [v, h] using hyv.symm
    have hvy : v ≠ y :=
      hyv.ne.symm
    have hyvSwap :
        (leftEdgeSwapGraph G x y z).Adj y v := by
      rw [leftEdgeSwapGraph, SimpleGraph.sup_adj]
      apply Or.inl
      rw [leftEdgeDeletedGraph, SimpleGraph.sdiff_adj]
      refine ⟨hyv, ?_⟩
      simp [SimpleGraph.edge_adj, M.roots_ne.symm, hyz]
    have hvInner : v ∈ D.lobe.inner := by
      rcases D.lobe.closed hyInner hyvSwap with hvInner | hvCut'
      · exact hvInner
      · exact False.elim (hvCut hvCut')
    have hvCarrier :
        v ∈ D.lobe.carrier :=
      Finset.mem_insert.mpr (Or.inr hvInner)
    have hvz : v ≠ z := by
      intro h
      have hvNotCarrier : v ∉ D.lobe.carrier := by
        simpa only [h] using D.other_not_carrier
      exact hvNotCarrier hvCarrier
    exact ⟨v, hvCarrier, hvx, hvy, hvz, hvCut⟩

/-- The carrier of the selected edge-swap lobe has at least three vertices. -/
theorem three_le_carrier_card_of_edgeSwap
    (M : MinimalCounterexample q G x y z)
    (hxz : G.Adj x z)
    (D : MinimalRootLobeData
      (leftEdgeSwapGraph G x y z) x z) :
    3 ≤ D.lobe.carrier.card := by
  obtain ⟨v, hvCarrier, hvx, hvy, -, -⟩ :=
    D.exists_ordinary_carrier_of_edgeSwap M hxz
  have hxCarrier : x ∈ D.lobe.carrier :=
    Finset.mem_insert.mpr (Or.inr D.root_mem)
  have hyCarrier :=
    D.other_root_mem_of_edgeSwap M
  have hsubset :
      ({x, y, v} : Finset V) ⊆ D.lobe.carrier := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxCarrier
    · exact hyCarrier
    · exact hvCarrier
  have hcard :=
    Finset.card_le_card hsubset
  have hthree :
      ({x, y, v} : Finset V).card = 3 := by
    simp [M.roots_ne, hvx.symm, hvy.symm]
  omega

end MinimalRootLobeData

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
The canonical minimum lobe selected on the `x`-side of the protected-edge
swap.
-/
noncomputable def edgeSwapLobe
    (M : MinimalCounterexample q G x y z)
    (hxz : G.Adj x z) :
    MinimalRootLobeData
      (leftEdgeSwapGraph G x y z) x z := by
  let S := M.edgeSwapCutSetup hxz
  exact Classical.choice
    (exists_minimalRootLobeData
      (leftEdgeSwapGraph G x y z) x z
      S.swap_connected S.swap_not_two_connected
      S.restored_two_connected
      (by
        have hfive := M.five_le_card
        omega))

/-- The other root belongs to the canonical edge-swap lobe. -/
theorem edgeSwapLobe_other_root_mem
    (M : MinimalCounterexample q G x y z)
    (hxz : G.Adj x z) :
    y ∈ (M.edgeSwapLobe hxz).lobe.carrier :=
  (M.edgeSwapLobe hxz).other_root_mem_of_edgeSwap M

/-- The canonical edge-swap lobe has at least three vertices. -/
theorem edgeSwapLobe_three_le_carrier_card
    (M : MinimalCounterexample q G x y z)
    (hxz : G.Adj x z) :
    3 ≤ (M.edgeSwapLobe hxz).lobe.carrier.card :=
  (M.edgeSwapLobe hxz).three_le_carrier_card_of_edgeSwap M hxz

/--
The canonical edge-swap lobe contains an ordinary vertex, distinct from
both roots and from its cut vertex.
-/
theorem edgeSwapLobe_exists_ordinary_carrier
    (M : MinimalCounterexample q G x y z)
    (hxz : G.Adj x z) :
    ∃ v ∈ (M.edgeSwapLobe hxz).lobe.carrier,
      v ≠ x ∧ v ≠ y ∧ v ≠ z ∧
        v ≠ (M.edgeSwapLobe hxz).lobe.cut :=
  (M.edgeSwapLobe hxz).exists_ordinary_carrier_of_edgeSwap M hxz

end MinimalCounterexample

end COY

end DeanK5
