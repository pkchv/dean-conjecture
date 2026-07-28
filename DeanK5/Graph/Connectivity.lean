import DeanK5.Graph.Separation

/-!
# Connectivity transport

The paper moves repeatedly between finite graphs on equivalent
carriers.  This file records that the project's explicit vertex-connectivity
predicate is invariant under graph isomorphism.
-/

open SimpleGraph
open scoped Sym2

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

/-- Adding edges preserves finite vertex connectivity. -/
theorem IsKConnected.mono
    [Fintype V]
    {G H : SimpleGraph V} {k : ℕ}
    (hG : IsKConnected G k)
    (hGH : G ≤ H) :
    IsKConnected H k := by
  constructor
  · exact hG.1
  · intro S hScard
    exact (hG.2 S hScard).mono
      (by
        intro a b hab
        exact hGH hab)

namespace ClassicalGraphTheory

/--
Every vertex of a finite `k`-connected graph has degree at least `k`.
This elementary separator consequence is kept in the low-level
connectivity module so that later theorem proofs can reuse it without
importing higher-level developments.
-/
theorem degree_at_least_connectivity
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hconnected : IsKConnected G k) :
    MinDegreeAtLeast G k := by
  classical
  intro v
  by_contra hdegree
  have hlt : finiteDegree G v < k :=
    Nat.lt_of_not_ge hdegree
  let S : Finset V := (G.neighborSet v).toFinset
  have hSlt : S.card < k := by
    change (G.neighborSet v).toFinset.card < k
    rw [← Set.ncard_eq_toFinset_card']
    change (G.neighborSet v).ncard < k at hlt
    exact hlt
  let T : Finset V := insert v S
  have hTcard : T.card < (Finset.univ : Finset V).card := by
    have hinsert := Finset.card_insert_le v S
    have horder := hconnected.1
    change T.card < Fintype.card V
    dsimp only [T]
    omega
  obtain ⟨w, -, hwT⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hTcard
  have hvS : v ∉ S := by
    simp [S]
  have hwS : w ∉ S := by
    intro hw
    exact hwT (Finset.mem_insert_of_mem hw)
  have hvw : v ≠ w := by
    intro hvw
    subst w
    exact hwT (Finset.mem_insert_self _ _)
  let vS : {x : V // x ∉ S} := ⟨v, hvS⟩
  let wS : {x : V // x ∉ S} := ⟨w, hwS⟩
  have hvwS : vS ≠ wS := by
    intro h
    exact hvw (congrArg Subtype.val h)
  have hreach :
      (G.induce {x : V | x ∉ S}).Reachable vS wS :=
    (hconnected.2 S hSlt) vS wS
  have hsupport :
      vS ∈ (G.induce {x : V | x ∉ S}).support :=
    SimpleGraph.mem_support_of_reachable hvwS hreach
  obtain ⟨z, hvz⟩ :=
    (G.induce {x : V | x ∉ S}).mem_support.mp hsupport
  apply z.2
  change G.Adj v z.1 at hvz
  simpa [S, SimpleGraph.mem_neighborSet] using hvz

end ClassicalGraphTheory

/-- A finite graph is 2-connected once its order, connectivity, and every
single-vertex deletion are supplied explicitly. -/
theorem isTwoConnected_of_connected_delete_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X)
    (horder : 3 ≤ Fintype.card X)
    (hconnected : G.Connected)
    (hdelete : ∀ x : X,
      (G.induce {z | z ≠ x}).Connected) :
    IsTwoConnected G := by
  constructor
  · exact horder
  · intro S hS
    by_cases hzero : S = ∅
    · subst S
      have hset : {v : X | v ∉ (∅ : Finset X)} = Set.univ := by
        ext v
        simp
      rw [hset]
      exact (G.induceUnivIso.connected_iff).2 hconnected
    · have hcard : S.card = 1 := by
        have hpos := Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hzero)
        omega
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
      have hset :
          {v : X | v ∉ ({x} : Finset X)} =
            {z : X | z ≠ x} := by
        ext v
        simp
      rw [hset]
      exact hdelete x

/--
Deleting any one edge from a finite 2-connected graph leaves a connected
graph.

The proof constructs an alternative route between the edge endpoints
through a third vertex, using connectedness after deleting each endpoint.
-/
theorem IsKConnected.connected_delete_edge
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hG : IsKConnected G 2) (a b : V) :
    (G.deleteEdges {s(a, b)}).Connected := by
  classical
  by_cases hab : a = b
  · subst b
    simpa using
      (show G.Connected from by
        have hEmpty :=
          hG.2 (∅ : Finset V) (by simp)
        have hset :
            {v : V | v ∉ (∅ : Finset V)} =
              (Set.univ : Set V) := by
          ext v
          simp
        rw [hset] at hEmpty
        exact (SimpleGraph.Iso.connected_iff
          (SimpleGraph.induceUnivIso G)).mp hEmpty)
  · have hPairCard : ({a, b} : Finset V).card = 2 := by
      simp [hab]
    have hPairSmaller :
        ({a, b} : Finset V).card <
          (Finset.univ : Finset V).card := by
      rw [hPairCard, Finset.card_univ]
      exact hG.1
    obtain ⟨c, -, hcPair⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card
        hPairSmaller
    have hcPair' : c ≠ a ∧ c ≠ b := by
      simpa [hab] using hcPair
    have hca : c ≠ a := hcPair'.1
    have hcb : c ≠ b := hcPair'.2
    have hDeleteB :=
      hG.2 ({b} : Finset V) (by simp)
    have hDeleteA :=
      hG.2 ({a} : Finset V) (by simp)
    let aB : {v : V // v ∉ ({b} : Finset V)} :=
      ⟨a, by simpa using hab⟩
    let cB : {v : V // v ∉ ({b} : Finset V)} :=
      ⟨c, by simpa using hcb⟩
    let cA : {v : V // v ∉ ({a} : Finset V)} :=
      ⟨c, by simpa using hca⟩
    let bA : {v : V // v ∉ ({a} : Finset V)} :=
      ⟨b, by simpa using Ne.symm hab⟩
    obtain ⟨p⟩ :=
      hDeleteB.preconnected aB cB
    obtain ⟨q⟩ :=
      hDeleteA.preconnected cA bA
    let pG : G.Walk a c :=
      p.map (Embedding.induce
        {v : V | v ∉ ({b} : Finset V)}).toHom
    let qG : G.Walk c b :=
      q.map (Embedding.induce
        {v : V | v ∉ ({a} : Finset V)}).toHom
    have hbAvoid : b ∉ pG.support := by
      intro hb
      change b ∈
        (p.map (Embedding.induce
          {v : V | v ∉ ({b} : Finset V)}).toHom).support at hb
      rw [SimpleGraph.Walk.support_map] at hb
      obtain ⟨v, -, hv⟩ := List.mem_map.mp hb
      apply v.2
      change v.1 = b at hv
      simpa using hv
    have haAvoid : a ∉ qG.support := by
      intro ha
      change a ∈
        (q.map (Embedding.induce
          {v : V | v ∉ ({a} : Finset V)}).toHom).support at ha
      rw [SimpleGraph.Walk.support_map] at ha
      obtain ⟨v, -, hv⟩ := List.mem_map.mp ha
      apply v.2
      change v.1 = a at hv
      simpa using hv
    have hpEdgeAvoid : s(a, b) ∉ pG.edges := by
      intro he
      exact hbAvoid (pG.snd_mem_support_of_mem_edges he)
    have hqEdgeAvoid : s(a, b) ∉ qG.edges := by
      intro he
      exact haAvoid (qG.fst_mem_support_of_mem_edges he)
    have hreach :
        (G.deleteEdges {s(a, b)}).Reachable a b := by
      exact ⟨
        (pG.toDeleteEdges {s(a, b)} (by
          intro e he
          simp only [Set.mem_singleton_iff]
          intro hes
          apply hpEdgeAvoid
          simpa [hes] using he)).append
        (qG.toDeleteEdges {s(a, b)} (by
          intro e he
          simp only [Set.mem_singleton_iff]
          intro hes
          apply hqEdgeAvoid
          simpa [hes] using he))⟩
    have hnotBridge : ¬G.IsBridge s(a, b) := by
      simpa [SimpleGraph.isBridge_iff] using hreach
    have hConnected : G.Connected := by
      have hEmpty :=
        hG.2 (∅ : Finset V) (by simp)
      have hset :
          {v : V | v ∉ (∅ : Finset V)} =
            (Set.univ : Set V) := by
        ext v
        simp
      rw [hset] at hEmpty
      exact (SimpleGraph.Iso.connected_iff
        (SimpleGraph.induceUnivIso G)).mp hEmpty
    exact hConnected.connected_delete_edge_of_not_isBridge
      hnotBridge

/-- Deleting one simple-graph edge from a finite 2-connected graph leaves it connected. -/
theorem IsKConnected.connected_sdiff_edge
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hG : IsKConnected G 2) (a b : V) :
    (G \ edge a b).Connected := by
  by_cases hab : a = b
  · subst b
    simpa [SimpleGraph.sdiff_edge] using
      hG.connected_delete_edge a a
  · simpa [← SimpleGraph.deleteEdges_edgeSet,
      SimpleGraph.edgeSet_edge_of_ne hab] using
      hG.connected_delete_edge a b

end DeanK5
