import DeanK5.EndLobeExistence
import DeanK5.Graph.Connectivity
import DeanK5.MengerTwo

/-!
# Classical finite graph theory

This module collects the ordinary finite-graph facts used by the paper.
-/

open scoped Sym2

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace ClassicalGraphTheory

/-- Finite degree is invariant under a graph isomorphism. -/
theorem finiteDegree_iso
    {W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) (v : V) :
    finiteDegree G v = finiteDegree H (e v) := by
  unfold finiteDegree
  exact Set.ncard_congr' (e.mapNeighborSet v)

/-- A left vertex in a finite complete bipartite graph has degree equal
to the cardinality of the right part. -/
theorem finiteDegree_completeBipartite_inl
    {A B : Type*} [Fintype A] [Fintype B]
    (a : A) :
    finiteDegree (completeBipartiteGraph A B) (Sum.inl a) =
      Fintype.card B := by
  unfold finiteDegree
  have hneighbor :
      (completeBipartiteGraph A B).neighborSet (Sum.inl a) =
        Set.range (Sum.inr : B → A ⊕ B) := by
    ext z
    cases z <;> simp [SimpleGraph.mem_neighborSet]
  rw [hneighbor, Set.ncard_range_of_injective Sum.inr_injective,
    Nat.card_eq_fintype_card]

private def completeBipartiteFiveCycleWalk :
    (completeBipartiteGraph (Fin 5) (Fin 5)).Walk
      (Sum.inl 0) (Sum.inl 0) :=
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inl 0) (Sum.inr 0) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inr 0) (Sum.inl 1) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inl 1) (Sum.inr 1) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inr 1) (Sum.inl 2) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inl 2) (Sum.inr 2) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inr 2) (Sum.inl 3) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inl 3) (Sum.inr 3) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inr 3) (Sum.inl 4) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inl 4) (Sum.inr 4) by simp) <|
  .cons (show (completeBipartiteGraph (Fin 5) (Fin 5)).Adj
      (Sum.inr 4) (Sum.inl 0) by simp) .nil

private theorem completeBipartiteFiveCycleWalk_isCycle :
    completeBipartiteFiveCycleWalk.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  simp [completeBipartiteFiveCycleWalk,
    SimpleGraph.Walk.isTrail_def]

private def completeBipartiteFiveCycle :
    SimpleCycle (completeBipartiteGraph (Fin 5) (Fin 5)) where
  base := Sum.inl 0
  walk := completeBipartiteFiveCycleWalk
  isCycle := completeBipartiteFiveCycleWalk_isCycle

private theorem completeBipartiteFiveCycle_length :
    completeBipartiteFiveCycle.length = 10 := by
  simp [completeBipartiteFiveCycle,
    completeBipartiteFiveCycleWalk, SimpleCycle.length]

/-- A complete graph on six vertices contains a 5-cycle. -/
theorem complete_six_has_five_cycle
    (G : SimpleGraph V)
    (hcomplete : IsCompleteGraphOfOrder G 6) :
    HasCycleLength G 5 := by
  classical
  obtain ⟨e⟩ := hcomplete
  let inclusion : Fin 5 ↪ Fin 6 :=
    Fin.castLEEmb (by omega)
  let f :
      cycleGraph 5 →g completeGraph (Fin 6) := {
    toFun := inclusion
    map_rel' := by
      intro a b hab
      simp only [top_adj]
      exact inclusion.injective.ne hab.ne
  }
  have hf : Function.Injective f :=
    inclusion.injective
  let C₅ : SimpleCycle (cycleGraph 5) := {
    base := 0
    walk := cycleGraph.cycle 2
    isCycle := cycleGraph.isCycle_cycle
  }
  let C₆ := C₅.mapInjectiveHom f hf
  let C := C₆.mapInjectiveHom
    e.symm.toHom e.symm.injective
  refine ⟨C, ?_⟩
  calc
    C.length = C₆.length := by
      simp only [C, SimpleCycle.mapInjectiveHom_length]
    _ = C₅.length := by
      simp only [C₆, SimpleCycle.mapInjectiveHom_length]
    _ = 5 := by
      simp [C₅, SimpleCycle.length]

/--
A complete bipartite graph with one part of size five and minimum degree
at least five contains a 10-cycle.
-/
theorem complete_bipartite_five_has_ten_cycle
    [Fintype V]
    (G : SimpleGraph V) (t : ℕ)
    (hcomplete : IsCompleteBipartiteOfParts G 5 t)
    (hdegree : MinDegreeAtLeast G 5) :
    HasCycleLength G 10 := by
  classical
  obtain ⟨e⟩ := hcomplete
  let left : V := e.symm (Sum.inl 0)
  have hleft : 5 ≤ finiteDegree G left :=
    hdegree left
  have hdegreeIso :=
    finiteDegree_iso G
      (completeBipartiteGraph (Fin 5) (Fin t))
      e left
  have heleft : e left = Sum.inl 0 := by
    simp [left]
  have ht : 5 ≤ t := by
    rw [hdegreeIso, heleft,
      finiteDegree_completeBipartite_inl] at hleft
    simpa using hleft
  let right : Fin 5 ↪ Fin t :=
    Fin.castLEEmb ht
  let vertexEmbedding :
      (Fin 5 ⊕ Fin 5) ↪ (Fin 5 ⊕ Fin t) :=
    Function.Embedding.sumMap
      (Function.Embedding.refl (Fin 5)) right
  let f :
      completeBipartiteGraph (Fin 5) (Fin 5) →g
        completeBipartiteGraph (Fin 5) (Fin t) := {
    toFun := vertexEmbedding
    map_rel' := by
      intro a b hab
      cases a <;> cases b <;>
        simp_all [vertexEmbedding]
  }
  have hf : Function.Injective f :=
    vertexEmbedding.injective
  let Cₜ :=
    completeBipartiteFiveCycle.mapInjectiveHom f hf
  let C := Cₜ.mapInjectiveHom
    e.symm.toHom e.symm.injective
  refine ⟨C, ?_⟩
  calc
    C.length = Cₜ.length := by
      simp only [C, SimpleCycle.mapInjectiveHom_length]
    _ = completeBipartiteFiveCycle.length := by
      simp only [Cₜ, SimpleCycle.mapInjectiveHom_length]
    _ = 10 := completeBipartiteFiveCycle_length

end ClassicalGraphTheory

end DeanK5
