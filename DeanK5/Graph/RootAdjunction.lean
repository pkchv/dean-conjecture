import DeanK5.Graph.Basic

/-!
# Adjoining one root vertex

This module contains the low-level graph, degree, path-transport, and
connectivity facts for adjoining a new vertex to a prescribed finite set.
It has no dependency on any published theorem.
-/

open Function
open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/-- Add one new vertex, adjacent precisely to the vertices in `Z`. -/
def adjoinRoot
    (G : SimpleGraph V) (Z : Finset V) : SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some u, some v => G.Adj u v
    | none, some v => v ∈ Z
    | some u, none => u ∈ Z
    | none, none => False
  symm := by
    constructor
    intro a b h
    cases a with
    | none =>
        cases b with
        | none => exact h
        | some v => exact h
    | some u =>
        cases b with
        | none => exact h
        | some v => exact G.symm.symm _ _ h
  loopless := by
    constructor
    intro a
    cases a <;> simp

@[simp] theorem adjoinRoot_adj_some_some
    (G : SimpleGraph V) (Z : Finset V) (u v : V) :
    (adjoinRoot G Z).Adj (some u) (some v) ↔ G.Adj u v :=
  Iff.rfl

@[simp] theorem adjoinRoot_adj_none_some
    (G : SimpleGraph V) (Z : Finset V) (v : V) :
    (adjoinRoot G Z).Adj none (some v) ↔ v ∈ Z :=
  Iff.rfl

@[simp] theorem adjoinRoot_adj_some_none
    (G : SimpleGraph V) (Z : Finset V) (v : V) :
    (adjoinRoot G Z).Adj (some v) none ↔ v ∈ Z :=
  Iff.rfl

/-- The old graph is an induced subgraph of the graph with the new root. -/
def someEmbedding
    (G : SimpleGraph V) (Z : Finset V) : G ↪g adjoinRoot G Z where
  toFun := some
  inj' := fun _ _ h => Option.some.inj h
  map_rel_iff' := by simp

/--
Map the explicit root-adjoined graph into an ambient graph.  Extra ambient
edges at `c` are allowed, so this is a homomorphism rather than a graph
embedding.
-/
def adjoinRootHom
    {W : Type*} {H : SimpleGraph W}
    (G : SimpleGraph V) (Z : Finset V)
    (f : G →g H) (c : W)
    (hZ : ∀ z ∈ Z, H.Adj c (f z)) :
    adjoinRoot G Z →g H where
  toFun
    | none => c
    | some v => f v
  map_rel' := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact False.elim hab
        | some v => exact hZ v hab
    | some u =>
        cases b with
        | none => exact (hZ u hab).symm
        | some v => exact f.map_rel' hab

theorem adjoinRootHom_injective
    {W : Type*} {H : SimpleGraph W}
    (G : SimpleGraph V) (Z : Finset V)
    (f : G →g H) (c : W)
    (hZ : ∀ z ∈ Z, H.Adj c (f z))
    (hf : Function.Injective f)
    (hc : c ∉ Set.range f) :
    Function.Injective (adjoinRootHom G Z f c hZ) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some v =>
          exact False.elim (hc ⟨v, by
            simpa [adjoinRootHom] using hab.symm⟩)
  | some u =>
      cases b with
      | none =>
          exact False.elim (hc ⟨u, by
            simpa [adjoinRootHom] using hab⟩)
      | some v =>
          simpa [adjoinRootHom] using hf (by
            simpa [adjoinRootHom] using hab)

theorem adjoinRoot_neighborSet_some [DecidableEq V]
    (G : SimpleGraph V) (Z : Finset V) (v : V) :
    (adjoinRoot G Z).neighborSet (some v) =
      if v ∈ Z then insert none (some '' G.neighborSet v)
      else some '' G.neighborSet v := by
  ext w
  by_cases hv : v ∈ Z
  · cases w <;> simp [adjoinRoot, hv]
  · cases w <;> simp [adjoinRoot, hv]

/-- An attached old vertex gains exactly the new root as one neighbour. -/
theorem finiteDegree_adjoinRoot_some
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : Finset V) (v : V) :
    finiteDegree (adjoinRoot G Z) (some v) =
      finiteDegree G v + if v ∈ Z then 1 else 0 := by
  unfold finiteDegree
  rw [adjoinRoot_neighborSet_some]
  by_cases hv : v ∈ Z
  · simp only [hv, if_pos]
    rw [Set.ncard_insert_of_notMem (by simp),
      Set.ncard_image_of_injective _ (fun _ _ h => Option.some.inj h)]
  · simp only [hv, if_false, add_zero]
    exact Set.ncard_image_of_injective _ (fun _ _ h => Option.some.inj h)

/-- Map a simple path through a graph embedding. -/
def SimplePath.mapEmbedding
    {G : SimpleGraph V} {W : Type*} {H : SimpleGraph W}
    {x y : V} (P : SimplePath G x y) (f : G ↪g H) :
    SimplePath H (f x) (f y) :=
  ⟨P.walk.map f.toHom, P.isPath.map f.injective⟩

@[simp] theorem SimplePath.mapEmbedding_length
    {G : SimpleGraph V} {W : Type*} {H : SimpleGraph W}
    {x y : V} (P : SimplePath G x y) (f : G ↪g H) :
    (P.mapEmbedding f).length = P.length := by
  simp [SimplePath.mapEmbedding, SimplePath.length]

/-- An embedding transports an admissible path family without changing lengths. -/
def AdmissiblePathFamily.mapEmbedding
    {G : SimpleGraph V} {W : Type*} {H : SimpleGraph W}
    {x y : V} {q : ℕ} (F : AdmissiblePathFamily G x y q)
    (f : G ↪g H) :
    AdmissiblePathFamily H (f x) (f y) q where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := F.start_ge_two
  path i := (F.path i).mapEmbedding f
  length_path i := by simp [F.length_path i]

@[simp] theorem adjoinRoot_sup_edge
    (G : SimpleGraph V) (Z : Finset V) (x y : V) :
    adjoinRoot (G ⊔ edge x y) Z =
      adjoinRoot G Z ⊔ edge (some x) (some y) := by
  ext a b
  cases a <;> cases b <;> simp [adjoinRoot, edge]

private def oldDeletion [Fintype V] [DecidableEq V]
    (S : Finset (Option V)) : Finset V :=
  Finset.univ.filter fun v => some v ∈ S

private theorem oldDeletion_card_le
    [Fintype V] [DecidableEq V] (S : Finset (Option V)) :
    (oldDeletion S).card ≤ S.card := by
  calc
    (oldDeletion S).card =
        ((oldDeletion S).image some).card := by
          symm
          exact Finset.card_image_of_injective _
            (fun _ _ h => Option.some.inj h)
    _ ≤ S.card := Finset.card_le_card (by
      intro w hw
      simp only [Finset.mem_image] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      simpa [oldDeletion] using hv)

private theorem exists_attached_vertex_outside
    [Fintype V] [DecidableEq V]
    (Z : Finset V) (S : Finset (Option V))
    (hZ : 2 ≤ Z.card) (hS : S.card < 2) :
    ∃ z ∈ Z, some z ∉ S := by
  by_contra h
  push Not at h
  have hsub : Z.image some ⊆ S := by
    intro w hw
    simp only [Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact h z hz
  have hcard : Z.card ≤ S.card := by
    rw [← Finset.card_image_of_injective Z
      (fun _ _ h => Option.some.inj h)]
    exact Finset.card_le_card hsub
  omega

/--
Adding a vertex with at least two neighbours preserves 2-connectivity.

The proof treats all deletion sets of cardinality less than two.  If the
new root survives, at least one of its two neighbours survives as well.
-/
theorem isTwoConnected_adjoinRoot
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : Finset V)
    (hG : IsTwoConnected G) (hZ : 2 ≤ Z.card) :
    IsTwoConnected (adjoinRoot G Z) := by
  constructor
  · have horder : 3 ≤ Fintype.card V := hG.1
    simp only [Fintype.card_option]
    omega
  · intro S hS
    let R := oldDeletion S
    have hRcard : R.card < 2 :=
      lt_of_le_of_lt (oldDeletion_card_le S) hS
    have hbase : (G.induce {v | v ∉ R}).Connected :=
      hG.2 R hRcard
    obtain ⟨z, hzZ, hzS⟩ :=
      exists_attached_vertex_outside Z S hZ hS
    have hzR : z ∉ R := by
      simpa [R, oldDeletion] using hzS
    let f :
        G.induce {v | v ∉ R} →g
          (adjoinRoot G Z).induce {w | w ∉ S} := {
      toFun v := ⟨some v.1, by
        simpa [R, oldDeletion] using v.2⟩
      map_rel' := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        exact hab
    }
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨some z, hzS⟩, ?_⟩
    rintro ⟨w, hw⟩
    cases w with
    | none =>
        exact (show
          ((adjoinRoot G Z).induce {w | w ∉ S}).Adj
            ⟨some z, hzS⟩ ⟨none, hw⟩ by
              exact hzZ).reachable
    | some v =>
        have hvR : v ∉ R := by
          simpa [R, oldDeletion] using hw
        have hr :=
          hbase.preconnected ⟨z, hzR⟩ ⟨v, hvR⟩
        simpa [f] using hr.map f

end DeanK5
