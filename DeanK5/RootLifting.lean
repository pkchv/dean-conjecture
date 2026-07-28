import DeanK5.Graph.RootAdjunction
import DeanK5.GHLMRootedInternal

/-!
# Root lifting (paper Section 3.3)

This file formalizes the bookkeeping behind paper Lemma 3.3. A new root is
joined to a specified set of vertices; the low-level construction, degree
calculation, and connectivity transport live in `Graph.RootAdjunction`.
-/

open Function
open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
The output of root lifting.  It is represented in the explicit graph
`adjoinRoot G Z`; for zero or one deficient vertex the resulting paths are
certified not to use the newly adjoined root.
-/
def RootLiftResult
    (G : SimpleGraph V) (Z : Finset V)
    (x y : V) (q : ℕ) : Prop :=
  ∃ family :
      AdmissiblePathFamily (adjoinRoot G Z) (some x) (some y) q,
    Z.card < 2 →
      ∀ i, none ∉ (family.path i).walk.support

/-- Root-lifted paths after mapping back into the paper's ambient block. -/
def AmbientRootLiftResult
    {W : Type*} (H : SimpleGraph W) (c : W)
    (x y : W) (q : ℕ) (allowed : Set W) (small : Prop) : Prop :=
  ∃ family : AdmissiblePathFamily H x y q,
    (∀ i v, v ∈ (family.path i).walk.support →
      v = c ∨ v ∈ allowed) ∧
    (small → ∀ i, c ∉ (family.path i).walk.support)

/--
Map a root-lifting result into an ambient graph, sending the fresh root to
the distinguished cut vertex `c`.
-/
theorem RootLiftResult.mapToAmbient
    {W : Type*} {H : SimpleGraph W}
    {G : SimpleGraph V} {Z : Finset V} {x y : V} {q : ℕ}
    (result : RootLiftResult G Z x y q)
    (f : G →g H) (c : W)
    (hZ : ∀ z ∈ Z, H.Adj c (f z))
    (hf : Function.Injective f)
    (hc : c ∉ Set.range f) :
    AmbientRootLiftResult H c (f x) (f y) q
      (Set.range f) (Z.card < 2) := by
  obtain ⟨F, havoid⟩ := result
  let φ := adjoinRootHom G Z f c hZ
  have hφ : Function.Injective φ :=
    adjoinRootHom_injective G Z f c hZ hf hc
  let F' := F.mapInjectiveHom φ hφ
  refine ⟨F', ?_⟩
  constructor
  · intro i v hv
    have hv' := hv
    change v ∈ ((F.path i).walk.map φ).support at hv'
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv'
    cases w with
    | none => exact Or.inl rfl
    | some a => exact Or.inr ⟨a, rfl⟩
  · intro hsmall i hcSupport
    have hcSupport' := hcSupport
    change c ∈ ((F.path i).walk.map φ).support at hcSupport'
    rw [SimpleGraph.Walk.support_map] at hcSupport'
    obtain ⟨w, hw, hφw⟩ := List.mem_map.mp hcSupport'
    have hwnone : w = none := by
      apply hφ
      simpa [φ, adjoinRootHom] using hφw
    exact havoid hsmall i (hwnone ▸ hw)

/--
Paper Lemma 3.3, in its graph-theoretic core form.

`D`, `Z ⊆ D`, and nonadjacency of the roots retain the context in which the
lemma is invoked in the paper.  Once 2-connectivity after adjoining the root
edge and the two explicit degree bounds in (3.4) are supplied, the core
argument does not use those bookkeeping hypotheses.  The ambient embedding
of this explicit root-adjoined graph into the paper's end block `B` is
deliberately left to each application.
-/
theorem root_lifting
    [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (D Z : Finset V) (x y : V)
    (hqTwo : 2 ≤ q) (hqFour : q ≤ 4)
    (hxy : x ≠ y)
    (_hnotadj : ¬ G.Adj x y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (_hZD : Z ⊆ D)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z)
    (hdeg : ∀ v, v ≠ x → v ≠ y → v ∉ Z →
      q + 1 ≤ finiteDegree G v)
    (hdegZ : ∀ z ∈ Z, q ≤ finiteDegree G z)
    (horder_one : Z.card = 1 → 4 ≤ Fintype.card V) :
    RootLiftResult G Z x y q := by
  rcases lt_trichotomy Z.card 1 with hzero | hone | hlarge
  · have hZ0 : Z = ∅ := Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hzero)
    obtain ⟨F⟩ := GHLM.rooted_admissible_paths_internal
      q G x y hqTwo hqFour hxy hconn
      (fun v hvx hvy => hdeg v hvx hvy (by simp [hZ0]))
    let F' := F.mapEmbedding (someEmbedding G Z)
    refine ⟨F', ?_⟩
    intro _ i
    simp [F', AdmissiblePathFamily.mapEmbedding,
      SimplePath.mapEmbedding, someEmbedding]
  · have hZ1 : Z.card = 1 := hone
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hZ1
    obtain ⟨F⟩ := COY.one_exception_rooted_paths_internal q G x y z
      hqTwo hqFour (horder_one (by simp)) hxy
      (by
        intro hzx
        apply hxZ
        simp [hzx])
      (by
        intro hzy
        apply hyZ
        simp [hzy])
      hconn
      (fun v hvx hvy hvz => hdeg v hvx hvy (by simpa using hvz))
    let F' := F.mapEmbedding (someEmbedding G {z})
    refine ⟨F', ?_⟩
    intro _ i
    simp [F', AdmissiblePathFamily.mapEmbedding,
      SimplePath.mapEmbedding, someEmbedding]
  · have hZ2 : 2 ≤ Z.card := hlarge
    have horderV : 3 ≤ Fintype.card V := hconn.1
    have horderOption : 4 ≤ Fintype.card (Option V) := by
      simp only [Fintype.card_option]
      omega
    have hconn' :
        IsTwoConnected
          (adjoinRoot G Z ⊔ edge (some x) (some y)) := by
      rw [← adjoinRoot_sup_edge]
      exact isTwoConnected_adjoinRoot (G ⊔ edge x y) Z hconn hZ2
    obtain ⟨F⟩ :=
      COY.one_exception_rooted_paths_internal q (adjoinRoot G Z)
        (some x) (some y) none hqTwo hqFour horderOption
        (by simpa using hxy) (by simp) (by simp) hconn' (by
          intro v hvx hvy hvroot
          cases v with
          | none => exact False.elim (hvroot rfl)
          | some v =>
              rw [finiteDegree_adjoinRoot_some]
              by_cases hvZ : v ∈ Z
              · have hv := hdegZ v hvZ
                simp only [hvZ, if_pos]
                omega
              · have hvx' : v ≠ x := by
                  intro h
                  exact hvx (by simp [h])
                have hvy' : v ≠ y := by
                  intro h
                  exact hvy (by simp [h])
                have hv := hdeg v hvx' hvy' hvZ
                simp only [hvZ, if_false, add_zero]
                exact hv)
    refine ⟨F, ?_⟩
    intro hsmall
    omega

end DeanK5
