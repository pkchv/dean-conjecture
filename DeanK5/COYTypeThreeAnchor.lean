import DeanK5.COYCoreStructure
import DeanK5.Graph.Connectivity

/-!
# A rooted 2-connected anchor inside a type-3 COY core

When the `S`-side of a type-3 core is the singleton `{s}`, its induced
carrier contains the complete bipartite graph between `{x, s}` and `T`.
After adjoining the root edge `xs`, deleting any one carrier vertex leaves
a connected graph.  This file records that elementary anchor explicitly
for the non-singleton-exterior induction.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace TypeThreeCore

variable [DecidableEq V]
  {G : SimpleGraph V} {x s : V} {ℓ : ℕ}

/-- The vertex type of the full carrier of a type-3 core. -/
abbrev Carrier (C : TypeThreeCore G x ℓ) :=
  (↑(Core.typeThree C).carrier : Set V)

/-- The graph induced by the full carrier of a type-3 core. -/
abbrev carrierGraph (C : TypeThreeCore G x ℓ) :
    SimpleGraph C.Carrier :=
  G.induce (↑(Core.typeThree C).carrier : Set V)

/-- The core root as a vertex of the induced carrier graph. -/
def rootVertex (C : TypeThreeCore G x ℓ) :
    C.Carrier :=
  ⟨x, (Core.typeThree C).root_mem_carrier⟩

/-- A selected `S`-vertex as a vertex of the induced carrier graph. -/
def sideVertex
    (C : TypeThreeCore G x ℓ)
    (s : V) (hs : s ∈ C.S) :
    C.Carrier :=
  ⟨s, (Core.typeThree C).S_subset_carrier
    (by simpa [Core.S] using hs)⟩

/--
If the `S`-side of a type-3 core is `{s}`, then the induced carrier,
rooted at `x` and `s`, is 2-connected.

The added edge `xs` is only the rooted-connectivity edge.  All other
adjacencies used below are genuine core edges in `G`.
-/
theorem carrierGraph_sup_root_side_two_connected
    (C : TypeThreeCore G x ℓ)
    (hS : C.S = {s}) :
    IsTwoConnected
      (C.carrierGraph ⊔
        edge C.rootVertex
          (C.sideVertex s (by rw [hS]; simp))) := by
  classical
  let hs : s ∈ C.S := by
    rw [hS]
    simp
  let xC : C.Carrier := C.rootVertex
  let sC : C.Carrier := C.sideVertex s hs
  let H : SimpleGraph C.Carrier :=
    C.carrierGraph ⊔ edge xC sC
  have hxs : x ≠ s := by
    intro h
    exact C.root_not_mem_S (h ▸ hs)
  have hxCsC : xC ≠ sC := by
    intro h
    exact hxs (congrArg Subtype.val h)
  have hrootSide : H.Adj xC sC := by
    change
      (C.carrierGraph ⊔ edge xC sC).Adj xC sC
    exact
      (le_sup_right :
        edge xC sC ≤
          C.carrierGraph ⊔ edge xC sC)
      (by simpa [SimpleGraph.edge_adj] using hxCsC)
  have hrootT :
      ∀ (v : C.Carrier), v.1 ∈ C.T →
        H.Adj xC v := by
    intro v hvT
    change
      (C.carrierGraph ⊔ edge xC sC).Adj xC v
    exact
      (le_sup_left :
        C.carrierGraph ≤
          C.carrierGraph ⊔ edge xC sC)
        (C.root_adj_T v.1 hvT)
  have hsideT :
      ∀ (v : C.Carrier), v.1 ∈ C.T →
        H.Adj sC v := by
    intro v hvT
    change
      (C.carrierGraph ⊔ edge xC sC).Adj sC v
    exact
      (le_sup_left :
        C.carrierGraph ≤
          C.carrierGraph ⊔ edge xC sC)
        (C.cross_adj v.1 hvT s hs).symm
  have hclassify :
      ∀ v : C.Carrier,
        v = xC ∨ v = sC ∨ v.1 ∈ C.T := by
    intro v
    have hv := v.2
    change
      v.1 ∈ insert x (C.S ∪ C.T) at hv
    simp only [Finset.mem_insert,
      Finset.mem_union] at hv
    rcases hv with hvx | hvS | hvT
    · exact Or.inl (Subtype.ext hvx)
    · have hvs : v.1 = s := by
        rw [hS] at hvS
        simpa using hvS
      exact Or.inr (Or.inl (Subtype.ext hvs))
    · exact Or.inr (Or.inr hvT)
  have horder : 3 ≤ Fintype.card C.Carrier := by
    have hTtwo : 2 ≤ C.T.card :=
      (Nat.le_max_right (ℓ + 1) 2).trans
        C.card_T_lower
    have hcard :
        Fintype.card C.Carrier =
          (insert x (C.S ∪ C.T)).card := by
      simp [Carrier, Core.carrier, Core.S, Core.T]
    rw [hcard]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_union_of_disjoint C.disjoint, hS]
      simp only [Finset.card_singleton]
      omega
    · simp only [Finset.mem_union]
      exact not_or_intro C.root_not_mem_S
        C.root_not_mem_T
  change IsTwoConnected H
  apply isTwoConnected_of_connected_delete_one H horder
  · rw [connected_iff_exists_forall_reachable]
    refine ⟨xC, ?_⟩
    intro v
    rcases hclassify v with hv | hv | hvT
    · subst v
      exact SimpleGraph.Reachable.refl xC
    · subst v
      exact hrootSide.reachable
    · exact (hrootT v hvT).reachable
  · intro r
    by_cases hrx : r = xC
    · have hsCr : sC ≠ r := by
        intro h
        exact hxCsC (hrx.symm.trans h.symm)
      let sD : {v : C.Carrier // v ≠ r} :=
        ⟨sC, hsCr⟩
      rw [connected_iff_exists_forall_reachable]
      refine ⟨sD, ?_⟩
      intro v
      rcases hclassify v.1 with hv | hv | hvT
      · apply False.elim
        apply v.2
        exact hv.trans hrx.symm
      · have hvsD : v = sD := by
          apply Subtype.ext
          exact hv
        subst v
        exact SimpleGraph.Reachable.refl sD
      · have hadj :
            (H.induce {v : C.Carrier | v ≠ r}).Adj
              sD v := by
          exact hsideT v.1 hvT
        exact hadj.reachable
    · have hxCr : xC ≠ r := by
        intro h
        exact hrx h.symm
      let xD : {v : C.Carrier // v ≠ r} :=
        ⟨xC, hxCr⟩
      rw [connected_iff_exists_forall_reachable]
      refine ⟨xD, ?_⟩
      intro v
      rcases hclassify v.1 with hv | hv | hvT
      · have hvxD : v = xD := by
          apply Subtype.ext
          exact hv
        subst v
        exact SimpleGraph.Reachable.refl xD
      · have hadj :
            (H.induce {v : C.Carrier | v ≠ r}).Adj
              xD v := by
          change H.Adj xC v.1
          simpa [hv] using hrootSide
        exact hadj.reachable
      · have hadj :
            (H.induce {v : C.Carrier | v ≠ r}).Adj
              xD v := by
          exact hrootT v.1 hvT
        exact hadj.reachable

end TypeThreeCore

end COY

end DeanK5
