import DeanK5.COYEdgeSwapSetup
import DeanK5.COYMinimalLobe

/-!
# The recursive rooted instance inside a protected-edge lobe

This file isolates the induction step at the end of COY Claim 3.2(2).
Once the selected edge-swap lobe has the required order and one ordinary
vertex, its induced graph is a strictly smaller rooted instance.  Its
admissible paths map back into the alleged counterexample.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
The recursive lobe construction contradicts minimality once its carrier,
order, and ordinary-vertex facts have been established.
-/
theorem contradiction_of_edge_swap_lobe
    (M : MinimalCounterexample q G x y z)
    (D : MinimalRootLobeData
      (leftEdgeSwapGraph G x y z) x z)
    (hyCarrier : y ∈ D.lobe.carrier)
    (horder :
      3 ≤ Fintype.card
        (↑D.lobe.carrier : Set V))
    (hordinary :
      ∃ w ∈ D.lobe.carrier,
        w ≠ x ∧ w ≠ y ∧ w ≠ D.lobe.cut) :
    False := by
  classical
  let H := leftEdgeDeletedGraph G x z
  let U := CutSide.Vertex D.lobe.inner D.lobe.cut
  let A := CutSide.graph H D.lobe.inner D.lobe.cut
  let xU : U :=
    CutSide.root D.lobe.inner D.lobe.cut x
      D.root_mem
  let yU : U := ⟨y, by
    simpa [U, CutSide.Vertex, CutSide.vertices,
      LobeRegion.carrier] using hyCarrier⟩
  let cU : U :=
    CutSide.cut D.lobe.inner D.lobe.cut
  have hxyU : xU ≠ yU := by
    intro h
    exact M.roots_ne (by
      simpa [xU, yU, CutSide.root,
        CutSide.innerVertex] using
        congrArg Subtype.val h)
  have hgraphIdentity :
      A ⊔ edge xU yU =
        D.lobe.blockGraph := by
    ext a b
    have hedge :
        (edge xU yU).Adj a b ↔
          (edge x y).Adj a.1 b.1 := by
      simp only [SimpleGraph.edge_adj]
      constructor
      · rintro ⟨hab | hab, hne⟩
        · rcases hab with ⟨rfl, rfl⟩
          exact ⟨Or.inl ⟨rfl, rfl⟩,
            fun h => hne (Subtype.ext h)⟩
        · rcases hab with ⟨rfl, rfl⟩
          exact ⟨Or.inr ⟨rfl, rfl⟩,
            fun h => hne (Subtype.ext h)⟩
      · rintro ⟨hab | hab, hne⟩
        · rcases hab with ⟨ha, hb⟩
          have ha' : a = xU := by
            apply Subtype.ext
            simpa [xU, CutSide.root,
              CutSide.innerVertex] using ha
          have hb' : b = yU := by
            apply Subtype.ext
            simpa [yU] using hb
          exact ⟨Or.inl ⟨ha', hb'⟩,
            fun h => hne (congrArg Subtype.val h)⟩
        · rcases hab with ⟨ha, hb⟩
          have ha' : a = yU := by
            apply Subtype.ext
            simpa [yU] using ha
          have hb' : b = xU := by
            apply Subtype.ext
            simpa [xU, CutSide.root,
              CutSide.innerVertex] using hb
          exact ⟨Or.inr ⟨ha', hb'⟩,
            fun h => hne (congrArg Subtype.val h)⟩
    change
      (H.Adj a.1 b.1 ∨ (edge xU yU).Adj a b) ↔
        (H ⊔ edge x y).Adj a.1 b.1
    rw [SimpleGraph.sup_adj]
    exact or_congr Iff.rfl hedge
  have hblockTwo :
      IsTwoConnected D.lobe.blockGraph :=
    ClassicalGraphTheory.minimal_within_block_two_connected_of_three_le_card
        D.initial D.lobe D.within D.minimal horder
  have hrooted : IsTwoConnected (A ⊔ edge xU yU) := by
    rw [hgraphIdentity]
    exact hblockTwo
  obtain ⟨w, hwCarrier, hwx, hwy, hwc⟩ :=
    hordinary
  let wU : U := ⟨w, by
    simpa [U, CutSide.Vertex, CutSide.vertices,
      LobeRegion.carrier] using hwCarrier⟩
  have hcomplexity :
      rootedComplexity A < rootedComplexity G := by
    apply rootedComplexity_lt_of_card_lt_of_edgeCount_le
    · apply CutSide.card_lt_of_not_mem
      simpa [CutSide.vertices, LobeRegion.carrier] using
        D.other_not_carrier
    · calc
        A.edgeSet.ncard ≤ H.edgeSet.ncard := by
          exact CutSide.edgeSet_ncard_le
            H D.lobe.inner D.lobe.cut
        _ ≤ G.edgeSet.ncard := by
          exact Set.ncard_le_ncard
            (SimpleGraph.edgeSet_mono sdiff_le)
            (Set.toFinite G.edgeSet)
  let I : RootedInstance q A xU yU cU := {
    q_pos := M.q_pos
    q_le_four := M.q_le_four
    roots_ne := hxyU
    rooted_two_connected := hrooted
    ordinary_nonempty := by
      refine ⟨wU, ?_, ?_, ?_⟩
      · intro h
        exact hwx (by
          simpa [wU, xU, CutSide.root,
            CutSide.innerVertex] using
            congrArg Subtype.val h)
      · intro h
        exact hwy (by
          simpa [wU, yU] using
            congrArg Subtype.val h)
      · intro h
        exact hwc (by
          simpa [wU, cU, CutSide.cut] using
            congrArg Subtype.val h)
    degree_lower := by
      intro v hvxU hvyU hvcU
      have hvInner :
          v.1 ∈ D.lobe.inner :=
        CutSide.mem_component_of_ne_cut v
          (by simpa [cU] using hvcU)
      have hvx : v.1 ≠ x := by
        intro h
        apply hvxU
        apply Subtype.ext
        simpa [xU] using h
      have hvy : v.1 ≠ y := by
        intro h
        apply hvyU
        apply Subtype.ext
        simpa [yU] using h
      have hvz : v.1 ≠ z := by
        intro h
        apply D.other_not_carrier
        simpa [h, CutSide.vertices,
          LobeRegion.carrier] using v.2
      have hinside :
          ∀ a, H.Adj v.1 a →
            a ∈
              (↑(CutSide.vertices
                D.lobe.inner D.lobe.cut) : Set V) := by
        intro a hva
        have hvaK :
            (leftEdgeSwapGraph G x y z).Adj v.1 a := by
          exact Or.inl hva
        rcases D.lobe.closed hvInner hvaK with
          haInner | haCut
        · exact Finset.mem_insert.mpr (Or.inr haInner)
        · exact Finset.mem_insert.mpr (Or.inl haCut)
      calc
        q + 1 ≤ finiteDegree G v.1 :=
          M.degree_lower v.1 hvx hvy hvz
        _ = finiteDegree H v.1 := by
          symm
          exact finiteDegree_sdiff_edge_of_ne
            G x z v.1 hvx hvz
        _ ≤ finiteDegree A v := by
          exact finiteDegree_le_induce
            H
            (↑(CutSide.vertices
              D.lobe.inner D.lobe.cut) : Set V)
            v hinside
  }
  obtain ⟨F⟩ :=
    M.smaller_solvable I hcomplexity
  let f : A →g G :=
    (SimpleGraph.Hom.ofLE
      (show H ≤ G from sdiff_le)).comp
      (CutSide.embedding
        H D.lobe.inner D.lobe.cut).toHom
  have hfInjective : Function.Injective f := by
    intro a b hab
    exact Subtype.ext hab
  let mapped :
      AdmissiblePathFamily G x y q := by
    change AdmissiblePathFamily G
      ((xU : U) : V) ((yU : U) : V) q
    exact F.mapInjectiveHom f hfInjective
  exact M.no_paths ⟨mapped⟩

end MinimalCounterexample

end COY

end DeanK5
