import DeanK5.ThreeSeparator
import DeanK5.Concatenation
import DeanK5.GHLMRootedInternal

/-!
# The `k = 5` connectivity step from BGLP Lemma 2.3

This file proves the exact specialization used by the paper.  It invokes the
internally proved rooted admissible-path theorem; the minimum-cut argument,
degree preservation, ambient transport, support disjointness, and cycle
closure are proved here.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

private theorem component_three_admissible_paths
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y : V) (hxy : x ≠ y)
    (hQ : ComponentRegion G {x, y} Q)
    (hconn : IsTwoConnected G)
    (hdeg : MinDegreeAtLeast G 4) :
    ∃ F : AdmissiblePathFamily G x y 3,
      ∀ i z, z ∈ (F.path i).walk.support →
        z ∈ Q ∨ z = x ∨ z = y := by
  let A := twoRootComponentBase G Q x y
  let rx := twoRootX Q x y
  let ry := twoRootY Q x y
  have hroots : rx ≠ ry := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hAconn :
      IsTwoConnected (A ⊔ edge rx ry) := by
    change IsTwoConnected
      (twoRootComponentBase G Q x y ⊔
        edge (twoRootX Q x y) (twoRootY Q x y))
    rw [twoRootComponentBase_sup_edge]
    exact one_component_two_cut_roots G Q x y hxy hQ hconn
  have hAdeg :
      ∀ z, z ≠ rx → z ≠ ry →
        4 ≤ finiteDegree A z := by
    intro z hzx hzy
    have hzClass :
        z.1 ∈ Q ∨ z.1 = x ∨ z.1 = y := by
      have h :
          z.1 = x ∨ z.1 = y ∨ z.1 ∈ Q := by
        simpa [twoRootVertices] using z.2
      tauto
    have hzQ : z.1 ∈ Q := by
      rcases hzClass with hzQ | hzx' | hzy'
      · exact hzQ
      · exact False.elim (hzx (by
          apply Subtype.ext
          simpa [rx, twoRootX] using hzx'))
      · exact False.elim (hzy (by
          apply Subtype.ext
          simpa [ry, twoRootY] using hzy'))
    exact (hdeg z.1).trans
      (by
        simpa [A] using
          finiteDegree_le_twoRootComponentBase_of_two_separator
            G Q x y z.1 hQ hzQ)
  obtain ⟨F⟩ :=
    GHLM.rooted_admissible_paths_internal
      3 A rx ry (by omega) (by omega) hroots hAconn hAdeg
  let f := twoRootComponentBaseHom G Q x y
  have hf : Function.Injective f :=
    twoRootComponentBaseHom_injective G Q x y
  let FM₀ := F.mapInjectiveHom f hf
  change AdmissiblePathFamily G x y 3 at FM₀
  refine ⟨FM₀, ?_⟩
  intro i z hz
  change z ∈
    ((F.path i).mapInjectiveHom f hf).walk.support at hz
  have hzRange :
      z ∈ Set.range f :=
    (F.path i).mem_range_of_mem_mapInjectiveHom_support
      f hf hz
  obtain ⟨a, rfl⟩ := hzRange
  have ha :
      a.1 ∈ Q ∨ a.1 = x ∨ a.1 = y := by
    have h :
        a.1 = x ∨ a.1 = y ∨ a.1 ∈ Q := by
      simpa [twoRootVertices] using a.2
    tauto
  simpa [f, twoRootComponentBaseHom] using ha

private theorem component_families_tail_disjoint
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q₀ Q₁ : Finset V}
    {x y : V} (hxy : x ≠ y)
    (hQ₀ : ComponentRegion G {x, y} Q₀)
    (hQ₁ : ComponentRegion G {x, y} Q₁)
    (hregions : Disjoint Q₀ Q₁)
    (F₀ F₁ : AdmissiblePathFamily G x y 3)
    (hsupport₀ :
      ∀ i z, z ∈ (F₀.path i).walk.support →
        z ∈ Q₀ ∨ z = x ∨ z = y)
    (hsupport₁ :
      ∀ i z, z ∈ (F₁.path i).walk.support →
        z ∈ Q₁ ∨ z = x ∨ z = y) :
    ∀ i j,
      (F₀.path i).walk.support.tail.Disjoint
        (F₁.reverse.path j).walk.support.tail := by
  intro i j
  apply List.disjoint_left.mpr
  intro z hz₀ hz₁
  have hz₀Support :
      z ∈ (F₀.path i).walk.support :=
    List.mem_of_mem_tail hz₀
  have hz₁Support :
      z ∈ (F₁.path j).walk.support := by
    have hzReverse :
        z ∈ (F₁.reverse.path j).walk.support :=
      List.mem_of_mem_tail hz₁
    simpa [AdmissiblePathFamily.reverse,
      SimplePath.reverse] using hzReverse
  have hz₀Reduced : z ∈ Q₀ ∨ z = y := by
    rcases hsupport₀ i z hz₀Support with
      hzQ₀ | hzx | hzy
    · exact Or.inl hzQ₀
    · exact False.elim
        ((F₀.path i).start_not_mem_tail
          (hzx ▸ hz₀))
    · exact Or.inr hzy
  have hz₁Reduced : z ∈ Q₁ ∨ z = x := by
    rcases hsupport₁ j z hz₁Support with
      hzQ₁ | hzx | hzy
    · exact Or.inl hzQ₁
    · exact Or.inr hzx
    · exact False.elim
        ((F₁.reverse.path j).start_not_mem_tail
          (hzy ▸ hz₁))
  rcases hz₀Reduced with hzQ₀ | hzy <;>
    rcases hz₁Reduced with hzQ₁ | hzx
  · exact (Finset.disjoint_left.mp hregions hzQ₀) hzQ₁
  · exact hQ₀.not_mem_separator hzQ₀ (by simp [hzx])
  · exact hQ₁.not_mem_separator hzQ₁ (by simp [hzy])
  · exact hxy (hzx.symm.trans hzy)

namespace BGLP

/--
The exact `k = 5`, `r = 1` consequence of BGLP Lemma 2.3 used in
the manuscript.  The proof is internal and depends only on GHLM's rooted
three-path theorem.
-/
theorem three_connected_of_two_connected_minDegree_four
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hconn : IsTwoConnected G)
    (hdeg : MinDegreeAtLeast G 4)
    (hno : ¬HasCycleDivisibleBy G 5) :
    IsKConnected G 3 := by
  classical
  have hVnonempty : Nonempty V :=
    Fintype.card_pos_iff.mp (by
      have horder := hconn.1
      omega)
  have horder : 5 ≤ Fintype.card V := by
    let v : V := Classical.choice hVnonempty
    have hfiniteDegree :
        finiteDegree G v = G.degree v := by
      unfold finiteDegree SimpleGraph.degree
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have hlt := G.degree_lt_card_verts v
    rw [← hfiniteDegree] at hlt
    have hlower := hdeg v
    omega
  constructor
  · exact horder.trans' (by omega)
  · intro S hScard
    by_contra hnotConnected
    have hScardLower : 2 ≤ S.card := by
      by_contra hsmall
      exact hnotConnected
        (hconn.2 S (by omega))
    have hScardEq : S.card = 2 := by
      omega
    obtain ⟨x, y, hxy, hSeq⟩ :=
      Finset.card_eq_two.mp hScardEq
    subst S
    have hsurvivor :
        Nonempty {v : V // v ∉ ({x, y} : Finset V)} := by
      have hcompPos :
          0 < ({x, y} : Finset V)ᶜ.card := by
        rw [Finset.card_compl]
        simp [hxy]
        omega
      obtain ⟨z, hz⟩ :=
        Finset.card_pos.mp hcompPos
      exact ⟨⟨z, by simpa using hz⟩⟩
    have hcut :
        IsVertexCut G {x, y} :=
      isVertexCut_of_not_connected
        G {x, y} hsurvivor hnotConnected
    obtain ⟨C₀, C₁, hCne⟩ := hcut
    let Q₀ := componentVertices G {x, y} C₀
    let Q₁ := componentVertices G {x, y} C₁
    have hQ₀ :
        ComponentRegion G {x, y} Q₀ :=
      componentRegion_componentVertices G {x, y} C₀
    have hQ₁ :
        ComponentRegion G {x, y} Q₁ :=
      componentRegion_componentVertices G {x, y} C₁
    have hregions : Disjoint Q₀ Q₁ :=
      disjoint_componentVertices G {x, y} hCne
    obtain ⟨F₀, hsupport₀⟩ :=
      component_three_admissible_paths
        G Q₀ x y hxy hQ₀ hconn hdeg
    obtain ⟨F₁, hsupport₁⟩ :=
      component_three_admissible_paths
        G Q₁ x y hxy hQ₁ hconn hdeg
    have hdisjoint :
        ∀ i j,
          (F₀.path i).walk.support.tail.Disjoint
            (F₁.reverse.path j).walk.support.tail :=
      component_families_tail_disjoint
        hxy hQ₀ hQ₁ hregions
        F₀ F₁ hsupport₀ hsupport₁
    exact hno
      (disjoint_three_by_three_forces_cycle_divisible_by_five
        G F₀ F₁.reverse hdisjoint)

end BGLP

end DeanK5
