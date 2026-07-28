import DeanK5.COYCutDecomposition
import DeanK5.COYCutPathLift
import DeanK5.COYSideConnectivity

/-!
# The recursive call on one side of a COY cut vertex

This file packages the smaller rooted instance used in COY Claim 3.2(1).
The exceptional vertex may or may not survive on the chosen side, so the
construction treats those two typed cases explicitly.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z c : V}
  {Q R : Finset V}

/--
Minimality solves the induced side of a cut vertex once its rooted
2-connectivity has been certified.  The other component makes the
induction measure strictly smaller.
-/
theorem recursive_family_on_cut_side
    (M : MinimalCounterexample q G x y z)
    (hQ : ComponentRegion G {c} Q)
    (hR : ComponentRegion G {c} R)
    (hQR : Disjoint Q R)
    (hx : x ∈ Q) (hy : y ∈ R)
    (hordinary : ∃ v ∈ Q, v ≠ x ∧ v ≠ z)
    (hsideConnected :
      IsTwoConnected
        (CutSide.graph G Q c ⊔
          edge (CutSide.root Q c x hx)
            (CutSide.cut Q c))) :
    Nonempty
      (AdmissiblePathFamily
        (CutSide.graph G Q c)
        (CutSide.root Q c x hx)
        (CutSide.cut Q c) q) := by
  let xU := CutSide.root Q c x hx
  let cU := CutSide.cut Q c
  have hxcU : xU ≠ cU :=
    CutSide.root_ne_cut hQ hx
  have hcomplexity :
      rootedComplexity (CutSide.graph G Q c) <
        rootedComplexity G :=
    CutSide.rootedComplexity_lt_of_disjoint_component
      hR hQR
  by_cases hzSide : z ∈ CutSide.vertices Q c
  · let zU : CutSide.Vertex Q c := ⟨z, hzSide⟩
    let I : RootedInstance q
        (CutSide.graph G Q c) xU cU zU := {
      q_pos := M.q_pos
      q_le_four := M.q_le_four
      roots_ne := hxcU
      rooted_two_connected := hsideConnected
      ordinary_nonempty := by
        obtain ⟨v, hvQ, hvx, hvz⟩ := hordinary
        let vU := CutSide.innerVertex Q c v hvQ
        have hvc : v ≠ c := by
          intro h
          exact hQ.not_mem_separator hvQ (by simp [h])
        refine ⟨vU, ?_, ?_, ?_⟩
        · intro h
          exact hvx (by
            simpa [vU, xU, CutSide.root,
              CutSide.innerVertex] using
              congrArg Subtype.val h)
        · intro h
          exact hvc (by
            simpa [vU, cU, CutSide.cut,
              CutSide.innerVertex] using
              congrArg Subtype.val h)
        · intro h
          exact hvz (by
            simpa [vU, zU, CutSide.innerVertex] using
              congrArg Subtype.val h)
      degree_lower := by
        intro v hvxU hvcU hvzU
        have hvQ :=
          CutSide.mem_component_of_ne_cut v
            (by simpa [cU] using hvcU)
        rw [CutSide.finiteDegree_graph_eq_of_ne_cut
          hQ v (by simpa [cU] using hvcU)]
        apply M.degree_lower v.1
        · intro hvx
          apply hvxU
          apply Subtype.ext
          simpa [xU] using hvx
        · intro hvy
          subst y
          exact Finset.disjoint_left.mp hQR hvQ hy
        · intro hvz
          apply hvzU
          apply Subtype.ext
          simpa [zU] using hvz
    }
    exact M.smaller_solvable I hcomplexity
  · let I : RootedInstance q
        (CutSide.graph G Q c) xU cU xU :=
      RootedInstance.ofNoExtraException
        q (CutSide.graph G Q c) xU cU
        M.q_pos M.q_le_four hxcU hsideConnected
        (by
          intro v hvxU hvcU
          have hvQ :=
            CutSide.mem_component_of_ne_cut v
              (by simpa [cU] using hvcU)
          rw [CutSide.finiteDegree_graph_eq_of_ne_cut
            hQ v (by simpa [cU] using hvcU)]
          apply M.degree_lower v.1
          · intro hvx
            apply hvxU
            apply Subtype.ext
            simpa [xU] using hvx
          · intro hvy
            subst y
            exact Finset.disjoint_left.mp hQR hvQ hy
          · intro hvz
            apply hzSide
            simpa [hvz] using v.2)
    exact M.smaller_solvable I hcomplexity

/--
COY Claim 3.2(1): the underlying graph of a minimal counterexample is
2-connected.

If a cut vertex existed, rooted two-connectivity would put the roots in
opposite deletion components.  On a side containing an ordinary vertex,
minimality supplies the required root-to-cut family; a fixed path through
the opposite component then lifts it to the forbidden ambient family.
-/
theorem underlying_two_connected
    (M : MinimalCounterexample q G x y z) :
    IsTwoConnected G := by
  by_contra hnotTwo
  obtain ⟨c, Cx, Cy, hCxCy, hx, hy⟩ :=
    M.exists_root_separating_cut hnotTwo
  let Qx := componentVertices G {c} Cx
  let Qy := componentVertices G {c} Cy
  have hQx : ComponentRegion G {c} Qx :=
    componentRegion_componentVertices G {c} Cx
  have hQy : ComponentRegion G {c} Qy :=
    componentRegion_componentVertices G {c} Cy
  have hdisjoint : Disjoint Qx Qy :=
    componentVertices_disjoint_of_ne G {c} hCxCy
  obtain hordX | hordY :=
    M.exists_ordinary_on_root_side
      c Cx Cy hCxCy hx hy
  · have hyNotQx : y ∉ Qx := by
      intro hyQx
      exact Finset.disjoint_left.mp hdisjoint hyQx hy
    have hsideNontrivial :
        ∃ v ∈ Qx, v ≠ x := by
      obtain ⟨v, hvQx, hvx, -⟩ := hordX
      exact ⟨v, hvQx, hvx⟩
    have hsideConnected :
        IsTwoConnected
          (CutSide.graph G Qx c ⊔
            edge (CutSide.root Qx c x hx)
              (CutSide.cut Qx c)) :=
      CutSide.graph_sup_root_cut_two_connected
        G Qx x y c hQx hx hyNotQx
        M.rooted_two_connected hsideNontrivial
    obtain ⟨F⟩ :=
      M.recursive_family_on_cut_side
        hQx hQy hdisjoint hx hy hordX
        hsideConnected
    exact M.no_paths
      (CutSide.lift_across_disjoint_component
        hQx hQy hdisjoint M.underlying_connected
        hx hy F)
  · let M' : MinimalCounterexample q G y x z :=
      M.swapRoots
    have hxNotQy : x ∉ Qy := by
      intro hxQy
      exact Finset.disjoint_left.mp hdisjoint hx hxQy
    have hsideNontrivial :
        ∃ v ∈ Qy, v ≠ y := by
      obtain ⟨v, hvQy, hvy, -⟩ := hordY
      exact ⟨v, hvQy, hvy⟩
    have hsideConnected :
        IsTwoConnected
          (CutSide.graph G Qy c ⊔
            edge (CutSide.root Qy c y hy)
              (CutSide.cut Qy c)) :=
      CutSide.graph_sup_root_cut_two_connected
        G Qy y x c hQy hy hxNotQy
        M'.rooted_two_connected hsideNontrivial
    obtain ⟨F⟩ :=
      M'.recursive_family_on_cut_side
        hQy hQx hdisjoint.symm hy hx hordY
        hsideConnected
    exact M'.no_paths
      (CutSide.lift_across_disjoint_component
        hQy hQx hdisjoint.symm M'.underlying_connected
        hy hx F)

end MinimalCounterexample

end COY

end DeanK5
