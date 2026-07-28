import DeanK5.COYProtectedEdge

/-!
# Cut decomposition of a COY minimal counterexample

This file begins COY Claim 3.2(1).  If the underlying graph had a cut
vertex, rooted two-connectivity forces the two roots into distinct
components after deleting that vertex.  The recursive path argument that
eliminates the cut is built on this certified decomposition.
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
If the underlying graph is not 2-connected, some cut vertex separates
the two roots into two explicitly named deletion components.
-/
theorem exists_root_separating_cut
    (M : MinimalCounterexample q G x y z)
    (hnotTwo : ¬IsTwoConnected G) :
    ∃ c : V,
      ∃ Cx Cy : (deleteVertices G {c}).ConnectedComponent,
        Cx ≠ Cy ∧
        x ∈ componentVertices G {c} Cx ∧
        y ∈ componentVertices G {c} Cy :=
  ComponentRegion.exists_root_separating_cut_of_sup_edge_two_connected
    G x y M.underlying_connected hnotTwo
    M.rooted_two_connected (by
      have hfive := M.five_le_card
      omega)

/--
Once two deletion components contain the two roots, there is no third
component: every surviving vertex belongs to one of those two sides.
-/
theorem cut_components_exhaust
    (M : MinimalCounterexample q G x y z)
    (c : V)
    (Cx Cy : (deleteVertices G {c}).ConnectedComponent)
    (hx : x ∈ componentVertices G {c} Cx)
    (hy : y ∈ componentVertices G {c} Cy)
    (v : V) :
    v = c ∨
      v ∈ componentVertices G {c} Cx ∨
      v ∈ componentVertices G {c} Cy :=
  ComponentRegion.cut_components_exhaust_of_sup_edge_two_connected
    M.rooted_two_connected c Cx Cy hx hy v

/--
At least one root side contains a vertex other than its root and the
exception.  This is the source proof's symmetry choice before the
recursive call.
-/
theorem exists_ordinary_on_root_side
    (M : MinimalCounterexample q G x y z)
    (c : V)
    (Cx Cy : (deleteVertices G {c}).ConnectedComponent)
    (_hxyComponents : Cx ≠ Cy)
    (hx : x ∈ componentVertices G {c} Cx)
    (hy : y ∈ componentVertices G {c} Cy) :
    (∃ v ∈ componentVertices G {c} Cx,
      v ≠ x ∧ v ≠ z) ∨
    (∃ v ∈ componentVertices G {c} Cy,
      v ≠ y ∧ v ≠ z) := by
  let P : Finset V := {x, y, z, c}
  have hprotectedCard : P.card ≤ 4 := by
    calc
      P.card ≤ ({y, z, c} : Finset V).card + 1 :=
        Finset.card_insert_le x {y, z, c}
      _ ≤ ({z, c} : Finset V).card + 2 := by
        have h := Finset.card_insert_le y {z, c}
        omega
      _ ≤ ({c} : Finset V).card + 3 := by
        have h := Finset.card_insert_le z {c}
        omega
      _ = 4 := by simp
  have hproper :
      P.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    have hfive := M.five_le_card
    omega
  obtain ⟨v, -, hvProtected⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hproper
  have hvx : v ≠ x := by
    intro h
    exact hvProtected (by simp [P, h])
  have hvy : v ≠ y := by
    intro h
    exact hvProtected (by simp [P, h])
  have hvz : v ≠ z := by
    intro h
    exact hvProtected (by simp [P, h])
  have hvc : v ≠ c := by
    intro h
    exact hvProtected (by simp [P, h])
  rcases M.cut_components_exhaust
      c Cx Cy hx hy v with
    h | hvCx | hvCy
  · exact False.elim (hvc h)
  · exact Or.inl ⟨v, hvCx, hvx, hvz⟩
  · exact Or.inr ⟨v, hvCy, hvy, hvz⟩

end MinimalCounterexample

end COY

end DeanK5
