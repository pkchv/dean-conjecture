import DeanK5.Graph.Blocks
import DeanK5.Graph.Connectivity
import DeanK5.Graph.RootAdjunction

/-!
# Adjoining a root to a nonseparable carrier

A nonseparable carrier need not induce a 2-connected graph under the
project's order convention: a bridge block has only two vertices.  Adjoining
a root at two carrier vertices nevertheless always produces a 2-connected
graph.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace IsNonseparableCarrier

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {S : Finset V}

/--
Deleting a carrier vertex after inducing is the same as first erasing that
vertex from the finite carrier and then inducing.
-/
private def eraseInduceIso
    (d : (↑S : Set V)) :
    (G.induce (↑S : Set V)).induce
        {w : (↑S : Set V) | w ≠ d} ≃g
      G.induce (↑(S.erase d.1) : Set V) where
  toEquiv := {
    toFun := fun w =>
      ⟨w.1.1, Finset.mem_erase.mpr
        ⟨fun h => w.2 (Subtype.ext h), w.1.2⟩⟩
    invFun := fun w =>
      ⟨⟨w.1, Finset.mem_of_mem_erase w.2⟩, by
        intro h
        exact (Finset.mem_erase.mp w.2).1
          (congrArg Subtype.val h)⟩
    left_inv := by
      intro w
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro w
      apply Subtype.ext
      rfl
  }
  map_rel_iff' := Iff.rfl

omit [Fintype V] in
/--
A nonseparable carrier of order at least three induces a 2-connected
graph.  The order hypothesis is necessary because nonseparable carriers
also include two-vertex bridge blocks.
-/
theorem isTwoConnected_induce
    (hS : IsNonseparableCarrier G S)
    (hcard : 3 ≤ S.card) :
    IsTwoConnected (G.induce (↑S : Set V)) := by
  apply isTwoConnected_of_connected_delete_one
  · simpa using hcard
  · exact hS.connected
  · intro d
    exact
      (SimpleGraph.Iso.connected_iff
        (eraseInduceIso (G := G) d)).mpr
          (hS.delete_connected d.1 d.2)

omit [Fintype V] in
private theorem deleteOld_connected
    (hS : IsNonseparableCarrier G S)
    (R : Finset (↑S : Set V)) (hR : R.card < 2) :
    ((G.induce (↑S : Set V)).induce
      {w : (↑S : Set V) | w ∉ R}).Connected := by
  by_cases hRempty : R = ∅
  · subst R
    have hset :
        {w : (↑S : Set V) |
          w ∉ (∅ : Finset (↑S : Set V))} = Set.univ := by
      ext w
      simp
    rw [hset]
    exact
      (SimpleGraph.Iso.connected_iff
        (SimpleGraph.induceUnivIso
          (G.induce (↑S : Set V)))).mpr hS.connected
  · have hRpos : 0 < R.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hRempty)
    have hRone : R.card = 1 := by omega
    obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp hRone
    have hset :
        {w : (↑S : Set V) |
          w ∉ ({d} : Finset (↑S : Set V))} =
            {w : (↑S : Set V) | w ≠ d} := by
      ext w
      simp
    rw [hset]
    exact
      (SimpleGraph.Iso.connected_iff
        (eraseInduceIso (G := G) d)).mpr
          (hS.delete_connected d.1 d.2)

private def oldDeletion
    (D : Finset (Option (↑S : Set V))) :
    Finset (↑S : Set V) :=
  Finset.univ.filter fun v => some v ∈ D

omit [Fintype V] in
private theorem oldDeletion_card_le
    (D : Finset (Option (↑S : Set V))) :
    (oldDeletion D).card ≤ D.card := by
  calc
    (oldDeletion D).card =
        ((oldDeletion D).image some).card := by
          symm
          exact Finset.card_image_of_injective _
            (fun _ _ h => Option.some.inj h)
    _ ≤ D.card := Finset.card_le_card (by
      intro w hw
      simp only [Finset.mem_image] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      simpa [oldDeletion] using hv)

omit [Fintype V] in
private theorem exists_attached_outside
    (Z : Finset (↑S : Set V))
    (D : Finset (Option (↑S : Set V)))
    (hZ : 2 ≤ Z.card) (hD : D.card < 2) :
    ∃ z ∈ Z, some z ∉ D := by
  by_contra h
  push Not at h
  have hsub : Z.image some ⊆ D := by
    intro w hw
    simp only [Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact h z hz
  have hcard : Z.card ≤ D.card := by
    rw [← Finset.card_image_of_injective Z
      (fun _ _ h => Option.some.inj h)]
    exact Finset.card_le_card hsub
  omega

omit [Fintype V] in
/--
Adjoining a root at two vertices of a nonseparable carrier produces a
2-connected graph, including when the carrier is a two-vertex bridge block.
-/
theorem isTwoConnected_adjoinRoot
    (hS : IsNonseparableCarrier G S)
    (Z : Finset (↑S : Set V)) (hZ : 2 ≤ Z.card) :
    IsTwoConnected
      (adjoinRoot (G.induce (↑S : Set V)) Z) := by
  constructor
  · have hcarrierOrder :
        2 ≤ Fintype.card (↑S : Set V) := by
      simpa using hS.card_ge_two
    simp only [Fintype.card_option]
    omega
  · intro D hD
    let R := oldDeletion D
    have hRcard : R.card < 2 :=
      lt_of_le_of_lt (oldDeletion_card_le D) hD
    have hbase :
        ((G.induce (↑S : Set V)).induce
          {v | v ∉ R}).Connected :=
      deleteOld_connected hS R hRcard
    obtain ⟨z, hzZ, hzD⟩ :=
      exists_attached_outside Z D hZ hD
    have hzR : z ∉ R := by
      simpa [R, oldDeletion] using hzD
    let f :
        (G.induce (↑S : Set V)).induce {v | v ∉ R} →g
          (adjoinRoot (G.induce (↑S : Set V)) Z).induce
            {w | w ∉ D} := {
      toFun v := ⟨some v.1, by
        simpa [R, oldDeletion] using v.2⟩
      map_rel' := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        exact hab
    }
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨some z, hzD⟩, ?_⟩
    rintro ⟨w, hw⟩
    cases w with
    | none =>
        exact (show
          (adjoinRoot
            (G.induce (↑S : Set V)) Z).induce
              {w | w ∉ D} |>.Adj
                ⟨some z, hzD⟩ ⟨none, hw⟩ by
                  exact hzZ).reachable
    | some v =>
        have hvR : v ∉ R := by
          simpa [R, oldDeletion] using hw
        have hr :=
          hbase.preconnected ⟨z, hzR⟩ ⟨v, hvR⟩
        convert hr.map f using 1 <;>
          apply Subtype.ext <;>
          rfl

end IsNonseparableCarrier

end DeanK5
