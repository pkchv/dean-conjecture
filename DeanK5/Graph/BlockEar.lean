import DeanK5.Graph.BlockIntersection

/-!
# External ears of graph blocks

An inclusion-maximal nonseparable carrier cannot have a path whose distinct
ends lie in the block and whose internal vertices lie outside it.  Joining
such an ear to a path inside the block would create a cycle contained in a
second block.  The two blocks would share both ear endpoints and hence be
equal, forcing the ear back into the original block.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace GraphBlock

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/--
Every simple path that meets a block exactly in its two distinct endpoints
is wholly contained in that block.

The conclusion is deliberately contradictory with any asserted external
support vertex; this is the ear-maximality form used by the block--cut
incidence argument.
-/
theorem path_subset_of_meets_only_at_ends
    (B : GraphBlock G)
    {u v : V}
    (huv : u ≠ v)
    (P : SimplePath G u v)
    (huB : u ∈ B.carrier)
    (hvB : v ∈ B.carrier)
    (hmeet :
      ∀ ⦃w : V⦄, w ∈ P.walk.support →
        w ∈ B.carrier → w = u ∨ w = v) :
    ∀ ⦃w : V⦄, w ∈ P.walk.support →
      w ∈ B.carrier := by
  classical
  intro w hwP
  by_contra hwB
  have hwu : w ≠ u := by
    intro h
    apply hwB
    simpa [h] using huB
  have hwv : w ≠ v := by
    intro h
    apply hwB
    simpa [h] using hvB
  obtain ⟨q, hqPath⟩ :=
    B.connected.preconnected.exists_isPath
      ⟨v, hvB⟩ ⟨u, huB⟩
  let inclusion :
      G.induce (↑B.carrier : Set V) →g G :=
    (Embedding.induce
      (↑B.carrier : Set V)).toHom
  let Q : SimplePath G v u := {
    walk := q.map inclusion
    isPath := hqPath.map Subtype.val_injective
  }
  have hQSupport :
      ∀ ⦃a : V⦄, a ∈ Q.walk.support →
        a ∈ B.carrier := by
    intro a ha
    change a ∈ (q.map inclusion).support at ha
    rw [SimpleGraph.Walk.support_map] at ha
    obtain ⟨aB, -, haValue⟩ :=
      List.mem_map.mp ha
    change aB.1 = a at haValue
    rw [← haValue]
    exact aB.2
  have hdisjoint :
      P.walk.support.tail.Disjoint
        Q.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro a haP haQ
    have haPSupport :
        a ∈ P.walk.support :=
      List.mem_of_mem_tail haP
    have haB :
        a ∈ B.carrier :=
      hQSupport (List.mem_of_mem_tail haQ)
    rcases hmeet haPSupport haB with hau | hav
    · subst a
      exact P.start_not_mem_tail haP
    · subst a
      exact Q.start_not_mem_tail haQ
  have hlength :
      1 < P.length := by
    have htripleCard :
        ({u, v, w} : Finset V).card = 3 := by
      simp [huv, hwu.symm, hwv.symm]
    have htripleSubset :
        ({u, v, w} : Finset V) ⊆
          P.walk.support.toFinset := by
      intro a ha
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · simp
      · simp
      · simpa using hwP
    have hcard :=
      Finset.card_le_card htripleSubset
    rw [htripleCard,
      List.toFinset_card_of_nodup
        P.isPath.support_nodup,
      P.walk.length_support] at hcard
    simpa [SimplePath.length] using
      (show 1 < P.walk.length by omega)
  let cycle : SimpleCycle G :=
    cycleOfDisjointPaths P Q hdisjoint
      (Or.inl hlength)
  have huCycle :
      u ∈ cycle.carrier := by
    apply SimpleCycle.mem_carrier.mpr
    simp [cycle, cycleOfDisjointPaths]
  have hvCycle :
      v ∈ cycle.carrier := by
    apply SimpleCycle.mem_carrier.mpr
    simp [cycle, cycleOfDisjointPaths]
  have hwCycle :
      w ∈ cycle.carrier := by
    apply SimpleCycle.mem_carrier.mpr
    simp [cycle, cycleOfDisjointPaths, hwP]
  obtain ⟨C, hcycleC, -⟩ :=
    GraphBlock.exists_containing_cycle cycle
  have huC : u ∈ C.carrier :=
    hcycleC huCycle
  have hvC : v ∈ C.carrier :=
    hcycleC hvCycle
  have hBC : B = C := by
    by_contra hne
    have hpair :
        ({u, v} : Finset V) ⊆
          B.carrier ∩ C.carrier := by
      intro a ha
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huB, huC⟩
      · exact Finset.mem_inter.mpr ⟨hvB, hvC⟩
    have hpairCard :
        ({u, v} : Finset V).card = 2 := by
      simp [huv]
    have hinterTwo :
        2 ≤ (B.carrier ∩ C.carrier).card := by
      rw [← hpairCard]
      exact Finset.card_le_card hpair
    exact
      (not_le_of_gt hinterTwo)
        (B.inter_card_le_one C hne)
  apply hwB
  rw [hBC]
  exact hcycleC hwCycle

end GraphBlock

end DeanK5
