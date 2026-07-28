import DeanK5.EndLobeExistence

/-!
# Root attachments to end lobes

The root-attachment statement used in the initial reduction is not a
separate block-cut-tree input.  Once the ordinary two-end-lobe theorem has
supplied the lobes, 2-connectivity of the ambient block forces the deleted
root to have a neighbor in the interior of each lobe.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {W : Type u} {V : Type v}

/--
Membership in a vertex set that is closed under adjacency propagates along
a walk.
-/
private theorem walk_end_mem_of_start_mem_of_closed
    {G : SimpleGraph V} {S : Set V} {x y : V}
    (w : G.Walk x y) (hx : x ∈ S)
    (hclosed :
      ∀ ⦃a b : V⦄, a ∈ S → G.Adj a b → b ∈ S) :
    y ∈ S := by
  induction w with
  | nil => exact hx
  | cons hab w ih =>
      exact ih (hclosed hx hab)

namespace ClassicalGraphTheory

/--
If an end lobe of the root-deleted graph had no neighbor of the deleted
root in its interior, its cut vertex would separate that interior from the
root in the ambient graph.
-/
private theorem exists_root_attachment
    [Fintype V] [DecidableEq V]
    {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (B : SimpleGraph V)
    (c : V) (ι : J ↪g B)
    (hc : c ∉ Set.range ι)
    (hdecomposition :
      ∀ v : V, v = c ∨ v ∈ Set.range ι)
    (hBtwo : IsTwoConnected B)
    (L : EndLobe J) :
    ∃ x : (↑L.inner : Set W),
      B.Adj c (ι x.1) := by
  classical
  by_contra hnone
  simp only [not_exists] at hnone
  obtain ⟨x, hx⟩ := L.inner_nonempty
  let S : Finset V := {ι L.cut}
  have hcS : c ∉ S := by
    intro hmem
    have heq : c = ι L.cut := by
      simpa [S] using hmem
    exact hc ⟨L.cut, heq.symm⟩
  have hxcut : x ≠ L.cut := by
    intro heq
    exact L.cut_not_inner (heq ▸ hx)
  have hxS : ι x ∉ S := by
    simp only [S, Finset.mem_singleton]
    exact fun heq => hxcut (ι.injective heq)
  let cS : {z : V // z ∉ S} := ⟨c, hcS⟩
  let xS : {z : V // z ∉ S} := ⟨ι x, hxS⟩
  have hcard : S.card < 2 := by
    simp [S]
  have hconnected :
      (B.induce {z : V | z ∉ S}).Connected :=
    hBtwo.2 S hcard
  have hreach :
      (B.induce {z : V | z ∉ S}).Reachable xS cS :=
    hconnected xS cS
  obtain ⟨w⟩ := hreach
  let innerImage : Set {z : V // z ∉ S} :=
    {z | ∃ a : W, a ∈ L.inner ∧ z.1 = ι a}
  have hxImage : xS ∈ innerImage := by
    exact ⟨x, hx, rfl⟩
  have hclosed :
      ∀ ⦃a b : {z : V // z ∉ S}⦄,
        a ∈ innerImage →
        (B.induce {z : V | z ∉ S}).Adj a b →
        b ∈ innerImage := by
    intro a b ha hab
    obtain ⟨aJ, haJ, haeq⟩ := ha
    have habB : B.Adj (ι aJ) b.1 := by
      change B.Adj a.1 b.1 at hab
      rw [haeq] at hab
      exact hab
    rcases hdecomposition b.1 with hbc | hbRange
    · exact False.elim
        (hnone ⟨aJ, haJ⟩ (hbc ▸ habB.symm))
    · obtain ⟨bJ, hbJ⟩ := hbRange
      have hab' : B.Adj (ι aJ) (ι bJ) := by
        simpa [hbJ] using habB
      have habJ : J.Adj aJ bJ :=
        ι.map_rel_iff.mp hab'
      rcases L.closed haJ habJ with hbInner | hbCut
      · exact ⟨bJ, hbInner, hbJ.symm⟩
      · exfalso
        apply b.2
        simp only [S, Finset.mem_singleton]
        calc
          b.1 = ι bJ := hbJ.symm
          _ = ι L.cut := congrArg ι hbCut
  have hcImage : cS ∈ innerImage :=
    walk_end_mem_of_start_mem_of_closed
      w hxImage hclosed
  obtain ⟨a, -, hca⟩ := hcImage
  exact hc ⟨a, hca.symm⟩

/--
The root-attachment form of the standard end-lobe argument follows from
the ordinary two-end-lobe theorem and 2-connectivity of the ambient graph.
-/
theorem two_end_lobes_with_root_attachments
    [Fintype V] [DecidableEq V]
    {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (B : SimpleGraph V)
    (c : V) (ι : J ↪g B)
    (hc : c ∉ Set.range ι)
    (hdecomposition :
      ∀ v : V, v = c ∨ v ∈ Set.range ι)
    (hBtwo : IsTwoConnected B)
    (hJconnected : J.Connected)
    (hJnotTwo : ¬ IsTwoConnected J)
    (hdegree : MinDegreeAtLeast J 3) :
    ∃ P : EndLobePair J,
      ∃ x₁ : (↑P.left.inner : Set W),
      ∃ x₂ : (↑P.right.inner : Set W),
        B.Adj c (ι x₁.1) ∧
        B.Adj c (ι x₂.1) := by
  obtain ⟨P⟩ :=
    two_end_lobes J hJconnected hJnotTwo hdegree
  obtain ⟨x₁, hx₁⟩ :=
    exists_root_attachment
      J B c ι hc hdecomposition hBtwo P.left
  obtain ⟨x₂, hx₂⟩ :=
    exists_root_attachment
      J B c ι hc hdecomposition hBtwo P.right
  exact ⟨P, x₁, x₂, hx₁, hx₂⟩

end ClassicalGraphTheory

end DeanK5
