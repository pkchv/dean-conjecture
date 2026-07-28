import DeanK5.COYSingletonExteriorOtherComponents
import DeanK5.Graph.Blocks

/-!
# Boundary compression of a nonseparable block

The compression used in COY Claim 3.12 retains one block vertex, collapses
an exterior attachment set to a second root, and leaves the other block
vertices unchanged.  The older component-compression theorem does not apply:
deleting the retained vertex from a block need not select an entire component
of the ambient graph.  Nonseparability of the block is exactly the local
connectivity input that is needed instead.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY.BoundaryCompression

variable [DecidableEq V]
  {G : SimpleGraph V} {B A : Finset V} {b : V}

private theorem erase_disjoint_insert
    (hb : b ∈ B) (hBA : Disjoint B A) :
    Disjoint (B.erase b) (insert b A) := by
  apply Finset.disjoint_left.mpr
  intro v hvQ hvT
  rw [Finset.mem_insert] at hvT
  rcases hvT with rfl | hvA
  · exact (Finset.mem_erase.mp hvQ).1 rfl
  · exact Finset.disjoint_left.mp hBA
      (Finset.mem_of_mem_erase hvQ) hvA

/--
The collapse map is injective on the retained block: only vertices outside
the block are identified.
-/
theorem collapse_injective_on_block
    (hb : b ∈ B) (hBA : Disjoint B A) :
    Set.InjOn (collapse (B.erase b) b) (↑B : Set V) := by
  intro u hu v hv huv
  have hQT :
      Disjoint (B.erase b) (insert b A) :=
    erase_disjoint_insert hb hBA
  have hbT : b ∈ insert b A := by simp
  by_cases hub : u = b
  · subst u
    have huRetained :
        collapse (B.erase b) b b = retainedRoot :=
      collapse_retained (B.erase b) b (by simp)
    have hvRetained :
        collapse (B.erase b) b v = retainedRoot := by
      rw [← huRetained]
      exact huv.symm
    exact
      ((collapse_eq_retained_iff hQT hbT v).1
        hvRetained).symm
  · have huQ : u ∈ B.erase b :=
      Finset.mem_erase.mpr ⟨hub, hu⟩
    by_cases hvb : v = b
    · subst v
      have hvRetained :
          collapse (B.erase b) b b = retainedRoot :=
        collapse_retained (B.erase b) b (by simp)
      have huRetained :
          collapse (B.erase b) b u = retainedRoot := by
        rw [← hvRetained]
        exact huv
      have : u = b :=
        (collapse_eq_retained_iff hQT hbT u).1
          huRetained
      exact False.elim (hub this)
    · have hvQ : v ∈ B.erase b :=
        Finset.mem_erase.mpr ⟨hvb, hv⟩
      have hinner :
          inner (⟨u, huQ⟩ : ↥(B.erase b)) =
            inner (⟨v, hvQ⟩ : ↥(B.erase b)) := by
        simpa [
          collapse_of_mem_component (B.erase b) b huQ,
          collapse_of_mem_component (B.erase b) b hvQ] using huv
      exact congrArg Subtype.val
        (inner_injective hinner)

private def blockHom
    (hb : b ∈ B) (hBA : Disjoint B A) :
    G.induce (↑B : Set V) →g
      rootedGraph G (B.erase b) (insert b A) b where
  toFun v := collapse (B.erase b) b v.1
  map_rel' := by
    intro u v huv
    apply Or.inl
    apply graph_adj_of_adj
    · by_cases hub : u.1 = b
      · exact Finset.mem_union_right _
          (by simp [hub])
      · exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hub, u.2⟩)
    · by_cases hvb : v.1 = b
      · exact Finset.mem_union_right _
          (by simp [hvb])
      · exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hvb, v.2⟩)
    · exact huv
    · intro heq
      exact huv.ne (Subtype.ext
        (collapse_injective_on_block hb hBA
          u.2 v.2 heq))

private theorem blockHom_retained
    (hb : b ∈ B) (hBA : Disjoint B A) :
    blockHom (G := G) hb hBA ⟨b, hb⟩ =
      (retainedRoot :
        BoundaryCompressionVertex (B.erase b)) := by
  exact collapse_retained (B.erase b) b (by simp)

private theorem blockHom_inner
    (hb : b ∈ B) (hBA : Disjoint B A)
    {d : V} (hd : d ∈ B.erase b) :
    blockHom (G := G) hb hBA
        ⟨d, Finset.mem_of_mem_erase hd⟩ =
      inner ⟨d, hd⟩ := by
  exact collapse_of_mem_component (B.erase b) b hd

private theorem blockHom_ne_collapsed
    (hb : b ∈ B) (hBA : Disjoint B A)
    (v : (↑B : Set V)) :
    blockHom (G := G) hb hBA v ≠
      (collapsedRoot :
        BoundaryCompressionVertex (B.erase b)) := by
  by_cases hvb : v.1 = b
  · have hv : v = ⟨b, hb⟩ := Subtype.ext hvb
    rw [hv, blockHom_retained hb hBA]
    simpa using
      (roots_ne :
        (collapsedRoot :
          BoundaryCompressionVertex (B.erase b)) ≠
            retainedRoot).symm
  · have hvQ : v.1 ∈ B.erase b :=
      Finset.mem_erase.mpr ⟨hvb, v.2⟩
    rw [show blockHom (G := G) hb hBA v =
      inner ⟨v.1, hvQ⟩ by
        exact collapse_of_mem_component
          (B.erase b) b hvQ]
    exact inner_ne_collapsed ⟨v.1, hvQ⟩

private theorem connected_delete_collapsed_of_nonseparable
    (hB : IsNonseparableCarrier G B)
    (hb : b ∈ B) (hBA : Disjoint B A) :
    ((rootedGraph G (B.erase b) (insert b A) b).induce
      {w | w ≠ (collapsedRoot :
        BoundaryCompressionVertex (B.erase b))}).Connected := by
  let R :=
    rootedGraph G (B.erase b) (insert b A) b
  let f :
      G.induce (↑B : Set V) →g
        R.induce
          {w | w ≠ (collapsedRoot :
            BoundaryCompressionVertex (B.erase b))} := {
    toFun := fun v =>
      ⟨blockHom (G := G) hb hBA v,
        blockHom_ne_collapsed hb hBA v⟩
    map_rel' := by
      intro u v huv
      exact (blockHom (G := G) hb hBA).map_rel' huv
  }
  rw [connected_iff_exists_forall_reachable]
  refine
    ⟨⟨retainedRoot, roots_ne.symm⟩, ?_⟩
  rintro ⟨w, hw⟩
  cases w with
  | none => exact False.elim (hw rfl)
  | some w =>
      cases w with
      | none =>
          exact SimpleGraph.Reachable.refl _
      | some d =>
          let bB : (↑B : Set V) := ⟨b, hb⟩
          let dB : (↑B : Set V) :=
            ⟨d.1, Finset.mem_of_mem_erase d.2⟩
          have hreach :=
            hB.connected.preconnected bB dB
          have hmapped := hreach.map f
          convert hmapped using 1
          · apply Subtype.ext
            exact (blockHom_retained hb hBA).symm
          · apply Subtype.ext
            exact (blockHom_inner hb hBA d.2).symm

private theorem connected_of_nonseparable
    (hB : IsNonseparableCarrier G B)
    (hb : b ∈ B) (hBA : Disjoint B A) :
    (rootedGraph G (B.erase b) (insert b A) b).Connected := by
  let R :=
    rootedGraph G (B.erase b) (insert b A) b
  have hdelete :=
    connected_delete_collapsed_of_nonseparable hB hb hBA
  rw [connected_iff_exists_forall_reachable]
  refine
    ⟨(collapsedRoot :
      BoundaryCompressionVertex (B.erase b)), ?_⟩
  intro w
  by_cases hw :
      w = (collapsedRoot :
        BoundaryCompressionVertex (B.erase b))
  · subst w
    exact SimpleGraph.Reachable.refl
      (collapsedRoot :
        BoundaryCompressionVertex (B.erase b))
  · let cD :
        {w : BoundaryCompressionVertex (B.erase b) |
          w ≠ (collapsedRoot :
            BoundaryCompressionVertex (B.erase b))} :=
      ⟨retainedRoot, roots_ne.symm⟩
    let wD :
        {w : BoundaryCompressionVertex (B.erase b) |
          w ≠ (collapsedRoot :
            BoundaryCompressionVertex (B.erase b))} :=
      ⟨w, hw⟩
    have htail : (R.induce
        {w | w ≠ (collapsedRoot :
          BoundaryCompressionVertex (B.erase b))}).Reachable cD wD :=
      hdelete.preconnected cD wD
    have htailR :=
      htail.map (Embedding.induce _).toHom
    change R.Reachable retainedRoot w at htailR
    have hrootEdge :
        R.Adj
          (collapsedRoot :
            BoundaryCompressionVertex (B.erase b))
          retainedRoot := by
      exact Or.inr (by
        simp [SimpleGraph.edge_adj, roots_ne])
    exact hrootEdge.reachable.trans htailR

private theorem connected_delete_retained_of_nonseparable
    (hB : IsNonseparableCarrier G B)
    (hb : b ∈ B) (hBA : Disjoint B A)
    {a d : V} (ha : a ∈ A)
    (hd : d ∈ B.erase b) (had : G.Adj a d) :
    ((rootedGraph G (B.erase b) (insert b A) b).induce
      {w | w ≠ (retainedRoot :
        BoundaryCompressionVertex (B.erase b))}).Connected := by
  let R :=
    rootedGraph G (B.erase b) (insert b A) b
  let Q := B.erase b
  let dQ : ↥Q := ⟨d, hd⟩
  have hrootAdj :
      R.Adj (collapsedRoot :
        BoundaryCompressionVertex Q) (inner dQ) := by
    apply Or.inl
    have haT : a ∈ insert b A := by simp [ha]
    have haQ : a ∉ Q := by
      intro haQ
      exact Finset.disjoint_left.mp hBA
        (Finset.mem_of_mem_erase haQ) ha
    have hab : a ≠ b := by
      intro hab
      subst a
      exact Finset.disjoint_left.mp hBA hb ha
    have had' :=
      graph_adj_of_adj
        (Q := Q) (T := insert b A) (t := b)
        (Finset.mem_union_right Q haT)
        (Finset.mem_union_left (insert b A) hd)
        had
        (by
          rw [collapse_of_boundary_ne Q b haQ hab,
            collapse_of_mem_component Q b hd]
          exact inner_ne_collapsed dQ |>.symm)
    rw [collapse_of_boundary_ne Q b haQ hab,
      collapse_of_mem_component Q b hd] at had'
    exact had'
  let f :
      G.induce (↑Q : Set V) →g
        R.induce
          {w | w ≠ (retainedRoot :
            BoundaryCompressionVertex Q)} := {
    toFun := fun v =>
      ⟨inner ⟨v.1, v.2⟩,
        inner_ne_retained ⟨v.1, v.2⟩⟩
    map_rel' := by
      intro u v huv
      change R.Adj
        (inner (⟨u.1, u.2⟩ : ↥Q))
        (inner (⟨v.1, v.2⟩ : ↥Q))
      apply Or.inl
      have hne :
          collapse Q b u.1 ≠ collapse Q b v.1 := by
        intro heq
        apply huv.ne
        apply Subtype.ext
        have hinner :
            inner (⟨u.1, u.2⟩ : ↥Q) =
              inner (⟨v.1, v.2⟩ : ↥Q) := by
          simpa [
            collapse_of_mem_component Q b u.2,
            collapse_of_mem_component Q b v.2] using heq
        exact congrArg Subtype.val
          (inner_injective hinner)
      have hadj := graph_adj_of_adj
        (G := G) (Q := Q) (T := insert b A) (t := b)
        (Finset.mem_union_left (insert b A) u.2)
        (Finset.mem_union_left (insert b A) v.2)
        huv hne
      simpa only [
        collapse_of_mem_component Q b u.2,
        collapse_of_mem_component Q b v.2] using hadj
  }
  rw [connected_iff_exists_forall_reachable]
  refine
    ⟨⟨inner dQ, inner_ne_retained dQ⟩, ?_⟩
  rintro ⟨w, hw⟩
  cases w with
  | none =>
      exact (show
        (R.induce {w | w ≠
          (retainedRoot :
            BoundaryCompressionVertex Q)}).Adj
          ⟨inner dQ, inner_ne_retained dQ⟩
          ⟨collapsedRoot, roots_ne⟩ from
            hrootAdj.symm).reachable
  | some w =>
      cases w with
      | none => exact False.elim (hw rfl)
      | some e =>
          let dQ' : (↑Q : Set V) := ⟨d, hd⟩
          let eQ : (↑Q : Set V) := ⟨e.1, e.2⟩
          have hreach :=
            (hB.delete_connected b hb).preconnected dQ' eQ
          convert hreach.map f using 1 <;>
            apply Subtype.ext <;> rfl

private theorem connected_delete_inner_of_nonseparable
    (hB : IsNonseparableCarrier G B)
    (hb : b ∈ B) (hBA : Disjoint B A)
    (d : ↥(B.erase b)) :
    ((rootedGraph G (B.erase b) (insert b A) b).induce
      {w | w ≠ inner d}).Connected := by
  let R :=
    rootedGraph G (B.erase b) (insert b A) b
  let D := B.erase d.1
  have hbD : b ∈ D := by
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp d.2).1.symm, hb⟩
  let f :
      G.induce (↑D : Set V) →g
        R.induce {w | w ≠ inner d} := {
    toFun := fun v =>
      ⟨collapse (B.erase b) b v.1, by
        intro h
        have hvd :
            v.1 = d.1 :=
          (collapse_eq_inner_iff
            (B.erase b) b d v.1).1 h
        exact (Finset.mem_erase.mp v.2).1 hvd⟩
    map_rel' := by
      intro u v huv
      apply Or.inl
      apply graph_adj_of_adj
      · by_cases hub : u.1 = b
        · exact Finset.mem_union_right _
            (by simp [hub])
        · exact Finset.mem_union_left _
            (Finset.mem_erase.mpr
              ⟨hub, Finset.mem_of_mem_erase u.2⟩)
      · by_cases hvb : v.1 = b
        · exact Finset.mem_union_right _
            (by simp [hvb])
        · exact Finset.mem_union_left _
            (Finset.mem_erase.mpr
              ⟨hvb, Finset.mem_of_mem_erase v.2⟩)
      · exact huv
      · intro heq
        exact huv.ne (Subtype.ext
          (collapse_injective_on_block hb hBA
            (Finset.mem_of_mem_erase u.2)
            (Finset.mem_of_mem_erase v.2) heq))
  }
  rw [connected_iff_exists_forall_reachable]
  let bD : (↑D : Set V) := ⟨b, hbD⟩
  let bR :
      {w : BoundaryCompressionVertex (B.erase b) |
        w ≠ inner d} :=
    ⟨retainedRoot, inner_ne_retained d |>.symm⟩
  refine ⟨bR, ?_⟩
  rintro ⟨w, hw⟩
  cases w with
  | none =>
      have hrootEdge :
          (R.induce {w | w ≠ inner d}).Adj
            bR ⟨collapsedRoot, inner_ne_collapsed d |>.symm⟩ := by
        change R.Adj retainedRoot collapsedRoot
        apply Or.inr
        rw [SimpleGraph.edge_adj]
        exact ⟨Or.inr ⟨rfl, rfl⟩, roots_ne.symm⟩
      exact hrootEdge.reachable
  | some w =>
      cases w with
      | none =>
          exact SimpleGraph.Reachable.refl bR
      | some e =>
          have hed : e.1 ≠ d.1 := by
            intro h
            apply hw
            have : e = d := Subtype.ext h
            rw [this]
            rfl
          let eD : (↑D : Set V) :=
            ⟨e.1, Finset.mem_erase.mpr
              ⟨hed, Finset.mem_of_mem_erase e.2⟩⟩
          have hreach :=
            (hB.delete_connected d.1
              (Finset.mem_of_mem_erase d.2)).preconnected bD eD
          have hmapped := hreach.map f
          convert hmapped using 1
          · apply Subtype.ext
            exact (collapse_retained
              (B.erase b) b (by simp)).symm
          · apply Subtype.ext
            exact (collapse_of_mem_component
              (B.erase b) b e.2).symm

/--
Collapsing a nonempty set of external attachments toward a retained block
vertex produces the 2-connected rooted graph required by the COY induction.
The carrier may be a two-vertex bridge block.
-/
theorem rootedGraph_twoConnected_of_nonseparable
    [Fintype V]
    (hB : IsNonseparableCarrier G B)
    (hb : b ∈ B) (hBA : Disjoint B A)
    (hattachment :
      ∃ a ∈ A, ∃ d ∈ B.erase b, G.Adj a d) :
    IsTwoConnected
      (rootedGraph G (B.erase b) (insert b A) b) := by
  obtain ⟨a, ha, d, hd, had⟩ := hattachment
  apply isTwoConnected_of_connected_delete_one
  · rw [card_vertex]
    have hBcard := hB.card_ge_two
    rw [Finset.card_erase_of_mem hb]
    omega
  · exact connected_of_nonseparable hB hb hBA
  · intro w
    cases w with
    | none =>
        exact
          connected_delete_collapsed_of_nonseparable
            hB hb hBA
    | some w =>
        cases w with
        | none =>
            exact
              connected_delete_retained_of_nonseparable
                hB hb hBA ha hd had
        | some d =>
            exact
              connected_delete_inner_of_nonseparable
                hB hb hBA d

end COY.BoundaryCompression

end DeanK5
