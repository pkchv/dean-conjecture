import DeanK5.Contraction
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# The two-link case of Menger's theorem

This file proves only the finite `k = 2` set version needed by the paper.
The proof is by induction under edge deletion and contraction.  Keeping the
result this specialized avoids importing a general flow or path-packing
development into the formal trust boundary.
-/

open scoped Sym2

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace MengerTwo

/-- A walk whose endpoints lie in the prescribed vertex sets. -/
structure SetWalk (G : SimpleGraph V) (A B : Finset V) where
  /-- The endpoint chosen in `A`. -/
  start : V
  /-- The endpoint chosen in `B`. -/
  finish : V
  /-- The underlying walk from `start` to `finish`. -/
  walk : G.Walk start finish
  start_mem : start ∈ A
  finish_mem : finish ∈ B

/-- Two completely vertex-disjoint walks between two prescribed sets. -/
def HasTwoLinks (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∃ P Q : SetWalk G A B,
    P.walk.support.Disjoint Q.walk.support

/-- Every walk from `A` to `B` meets `X`. -/
def Separates (G : SimpleGraph V)
    (A B X : Finset V) : Prop :=
  ∀ P : SetWalk G A B,
    ∃ x ∈ P.walk.support, x ∈ X

theorem Separates.symm
    {G : SimpleGraph V} {A B X : Finset V}
    (h : Separates G A B X) :
    Separates G B A X := by
  intro P
  let Q : SetWalk G A B := {
    start := P.finish
    finish := P.start
    walk := P.walk.reverse
    start_mem := P.finish_mem
    finish_mem := P.start_mem
  }
  obtain ⟨x, hx, hxX⟩ := h Q
  exact ⟨x, by simpa [Q] using hx, hxX⟩

/-- Bypassing repetitions preserves prescribed endpoints and can only
shrink support. -/
def SetWalk.toSimplePath
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    SimplePath G P.start P.finish :=
  ⟨P.walk.toPath, P.walk.bypass_isPath⟩

theorem SetWalk.support_toSimplePath_subset
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    P.toSimplePath.walk.support ⊆ P.walk.support :=
  P.walk.support_toPath_subset_support

/-- A two-link walk certificate gives the simple paths used by the paper. -/
theorem HasTwoLinks.simplePaths
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (h : HasTwoLinks G A B) :
    ∃ a₁ a₂ b₁ b₂ : V,
      a₁ ∈ A ∧ a₂ ∈ A ∧
      b₁ ∈ B ∧ b₂ ∈ B ∧
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      ∃ P₁ : SimplePath G a₁ b₁,
      ∃ P₂ : SimplePath G a₂ b₂,
        P₁.walk.support.Disjoint P₂.walk.support := by
  obtain ⟨P, Q, hPQ⟩ := h
  let P' := P.toSimplePath
  let Q' := Q.toSimplePath
  have hdisj :
      P'.walk.support.Disjoint Q'.walk.support := by
    apply List.disjoint_left.mpr
    intro z hzP hzQ
    exact List.disjoint_left.mp hPQ
      (P.support_toSimplePath_subset hzP)
      (Q.support_toSimplePath_subset hzQ)
  have hstart : P.start ≠ Q.start := by
    intro h
    apply List.disjoint_left.mp hdisj
      P'.walk.start_mem_support
    rw [h]
    exact Q'.walk.start_mem_support
  have hfinish : P.finish ≠ Q.finish := by
    intro h
    apply List.disjoint_left.mp hdisj
      P'.walk.end_mem_support
    rw [h]
    exact Q'.walk.end_mem_support
  exact ⟨P.start, Q.start, P.finish, Q.finish,
    P.start_mem, Q.start_mem, P.finish_mem, Q.finish_mem,
    hstart, hfinish, P', Q', hdisj⟩

/-- A first-hit truncation of a set-walk. -/
noncomputable def SetWalk.trimFinish
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    SetWalk G A B :=
  let hnonempty :
      {x ∈ B | x ∈ P.walk.support}.Nonempty := by
    refine ⟨P.finish, ?_⟩
    simp [P.finish_mem]
  let h :=
    P.walk.exists_mem_support_forall_mem_support_imp_eq
      B hnonempty
  let x := Classical.choose h
  let hxB := (Classical.choose_spec h).1
  let hxPExists := (Classical.choose_spec h).2
  let hxP := Classical.choose hxPExists
  {
    start := P.start
    finish := x
    walk := P.walk.takeUntil x hxP
    start_mem := P.start_mem
    finish_mem := hxB
  }

theorem SetWalk.trimFinish_support_subset
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    P.trimFinish.walk.support ⊆ P.walk.support := by
  classical
  apply P.walk.support_takeUntil_subset_support

theorem SetWalk.trimFinish_meets_finish_set_only_at_end
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    ∀ x ∈ P.trimFinish.walk.support,
      x ∈ B → x = P.trimFinish.finish := by
  classical
  dsimp only [SetWalk.trimFinish]
  let hnonempty :
      {x ∈ B | x ∈ P.walk.support}.Nonempty := by
    refine ⟨P.finish, ?_⟩
    simp [P.finish_mem]
  let h :=
    P.walk.exists_mem_support_forall_mem_support_imp_eq
      B hnonempty
  intro x hx hB
  exact Classical.choose_spec
    (Classical.choose_spec h).2 x hB hx

/-- First hit the target set and then bypass repetitions. -/
noncomputable def SetWalk.trimSimpleFinish
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    SetWalk G A B := {
  start := P.trimFinish.start
  finish := P.trimFinish.finish
  walk := P.trimFinish.walk.toPath
  start_mem := P.trimFinish.start_mem
  finish_mem := P.trimFinish.finish_mem
}

theorem SetWalk.trimSimpleFinish_isPath
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    P.trimSimpleFinish.walk.IsPath :=
  P.trimFinish.walk.bypass_isPath

theorem SetWalk.trimSimpleFinish_support_subset
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    P.trimSimpleFinish.walk.support ⊆ P.walk.support := by
  intro x hx
  apply P.trimFinish_support_subset
  exact P.trimFinish.walk.support_toPath_subset_support hx

theorem SetWalk.trimSimpleFinish_meets_finish_set_only_at_end
    [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V}
    (P : SetWalk G A B) :
    ∀ x ∈ P.trimSimpleFinish.walk.support,
      x ∈ B → x = P.trimSimpleFinish.finish := by
  intro x hx hB
  apply P.trimFinish_meets_finish_set_only_at_end x
    (P.trimFinish.walk.support_toPath_subset_support hx) hB

section Contraction

variable [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem exists_lift_contracted_adj
    (G : SimpleGraph V) (q r a : V)
    (hqr : q ≠ r) (hqrAdj : G.Adj q r)
    {z : ContractPairVertex V q r}
    (h :
      (contractPair G q r).Adj
        (contractVertex q r a) z) :
    ∃ c : V, contractVertex q r c = z ∧
      ∃ p : G.Walk a c,
        ∀ x ∈ p.support,
          contractVertex q r x =
              contractVertex q r a ∨
            contractVertex q r x = z := by
  classical
  cases z with
  | none =>
      by_cases haq : a = q
      · subst a
        simp [contractVertex] at h
      by_cases har : a = r
      · subst a
        simp [contractVertex] at h
      have haContract :
          contractVertex q r a =
            some ⟨a, haq, har⟩ := by
        simp [contractVertex, haq, har]
      rw [haContract] at h
      rcases h with haQ | haR
      · refine ⟨q, by simp [contractVertex],
          haQ.toWalk, ?_⟩
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by simp [contractVertex])
      · refine ⟨r, by simp [contractVertex],
          haR.toWalk, ?_⟩
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by simp [contractVertex])
  | some w =>
      by_cases haq : a = q
      · subst a
        have h' : G.Adj q w.1 ∨ G.Adj r w.1 := by
          simpa [contractVertex] using h
        rcases h' with hqw | hrw
        · refine ⟨w.1, by
              simp [contractVertex, w.2.1, w.2.2],
            hqw.toWalk, ?_⟩
          intro x hx
          simp at hx
          rcases hx with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (by
              simp [contractVertex, w.2.1, w.2.2])
        · let p : G.Walk q w.1 :=
            .cons hqrAdj (.cons hrw .nil)
          refine ⟨w.1, by
              simp [contractVertex, w.2.1, w.2.2],
            p, ?_⟩
          intro x hx
          simp only [p, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | hx
          · exact Or.inl rfl
          · exact Or.inl (by simp [contractVertex])
          · exact Or.inr (by
              simp [contractVertex, w.2.1, w.2.2])
          · contradiction
      · by_cases har : a = r
        · subst a
          have h' : G.Adj q w.1 ∨ G.Adj r w.1 := by
            simpa [contractVertex] using h
          rcases h' with hqw | hrw
          · let p : G.Walk r w.1 :=
              .cons hqrAdj.symm (.cons hqw .nil)
            refine ⟨w.1, by
                simp [contractVertex, w.2.1, w.2.2],
              p, ?_⟩
            intro x hx
            simp only [p, SimpleGraph.Walk.support_cons,
              SimpleGraph.Walk.support_nil, List.mem_cons] at hx
            rcases hx with rfl | rfl | rfl | hx
            · exact Or.inl rfl
            · exact Or.inl (by simp [contractVertex])
            · exact Or.inr (by
                simp [contractVertex, w.2.1, w.2.2])
            · contradiction
          · refine ⟨w.1, by
                simp [contractVertex, w.2.1, w.2.2],
              hrw.toWalk, ?_⟩
            intro x hx
            simp at hx
            rcases hx with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (by
                simp [contractVertex, w.2.1, w.2.2])
        · have haContract :
              contractVertex q r a =
                some ⟨a, haq, har⟩ := by
            simp [contractVertex, haq, har]
          have haw : G.Adj a w.1 := by
            simpa [haContract] using h
          refine ⟨w.1, by
              simp [contractVertex, w.2.1, w.2.2],
            haw.toWalk, ?_⟩
          intro x hx
          simp at hx
          rcases hx with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (by
              simp [contractVertex, w.2.1, w.2.2])

omit [Fintype V] in
/--
Every walk in an edge contraction lifts to the original graph once
preimages of its endpoints are fixed.  Every lifted vertex maps back to a
vertex of the contracted walk.
-/
theorem exists_pull_contracted_walk
    (G : SimpleGraph V) (q r : V)
    (hqr : q ≠ r) (hqrAdj : G.Adj q r)
    {u v : ContractPairVertex V q r}
    (p : (contractPair G q r).Walk u v)
    {a b : V}
    (ha : contractVertex q r a = u)
    (hb : contractVertex q r b = v) :
    ∃ P : G.Walk a b,
      ∀ x ∈ P.support,
        contractVertex q r x ∈ p.support := by
  classical
  induction p generalizing a with
  | nil =>
      have habContract :
          contractVertex q r a =
            contractVertex q r b :=
        ha.trans hb.symm
      rcases (contractVertex_eq_iff q r a b).1 habContract with
        hab | ⟨haqr, hbqr⟩
      · subst b
        refine ⟨.nil, ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.support_nil,
          List.mem_singleton] at hx ⊢
        subst x
        exact ha
      · rcases haqr with rfl | rfl <;>
          rcases hbqr with rfl | rfl
        · refine ⟨.nil, by simp [ha]⟩
        · refine ⟨hqrAdj.toWalk, ?_⟩
          intro x hx
          simp at hx
          rcases hx with rfl | rfl <;>
            simpa [contractVertex] using ha
        · refine ⟨hqrAdj.symm.toWalk, ?_⟩
          intro x hx
          simp at hx
          rcases hx with rfl | rfl <;>
            simpa [contractVertex] using hb
        · refine ⟨.nil, by simp [hb]⟩
  | @cons u m v hum p ih =>
      obtain ⟨c, hc, R, hR⟩ :=
        exists_lift_contracted_adj
          G q r a hqr hqrAdj (ha ▸ hum)
      obtain ⟨S, hS⟩ :=
        ih hc hb
      refine ⟨R.append S, ?_⟩
      intro x hx
      simp only [SimpleGraph.Walk.support_append,
        List.mem_append] at hx
      rcases hx with hxR | hxS
      · rcases hR x hxR with hxa | hxc
        · rw [hxa, ha]
          exact (SimpleGraph.Walk.cons hum p).start_mem_support
        · rw [hxc]
          exact List.mem_cons.mpr
            (Or.inr p.start_mem_support)
      · exact List.mem_cons.mpr
          (Or.inr (hS x (List.mem_of_mem_tail hxS)))

/-- Push a set-walk through an edge contraction. -/
def SetWalk.pushContraction
    (G : SimpleGraph V) (q r : V)
    {A B : Finset V} (P : SetWalk G A B) :
    SetWalk (contractPair G q r)
      (A.image (contractVertex q r))
      (B.image (contractVertex q r)) := {
  start := contractVertex q r P.start
  finish := contractVertex q r P.finish
  walk := SimpleGraph.Walk.mapOrContract
    (contractVertex q r)
    (contractVertex_eq_or_adj G q r) P.walk
  start_mem := Finset.mem_image.mpr
    ⟨P.start, P.start_mem, rfl⟩
  finish_mem := Finset.mem_image.mpr
    ⟨P.finish, P.finish_mem, rfl⟩
}

/-- A separator in the contraction pulls back to a separator in the
original graph. -/
theorem Separates.contractionPreimage
    (G : SimpleGraph V) (q r : V)
    {A B :
      Finset V}
    {Y : Finset (ContractPairVertex V q r)}
    (hsep :
      Separates (contractPair G q r)
        (A.image (contractVertex q r))
        (B.image (contractVertex q r)) Y) :
    Separates G A B (DeanK5.contractionPreimage q r Y) := by
  intro P
  obtain ⟨z, hzP, hzY⟩ :=
    hsep (P.pushContraction G q r)
  obtain ⟨x, hxP, hfx⟩ :=
    SimpleGraph.Walk.exists_of_mem_support_mapOrContract
      (contractVertex q r)
      (contractVertex_eq_or_adj G q r) P.walk hzP
  refine ⟨x, hxP, ?_⟩
  rw [contractionPreimage_mem]
  rwa [hfx]

omit [Fintype V] in
/-- Two disjoint links in a contraction lift to two disjoint links in the
original graph. -/
theorem HasTwoLinks.of_contraction
    (G : SimpleGraph V) (q r : V)
    (hqr : q ≠ r) (hqrAdj : G.Adj q r)
    (A B : Finset V)
    (h :
      HasTwoLinks (contractPair G q r)
        (A.image (contractVertex q r))
        (B.image (contractVertex q r))) :
    HasTwoLinks G A B := by
  classical
  obtain ⟨P, Q, hPQ⟩ := h
  obtain ⟨a, haA, ha⟩ :=
    Finset.mem_image.mp P.start_mem
  obtain ⟨b, hbB, hb⟩ :=
    Finset.mem_image.mp P.finish_mem
  obtain ⟨c, hcA, hc⟩ :=
    Finset.mem_image.mp Q.start_mem
  obtain ⟨d, hdB, hd⟩ :=
    Finset.mem_image.mp Q.finish_mem
  obtain ⟨p, hp⟩ :=
    exists_pull_contracted_walk
      G q r hqr hqrAdj P.walk ha hb
  obtain ⟨s, hs⟩ :=
    exists_pull_contracted_walk
      G q r hqr hqrAdj Q.walk hc hd
  let P' : SetWalk G A B := {
    start := a
    finish := b
    walk := p
    start_mem := haA
    finish_mem := hbB
  }
  let Q' : SetWalk G A B := {
    start := c
    finish := d
    walk := s
    start_mem := hcA
    finish_mem := hdB
  }
  refine ⟨P', Q', ?_⟩
  apply List.disjoint_left.mpr
  intro x hxP hxQ
  apply List.disjoint_left.mp hPQ
    (hp x hxP)
  exact hs x hxQ

end Contraction

section Deletion

variable [Fintype V] [DecidableEq V]

/-- Regard a set-walk in an edge-deleted graph as a walk in the original
graph. -/
def SetWalk.ofDeleteEdge
    (G : SimpleGraph V) (e : Sym2 V)
    {A B : Finset V}
    (P : SetWalk (G.deleteEdges {e}) A B) :
    SetWalk G A B := {
  start := P.start
  finish := P.finish
  walk := P.walk.transfer G (by
    intro edge hedge
    have hdel :=
      SimpleGraph.Walk.edges_subset_edgeSet P.walk hedge
    change edge ∈ (G.deleteEdges {e}).edgeSet at hdel
    rw [SimpleGraph.edgeSet_deleteEdges] at hdel
    exact hdel.1)
  start_mem := P.start_mem
  finish_mem := P.finish_mem
}

omit [Fintype V] [DecidableEq V] in
@[simp] theorem SetWalk.ofDeleteEdge_support
    (G : SimpleGraph V) (e : Sym2 V)
    {A B : Finset V}
    (P : SetWalk (G.deleteEdges {e}) A B) :
    (P.ofDeleteEdge G e).walk.support =
      P.walk.support := by
  simp [SetWalk.ofDeleteEdge]

omit [Fintype V] [DecidableEq V] in
theorem HasTwoLinks.of_deleteEdge
    (G : SimpleGraph V) (e : Sym2 V)
    (A B : Finset V)
    (h : HasTwoLinks (G.deleteEdges {e}) A B) :
    HasTwoLinks G A B := by
  obtain ⟨P, Q, hPQ⟩ := h
  refine ⟨P.ofDeleteEdge G e, Q.ofDeleteEdge G e, ?_⟩
  simpa using hPQ

omit [Fintype V] in
/--
If both endpoints of the deleted edge lie in an `A`--`B` separator `X`,
then an `A`--`X` separator in the edge-deleted graph already separates
`A` from `B` in the original graph.
-/
theorem separates_of_deleteEdge_to_separator
    (G : SimpleGraph V) (q r : V)
    (hqrAdj : G.Adj q r)
    {A B X Z : Finset V}
    (hqX : q ∈ X) (hrX : r ∈ X)
    (hX : Separates G A B X)
    (hZ : Separates (G.deleteEdges {s(q, r)}) A X Z) :
    Separates G A B Z := by
  classical
  intro P
  obtain ⟨x₀, hx₀P, hx₀X⟩ := hX P
  have hhit :
      {x ∈ X | x ∈ P.walk.support}.Nonempty := by
    refine ⟨x₀, ?_⟩
    simp [hx₀X, hx₀P]
  obtain ⟨x, hxX, hxP, hfirst⟩ :=
    P.walk.exists_mem_support_forall_mem_support_imp_eq
      X hhit
  let Rwalk := P.walk.takeUntil x hxP
  have hedgeAvoid : s(q, r) ∉ Rwalk.edges := by
    intro he
    have hqR : q ∈ Rwalk.support :=
      Rwalk.fst_mem_support_of_mem_edges he
    have hrR : r ∈ Rwalk.support :=
      Rwalk.snd_mem_support_of_mem_edges he
    have hqx : q = x := hfirst q hqX hqR
    have hrx : r = x := hfirst r hrX hrR
    exact hqrAdj.ne (hqx.trans hrx.symm)
  let R : SetWalk (G.deleteEdges {s(q, r)}) A X := {
    start := P.start
    finish := x
    walk := Rwalk.toDeleteEdge s(q, r) hedgeAvoid
    start_mem := P.start_mem
    finish_mem := hxX
  }
  obtain ⟨z, hzR, hzZ⟩ := hZ R
  refine ⟨z, ?_, hzZ⟩
  apply P.walk.support_takeUntil_subset_support hxP
  simpa [R, Rwalk] using hzR

end Deletion

section Stitching

variable [DecidableEq V]

/--
Two target-minimal simple set-walks approaching a separator from opposite
sides can meet only at their common target endpoint.
-/
theorem eq_finish_of_mem_both_sides
    {G : SimpleGraph V} {A B X : Finset V}
    (hsep : Separates G A B X)
    (P : SetWalk G A X) (Q : SetWalk G B X)
    (hPpath : P.walk.IsPath) (hQpath : Q.walk.IsPath)
    (hPfirst :
      ∀ x ∈ P.walk.support, x ∈ X → x = P.finish)
    (hQfirst :
      ∀ x ∈ Q.walk.support, x ∈ X → x = Q.finish)
    {z : V} (hzP : z ∈ P.walk.support)
    (hzQ : z ∈ Q.walk.support) :
    z = P.finish ∧ z = Q.finish := by
  by_contra h
  have hzNotX : z ∉ X := by
    intro hzX
    exact h ⟨hPfirst z hzP hzX, hQfirst z hzQ hzX⟩
  let pz := P.walk.takeUntil z hzP
  let qz := Q.walk.takeUntil z hzQ
  let R : SetWalk G A B := {
    start := P.start
    finish := Q.start
    walk := pz.append qz.reverse
    start_mem := P.start_mem
    finish_mem := Q.start_mem
  }
  obtain ⟨x, hxR, hxX⟩ := hsep R
  have hPfinishNe : P.finish ≠ z := by
    intro hpz
    exact hzNotX (hpz ▸ P.finish_mem)
  have hQfinishNe : Q.finish ≠ z := by
    intro hqz
    exact hzNotX (hqz ▸ Q.finish_mem)
  simp only [R, SimpleGraph.Walk.support_append,
    List.mem_append] at hxR
  rcases hxR with hxP | hxQ
  · have hxPfull :
        x ∈ P.walk.support :=
      P.walk.support_takeUntil_subset_support hzP hxP
    have hxEq : x = P.finish :=
      hPfirst x hxPfull hxX
    subst x
    exact
      (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        hPpath hzP hPfinishNe) hxP
  · have hxQreverse :
        x ∈ qz.reverse.support :=
      List.mem_of_mem_tail hxQ
    have hxQprefix :
        x ∈ qz.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hxQreverse
    have hxQfull :
        x ∈ Q.walk.support :=
      Q.walk.support_takeUntil_subset_support hzQ hxQprefix
    have hxEq : x = Q.finish :=
      hQfirst x hxQfull hxX
    subst x
    exact
      (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        hQpath hzQ hQfinishNe) hxQprefix

/-- Append an `A`--`X` walk to the reverse of a `B`--`X` walk with the
same endpoint in `X`. -/
def SetWalk.stitch
    {G : SimpleGraph V} {A B X : Finset V}
    (P : SetWalk G A X) (Q : SetWalk G B X)
    (hfinish : P.finish = Q.finish) :
    SetWalk G A B := {
  start := P.start
  finish := Q.start
  walk := P.walk.append
    (Q.walk.reverse.copy hfinish.symm rfl)
  start_mem := P.start_mem
  finish_mem := Q.start_mem
}

omit [DecidableEq V] in
theorem SetWalk.stitch_support_cases
    {G : SimpleGraph V} {A B X : Finset V}
    (P : SetWalk G A X) (Q : SetWalk G B X)
    (hfinish : P.finish = Q.finish)
    {z : V}
    (hz : z ∈ (P.stitch Q hfinish).walk.support) :
    z ∈ P.walk.support ∨ z ∈ Q.walk.support := by
  simp only [SetWalk.stitch,
    SimpleGraph.Walk.support_append,
    List.mem_append] at hz
  rcases hz with hzP | hzQ
  · exact Or.inl hzP
  · right
    have hzQ' :
        z ∈ (Q.walk.reverse.copy hfinish.symm rfl).support :=
      List.mem_of_mem_tail hzQ
    simpa [SimpleGraph.Walk.support_reverse] using hzQ'

/-- Stitch two disjoint `A`--`X` links to two disjoint `B`--`X` links
across a two-vertex `A`--`B` separator. -/
theorem stitch_two_links
    {G : SimpleGraph V} {A B X : Finset V}
    (hXcard : X.card = 2)
    (hsep : Separates G A B X)
    (hAX : HasTwoLinks G A X)
    (hBX : HasTwoLinks G B X) :
    HasTwoLinks G A B := by
  classical
  obtain ⟨P₀, P₁, hPdisj⟩ := hAX
  obtain ⟨Q₀, Q₁, hQdisj⟩ := hBX
  let P₀' := P₀.trimSimpleFinish
  let P₁' := P₁.trimSimpleFinish
  let Q₀' := Q₀.trimSimpleFinish
  let Q₁' := Q₁.trimSimpleFinish
  have hPdisj' :
      P₀'.walk.support.Disjoint
        P₁'.walk.support := by
    apply List.disjoint_left.mpr
    intro z hz₀ hz₁
    exact List.disjoint_left.mp hPdisj
      (P₀.trimSimpleFinish_support_subset hz₀)
      (P₁.trimSimpleFinish_support_subset hz₁)
  have hQdisj' :
      Q₀'.walk.support.Disjoint
        Q₁'.walk.support := by
    apply List.disjoint_left.mpr
    intro z hz₀ hz₁
    exact List.disjoint_left.mp hQdisj
      (Q₀.trimSimpleFinish_support_subset hz₀)
      (Q₁.trimSimpleFinish_support_subset hz₁)
  have hPfinishNe : P₀'.finish ≠ P₁'.finish := by
    intro h
    apply List.disjoint_left.mp hPdisj'
      P₀'.walk.end_mem_support
    rw [h]
    exact P₁'.walk.end_mem_support
  have hQfinishNe : Q₀'.finish ≠ Q₁'.finish := by
    intro h
    apply List.disjoint_left.mp hQdisj'
      Q₀'.walk.end_mem_support
    rw [h]
    exact Q₁'.walk.end_mem_support
  have hPcover :
      ({P₀'.finish, P₁'.finish} : Finset V) = X := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact P₀'.finish_mem
      · exact P₁'.finish_mem
    · simp [hPfinishNe, hXcard]
  have hQcover :
      ({Q₀'.finish, Q₁'.finish} : Finset V) = X := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Q₀'.finish_mem
      · exact Q₁'.finish_mem
    · simp [hQfinishNe, hXcard]
  have hP₀match :
      P₀'.finish = Q₀'.finish ∨
        P₀'.finish = Q₁'.finish := by
    have : P₀'.finish ∈
        ({Q₀'.finish, Q₁'.finish} : Finset V) := by
      rw [hQcover]
      exact P₀'.finish_mem
    simpa using this
  have crossEq
      (P : SetWalk G A X) (Q : SetWalk G B X)
      (hPpath : P.walk.IsPath)
      (hQpath : Q.walk.IsPath)
      (hPfirst :
        ∀ x ∈ P.walk.support, x ∈ X → x = P.finish)
      (hQfirst :
        ∀ x ∈ Q.walk.support, x ∈ X → x = Q.finish)
      {z : V} (hzP : z ∈ P.walk.support)
      (hzQ : z ∈ Q.walk.support) :
      z = P.finish ∧ z = Q.finish :=
    eq_finish_of_mem_both_sides hsep P Q
      hPpath hQpath hPfirst hQfirst hzP hzQ
  rcases hP₀match with h00 | h01
  · have h11 : P₁'.finish = Q₁'.finish := by
      have hmem : P₁'.finish ∈
          ({Q₀'.finish, Q₁'.finish} : Finset V) := by
        rw [hQcover]
        exact P₁'.finish_mem
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hmem
      exact hmem.resolve_left
        (fun h10 => hPfinishNe
          (h00.trans h10.symm))
    refine ⟨P₀'.stitch Q₀' h00,
      P₁'.stitch Q₁' h11, ?_⟩
    apply List.disjoint_left.mpr
    intro z hz₀ hz₁
    rcases P₀'.stitch_support_cases Q₀' h00 hz₀ with
        hzP₀ | hzQ₀ <;>
      rcases P₁'.stitch_support_cases Q₁' h11 hz₁ with
        hzP₁ | hzQ₁
    · exact List.disjoint_left.mp hPdisj' hzP₀ hzP₁
    · obtain ⟨hz0, hz1⟩ :=
        crossEq P₀' Q₁'
          P₀.trimSimpleFinish_isPath
          Q₁.trimSimpleFinish_isPath
          P₀.trimSimpleFinish_meets_finish_set_only_at_end
          Q₁.trimSimpleFinish_meets_finish_set_only_at_end
          hzP₀ hzQ₁
      exact hQfinishNe
        (h00.symm.trans (hz0.symm.trans hz1))
    · obtain ⟨hz1, hz0⟩ :=
        crossEq P₁' Q₀'
          P₁.trimSimpleFinish_isPath
          Q₀.trimSimpleFinish_isPath
          P₁.trimSimpleFinish_meets_finish_set_only_at_end
          Q₀.trimSimpleFinish_meets_finish_set_only_at_end
          hzP₁ hzQ₀
      exact hPfinishNe
        (h00.trans (hz0.symm.trans hz1))
    · exact List.disjoint_left.mp hQdisj' hzQ₀ hzQ₁
  · have h10 : P₁'.finish = Q₀'.finish := by
      have hmem : P₁'.finish ∈
          ({Q₀'.finish, Q₁'.finish} : Finset V) := by
        rw [hQcover]
        exact P₁'.finish_mem
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hmem
      exact hmem.resolve_right
        (fun h11 => hPfinishNe
          (h01.trans h11.symm))
    refine ⟨P₀'.stitch Q₁' h01,
      P₁'.stitch Q₀' h10, ?_⟩
    apply List.disjoint_left.mpr
    intro z hz₀ hz₁
    rcases P₀'.stitch_support_cases Q₁' h01 hz₀ with
        hzP₀ | hzQ₁ <;>
      rcases P₁'.stitch_support_cases Q₀' h10 hz₁ with
        hzP₁ | hzQ₀
    · exact List.disjoint_left.mp hPdisj' hzP₀ hzP₁
    · obtain ⟨hz0, hz1⟩ :=
        crossEq P₀' Q₀'
          P₀.trimSimpleFinish_isPath
          Q₀.trimSimpleFinish_isPath
          P₀.trimSimpleFinish_meets_finish_set_only_at_end
          Q₀.trimSimpleFinish_meets_finish_set_only_at_end
          hzP₀ hzQ₀
      exact hQfinishNe
        (hz1.symm.trans (hz0.trans h01))
    · obtain ⟨hz1, hz0⟩ :=
        crossEq P₁' Q₁'
          P₁.trimSimpleFinish_isPath
          Q₁.trimSimpleFinish_isPath
          P₁.trimSimpleFinish_meets_finish_set_only_at_end
          Q₁.trimSimpleFinish_meets_finish_set_only_at_end
          hzP₁ hzQ₁
      exact hPfinishNe
        (h01.trans (hz0.symm.trans hz1))
    · exact List.disjoint_left.mp hQdisj'.symm hzQ₁ hzQ₀

end Stitching

section Induction

variable [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem bottom_dichotomy
    (A B : Finset V) :
    HasTwoLinks (⊥ : SimpleGraph V) A B ∨
      ∃ X : Finset V,
        X.card < 2 ∧ Separates (⊥ : SimpleGraph V) A B X := by
  classical
  by_cases hcard : 2 ≤ (A ∩ B).card
  · have hone : 1 < (A ∩ B).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp hone
    let P : SetWalk (⊥ : SimpleGraph V) A B := {
      start := a
      finish := a
      walk := .nil
      start_mem := (Finset.mem_inter.mp ha).1
      finish_mem := (Finset.mem_inter.mp ha).2
    }
    let Q : SetWalk (⊥ : SimpleGraph V) A B := {
      start := b
      finish := b
      walk := .nil
      start_mem := (Finset.mem_inter.mp hb).1
      finish_mem := (Finset.mem_inter.mp hb).2
    }
    left
    refine ⟨P, Q, ?_⟩
    apply List.disjoint_left.mpr
    intro z hzP hzQ
    simp only [P, Q, SimpleGraph.Walk.support_nil,
      List.mem_singleton] at hzP hzQ
    exact hab (hzP.symm.trans hzQ)
  · right
    refine ⟨A ∩ B, by omega, ?_⟩
    rintro ⟨a, b, p, ha, hb⟩
    cases p with
    | nil =>
        exact ⟨a, by simp,
          Finset.mem_inter.mpr ⟨ha, hb⟩⟩
    | @cons a c b hac p =>
        simp at hac

omit [DecidableEq V] in
private theorem card_deleteEdge_lt
    (G : SimpleGraph V) {q r : V}
    (hqrAdj : G.Adj q r) :
    (G.deleteEdges {s(q, r)}).edgeSet.ncard <
      G.edgeSet.ncard := by
  classical
  rw [SimpleGraph.edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_lt_of_mem hqrAdj

private theorem dichotomy_of_card_bound (n : ℕ) :
    ∀ (W : Type u) [Fintype W] [DecidableEq W],
      Fintype.card W ≤ n →
      ∀ (G : SimpleGraph W) (A B : Finset W),
        HasTwoLinks G A B ∨
          ∃ X : Finset W,
            X.card < 2 ∧ Separates G A B X := by
  induction n using Nat.strong_induction_on with
  | h n vertexIH =>
      intro W _ _ hW G A B
      generalize hedgeCount :
        G.edgeSet.ncard = m
      induction m using Nat.strong_induction_on generalizing G A B with
      | h m edgeIH =>
          by_cases hbot : G = ⊥
          · subst G
            exact bottom_dichotomy A B
          obtain ⟨e, he⟩ :=
            SimpleGraph.edgeSet_nonempty.mpr hbot
          induction e using Sym2.inductionOn with
          | _ q r =>
              have hqrAdj : G.Adj q r := by
                simpa [SimpleGraph.mem_edgeSet] using he
              have hqr : q ≠ r := hqrAdj.ne
              let C := contractPair G q r
              let f := contractVertex q r
              have hCcard :
                  Fintype.card (ContractPairVertex W q r) <
                    n :=
                (card_contractPairVertex_lt q r hqr).trans_le hW
              have hcontract :=
                vertexIH
                  (Fintype.card (ContractPairVertex W q r))
                  hCcard
                  (ContractPairVertex W q r)
                  le_rfl C (A.image f) (B.image f)
              rcases hcontract with hlinks | ⟨Y, hYcard, hYsep⟩
              · exact Or.inl
                  (HasTwoLinks.of_contraction
                    G q r hqr hqrAdj A B hlinks)
              · let X : Finset W :=
                  DeanK5.contractionPreimage q r Y
                have hXsep : Separates G A B X := by
                  exact hYsep.contractionPreimage G q r
                have hXle : X.card ≤ 2 := by
                  have hbound :=
                    contractionPreimage_card_le q r Y
                  change X.card ≤
                    Y.card + if none ∈ Y then 1 else 0 at hbound
                  split at hbound <;> omega
                by_cases hXsmall : X.card < 2
                · exact Or.inr ⟨X, hXsmall, hXsep⟩
                have hXcard : X.card = 2 := by omega
                have hnone : none ∈ Y := by
                  by_contra hnone
                  have hbound :=
                    contractionPreimage_card_le q r Y
                  change X.card ≤
                    Y.card + if none ∈ Y then 1 else 0 at hbound
                  simp [hnone] at hbound
                  omega
                have hqX : q ∈ X := by
                  change q ∈ contractionPreimage q r Y
                  rw [contractionPreimage_mem]
                  simpa [contractVertex] using hnone
                have hrX : r ∈ X := by
                  change r ∈ contractionPreimage q r Y
                  rw [contractionPreimage_mem]
                  simpa [contractVertex] using hnone
                let H := G.deleteEdges {s(q, r)}
                have hHcount :
                    H.edgeSet.ncard < m := by
                  rw [← hedgeCount]
                  exact card_deleteEdge_lt G hqrAdj
                have hAXdichotomy :=
                  edgeIH H.edgeSet.ncard hHcount
                    H A X rfl
                rcases hAXdichotomy with
                    hAX | ⟨Z, hZcard, hZsep⟩
                · have hBXdichotomy :=
                    edgeIH H.edgeSet.ncard hHcount
                      H B X rfl
                  rcases hBXdichotomy with
                      hBX | ⟨Z, hZcard, hZsep⟩
                  · have hAXG :
                        HasTwoLinks G A X :=
                      HasTwoLinks.of_deleteEdge
                        G s(q, r) A X hAX
                    have hBXG :
                        HasTwoLinks G B X :=
                      HasTwoLinks.of_deleteEdge
                        G s(q, r) B X hBX
                    exact Or.inl
                      (stitch_two_links hXcard hXsep
                        hAXG hBXG)
                  · have hsepBA :
                        Separates G B A Z :=
                      separates_of_deleteEdge_to_separator
                        G q r hqrAdj hqX hrX
                        hXsep.symm hZsep
                    exact Or.inr
                      ⟨Z, hZcard, hsepBA.symm⟩
                · have hsepAB :
                      Separates G A B Z :=
                    separates_of_deleteEdge_to_separator
                      G q r hqrAdj hqX hrX
                      hXsep hZsep
                  exact Or.inr ⟨Z, hZcard, hsepAB⟩

/-- The finite two-link set form of Menger's theorem. -/
theorem two_links_or_small_separator
    (G : SimpleGraph V) (A B : Finset V) :
    HasTwoLinks G A B ∨
      ∃ X : Finset V,
        X.card < 2 ∧ Separates G A B X :=
  dichotomy_of_card_bound
    (Fintype.card V) V le_rfl G A B

/-- Two-connectivity excludes the one-vertex separator alternative. -/
theorem two_links_of_two_connected
    (G : SimpleGraph V)
    (hconnected : IsTwoConnected G)
    (A B : Finset V)
    (hAcard : A.card = 2)
    (hBcard : B.card = 2)
    (_hAB : Disjoint A B) :
    HasTwoLinks G A B := by
  classical
  rcases two_links_or_small_separator G A B with
      hlinks | ⟨X, hXcard, hsep⟩
  · exact hlinks
  · exfalso
    have hXA : X.card < A.card := by
      omega
    have hXB : X.card < B.card := by
      omega
    obtain ⟨a, haA, haX⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hXA
    obtain ⟨b, hbB, hbX⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hXB
    let aX : {v : V // v ∉ X} := ⟨a, haX⟩
    let bX : {v : V // v ∉ X} := ⟨b, hbX⟩
    obtain ⟨p⟩ :=
      (hconnected.2 X hXcard) aX bX
    let f :
        G.induce {v : V | v ∉ X} →g G :=
      (SimpleGraph.Embedding.induce
        (G := G) {v : V | v ∉ X}).toHom
    let P : SetWalk G A B := {
      start := a
      finish := b
      walk := p.map f
      start_mem := haA
      finish_mem := hbB
    }
    obtain ⟨x, hxP, hxX⟩ := hsep P
    change x ∈ (p.map f).support at hxP
    rw [SimpleGraph.Walk.support_map] at hxP
    obtain ⟨z, hz, hzx⟩ :=
      List.mem_map.mp hxP
    change z.1 = x at hzx
    apply z.2
    rw [hzx]
    exact hxX

end Induction

end MengerTwo

namespace ClassicalGraphTheory

/--
The two-link form of finite vertex Menger used in the paper.  It is
derived internally from the deletion definition of 2-connectivity.
-/
theorem two_disjoint_set_paths
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hconnected : IsTwoConnected G)
    (A B : Finset V)
    (hAcard : A.card = 2)
    (hBcard : B.card = 2)
    (hAB : Disjoint A B) :
    ∃ a₁ a₂ b₁ b₂ : V,
      a₁ ∈ A ∧ a₂ ∈ A ∧
      b₁ ∈ B ∧ b₂ ∈ B ∧
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      ∃ P₁ : SimplePath G a₁ b₁,
      ∃ P₂ : SimplePath G a₂ b₂,
        P₁.walk.support.Disjoint P₂.walk.support := by
  exact
    (MengerTwo.two_links_of_two_connected
      G hconnected A B hAcard hBcard hAB).simplePaths

end ClassicalGraphTheory

end DeanK5
