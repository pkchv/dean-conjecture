import DeanK5.ClassicalGraphTheory

/-!
# Existence of a theta

This file replaces the standard theta-existence dependency.  A branch
vertex supplies three distinct neighbors.  After deleting the branch
vertex, 2-connectivity leaves a connected graph.  A path between two of the
neighbors and a first-hit path from the third neighbor to that path form
three internally disjoint branches.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace SimplePath

/--
Given a simple path whose final vertex lies in `S`, take its initial segment
through the first vertex of `S`.  The returned segment meets `S` only at its
final vertex.
-/
theorem exists_first_hit_segment
    [DecidableEq V]
    {G : SimpleGraph V} {x y : V}
    (R : SimplePath G x y) (S : Finset V)
    (hy : y ∈ S) :
    ∃ z : V, z ∈ S ∧
      ∃ Q : SimplePath G x z,
        (∀ w ∈ Q.walk.support,
          w ∈ R.walk.support) ∧
        (∀ w ∈ Q.walk.support,
          w ∈ S → w = z) := by
  rcases R with ⟨r, hr⟩
  induction r with
  | nil =>
      rename_i u
      refine ⟨u, hy, ⟨.nil, by simp⟩, ?_, ?_⟩
      · simp
      · intro w hw _hwS
        simpa using hw
  | @cons x z y hxz r ih =>
      by_cases hx : x ∈ S
      · refine ⟨x, hx, ⟨.nil, by simp⟩, ?_, ?_⟩
        · simp
        · intro w hw _hwS
          simpa using hw
      · have hrTail : r.IsPath :=
          by simpa using hr.tail
        obtain ⟨q, hqS, Q, hQsub, hQhit⟩ :=
          ih hy hrTail
        have hxNotQ : x ∉ Q.walk.support := by
          intro hxQ
          have hxR : x ∈ r.support :=
            hQsub x hxQ
          have hnodup :
              (x :: r.support).Nodup := by
            simpa using hr.support_nodup
          exact (List.nodup_cons.mp hnodup).1 hxR
        let Q' : SimplePath G x q := {
          walk := Q.walk.cons hxz
          isPath := Q.isPath.cons hxNotQ
        }
        refine ⟨q, hqS, Q', ?_, ?_⟩
        · intro w hw
          simp only [Q', SimpleGraph.Walk.support_cons,
            List.mem_cons] at hw ⊢
          exact hw.elim Or.inl
            (fun hwQ => Or.inr (hQsub w hwQ))
        · intro w hw hwS
          simp only [Q', SimpleGraph.Walk.support_cons,
            List.mem_cons] at hw
          rcases hw with rfl | hwQ
          · exact False.elim (hx hwS)
          · exact hQhit w hwQ hwS

/-- The final vertex of a simple path does not occur before the end. -/
theorem end_not_mem_dropLast_support
    {G : SimpleGraph V} {x y : V}
    (P : SimplePath G x y) :
    y ∉ P.walk.support.dropLast := by
  intro hy
  have hnodup := P.isPath.support_nodup
  rw [← P.walk.dropLast_support_concat,
    List.nodup_append] at hnodup
  exact (hnodup.2.2 y hy y (by simp)) rfl

/--
A first-hit segment, with respect to the support of another path, is
internally disjoint from that path.
-/
theorem dropLast_disjoint_of_meets_only_at_end
    [DecidableEq V]
    {G : SimpleGraph V} {x a b y : V}
    (Q : SimplePath G x y)
    (P : SimplePath G a b)
    (hmeet :
      ∀ z ∈ Q.walk.support,
        z ∈ P.walk.support.toFinset → z = y) :
    Q.walk.support.dropLast.Disjoint
      P.walk.support := by
  apply List.disjoint_left.mpr
  intro z hzQ hzP
  have hzQSupport :
      z ∈ Q.walk.support :=
    List.mem_of_mem_dropLast hzQ
  have hzy : z = y :=
    hmeet z hzQSupport (by simpa using hzP)
  subst z
  exact Q.end_not_mem_dropLast_support hzQ

/--
Splitting a simple path at one of its vertices gives two branches that are
internally disjoint when both are oriented toward the split vertex.
-/
theorem split_dropLast_disjoint
    [DecidableEq V]
    {G : SimpleGraph V} {a b y : V}
    (P : SimplePath G a b)
    (hy : y ∈ P.walk.support) :
    (P.walk.takeUntil y hy).support.dropLast.Disjoint
      (P.walk.dropUntil y hy).reverse.support.dropLast := by
  have hsplit :
      (P.walk.takeUntil y hy).support.Disjoint
        (P.walk.dropUntil y hy).support.tail := by
    have hnodup := P.isPath.support_nodup
    rw [← P.walk.take_spec hy,
      SimpleGraph.Walk.support_append,
      List.nodup_append] at hnodup
    apply List.disjoint_left.mpr
    intro z hzLeft hzRight
    exact (hnodup.2.2 z hzLeft z hzRight) rfl
  apply List.disjoint_left.mpr
  intro z hzLeft hzRight
  apply (List.disjoint_left.mp hsplit
    (List.mem_of_mem_dropLast hzLeft))
  have hzRight' :
      z ∈
        ((P.walk.dropUntil y hy).support.reverse).dropLast := by
    simpa [SimpleGraph.Walk.support_reverse] using hzRight
  have :
      z ∈ (P.walk.dropUntil y hy).support.tail.reverse := by
    simpa using hzRight'
  simpa using this

end SimplePath

private theorem dropLast_map
    {α β : Type*} (f : α → β) (l : List α) :
    (l.map f).dropLast = l.dropLast.map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases l with
      | nil => rfl
      | cons b l =>
          change
            (f a :: (b :: l).map f).dropLast =
              ((a :: b :: l).dropLast).map f
          rw [List.dropLast_cons_of_ne_nil (by simp),
            List.dropLast_cons_of_ne_nil (by simp),
            List.map_cons]
          congr 1

/-- The carrier remaining after deleting one vertex. -/
def deletedVertexSet (v : V) : Set V :=
  {z | z ∉ ({v} : Finset V)}

/--
Map a path in `G-v` back to `G` and prefix its first vertex by the edge
from `v`.
-/
def thetaArm
    {G : SimpleGraph V} (v : V)
    {a y : deletedVertexSet v}
    (P : SimplePath (G.induce (deletedVertexSet v)) a y)
    (hva : G.Adj v a.1) :
    SimplePath G v y.1 := by
  let f :
      G.induce (deletedVertexSet v) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (deletedVertexSet v)).toHom
  let Q := P.mapInjectiveHom f
    (SimpleGraph.Embedding.induce
      (G := G) (deletedVertexSet v)).injective
  have hvQ : v ∉ Q.walk.support := by
    intro hv
    change v ∈ (P.walk.map f).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨z, -, hz⟩ := List.mem_map.mp hv
    change z.1 = v at hz
    apply z.2
    simpa using hz
  exact {
    walk := Q.walk.cons hva
    isPath := Q.isPath.cons hvQ
  }

@[simp] theorem thetaArm_internalSupport
    {G : SimpleGraph V} (v : V)
    {a y : deletedVertexSet v}
    (P : SimplePath (G.induce (deletedVertexSet v)) a y)
    (hva : G.Adj v a.1) :
    (thetaArm v P hva).internalSupport =
      P.walk.support.dropLast.map Subtype.val := by
  change
    ((P.walk.map
      (SimpleGraph.Embedding.induce
        (G := G) (deletedVertexSet v)).toHom).support).dropLast =
      P.walk.support.dropLast.map Subtype.val
  rw [SimpleGraph.Walk.support_map,
    dropLast_map]
  apply List.map_congr_left
  intro z _hz
  rfl

theorem thetaArm_walk_ne
    {G : SimpleGraph V} (v : V)
    {a b y : deletedVertexSet v}
    (P : SimplePath (G.induce (deletedVertexSet v)) a y)
    (Q : SimplePath (G.induce (deletedVertexSet v)) b y)
    (hva : G.Adj v a.1) (hvb : G.Adj v b.1)
    (hab : a ≠ b) :
    (thetaArm v P hva).walk ≠
      (thetaArm v Q hvb).walk := by
  intro hwalk
  have hsnd :=
    congrArg (fun w => w.snd) hwalk
  apply hab
  apply Subtype.ext
  simpa [thetaArm, SimplePath.mapInjectiveHom] using hsnd

theorem thetaArm_internal_disjoint
    {G : SimpleGraph V} (v : V)
    {a b y : deletedVertexSet v}
    (P : SimplePath (G.induce (deletedVertexSet v)) a y)
    (Q : SimplePath (G.induce (deletedVertexSet v)) b y)
    (hva : G.Adj v a.1) (hvb : G.Adj v b.1)
    (hdisj :
      P.walk.support.dropLast.Disjoint
        Q.walk.support.dropLast) :
    (thetaArm v P hva).internalSupport.Disjoint
      (thetaArm v Q hvb).internalSupport := by
  rw [thetaArm_internalSupport,
    thetaArm_internalSupport]
  apply List.disjoint_left.mpr
  intro z hzP hzQ
  obtain ⟨p, hp, hpz⟩ :=
    List.mem_map.mp hzP
  obtain ⟨q, hq, hqz⟩ :=
    List.mem_map.mp hzQ
  have hpq : p = q := by
    apply Subtype.ext
    exact hpz.trans hqz.symm
  subst q
  exact (List.disjoint_left.mp hdisj hp) hq

namespace ClassicalGraphTheory

/--
A finite 2-connected graph with a vertex of degree at least three contains
a theta.
-/
theorem exists_theta_of_two_connected
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hconn : IsTwoConnected G)
    (hbranch : ∃ v : V, 3 ≤ finiteDegree G v) :
    Nonempty (Theta G) := by
  classical
  obtain ⟨v, hvdegree⟩ := hbranch
  have hneighborCard :
      2 < (G.neighborSet v).toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card']
    change 2 < finiteDegree G v
    omega
  obtain ⟨a, ha, b, hb, c, hc,
      hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp hneighborCard
  have hva : G.Adj v a := by
    simpa [SimpleGraph.mem_neighborSet] using ha
  have hvb : G.Adj v b := by
    simpa [SimpleGraph.mem_neighborSet] using hb
  have hvc : G.Adj v c := by
    simpa [SimpleGraph.mem_neighborSet] using hc
  let aD : deletedVertexSet v :=
    ⟨a, by
      simp only [deletedVertexSet,
        Finset.mem_singleton]
      exact hva.ne.symm⟩
  let bD : deletedVertexSet v :=
    ⟨b, by
      simp only [deletedVertexSet,
        Finset.mem_singleton]
      exact hvb.ne.symm⟩
  let cD : deletedVertexSet v :=
    ⟨c, by
      simp only [deletedVertexSet,
        Finset.mem_singleton]
      exact hvc.ne.symm⟩
  have habD : aD ≠ bD := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hacD : aD ≠ cD := by
    intro h
    exact hac (congrArg Subtype.val h)
  have hbcD : bD ≠ cD := by
    intro h
    exact hbc (congrArg Subtype.val h)
  let H := G.induce (deletedVertexSet v)
  have hHconnected : H.Connected := by
    simpa [H, deletedVertexSet] using
      hconn.2 ({v} : Finset V) (by simp)
  obtain ⟨p, hp⟩ :=
    hHconnected.exists_isPath aD bD
  let P : SimplePath H aD bD := ⟨p, hp⟩
  obtain ⟨r, hr⟩ :=
    hHconnected.exists_isPath cD aD
  let R : SimplePath H cD aD := ⟨r, hr⟩
  let S : Finset (deletedVertexSet v) :=
    P.walk.support.toFinset
  have haS : aD ∈ S := by
    simp [S, P]
  obtain ⟨yD, hyS, Q, hQsub, hQhit⟩ :=
    R.exists_first_hit_segment S haS
  have hyP : yD ∈ P.walk.support := by
    simpa [S] using hyS
  let A : SimplePath H aD yD := {
    walk := P.walk.takeUntil yD hyP
    isPath := P.isPath.takeUntil hyP
  }
  let B₀ : SimplePath H yD bD := {
    walk := P.walk.dropUntil yD hyP
    isPath := P.isPath.dropUntil hyP
  }
  let B : SimplePath H bD yD :=
    B₀.reverse
  have hAB :
      A.walk.support.dropLast.Disjoint
        B.walk.support.dropLast := by
    simpa [A, B, B₀, SimplePath.reverse] using
      P.split_dropLast_disjoint hyP
  have hQP :
      Q.walk.support.dropLast.Disjoint
        P.walk.support :=
    Q.dropLast_disjoint_of_meets_only_at_end
      P hQhit
  have hAQ :
      A.walk.support.dropLast.Disjoint
        Q.walk.support.dropLast := by
    apply List.disjoint_left.mpr
    intro z hzA hzQ
    apply (List.disjoint_left.mp hQP hzQ)
    apply P.walk.support_takeUntil_subset_support hyP
    exact List.mem_of_mem_dropLast hzA
  have hBQ :
      B.walk.support.dropLast.Disjoint
        Q.walk.support.dropLast := by
    apply List.disjoint_left.mpr
    intro z hzB hzQ
    apply (List.disjoint_left.mp hQP hzQ)
    apply P.walk.support_dropUntil_subset_support hyP
    have hzBSupport :
        z ∈ B.walk.support :=
      List.mem_of_mem_dropLast hzB
    simpa [B, B₀, SimplePath.reverse,
      SimpleGraph.Walk.support_reverse] using hzBSupport
  let P₀ : SimplePath G v yD.1 :=
    thetaArm v A hva
  let P₁ : SimplePath G v yD.1 :=
    thetaArm v B hvb
  let P₂ : SimplePath G v yD.1 :=
    thetaArm v Q hvc
  refine ⟨{
    x := v
    y := yD.1
    roots_ne := by
      intro hvy
      apply yD.2
      simp [deletedVertexSet, hvy]
    path := ![P₀, P₁, P₂]
    paths_ne := ?_
    internal_disjoint := ?_
  }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact thetaArm_walk_ne
        v A B hva hvb habD
    · exact thetaArm_walk_ne
        v A Q hva hvc hacD
    · exact (thetaArm_walk_ne
        v A B hva hvb habD).symm
    · exact False.elim (hij rfl)
    · exact thetaArm_walk_ne
        v B Q hvb hvc hbcD
    · exact (thetaArm_walk_ne
        v A Q hva hvc hacD).symm
    · exact (thetaArm_walk_ne
        v B Q hvb hvc hbcD).symm
    · exact False.elim (hij rfl)
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact thetaArm_internal_disjoint
        v A B hva hvb hAB
    · exact thetaArm_internal_disjoint
        v A Q hva hvc hAQ
    · exact (thetaArm_internal_disjoint
        v A B hva hvb hAB).symm
    · exact False.elim (hij rfl)
    · exact thetaArm_internal_disjoint
        v B Q hvb hvc hBQ
    · exact (thetaArm_internal_disjoint
        v A Q hva hvc hAQ).symm
    · exact (thetaArm_internal_disjoint
        v B Q hvb hvc hBQ).symm
    · exact False.elim (hij rfl)

end ClassicalGraphTheory

end DeanK5
