import DeanK5.Graph.BlockCutIncidence
import DeanK5.Graph.BlockEar
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The block--cut incidence tree

This file proves the acyclicity part of the finite block--cut tree
construction.  The proof uses an auxiliary graph made from all blocks other
than one fixed block `B`.  No edge of that auxiliary graph can have two ends
in `B`, while an incidence walk avoiding the node `B` realizes an ambient
walk in the auxiliary graph.  An incidence cycle would therefore give an
external ear of `B`, contradicting block maximality.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
The ambient edges covered by some block other than `B`.

The explicit ambient-adjacency conjunct makes the identity map to `G` a
graph homomorphism.  The block witness is used both to realize incidence
walks and to exclude edges with two ends in `B`.
-/
def otherBlockGraph
    [DecidableEq V]
    (G : SimpleGraph V) (B : GraphBlock G) :
    SimpleGraph V where
  Adj u v :=
    G.Adj u v ∧
      ∃ C : GraphBlock G,
        C ≠ B ∧ u ∈ C.carrier ∧ v ∈ C.carrier
  symm := by
    constructor
    rintro u v ⟨huv, C, hCB, huC, hvC⟩
    exact ⟨huv.symm, C, hCB, hvC, huC⟩
  loopless := by
    constructor
    intro v h
    exact G.loopless.irrefl v h.1

namespace OtherBlockGraph

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {B : GraphBlock G}

/-- The auxiliary graph includes into the original graph. -/
def inclusion :
    otherBlockGraph G B →g G where
  toFun := id
  map_rel' := fun h => h.1

omit [Fintype V] in
/-- Every path inside a block distinct from `B` is available in the
auxiliary graph. -/
theorem reachable_of_mem_block
    (C : GraphBlock G)
    (hCB : C ≠ B)
    {u v : V}
    (huC : u ∈ C.carrier)
    (hvC : v ∈ C.carrier) :
    (otherBlockGraph G B).Reachable u v := by
  let f :
      G.induce (↑C.carrier : Set V) →g
        otherBlockGraph G B := {
    toFun := Subtype.val
    map_rel' := fun {x y} hxy =>
      ⟨hxy, C, hCB, x.2, y.2⟩
  }
  exact
    (C.connected.preconnected
      ⟨u, huC⟩ ⟨v, hvC⟩).map f

omit [Fintype V] in
/-- No auxiliary edge has two ends in the omitted block. -/
theorem not_adj_of_mem_carrier
    {u v : V}
    (huB : u ∈ B.carrier)
    (hvB : v ∈ B.carrier) :
    ¬(otherBlockGraph G B).Adj u v := by
  rintro ⟨huv, C, hCB, huC, hvC⟩
  have hpair :
      ({u, v} : Finset V) ⊆
        B.carrier ∩ C.carrier := by
    intro w hw
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨huB, huC⟩
    · exact Finset.mem_inter.mpr ⟨hvB, hvC⟩
  have hpairCard :
      ({u, v} : Finset V).card = 2 := by
    simp [huv.ne]
  have hinterTwo :
      2 ≤ (B.carrier ∩ C.carrier).card := by
    rw [← hpairCard]
    exact Finset.card_le_card hpair
  exact
    (not_le_of_gt hinterTwo)
      (B.inter_card_le_one C hCB.symm)

/--
Two distinct vertices of the omitted block lie in different components of
the auxiliary graph.

Otherwise choose a reachable block vertex at minimum positive distance from
the first one.  A shortest path to it meets `B` only at its two ends.  After
mapping that path to `G`, external-ear maximality forces the entire path
back into `B`, contradicting `not_adj_of_mem_carrier` at its first edge.
-/
theorem not_reachable_of_ne_of_mem_carrier
    {u v : V}
    (huB : u ∈ B.carrier)
    (hvB : v ∈ B.carrier)
    (huv : u ≠ v) :
    ¬(otherBlockGraph G B).Reachable u v := by
  classical
  intro huvReachable
  let targets : Finset V :=
    (B.carrier.erase u).filter
      ((otherBlockGraph G B).Reachable u)
  have hvTargets : v ∈ targets := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨huv.symm, hvB⟩,
        huvReachable⟩
  have htargetsNonempty : targets.Nonempty :=
    ⟨v, hvTargets⟩
  obtain ⟨b, hbTargets, hbMinimal⟩ :=
    Finset.exists_min_image targets
      (fun w => (otherBlockGraph G B).dist u w)
      htargetsNonempty
  have hbErase :
      b ∈ B.carrier.erase u :=
    (Finset.mem_filter.mp hbTargets).1
  have hbB : b ∈ B.carrier :=
    Finset.mem_of_mem_erase hbErase
  have hub : u ≠ b :=
    (Finset.mem_erase.mp hbErase).1.symm
  have hubReachable :
      (otherBlockGraph G B).Reachable u b :=
    (Finset.mem_filter.mp hbTargets).2
  obtain ⟨p, hpPath, hpLength⟩ :=
    hubReachable.exists_path_of_dist
  have hpMeet :
      ∀ ⦃w : V⦄, w ∈ p.support →
        w ∈ B.carrier →
          w = u ∨ w = b := by
    intro w hwSupport hwB
    by_cases hwu : w = u
    · exact Or.inl hwu
    right
    by_contra hwb
    have hprefixReach :
        (otherBlockGraph G B).Reachable u w :=
      ⟨p.takeUntil w hwSupport⟩
    have hwTargets : w ∈ targets := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hwu, hwB⟩,
          hprefixReach⟩
    have hminimal :
        (otherBlockGraph G B).dist u b ≤
          (otherBlockGraph G B).dist u w :=
      hbMinimal w hwTargets
    have hprefixLength :
        (p.takeUntil w hwSupport).length =
          (otherBlockGraph G B).dist u w :=
      length_eq_dist_of_subwalk hpLength
        (p.isSubwalk_takeUntil hwSupport)
    have hstrict :
        (p.takeUntil w hwSupport).length < p.length :=
      p.length_takeUntil_lt_length hwSupport hwb
    omega
  let P : SimplePath G u b := {
    walk := p.map inclusion
    isPath := hpPath.map Function.injective_id
  }
  have hPMeet :
      ∀ ⦃w : V⦄, w ∈ P.walk.support →
        w ∈ B.carrier →
          w = u ∨ w = b := by
    intro w hwP hwB
    apply hpMeet ?_ hwB
    change w ∈ (p.map inclusion).support at hwP
    rw [SimpleGraph.Walk.support_map] at hwP
    obtain ⟨a, ha, haw⟩ :=
      List.mem_map.mp hwP
    change a = w at haw
    simpa [haw] using ha
  have hPSubset :
      ∀ ⦃w : V⦄, w ∈ P.walk.support →
        w ∈ B.carrier :=
    B.path_subset_of_meets_only_at_ends
      hub P huB hbB hPMeet
  have hpNotNil : ¬p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hub
  have hsndSupport :
      p.snd ∈ p.support :=
    List.mem_of_mem_tail
      (p.snd_mem_tail_support hpNotNil)
  have hsndP :
      p.snd ∈ P.walk.support := by
    change p.snd ∈ (p.map inclusion).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr
      ⟨p.snd, hsndSupport, rfl⟩
  have hsndB :
      p.snd ∈ B.carrier :=
    hPSubset hsndP
  exact
    not_adj_of_mem_carrier
      huB hsndB (p.adj_snd hpNotNil)

end OtherBlockGraph

namespace BlockCutIncidence

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

omit [Fintype V] in
/-- A neighbor of a block node in the incidence graph is a cut node. -/
private theorem exists_cut_eq_of_adj_block
    (B : GraphBlock G)
    (n : BlockCutNode G)
    (h : (blockCutIncidence G).Adj (.inl B) n) :
    ∃ c : {v : V // IsCutVertex G v},
      n = .inr c := by
  cases n with
  | inl C =>
      exact False.elim
        (not_blockCutIncidence_adj_block_block G B C h)
  | inr c =>
      exact ⟨c, rfl⟩

omit [Fintype V] in
/-- Every incidence cycle contains a block node. -/
private theorem exists_block_mem_support
    {n : BlockCutNode G}
    (w : (blockCutIncidence G).Walk n n)
    (hw : w.IsCycle) :
    ∃ B : GraphBlock G,
      (Sum.inl B : BlockCutNode G) ∈ w.support := by
  cases n with
  | inl B =>
      exact ⟨B, w.start_mem_support⟩
  | inr c =>
      have hn : ¬w.Nil := hw.not_nil
      have hfirst :
          (blockCutIncidence G).Adj
            (.inr c) w.snd :=
        w.adj_snd hn
      cases hs : w.snd with
      | inl B =>
          refine ⟨B, ?_⟩
          have hsndMem :
              w.snd ∈ w.support :=
            List.mem_of_mem_tail
              (w.snd_mem_tail_support hn)
          simpa [hs] using hsndMem
      | inr d =>
          rw [hs] at hfirst
          exact False.elim
            (not_blockCutIncidence_adj_cut_cut
              G c d hfirst)

omit [Fintype V] in
/--
An incidence walk between cut nodes that avoids one block node realizes an
ambient walk using only blocks other than the avoided block.
-/
theorem reachable_in_otherBlockGraph_of_walk
    (B : GraphBlock G)
    (c d : {v : V // IsCutVertex G v})
    (p :
      (blockCutIncidence G).Walk
        (.inr c) (.inr d))
    (havoid :
      (Sum.inl B : BlockCutNode G) ∉ p.support) :
    (otherBlockGraph G B).Reachable c.1 d.1 := by
  let Reached : BlockCutNode G → Prop
    | .inr e =>
        (otherBlockGraph G B).Reachable c.1 e.1
    | .inl C =>
        C ≠ B ∧
          ∃ u ∈ C.carrier,
            (otherBlockGraph G B).Reachable c.1 u
  have hstep :
      ∀ {a b : BlockCutNode G},
        (blockCutIncidence G).Adj a b →
          Reached a →
            b ≠ .inl B →
              Reached b := by
    intro a b hab ha hbB
    cases a with
    | inl C =>
        cases b with
        | inl D =>
            exact False.elim
              (not_blockCutIncidence_adj_block_block
                G C D hab)
        | inr e =>
            obtain ⟨hCB, u, huC, hcu⟩ := ha
            exact
              hcu.trans
                (OtherBlockGraph.reachable_of_mem_block
                  C hCB huC hab)
    | inr e =>
        cases b with
        | inr f =>
            exact False.elim
              (not_blockCutIncidence_adj_cut_cut
                G e f hab)
        | inl C =>
            have hCB : C ≠ B := by
              intro hEq
              apply hbB
              simp [hEq]
            exact
              ⟨hCB, e.1, hab, ha⟩
  have hpropagate :
      ∀ {a b : BlockCutNode G}
        (q : (blockCutIncidence G).Walk a b),
        Reached a →
          (Sum.inl B : BlockCutNode G) ∉ q.support →
            Reached b := by
    intro a b q
    induction q with
    | nil =>
        intro ha _
        exact ha
    | @cons a m b ham q ih =>
        intro ha hqAvoid
        have hmAvoid :
            m ≠ (Sum.inl B : BlockCutNode G) := by
          intro hm
          apply hqAvoid
          subst m
          simp
        have hmReached :
            Reached m :=
          hstep ham ha hmAvoid
        have htailAvoid :
            (Sum.inl B : BlockCutNode G) ∉
              q.support := by
          intro hmem
          apply hqAvoid
          simp [hmem]
        exact ih hmReached htailAvoid
  exact hpropagate p
    (SimpleGraph.Reachable.refl c.1) havoid

/--
The block--cut incidence graph of a finite graph is acyclic.

Connectedness of the ambient graph is not needed for this half of the
block--cut tree theorem: maximality and the intersection bound for graph
blocks already exclude incidence cycles.
-/
theorem isAcyclic :
    (blockCutIncidence G).IsAcyclic := by
  intro n w hw
  classical
  obtain ⟨B, hBSupport⟩ :=
    exists_block_mem_support w hw
  let r :=
    w.rotate
      (Sum.inl B : BlockCutNode G)
      hBSupport
  have hrCycle : r.IsCycle :=
    hw.rotate hBSupport
  have hrNotNil : ¬r.Nil :=
    hrCycle.not_nil
  have hrTailNotNil : ¬r.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    have htailLength :
        r.tail.length + 1 = r.length :=
      r.length_tail_add_one hrNotNil
    have hthree : 3 ≤ r.length :=
      hrCycle.three_le_length
    omega
  have hfirst :
      (blockCutIncidence G).Adj
        (.inl B) r.snd :=
    r.adj_snd hrNotNil
  obtain ⟨c, hc⟩ :=
    exists_cut_eq_of_adj_block B r.snd hfirst
  have hlast :
      (blockCutIncidence G).Adj
        (.inl B) r.tail.penultimate :=
    (r.tail.adj_penultimate hrTailNotNil).symm
  obtain ⟨d, hd⟩ :=
    exists_cut_eq_of_adj_block
      B r.tail.penultimate hlast
  let q :
      (blockCutIncidence G).Walk
        (.inr c) (.inr d) :=
    r.tail.dropLast.copy hc hd
  have hqAvoid :
      (Sum.inl B : BlockCutNode G) ∉ q.support := by
    have htailNodup :
        r.tail.support.Nodup :=
      hrCycle.isPath_tail.support_nodup
    have hdecomp :
        r.tail.dropLast.support ++
            [(Sum.inl B : BlockCutNode G)] =
          r.tail.support :=
      r.tail.support_dropLast_concat hrTailNotNil
    rw [← hdecomp, List.nodup_append] at htailNodup
    have hnot :
        (Sum.inl B : BlockCutNode G) ∉
          r.tail.dropLast.support := by
      intro hmem
      exact
        htailNodup.2.2
          (Sum.inl B) hmem
          (Sum.inl B) (by simp) rfl
    simpa [q] using hnot
  have hreach :
      (otherBlockGraph G B).Reachable c.1 d.1 :=
    reachable_in_otherBlockGraph_of_walk
      B c d q hqAvoid
  have hcB : c.1 ∈ B.carrier := by
    rw [hc] at hfirst
    exact hfirst
  have hdB : d.1 ∈ B.carrier := by
    rw [hd] at hlast
    exact hlast
  have hpenultimate :
      r.penultimate = r.tail.penultimate := by
    refine r.notNilRec
      (motive := fun p _ =>
        ¬p.tail.Nil →
          p.penultimate = p.tail.penultimate)
      ?_ hrNotNil hrTailNotNil
    intro u v t h p hpTail
    cases p with
    | nil =>
        simp at hpTail
    | cons h' p =>
        rfl
  have hcd : c.1 ≠ d.1 := by
    intro hEq
    apply hrCycle.snd_ne_penultimate
    have hcdSubtype : c = d :=
      Subtype.ext hEq
    have hsndTail :
        r.snd = r.tail.penultimate :=
      hc.trans
        ((congrArg Sum.inr hcdSubtype).trans hd.symm)
    exact hsndTail.trans hpenultimate.symm
  exact
    (OtherBlockGraph.not_reachable_of_ne_of_mem_carrier
      hcB hdB hcd) hreach

/--
For a finite connected graph of order at least two, the block--cut
incidence graph is a tree.
-/
theorem isTree
    (hconnected : G.Connected)
    (horder : 2 ≤ Fintype.card V) :
    (blockCutIncidence G).IsTree where
  connected :=
    BlockCutIncidence.connected hconnected horder
  isAcyclic :=
    BlockCutIncidence.isAcyclic

end BlockCutIncidence

end DeanK5
