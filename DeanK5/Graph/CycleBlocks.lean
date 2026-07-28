import DeanK5.Graph.Blocks

/-!
# Simple cycles lie in graph blocks

This file connects the walk-based `SimpleCycle` API to the carrier-based
block theory.  The vertices of a simple cycle form a nonseparable carrier:
the cycle is connected, and deleting any one of its vertices leaves the
remaining vertices connected along the complementary path.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace SimpleCycle

variable [DecidableEq V] {G : SimpleGraph V}

/--
The finite vertex carrier of a simple cycle.

The tail of the support is used because a closed walk records its base
vertex at both ends.  For a simple cycle that tail is nodup and contains
each cycle vertex exactly once.
-/
def carrier (C : SimpleCycle G) : Finset V :=
  C.walk.support.tail.toFinset

/-- Membership in a cycle carrier is membership in its walk support. -/
@[simp]
theorem mem_carrier {C : SimpleCycle G} {v : V} :
    v ∈ C.carrier ↔ v ∈ C.walk.support := by
  rw [carrier, List.mem_toFinset]
  constructor
  · exact List.mem_of_mem_tail
  · intro hv
    rw [C.walk.mem_support_iff] at hv
    exact hv.elim
      (fun h => h ▸ C.walk.end_mem_tail_support C.isCycle.not_nil)
      id

/-- A cycle carrier has as many vertices as the cycle has edges. -/
@[simp]
theorem card_carrier (C : SimpleCycle G) :
    C.carrier.card = C.length := by
  rw [carrier, List.toFinset_card_of_nodup C.isCycle.support_nodup]
  simp [SimpleCycle.length]

/--
After rotating a cycle to a chosen vertex, removing that vertex leaves the
support of the path obtained by dropping the first and last cycle edges.
-/
private theorem mem_tail_dropLast_rotate_iff
    (C : SimpleCycle G) {v w : V}
    (hv : v ∈ C.walk.support) :
    w ∈ ((C.walk.rotate v hv).tail.dropLast).support ↔
      w ∈ C.walk.support ∧ w ≠ v := by
  let r := C.walk.rotate v hv
  have hrCycle : r.IsCycle := C.isCycle.rotate hv
  have hrNotNil : ¬ r.Nil := hrCycle.not_nil
  have hrTailNotNil : ¬ r.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    have hlen : r.length = C.walk.length := by
      simp [r]
    have htail :
        r.tail.length + 1 = r.length :=
      r.length_tail_add_one hrNotNil
    have hthree : 3 ≤ C.walk.length :=
      C.isCycle.three_le_length
    omega
  have hvTail : v ∈ r.support.tail :=
    r.end_mem_tail_support hrNotNil
  have htailNe : r.support.tail ≠ [] :=
    List.ne_nil_of_mem hvTail
  have hlast : r.support.tail.getLast htailNe = v := by
    calc
      r.support.tail.getLast htailNe =
          r.tail.support.getLast r.tail.support_ne_nil :=
        List.getLast_congr htailNe r.tail.support_ne_nil
          (r.support_tail_of_not_nil hrNotNil).symm
      _ = v := r.tail.getLast_support
  have hvNotDrop : v ∉ r.support.tail.dropLast := by
    intro hvDrop
    have hnodup : r.support.tail.Nodup :=
      hrCycle.support_nodup
    have hdecomp :
        r.support.tail.dropLast ++ [v] = r.support.tail := by
      simpa [hlast] using
        (List.dropLast_concat_getLast htailNe)
    rw [← hdecomp, List.nodup_append] at hnodup
    exact (hnodup.2.2 v hvDrop v (by simp)) rfl
  have hqSupport :
      r.tail.dropLast.support =
        r.support.tail.dropLast := by
    rw [SimpleGraph.Walk.support_dropLast hrTailNotNil,
      SimpleGraph.Walk.support_tail_of_not_nil r hrNotNil]
  rw [hqSupport]
  have hrotate (x : V) :
      x ∈ r.support ↔ x ∈ C.walk.support := by
    simp [r, C.walk.mem_support_rotate_iff v hv]
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · apply (hrotate w).1
      exact List.mem_of_mem_tail
        (List.mem_of_mem_dropLast hw)
    · exact fun hwv => hvNotDrop (hwv ▸ hw)
  · rintro ⟨hwSupport, hwv⟩
    have hwRotate : w ∈ r.support := by
      exact (hrotate w).2 hwSupport
    have hwTail : w ∈ r.support.tail := by
      rw [SimpleGraph.Walk.mem_support_iff r] at hwRotate
      exact hwRotate.resolve_left hwv
    apply List.mem_dropLast_of_mem_of_ne_getLast hwTail
    simpa [hlast] using hwv

/-- The vertex carrier of every simple cycle is nonseparable. -/
theorem carrier_nonseparable (C : SimpleCycle G) :
    IsNonseparableCarrier G C.carrier := by
  refine {
    card_ge_two := by
      rw [C.card_carrier]
      exact (C.three_le_length).trans' (by omega)
    connected := ?_
    delete_connected := ?_
  }
  · have hset :
        (↑C.carrier : Set V) =
          {v : V | v ∈ C.walk.support} := by
      ext v
      simp
    rw [hset]
    exact C.walk.connected_induce_support
  · intro v hv
    have hvSupport : v ∈ C.walk.support :=
      C.mem_carrier.mp hv
    let q := (C.walk.rotate v hvSupport).tail.dropLast
    have hset :
        (↑(C.carrier.erase v) : Set V) =
          {w : V | w ∈ q.support} := by
      ext w
      rw [Set.mem_setOf_eq]
      simp only [Finset.mem_coe, Finset.mem_erase]
      constructor
      · rintro ⟨hwv, hwCarrier⟩
        exact (mem_tail_dropLast_rotate_iff C hvSupport).2
          ⟨C.mem_carrier.mp hwCarrier, hwv⟩
      · intro hwq
        have hw :=
          (mem_tail_dropLast_rotate_iff C hvSupport).1 hwq
        exact ⟨hw.2, C.mem_carrier.mpr hw.1⟩
    rw [hset]
    exact q.connected_induce_support

/-- Every simple cycle has at least three vertices in its carrier. -/
theorem three_le_card_carrier (C : SimpleCycle G) :
    3 ≤ C.carrier.card := by
  rw [C.card_carrier]
  exact C.three_le_length

end SimpleCycle

namespace GraphBlock

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/--
Every simple cycle in a finite graph is contained in a graph block.  The
containing block consequently has at least three vertices.
-/
theorem exists_containing_cycle (C : SimpleCycle G) :
    ∃ B : GraphBlock G,
      C.carrier ⊆ B.carrier ∧ 3 ≤ B.carrier.card := by
  obtain ⟨B, hCB⟩ :=
    GraphBlock.exists_extension C.carrier_nonseparable
  refine ⟨B, hCB, ?_⟩
  exact C.three_le_card_carrier.trans
    (Finset.card_le_card hCB)

/--
Let `u` and `v` be distinct neighbors of `c`.  If a simple `u`-`v` path
avoids `c`, then `c`, `u`, and `v` lie together in a graph block of order
at least three.

The two incident edges at `c` close the avoiding path to a certified simple
cycle, so this is a convenient interface for later attachment arguments.
-/
theorem exists_containing_center_and_path_ends
    {c u v : V}
    (huv : u ≠ v)
    (hcu : G.Adj c u)
    (hcv : G.Adj c v)
    (P : SimplePath G u v)
    (hcAvoid : c ∉ P.walk.support) :
    ∃ B : GraphBlock G,
      c ∈ B.carrier ∧
      u ∈ B.carrier ∧
      v ∈ B.carrier ∧
      3 ≤ B.carrier.card := by
  let closing : G.Walk u c :=
    P.walk.concat hcv.symm
  have hclosingPath : closing.IsPath := by
    exact P.isPath.concat hcAvoid hcv.symm
  have hclosingEdge :
      s(c, u) ∉ closing.edges := by
    intro he
    have he' :
        s(c, u) ∈ P.walk.edges ∨
          s(c, u) = s(v, c) := by
      simpa [closing] using he
    rcases he' with heP | heLast
    · exact hcAvoid
        (P.walk.fst_mem_support_of_mem_edges heP)
    · rw [Sym2.eq_iff] at heLast
      rcases heLast with hcvEq | huvEq
      · exact hcv.ne hcvEq.1
      · exact huv huvEq.2
  let C : SimpleCycle G := {
    base := c
    walk := closing.cons hcu
    isCycle :=
      (SimpleGraph.Walk.cons_isCycle_iff closing hcu).2
        ⟨hclosingPath, hclosingEdge⟩
  }
  have hcC : c ∈ C.carrier :=
    C.mem_carrier.mpr C.walk.start_mem_support
  have huC : u ∈ C.carrier := by
    apply C.mem_carrier.mpr
    simp [C, closing]
  have hvC : v ∈ C.carrier := by
    apply C.mem_carrier.mpr
    simp [C, closing]
  obtain ⟨B, hCB, hcard⟩ :=
    GraphBlock.exists_containing_cycle C
  exact
    ⟨B, hCB hcC, hCB huC, hCB hvC, hcard⟩

end GraphBlock

end DeanK5
