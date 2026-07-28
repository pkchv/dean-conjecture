import DeanK5.Graph.BlockBoundary
import DeanK5.Graph.FeasibleBlocks
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Anchoring a feasible block toward a marked vertex

The source cases (B1)--(B3) all choose the side of a feasible block facing
the second root.  This file packages their common content without referring
to a block-cut-tree representation.

Choose a carrier vertex of minimum distance from the marked target.  A
shortest path to it meets the block only at that endpoint.  If the endpoint
is not the target itself, the last edge of the path enters the block from
outside, so the endpoint is a cut vertex.  Since a feasible block has at
most two cut-or-marked vertices, one further vertex covers every remaining
exception.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
The uniform information supplied by the source choices (B1)--(B3).

`b` is the block endpoint facing `target`, `zPrime` covers the possible
second cut-or-marked vertex, and `pathToTarget` is the fixed connector that
does not re-enter the block.  The two selected vertices are allowed to
coincide.
-/
structure FeasibleBlockAnchor
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (marked : Finset V)
    (B : GraphBlock G) (target : V) where
  /-- The carrier vertex facing the marked target. -/
  b : V
  /-- The possible second cut-or-marked block vertex. -/
  zPrime : V
  /-- A certified ordinary vertex of the feasible block. -/
  ordinary : V
  /-- The anchor belongs to the block. -/
  b_mem : b ∈ B.carrier
  /-- The possible second exception also belongs to the block. -/
  zPrime_mem : zPrime ∈ B.carrier
  /-- The anchor is the target itself or a global cut vertex. -/
  b_eq_target_or_cut : b = target ∨ IsCutVertex G b
  /-- The anchor is cut or marked. -/
  b_special : b ∈ cutVertices G ∪ marked
  /-- The second selected vertex is cut or marked. -/
  zPrime_special : zPrime ∈ cutVertices G ∪ marked
  /-- The two selected vertices cover every special block vertex. -/
  special_subset :
    B.carrier ∩ (cutVertices G ∪ marked) ⊆ {b, zPrime}
  /-- The certified ordinary vertex belongs to the block. -/
  ordinary_mem : ordinary ∈ B.carrier
  /-- The certified ordinary vertex is neither cut nor marked. -/
  ordinary_not_special : ordinary ∉ cutVertices G ∪ marked
  /-- A fixed path from the anchor to the target. -/
  pathToTarget : SimplePath G b target
  /-- The fixed path meets the block only at its anchor. -/
  path_meets_carrier_only_at_b :
    ∀ ⦃v : V⦄, v ∈ pathToTarget.walk.support →
      v ∈ B.carrier → v = b

namespace GraphBlock

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/--
Every block in a connected finite graph has an anchor facing any prescribed
target.  A shortest target-to-block path supplies a connector whose only
block vertex is its endpoint.
-/
theorem exists_anchor_path_to
    (hconnected : G.Connected)
    (B : GraphBlock G) (target : V) :
    ∃ (b : V) (R : SimplePath G b target),
      b ∈ B.carrier ∧
        (b = target ∨ IsCutVertex G b) ∧
          ∀ ⦃v : V⦄, v ∈ R.walk.support →
            v ∈ B.carrier → v = b := by
  classical
  have hcarrierNonempty : B.carrier.Nonempty := by
    exact Finset.card_pos.mp (by
      have := B.card_ge_two
      omega)
  obtain ⟨b, hbCarrier, hbMinimal⟩ :=
    Finset.exists_min_image B.carrier
      (fun v => G.dist target v) hcarrierNonempty
  obtain ⟨p, hpPath, hpLength⟩ :=
    hconnected.exists_path_of_dist target b
  have hmeet :
      ∀ ⦃v : V⦄, v ∈ p.support →
        v ∈ B.carrier → v = b := by
    intro v hvSupport hvCarrier
    by_contra hvb
    have htakeLength :
        (p.takeUntil v hvSupport).length =
          G.dist target v :=
      length_eq_dist_of_subwalk hpLength
        (p.isSubwalk_takeUntil hvSupport)
    have hstrict :
        (p.takeUntil v hvSupport).length < p.length :=
      p.length_takeUntil_lt_length hvSupport hvb
    have hminimal :
        G.dist target b ≤ G.dist target v :=
      hbMinimal v hvCarrier
    omega
  have hbTargetOrCut :
      b = target ∨ IsCutVertex G b := by
    by_cases hbTarget : b = target
    · exact Or.inl hbTarget
    · right
      obtain ⟨a, hba, tail, hreverse⟩ :=
        p.reverse.exists_eq_cons_of_ne hbTarget
      have haReverseSupport : a ∈ p.reverse.support := by
        rw [hreverse]
        simp
      have haSupport : a ∈ p.support := by
        simpa [SimpleGraph.Walk.support_reverse] using
          haReverseSupport
      have haOutside : a ∉ B.carrier := by
        intro haCarrier
        have hab : a = b :=
          hmeet haSupport haCarrier
        exact hba.ne hab.symm
      exact B.isCutVertex_of_adj_outside
        hconnected hbCarrier hba haOutside
  let R : SimplePath G b target := {
    walk := p.reverse
    isPath := hpPath.reverse
  }
  refine ⟨b, R, hbCarrier, hbTargetOrCut, ?_⟩
  intro v hvSupport hvCarrier
  apply hmeet (v := v) ?_ hvCarrier
  simpa [R, SimpleGraph.Walk.support_reverse] using hvSupport

/--
A feasible block, oriented toward a marked target, admits the complete
uniform anchor package used after COY Claim 3.11.
-/
theorem exists_feasibleBlockAnchor
    (hconnected : G.Connected)
    (marked : Finset V)
    (B : GraphBlock G) (target : V)
    (htarget : target ∈ marked)
    (hfeasible : IsFeasibleBlock G marked B) :
    Nonempty (FeasibleBlockAnchor G marked B target) := by
  classical
  obtain
      ⟨b, pathToTarget, hbCarrier,
        hbTargetOrCut, hpathMeet⟩ :=
    B.exists_anchor_path_to hconnected target
  let special :=
    B.carrier ∩ (cutVertices G ∪ marked)
  have hbSpecial : b ∈ cutVertices G ∪ marked := by
    rcases hbTargetOrCut with hbTarget | hbCut
    · exact Finset.mem_union_right _ (hbTarget ▸ htarget)
    · exact Finset.mem_union_left _ (by simpa using hbCut)
  have hbSpecialCarrier : b ∈ special :=
    Finset.mem_inter.mpr ⟨hbCarrier, hbSpecial⟩
  let remaining := special.erase b
  have hremainingCard : remaining.card ≤ 1 := by
    have hspecialCard : special.card ≤ 2 := by
      exact hfeasible.1
    rw [show remaining = special.erase b by rfl,
      Finset.card_erase_of_mem hbSpecialCarrier]
    omega
  obtain ⟨ordinary, hordinary⟩ := hfeasible.2
  have hordinaryCarrier : ordinary ∈ B.carrier :=
    (Finset.mem_sdiff.mp hordinary).1
  have hordinaryNotSpecial :
      ordinary ∉ cutVertices G ∪ marked :=
    (Finset.mem_sdiff.mp hordinary).2
  by_cases hremaining : remaining.Nonempty
  · let zPrime := hremaining.choose
    have hzRemaining : zPrime ∈ remaining :=
      hremaining.choose_spec
    have hzSpecialCarrier : zPrime ∈ special :=
      Finset.mem_of_mem_erase hzRemaining
    have hzSpecial : zPrime ∈ cutVertices G ∪ marked :=
      (Finset.mem_inter.mp hzSpecialCarrier).2
    refine ⟨{
      b := b
      zPrime := zPrime
      ordinary := ordinary
      b_mem := hbCarrier
      zPrime_mem := (Finset.mem_inter.mp hzSpecialCarrier).1
      b_eq_target_or_cut := hbTargetOrCut
      b_special := hbSpecial
      zPrime_special := hzSpecial
      special_subset := ?_
      ordinary_mem := hordinaryCarrier
      ordinary_not_special := hordinaryNotSpecial
      pathToTarget := pathToTarget
      path_meets_carrier_only_at_b := hpathMeet
    }⟩
    intro v hvSpecial
    by_cases hvb : v = b
    · simp [hvb]
    · have hvRemaining : v ∈ remaining := by
        exact Finset.mem_erase.mpr ⟨hvb, hvSpecial⟩
      have hvz : v = zPrime :=
        Finset.card_le_one.mp hremainingCard
          v hvRemaining zPrime hzRemaining
      simp [hvz]
  · have hremainingEmpty : remaining = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hremaining
    refine ⟨{
      b := b
      zPrime := b
      ordinary := ordinary
      b_mem := hbCarrier
      zPrime_mem := hbCarrier
      b_eq_target_or_cut := hbTargetOrCut
      b_special := hbSpecial
      zPrime_special := hbSpecial
      special_subset := ?_
      ordinary_mem := hordinaryCarrier
      ordinary_not_special := hordinaryNotSpecial
      pathToTarget := pathToTarget
      path_meets_carrier_only_at_b := hpathMeet
    }⟩
    intro v hvSpecial
    have hvb : v = b := by
      by_contra hvb
      have hvRemaining : v ∈ remaining :=
        Finset.mem_erase.mpr ⟨hvb, hvSpecial⟩
      rw [hremainingEmpty] at hvRemaining
      simp at hvRemaining
    simp [hvb]

end GraphBlock

end DeanK5
