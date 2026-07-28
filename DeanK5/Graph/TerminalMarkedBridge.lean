import DeanK5.Graph.BlockCutSides
import DeanK5.Graph.ProtectedCutPair

/-!
# A terminal protected bridge behind a cut vertex

Let `y` and `z` be the two protected vertices in a finite connected graph
with no feasible block.  If a component behind a cut vertex contains `z`,
then a minimum end block inside that component is a bridge whose only inner
vertex is `z`.  This file packages that consequence in the form needed for
the `z`-end-block construction in COY Claim 3.11.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace ProtectedCutPair

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {y z : V}

/--
The side containing `z` behind any cut vertex contains a terminal bridge at
`z`.  Its other endpoint is distinct from both protected vertices, and
deleting that endpoint leaves `{z}` as a component region.
-/
theorem Context.exists_terminalMarkedBridge
    (C : Context G y z)
    {c : V} (hcut : IsCutVertex G c)
    (Q : (deleteVertices G {c}).ConnectedComponent)
    (hzQ : z ∈ componentVertices G {c} Q) :
    ∃ bz : V,
      bz ≠ y ∧
      bz ≠ z ∧
      IsCutVertex G bz ∧
      G.Adj z bz ∧
      ComponentRegion G {bz} {z} := by
  obtain ⟨L, hLinner, hLcut⟩ :=
    LobeRegion.exists_ofComponent C.connected c Q
  obtain ⟨E⟩ :=
    EndBlock.exists_certificate C.connected L
  have hblockCard :
      E.block.carrier.card ≤ 2 :=
    graphBlock_card_le_two_of_no_feasibleBlock
      C.connected ({y, z} : Finset V)
        (by
          simpa using
            (Finset.card_insert_le y ({z} : Finset V)))
        C.noFeasible E.block
  have hinnerCard :
      E.region.inner.card = 1 :=
    E.inner_card_eq_one_of_block_card_le_two hblockCard
  obtain ⟨v, hinnerEq⟩ :=
    Finset.card_eq_one.mp hinnerCard
  have hvInner : v ∈ E.region.inner := by
    simp [hinnerEq]
  have hvMarked : v ∈ ({y, z} : Finset V) :=
    E.inner_mem_marked_of_no_feasibleBlock_of_card_le_two
      ({y, z} : Finset V) C.noFeasible hblockCard hvInner
  have hvQ : v ∈ componentVertices G {c} Q := by
    have hsubset :
        E.region.inner ⊆ L.inner :=
      E.withinInitial.1
    rw [hLinner] at hsubset
    exact hsubset hvInner
  have hyNotQ : y ∉ componentVertices G {c} Q := by
    rcases
        C.deletionComponent_contains_exactly_one
          hcut Q with
      hcase | hcase
    · exact False.elim (hcase.2 hzQ)
    · exact hcase.2
  have hvz : v = z := by
    have hv : v = y ∨ v = z := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        hvMarked
    rcases hv with rfl | hvz
    · exact False.elim (hyNotQ hvQ)
    · exact hvz
  have hregionInner : E.region.inner = {z} := by
    simpa [hvz] using hinnerEq
  have hbzInitial :
      E.region.cut ∈
        insert c (componentVertices G {c} Q) := by
    simpa [hLcut, hLinner] using E.withinInitial.2
  have hbzNeY : E.region.cut ≠ y := by
    intro hbzy
    have hyInitial :
        y ∈ insert c (componentVertices G {c} Q) := by
      simpa [hbzy] using hbzInitial
    rcases Finset.mem_insert.mp hyInitial with hyc | hyQ
    · exact (C.cut_ne_marked hcut).1 hyc.symm
    · exact hyNotQ hyQ
  have hbzNeZ : E.region.cut ≠ z := by
    intro hbzz
    apply E.region.cut_not_inner
    rw [hregionInner, hbzz]
    simp
  have hyNotCarrier :
      y ∉ E.region.carrier := by
    intro hyCarrier
    rw [LobeRegion.carrier, hregionInner] at hyCarrier
    rcases Finset.mem_insert.mp hyCarrier with
        hyCut | hyZ
    · exact hbzNeY hyCut.symm
    · exact C.distinct (by simpa using hyZ)
  have hbzCut :
      IsCutVertex G E.region.cut :=
    E.region.isCutVertex_of_not_mem_carrier
      C.connected hyNotCarrier
  obtain ⟨w, hwInner, hcutw⟩ :=
    E.region.cut_adj_inner
  have hwz : w = z := by
    simpa [hregionInner] using hwInner
  refine
    ⟨E.region.cut, hbzNeY, hbzNeZ, hbzCut,
      ?_, ?_⟩
  · simpa [hwz] using hcutw.symm
  · simpa [hregionInner] using E.region.componentRegion

end ProtectedCutPair

end DeanK5
