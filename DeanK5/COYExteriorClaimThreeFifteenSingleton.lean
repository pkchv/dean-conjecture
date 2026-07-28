import DeanK5.COYExteriorClaimThreeFifteenBPrime
import DeanK5.COYExteriorClaimThreeFifteenClosure

/-!
# The singleton-neighbour branch of COY Claim 3.15(1)

Assume the unique type-three `S`-vertex `s` has exactly one neighbour `v`
in the selected block.  The source recursive graph is
`B' = G[B ∪ {x}]`, rooted at `x,b`, with exceptional vertex `v`.

This file proves the exact degree preservation, rooted connectivity,
strict-smaller complexity, and connector separation required by the
recursive call.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s v : V}
  {P : PreferredWorkingCoreData G x y z}

/--
At a nonexceptional block vertex, inducing first on the exterior component
and then on the block loses no neighbours.
-/
theorem exterior_degree_eq_bPrimeBlock_degree
    (C : P.ExteriorFeasibleBlockChoice)
    (hzPrime : C.zPrime = C.b)
    {d : V} (hd : d ∈ C.compressionInterior) :
    finiteDegree P.exteriorGraph
        (C.exteriorVertex
          (Finset.mem_of_mem_erase hd)) =
      finiteDegree C.bPrimeBlockGraph
        ⟨d, Finset.mem_of_mem_erase hd⟩ := by
  let dE :=
    C.exteriorVertex (Finset.mem_of_mem_erase hd)
  let dB : C.BPrimeBlockVertex :=
    ⟨d, Finset.mem_of_mem_erase hd⟩
  have hdb : d ≠ C.b :=
    (Finset.mem_erase.mp hd).1
  have hdz : d ≠ C.zPrime := by
    simpa [hzPrime] using hdb
  have himageExterior :
      Subtype.val ''
          P.exteriorGraph.neighborSet dE =
        G.neighborSet d ∩
          (↑C.ambientCarrier : Set V) := by
    ext w
    constructor
    · rintro ⟨wE, hdw, rfl⟩
      have hwBlock :
          wE ∈ C.block.carrier :=
        C.exterior_neighbor_mem_block
          (Finset.mem_of_mem_erase hd)
          hdb hdz hdw
      exact
        ⟨hdw, C.mem_ambientCarrier.mpr
          ⟨wE, hwBlock, rfl⟩⟩
    · rintro ⟨hdw, hwBlock⟩
      let wE : P.ExteriorVertex :=
        ⟨w, C.ambientCarrier_subset_otherRegion
          hwBlock⟩
      exact ⟨wE, hdw, rfl⟩
  have himageBlock :
      Subtype.val ''
          C.bPrimeBlockGraph.neighborSet dB =
        G.neighborSet d ∩
          (↑C.ambientCarrier : Set V) := by
    ext w
    constructor
    · rintro ⟨wB, hdw, rfl⟩
      exact ⟨hdw, wB.2⟩
    · rintro ⟨hdw, hwBlock⟩
      exact ⟨⟨w, hwBlock⟩, hdw, rfl⟩
  unfold finiteDegree
  calc
    (P.exteriorGraph.neighborSet dE).ncard =
        (Subtype.val ''
          P.exteriorGraph.neighborSet dE).ncard := by
      rw [Set.ncard_image_of_injective _
        Subtype.val_injective]
    _ =
        (G.neighborSet d ∩
          (↑C.ambientCarrier : Set V)).ncard := by
      rw [himageExterior]
    _ =
        (Subtype.val ''
          C.bPrimeBlockGraph.neighborSet dB).ncard := by
      rw [himageBlock]
    _ =
        (C.bPrimeBlockGraph.neighborSet dB).ncard := by
      rw [Set.ncard_image_of_injective _
        Subtype.val_injective]

/--
In the singleton case, every nonexceptional vertex `d ≠ v` retains its
entire ambient degree in `G[B ∪ {x}]`.
-/
theorem finiteDegree_le_singleBPrime
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    (hzPrime : C.zPrime = C.b)
    (hboundary : C.coreAttachments = {x, s})
    (hside : C.blockNeighbors s = {v})
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdv : d ≠ v) :
    finiteDegree G d ≤
      finiteDegree C.singleBPrime
        (some
          (⟨d, Finset.mem_of_mem_erase hd⟩ :
            C.BPrimeBlockVertex)) := by
  have hdB : d ∈ C.ambientCarrier :=
    Finset.mem_of_mem_erase hd
  have hdRegion :
      d ∈ P.working.rooted.otherRegion :=
    C.ambientCarrier_subset_otherRegion hdB
  have hsplit :
      finiteDegree G d =
        finiteDegree P.exteriorGraph
            (C.exteriorVertex hdB) +
          (G.neighborSet d ∩
            (↑P.working.rooted.core.carrier :
              Set V)).ncard := by
    simpa [exteriorVertex] using
      (ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
        P.working.rooted.otherRegion_componentRegion
        hdRegion)
  have hcoreOne :=
    C.interior_coreNeighbor_ncard_le_one
      M D hzPrime hd
  have hsNotAdj :
      ¬G.Adj d s :=
    C.not_adj_side_of_blockNeighbors_eq_singleton
      hside hd hdv
  have hbase :
      finiteDegree P.exteriorGraph
          (C.exteriorVertex hdB) =
        finiteDegree C.bPrimeBlockGraph
          ⟨d, hdB⟩ :=
    C.exterior_degree_eq_bPrimeBlock_degree
      hzPrime hd
  change
    finiteDegree G d ≤
      finiteDegree
        (adjoinRoot C.bPrimeBlockGraph
          (C.bPrimeAttachments x))
        (some
          (⟨d, hdB⟩ :
            C.BPrimeBlockVertex))
  rw [finiteDegree_adjoinRoot_some]
  by_cases hdx : G.Adj d x
  · have hxAttach :
        (⟨d, hdB⟩ :
          C.BPrimeBlockVertex) ∈
            C.bPrimeAttachments x := by
      exact C.mem_bPrimeAttachments.mpr hdx.symm
    rw [if_pos hxAttach]
    omega
  · have hxNotAttach :
        (⟨d, hdB⟩ :
          C.BPrimeBlockVertex) ∉
            C.bPrimeAttachments x := by
      intro h
      exact hdx
        (C.mem_bPrimeAttachments.mp h).symm
    rw [if_neg hxNotAttach, add_zero]
    have hcoreEmpty :
        G.neighborSet d ∩
            (↑P.working.rooted.core.carrier :
              Set V) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hwPair :=
        C.core_neighbor_mem_pair hboundary hd
          hw.2 hw.1
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hwPair
      rcases hwPair with rfl | rfl
      · exact hdx hw.1
      · exact hsNotAdj hw.1
    rw [hcoreEmpty] at hsplit
    simp at hsplit
    omega

/-- In the singleton case, the named exceptional vertex really lies in
`B-b`. -/
theorem singleton_neighbor_mem_compressionInterior
    (C : P.ExteriorFeasibleBlockChoice)
    (hboundary : C.coreAttachments = {x, s})
    (hside : C.blockNeighbors s = {v}) :
    v ∈ C.compressionInterior := by
  obtain ⟨d, hd, hsd⟩ :=
    C.exists_side_attachment_in_compressionInterior
      hboundary
  have hdSide : d ∈ C.blockNeighbors s :=
    C.mem_blockNeighbors.mpr
      ⟨Finset.mem_of_mem_erase hd, hsd⟩
  rw [hside] at hdSide
  have hdv : d = v := by
    simpa using hdSide
  simpa [hdv] using hd

/-- The exceptional vertex of the recursive singleton graph. -/
def singleBPrimeException
    (C : P.ExteriorFeasibleBlockChoice)
    (hv : v ∈ C.compressionInterior) :
    Option C.BPrimeBlockVertex :=
  some ⟨v, Finset.mem_of_mem_erase hv⟩

/--
The singleton recursive graph has enough vertices to choose an ordinary
vertex outside its two roots and its named exception.
-/
theorem exists_singleBPrime_ordinary
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    (hzPrime : C.zPrime = C.b)
    (hS : D.core.S = {s})
    (hboundary : C.coreAttachments = {x, s})
    (hside : C.blockNeighbors s = {v}) :
    ∃ w : Option C.BPrimeBlockVertex,
      w ≠ C.singleBPrimeRoot ∧
        w ≠ C.singleBPrimeAnchor ∧
          w ≠ C.singleBPrimeException
            (C.singleton_neighbor_mem_compressionInterior
              hboundary hside) := by
  have hvInterior :=
    C.singleton_neighbor_mem_compressionInterior
      hboundary hside
  have hvB : v ∈ C.ambientCarrier :=
    Finset.mem_of_mem_erase hvInterior
  have hvOrdinary :=
    C.exteriorOrdinaryOfInterior hzPrime hvInterior
  have hqThree :
      3 ≤ q :=
    P.three_le_q_of_typeThree_singleton_side
      M D.core D.core_eq hS
      (P.otherRegion_ne_singleton M)
  have hvx : v ≠ x := by
    intro h
    exact Finset.disjoint_left.mp
      C.ambientCarrier_disjoint_core hvB
      (Eq.mp
        (congrArg
          (fun a =>
            a ∈ P.working.rooted.core.carrier)
          h.symm)
        P.working.rooted.core.root_mem_carrier)
  have hvy : v ≠ y := by
    exact C.ordinary_block_vertex_ne_y
      hvB (Finset.mem_erase.mp hvInterior).1
      (by
        simpa [hzPrime] using
          (Finset.mem_erase.mp hvInterior).1)
  have hvz : v ≠ z := by
    exact C.ordinary_block_vertex_ne_z
      hvB (Finset.mem_erase.mp hvInterior).1
      (by
        simpa [hzPrime] using
          (Finset.mem_erase.mp hvInterior).1)
  have hambientLower :
      q + 1 ≤ finiteDegree G v :=
    M.degree_lower v hvx hvy hvz
  have hsplit :
      finiteDegree G v =
        finiteDegree P.exteriorGraph
            (C.exteriorVertex hvB) +
          (G.neighborSet v ∩
            (↑P.working.rooted.core.carrier :
              Set V)).ncard := by
    simpa [exteriorVertex] using
      (ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
        P.working.rooted.otherRegion_componentRegion
        (C.ambientCarrier_subset_otherRegion hvB))
  have hcoreOne :=
    C.interior_coreNeighbor_ncard_le_one
      M D hzPrime hvInterior
  have hblockDegree :
      finiteDegree P.exteriorGraph
          (C.exteriorVertex hvB) =
        finiteDegree C.bPrimeBlockGraph
          ⟨v, hvB⟩ :=
    C.exterior_degree_eq_bPrimeBlock_degree
      hzPrime hvInterior
  have hdegreeThree :
      3 ≤ finiteDegree C.bPrimeBlockGraph
        ⟨v, hvB⟩ := by
    omega
  have hneighborProper :
      C.bPrimeBlockGraph.neighborSet
          (⟨v, hvB⟩ :
            C.BPrimeBlockVertex) ≠ Set.univ := by
    intro h
    have hloop :
        (⟨v, hvB⟩ :
          C.BPrimeBlockVertex) ∈
            C.bPrimeBlockGraph.neighborSet
              ⟨v, hvB⟩ := by
      rw [h]
      simp
    exact C.bPrimeBlockGraph.loopless.irrefl _ hloop
  have hdegreeLt :
      finiteDegree C.bPrimeBlockGraph
          (⟨v, hvB⟩ :
            C.BPrimeBlockVertex) <
        Fintype.card C.BPrimeBlockVertex := by
    unfold finiteDegree
    simpa [Nat.card_eq_fintype_card] using
      Set.ncard_lt_card hneighborProper
  have horder :
      3 ≤ Fintype.card C.BPrimeBlockVertex := by
    omega
  obtain ⟨w, hwb, hwv⟩ :=
    exists_avoiding_two_of_three_le
      C.bPrimeAnchor
      (⟨v, hvB⟩ : C.BPrimeBlockVertex)
      horder
  refine
    ⟨some w, (by simp [singleBPrimeRoot]),
      ?_, ?_⟩
  · intro h
    exact hwb (Option.some.inj h)
  · intro h
    exact hwv (Option.some.inj h)

/-- The singleton recursive graph has fewer vertices than the ambient graph. -/
theorem singleBPrime_vertex_card_lt
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    (hS : D.core.S = {s}) :
    Fintype.card (Option C.BPrimeBlockVertex) <
      Fintype.card V := by
  have hsSide : s ∈ D.core.S := by
    rw [hS]
    simp
  have hsWorkingCore :
      s ∈ P.working.rooted.core.carrier := by
    rw [D.core_eq]
    exact (Core.typeThree D.core).S_subset_carrier
      (by simpa [Core.S] using hsSide)
  refine
    Fintype.card_lt_of_injective_of_notMem
      (b := s) C.singleBPrimeHom
      C.singleBPrimeHom_injective ?_
  rintro ⟨w, hw⟩
  cases w with
  | none =>
      change x = s at hw
      apply D.core.root_not_mem_S
      exact
        Eq.mp
          (congrArg
            (fun a => a ∈ D.core.S)
            hw.symm)
          hsSide
  | some d =>
      change d.1 = s at hw
      exact Finset.disjoint_left.mp
        C.ambientCarrier_disjoint_core d.2
        (Eq.mp
          (congrArg
            (fun a =>
              a ∈ P.working.rooted.core.carrier)
            hw.symm)
          hsWorkingCore)

/-- The injective graph homomorphism bounds the recursive edge count. -/
theorem singleBPrime_edgeSet_ncard_le
    (C : P.ExteriorFeasibleBlockChoice) :
    C.singleBPrime.edgeSet.ncard ≤
      G.edgeSet.ncard := by
  let f := C.singleBPrimeHom
  have hsubset :
      Sym2.map f '' C.singleBPrime.edgeSet ⊆
        G.edgeSet :=
    f.image_edgeSet_subset
  calc
    C.singleBPrime.edgeSet.ncard =
        (Sym2.map f ''
          C.singleBPrime.edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective
          C.singleBPrimeHom_injective)]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

/-- The singleton recursive graph is strictly smaller in the COY measure. -/
theorem singleBPrime_complexity_lt
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    (hS : D.core.S = {s}) :
    rootedComplexity C.singleBPrime <
      rootedComplexity G :=
  rootedComplexity_lt_of_card_lt_of_edgeCount_le
    (C.singleBPrime_vertex_card_lt D hS)
    C.singleBPrime_edgeSet_ncard_le

/--
Every mapped `x`--`b` path in the singleton recursive graph is disjoint
from the tail of the fixed `b`--`y` connector.
-/
theorem singleBPrime_path_disjoint_pathToY
    (C : P.ExteriorFeasibleBlockChoice)
    (Q : SimplePath C.singleBPrime
      C.singleBPrimeRoot C.singleBPrimeAnchor) :
    (Q.mapInjectiveHom C.singleBPrimeHom
        C.singleBPrimeHom_injective).walk.support.Disjoint
      C.pathToY.walk.support.tail := by
  apply List.disjoint_left.mpr
  intro a haMapped haTail
  have haConnector :
      a ∈ C.pathToY.walk.support :=
    List.mem_of_mem_tail haTail
  change
    a ∈ (Q.walk.map C.singleBPrimeHom).support
      at haMapped
  rw [SimpleGraph.Walk.support_map] at haMapped
  obtain ⟨w, hwQ, hwValue⟩ :=
    List.mem_map.mp haMapped
  cases w with
  | none =>
      change x = a at hwValue
      have haRegion :=
        C.pathToY_support_mem_otherRegion
          haConnector
      exact
        P.working.rooted.otherRegion_componentRegion.not_mem_separator
          haRegion
          (Eq.mp
            (congrArg
              (fun u =>
                u ∈ P.working.rooted.core.carrier)
              hwValue)
            P.working.rooted.core.root_mem_carrier)
  | some d =>
      change d.1 = a at hwValue
      have haBlock :
          ∃ w ∈ C.block.carrier, w.1 = a := by
        have hdAmbient := d.2
        change d.1 ∈ C.ambientCarrier at hdAmbient
        rw [C.mem_ambientCarrier] at hdAmbient
        obtain ⟨w, hw, hwVal⟩ := hdAmbient
        exact ⟨w, hw, hwVal.trans hwValue⟩
      have hab :
          a = C.b :=
        C.pathToY_meets_block_only_at_b
          haConnector haBlock
      exact C.pathToY.start_not_mem_tail
        (by simpa [hab] using haTail)

/-- The complete rooted instance in the singleton-neighbour branch. -/
theorem singleBPrime_recursiveInstance
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    (hzPrime : C.zPrime = C.b)
    (hS : D.core.S = {s})
    (hboundary : C.coreAttachments = {x, s})
    (hside : C.blockNeighbors s = {v}) :
    RootedInstance q C.singleBPrime
      C.singleBPrimeRoot C.singleBPrimeAnchor
      (C.singleBPrimeException
        (C.singleton_neighbor_mem_compressionInterior
          hboundary hside)) where
  q_pos := M.q_pos
  q_le_four := M.q_le_four
  roots_ne := by simp [singleBPrimeRoot, singleBPrimeAnchor]
  rooted_two_connected :=
    C.singleBPrime_rooted_twoConnected hboundary
  ordinary_nonempty :=
    C.exists_singleBPrime_ordinary
      M D hzPrime hS hboundary hside
  degree_lower := by
    intro w hwRoot hwAnchor hwException
    cases w with
    | none =>
        exact False.elim (hwRoot rfl)
    | some d =>
        have hdb : d.1 ≠ C.b := by
          intro h
          apply hwAnchor
          apply congrArg some
          apply Subtype.ext
          exact h
        have hdInterior :
            d.1 ∈ C.compressionInterior :=
          Finset.mem_erase.mpr ⟨hdb, d.2⟩
        have hdv : d.1 ≠ v := by
          intro h
          apply hwException
          apply congrArg some
          apply Subtype.ext
          exact h
        have hdNotX : d.1 ≠ x := by
          intro h
          exact Finset.disjoint_left.mp
            C.ambientCarrier_disjoint_core d.2
            (Eq.mp
              (congrArg
                (fun a =>
                  a ∈ P.working.rooted.core.carrier)
                h.symm)
              P.working.rooted.core.root_mem_carrier)
        have hdNotY :
            d.1 ≠ y :=
          C.ordinary_block_vertex_ne_y
            d.2 hdb (by simpa [hzPrime] using hdb)
        have hdNotZ :
            d.1 ≠ z :=
          C.ordinary_block_vertex_ne_z
            d.2 hdb (by simpa [hzPrime] using hdb)
        have hambient :=
          M.degree_lower d.1
            hdNotX hdNotY hdNotZ
        have hpreserved :=
          C.finiteDegree_le_singleBPrime
            M D hzPrime hboundary hside
            hdInterior hdv
        exact hambient.trans hpreserved

/--
The singleton-neighbour alternative proves Claim 3.15(1).
-/
theorem meetsProtectedInterior_of_sideBlockNeighbors_eq_singleton
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    (hS : D.core.S = {s})
    (hboundary : C.coreAttachments = {x, s})
    (hside : C.blockNeighbors s = {v}) :
    C.MeetsProtectedInterior := by
  by_contra hnot
  have hyNot :
      y ∉ C.compressionInterior := by
    intro hy
    exact hnot (Or.inl hy)
  have hzPrimeNot :
      C.zPrime ∉ C.compressionInterior := by
    intro hz
    exact hnot (Or.inr hz)
  have hzPrime :
      C.zPrime = C.b :=
    C.zPrime_eq_b_of_not_mem_compressionInterior
      hzPrimeNot
  let I :=
    C.singleBPrime_recursiveInstance
      M D hzPrime hS hboundary hside
  exact
    false_of_claimThreeFifteen_recursiveInstance
      M I
      (C.singleBPrime_complexity_lt D hS)
      C.singleBPrimeHom
      C.singleBPrimeHom_injective
      rfl
      C.pathToY
      C.singleBPrime_path_disjoint_pathToY

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
