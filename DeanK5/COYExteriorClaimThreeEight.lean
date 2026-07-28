import DeanK5.Graph.ComponentPruning
import DeanK5.COYTypeThreeAnchor
import DeanK5.COYWorkingCoreSelection
import DeanK5.COYPathOperations

/-!
# COY Claim 3.8

In the non-singleton exterior case, a selected type-3 working core whose
`S`-side is a singleton has a `T`-attachment to the exterior component.

The proof follows the source induction.  If no `T`-attachment existed, prune
the exterior component and root the remaining graph at the original core
root and the unique `S`-vertex.  The singleton-`S` type-3 core supplies a
2-connected anchor, while component pruning preserves rooted
2-connectivity.  Every ordinary surviving vertex keeps its exact ambient
degree.  Recursive paths in the pruned graph lift to the ambient graph and
are then extended along one fixed path through the exterior component.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

private theorem induced_edgeSet_ncard_le
    [Fintype V]
    (G : SimpleGraph V) (U : Set V) :
    (G.induce U).edgeSet.ncard ≤ G.edgeSet.ncard := by
  let e : G.induce U ↪g G :=
    Embedding.induce U
  have hsubset :
      Sym2.map e '' (G.induce U).edgeSet ⊆ G.edgeSet :=
    e.toHom.image_edgeSet_subset
  calc
    (G.induce U).edgeSet.ncard =
        (Sym2.map e '' (G.induce U).edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective e.injective)]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

private theorem outside_card_lt
    [Fintype V] [DecidableEq V]
    (Q : Finset V) (hQ : Q.Nonempty) :
    Fintype.card {v : V // v ∉ Q} < Fintype.card V := by
  obtain ⟨q, hqQ⟩ := hQ
  refine Fintype.card_lt_of_injective_of_notMem
    (b := q) (fun v : {v : V // v ∉ Q} => v.1)
    Subtype.val_injective ?_
  rintro ⟨v, rfl⟩
  exact v.2 hqQ

private theorem finiteDegree_induce_eq_of_neighbors_survive
    [Fintype V] {U : Set V} [Fintype U]
    (G : SimpleGraph V) (v : U)
    (hinside : ∀ w, G.Adj v.1 w → w ∈ U) :
    finiteDegree (G.induce U) v = finiteDegree G v.1 := by
  let N : Set V := G.neighborSet v.1
  let NI : Set U := (G.induce U).neighborSet v
  have himage : Subtype.val '' NI = N := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hw
      exact ⟨⟨w, hinside w hw⟩, hw, rfl⟩
  unfold finiteDegree
  change NI.ncard = N.ncard
  rw [← himage,
    Set.ncard_image_of_injective _ Subtype.val_injective]

private theorem exists_unique_side_attachment_of_no_T
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x s : V} {ℓ : ℕ}
    (C : TypeThreeCore G x ℓ)
    {Q : Finset V}
    (hQ : ComponentRegion G (Core.typeThree C).carrier Q)
    (hS : C.S = {s})
    (hconn : IsTwoConnected G)
    (hno :
      ¬(Core.typeThree C).HasTAttachment Q) :
    ∃ a ∈ Q, G.Adj s a := by
  obtain ⟨a, haQ, t, htCarrier, htx, hta⟩ :=
    (Core.typeThree C).exists_nonroot_attachment hQ hconn
  have htParts :
      t = x ∨ t ∈ C.S ∨ t ∈ C.T := by
    simpa [Core.carrier, Core.S, Core.T] using htCarrier
  rcases htParts with htx' | htS | htT
  · exact False.elim (htx htx')
  · have hts : t = s := by
      simpa [hS] using htS
    subst t
    exact ⟨a, haQ, hta⟩
  · apply False.elim
    apply hno
    refine ⟨a, haQ, t, ?_, hta⟩
    simpa [Core.T] using htT

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

private theorem false_of_no_T_attachment_typeThree_card_S_one
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (C : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree C)
    (hS : C.S.card = 1)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hno :
      ¬(Core.typeThree C).HasTAttachment
        P.working.rooted.otherRegion) :
    False := by
  classical
  obtain ⟨s, hSset⟩ := Finset.card_eq_one.mp hS
  have hsS : s ∈ C.S := by
    rw [hSset]
    simp
  let Q := P.working.rooted.otherRegion
  have hQ :
      ComponentRegion G (Core.typeThree C).carrier Q := by
    have hQ' :=
      P.working.rooted.otherRegion_componentRegion
    rw [hcore] at hQ'
    exact hQ'
  have hyQ : y ∈ Q := by
    exact P.working.rooted.other_root_mem_otherRegion
  have hQtwo : 1 < Q.card := by
    have hother : ∃ v ∈ Q, v ≠ y := by
      by_contra h
      push Not at h
      apply hregion
      change Q = {y}
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hyQ, fun v hv => h v hv⟩
    obtain ⟨v, hvQ, hvy⟩ := hother
    exact Finset.one_lt_card.mpr
      ⟨y, hyQ, v, hvQ, hvy.symm⟩
  have hxCarrier :
      x ∈ (Core.typeThree C).carrier :=
    (Core.typeThree C).root_mem_carrier
  have hsCarrier :
      s ∈ (Core.typeThree C).carrier :=
    (Core.typeThree C).S_subset_carrier
      (by simpa [Core.S] using hsS)
  let x' :=
    ComponentPruning.boundaryVertex hQ x hxCarrier
  let s' :=
    ComponentPruning.boundaryVertex hQ s hsCarrier
  let H : SimpleGraph (ComponentPruning.Outside Q) :=
    G.induce {v | v ∉ Q}
  have hanchor :
      IsTwoConnected
        (G.induce
            (↑(Core.typeThree C).carrier : Set V) ⊔
          edge
            (⟨x, hxCarrier⟩ :
              (↑(Core.typeThree C).carrier : Set V))
            (⟨s, hsCarrier⟩ :
              (↑(Core.typeThree C).carrier : Set V))) := by
    simpa [TypeThreeCore.carrierGraph,
      TypeThreeCore.rootVertex,
      TypeThreeCore.sideVertex] using
      C.carrierGraph_sup_root_side_two_connected hSset
  have hrooted :
      IsTwoConnected (H ⊔ edge x' s') := by
    exact ComponentPruning.rooted_two_connected
      M.underlying_two_connected hQ hxCarrier hsCarrier hanchor
  have hxs : x ≠ s := by
    intro h
    subst s
    exact C.root_not_mem_S hsS
  have hroots : x' ≠ s' := by
    intro h
    exact hxs (congrArg Subtype.val h)
  let e : ComponentPruning.Outside Q :=
    if hzQ : z ∈ Q then x' else ⟨z, hzQ⟩
  have hTtwo : 1 < C.T.card := by
    have hbound :
        2 ≤ C.T.card :=
      (Nat.le_max_right (P.working.rank + 1) 2).trans
        C.card_T_lower
    omega
  obtain ⟨t, htT, htz⟩ :=
    C.T.exists_mem_ne hTtwo z
  have htCarrier :
      t ∈ (Core.typeThree C).carrier :=
    (Core.typeThree C).T_subset_carrier
      (by simpa [Core.T] using htT)
  have htQ : t ∉ Q :=
    fun htQ => hQ.not_mem_separator htQ htCarrier
  let t' : ComponentPruning.Outside Q := ⟨t, htQ⟩
  have htx : t ≠ x := by
    intro h
    subst t
    exact C.root_not_mem_T htT
  have hts : t ≠ s := by
    intro h
    subst t
    exact Finset.disjoint_left.mp C.disjoint hsS htT
  have htX : t' ≠ x' := by
    intro h
    exact htx (congrArg Subtype.val h)
  have htS : t' ≠ s' := by
    intro h
    exact hts (congrArg Subtype.val h)
  have htE : t' ≠ e := by
    by_cases hzQ : z ∈ Q
    · simpa [e, hzQ] using htX
    · have htZ :
          t' ≠ (⟨z, hzQ⟩ :
            ComponentPruning.Outside Q) := by
        intro h
        exact htz (congrArg Subtype.val h)
      simpa [e, hzQ] using htZ
  let I : RootedInstance q H x' s' e := {
    q_pos := M.q_pos
    q_le_four := M.q_le_four
    roots_ne := hroots
    rooted_two_connected := hrooted
    ordinary_nonempty := ⟨t', htX, htS, htE⟩
    degree_lower := by
      intro v hvx hvs hve
      have hvx' : v.1 ≠ x := by
        intro h
        apply hvx
        apply Subtype.ext
        exact h
      have hvs' : v.1 ≠ s := by
        intro h
        apply hvs
        apply Subtype.ext
        exact h
      have hvy' : v.1 ≠ y := by
        intro h
        apply v.2
        simpa [h] using hyQ
      have hvz' : v.1 ≠ z := by
        by_cases hzQ : z ∈ Q
        · intro h
          apply v.2
          simpa [h] using hzQ
        · intro h
          apply hve
          apply Subtype.ext
          simpa [e, hzQ] using h
      have hinside :
          ∀ w, G.Adj v.1 w →
            w ∈ ({w : V | w ∉ Q} : Set V) := by
        intro w hvw
        change w ∉ Q
        intro hwQ
        have hvCarrier :
            v.1 ∈ (Core.typeThree C).carrier := by
          by_contra hvNotCarrier
          apply v.2
          exact hQ.closed hwQ hvw.symm hvNotCarrier
        have hvParts :
            v.1 = x ∨ v.1 ∈ C.S ∨ v.1 ∈ C.T := by
          simpa [Core.carrier, Core.S, Core.T] using
            hvCarrier
        rcases hvParts with hvRoot | hvSide | hvT
        · exact hvx' hvRoot
        · have hvEqS : v.1 = s := by
            simpa [hSset] using hvSide
          exact hvs' hvEqS
        · apply hno
          refine ⟨w, hwQ, v.1, ?_, hvw⟩
          simpa [Core.T] using hvT
      have hdegreeEq :=
        finiteDegree_induce_eq_of_neighbors_survive
          (U := {w : V | w ∉ Q}) G v hinside
      change
        q + 1 ≤
          finiteDegree (G.induce {w : V | w ∉ Q}) v
      rw [hdegreeEq]
      exact M.degree_lower v.1 hvx' hvy' hvz'
  }
  have hcard :
      Fintype.card (ComponentPruning.Outside Q) <
        Fintype.card V :=
    outside_card_lt Q
      (Finset.card_pos.mp (by omega))
  have hedge :
      H.edgeSet.ncard ≤ G.edgeSet.ncard := by
    exact induced_edgeSet_ncard_le G {v | v ∉ Q}
  have hcomplexity :
      rootedComplexity H < rootedComplexity G :=
    rootedComplexity_lt_of_card_lt_of_edgeCount_le
      hcard hedge
  obtain ⟨F⟩ := M.smaller_solvable I hcomplexity
  obtain ⟨a, haQ, hsa⟩ :=
    exists_unique_side_attachment_of_no_T
      C hQ hSset M.underlying_two_connected hno
  let connector : SimplePath G s y :=
    hQ.boundaryPath hsCarrier haQ hyQ hsa
  let inclusion : H ↪g G :=
    Embedding.induce {v | v ∉ Q}
  let mapped : AdmissiblePathFamily G x s q :=
    F.mapInjectiveHom inclusion.toHom inclusion.injective
  have hdisjoint :
      ∀ i, (mapped.path i).walk.support.Disjoint
        connector.walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvMapped hvConnector
    have hvRange :
        v ∈ Set.range inclusion := by
      have hvMap :
          v ∈ ((F.path i).walk.map inclusion.toHom).support := by
        change
          v ∈ ((F.path i).walk.map inclusion.toHom).support
          at hvMapped
        exact hvMapped
      rw [SimpleGraph.Walk.support_map] at hvMap
      obtain ⟨w, -, hwv⟩ := List.mem_map.mp hvMap
      exact ⟨w, hwv⟩
    obtain ⟨w, rfl⟩ := hvRange
    have hwQ :
        (inclusion w : V) ∈ Q :=
      hQ.boundaryPath_tail_subset
        hsCarrier haQ hyQ hsa
        (by simpa [connector] using hvConnector)
    exact w.2 hwQ
  apply M.no_paths
  exact ⟨mapped.appendFixed connector hdisjoint⟩

/--
COY Claim 3.8 in the selected working-core interface: in the
non-singleton exterior case, a type-3 core with singleton `S` has an
attachment from its `T`-side to the exterior component.
-/
theorem hasTAttachment_of_typeThree_card_S_one
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (C : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree C)
    (hS : C.S.card = 1)
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    (Core.typeThree C).HasTAttachment
      P.working.rooted.otherRegion := by
  by_contra hno
  exact false_of_no_T_attachment_typeThree_card_S_one
    M P C hcore hS hregion hno

end PreferredWorkingCoreData

end COY

end DeanK5
