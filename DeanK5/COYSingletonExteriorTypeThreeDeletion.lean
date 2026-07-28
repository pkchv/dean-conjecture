import DeanK5.COYSingletonExteriorTypeThree
import DeanK5.COYSingletonExteriorTwinDeletion
import DeanK5.COYPathOperations

/-!
# The singleton exterior with a type-3 COY core

This file completes COY Case 1.3.  Claims 3.5--3.7 and the failure of
condition (T) force the two sides of the selected type-3 core to have
orders two and one.  Deleting the original roots leaves a smaller rooted
instance on the two vertices of the first side.  The artificial edge
between those vertices is used only to certify rooted 2-connectivity;
the recursively obtained paths lie in the deletion graph itself and lift
through the two deleted root edges.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredOrientationData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
In the natural type-3 singleton-exterior case, Claim 3.7 supplies all
witnesses for condition (T) except its order hypothesis.  Its failure
therefore forces `|T| = 2`.  Claim 3.6 then makes `S` nonempty, and the
type-3 core inequalities force `|S| = 1`.
-/
theorem typeThree_singleton_cardinalities
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (W : TypeThreeOtherComponentWitness D C) :
    C.T.card = 2 ∧ C.S.card = 1 := by
  classical
  change D.chosen.rooted.otherRegion = {y} at hregion
  have htype :
      D.chosen.rooted.core.typeNumber = 3 := by
    rw [hcore]
    rfl
  have hneighbors :=
    D.neighborSets_eq_T_of_natural_singleton
      M hnot hregion (Or.inr htype)
  have hNy :
      G.neighborSet y = (↑C.T : Set V) := by
    simpa [hcore, Core.T] using hneighbors.2
  have hNx :
      G.neighborSet x = (↑C.T : Set V) :=
    hneighbors.1.trans hNy
  have hTle : C.T.card ≤ 2 := by
    by_contra h
    have hthree : 3 ≤ C.T.card := by omega
    apply hnot
    exact ⟨{
      core := C
      core_eq := hcore
      three_le_T := hthree
      exterior_singleton := hregion
      root_neighbors := by
        intro v
        rw [← SimpleGraph.mem_neighborSet, hNx]
        rfl
      other_root_neighbors := by
        intro v
        rw [← SimpleGraph.mem_neighborSet, hNy]
        rfl
      component := W.component
      component_ne_other := W.component_ne_other
      ordinary := W.ordinary
      ordinary_mem := W.ordinary_mem
      ordinary_ne_exception := W.ordinary_ne_exception
      attachment := W.attachment
      attachment_mem := W.attachment_mem
      t₀ := W.terminal
      t₀_mem := W.terminal_mem
      t₀_adj_attachment := W.terminal_adj_attachment
    }⟩
  have hTge : 2 ≤ C.T.card :=
    (Nat.le_max_right (D.chosen.rank + 1) 2).trans
      C.card_T_lower
  have hcardT : C.T.card = 2 := by omega
  obtain ⟨d, hd, s, hs, hsd⟩ :=
    D.attachment_to_S_of_natural_singleton
      M hnot hregion (Or.inr htype)
      W.component W.component_ne_other
      ⟨W.ordinary, W.ordinary_mem,
        W.ordinary_ne_exception⟩
  have hsC : s ∈ C.S := by
    simpa [hcore, Core.S] using hs
  have hSpos : 0 < C.S.card :=
    Finset.card_pos.mpr ⟨s, hsC⟩
  have hrankPos : 1 ≤ D.chosen.rank := by
    rw [C.card_S] at hSpos
    omega
  have hrankUpper :
      D.chosen.rank + 1 ≤ C.T.card :=
    (Nat.le_max_left (D.chosen.rank + 1) 2).trans
      C.card_T_lower
  have hrankEq : D.chosen.rank = 1 := by
    omega
  refine ⟨hcardT, ?_⟩
  rw [C.card_S, hrankEq]

end PreferredOrientationData

namespace SingletonTwinDeletion

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z a b w : V}

/--
The recursive contradiction behind COY Case 1.3, stated only in terms of
two nonadjacent roots with the same two-element neighborhood.

The vertex `w` is an ordinary surviving vertex.  It supplies the recursive
instance's nonexceptional vertex when `z` also survives deletion.
-/
theorem contradiction
    (M : MinimalCounterexample q G x y z)
    (hab : a ≠ b)
    (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hNx : G.neighborSet x = ({a, b} : Set V))
    (hNy : G.neighborSet y = ({a, b} : Set V))
    (hwx : w ≠ x) (hwy : w ≠ y)
    (hwa : w ≠ a) (hwb : w ≠ b)
    (hwz : w ≠ z) :
    False := by
  classical
  let A := graph G x y
  let aA : Vertex x y :=
    vertex x y a hax hay
  let bA : Vertex x y :=
    vertex x y b hbx hby
  have habA : aA ≠ bA := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hrooted :
      IsTwoConnected (A ⊔ edge aA bA) := by
    exact sup_edge_two_connected_of_five_le_card
      M.underlying_two_connected M.five_le_card
      M.roots_ne M.roots_not_adj hab
      hax hay hbx hby hNx hNy
  have hcomplexity :
      rootedComplexity A < rootedComplexity G := by
    apply rootedComplexity_lt_of_card_lt_of_edgeCount_le
    · rw [card_vertex x y M.roots_ne]
      have hfive := M.five_le_card
      omega
    · exact edgeSet_ncard_le G x y
  have hdegreeWithException :
      ∀ v : Vertex x y, v ≠ aA → v ≠ bA →
        v.1 ≠ z → q + 1 ≤ finiteDegree A v := by
    intro v hva hvb hvz
    have hvAB : v.1 ∉ ({a, b} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      intro hv
      rcases hv with hv | hv
      · apply hva
        apply Subtype.ext
        exact hv
      · apply hvb
        apply Subtype.ext
        exact hv
    calc
      q + 1 ≤ finiteDegree G v.1 :=
        M.degree_lower v.1 v.2.1 v.2.2 hvz
      _ ≤ finiteDegree A v :=
        finiteDegree_le_graph v hvAB hNx hNy
  have hfamily :
      Nonempty (AdmissiblePathFamily A aA bA q) := by
    by_cases hz : z ≠ x ∧ z ≠ y
    · let zA : Vertex x y :=
        vertex x y z hz.1 hz.2
      let wA : Vertex x y :=
        vertex x y w hwx hwy
      let I : RootedInstance q A aA bA zA := {
        q_pos := M.q_pos
        q_le_four := M.q_le_four
        roots_ne := habA
        rooted_two_connected := hrooted
        ordinary_nonempty := by
          refine ⟨wA, ?_, ?_, ?_⟩
          · intro h
            exact hwa (congrArg Subtype.val h)
          · intro h
            exact hwb (congrArg Subtype.val h)
          · intro h
            exact hwz (congrArg Subtype.val h)
        degree_lower := by
          intro v hva hvb hvz
          apply hdegreeWithException v hva hvb
          intro h
          apply hvz
          apply Subtype.ext
          exact h
      }
      exact M.smaller_solvable I hcomplexity
    · have hzRemoved : z = x ∨ z = y := by
        by_cases hzx : z = x
        · exact Or.inl hzx
        · right
          by_contra hzy
          exact hz ⟨hzx, hzy⟩
      let I : RootedInstance q A aA bA aA :=
        RootedInstance.ofNoExtraException
          q A aA bA M.q_pos M.q_le_four
          habA hrooted
          (by
            intro v hva hvb
            apply hdegreeWithException v hva hvb
            rcases hzRemoved with rfl | rfl
            · exact v.2.1
            · exact v.2.2)
      exact M.smaller_solvable I hcomplexity
  obtain ⟨F⟩ := hfamily
  let mapped : AdmissiblePathFamily G a b q := by
    change AdmissiblePathFamily G
      ((aA : Vertex x y) : V)
      ((bA : Vertex x y) : V) q
    exact F.mapInjectiveHom
      (embedding G x y).toHom
      (embedding G x y).injective
  have hxa : G.Adj x a := by
    have haN : a ∈ G.neighborSet x := by
      rw [hNx]
      simp
    simpa [SimpleGraph.mem_neighborSet] using haN
  let left : SimplePath G x a :=
    SimplePath.ofAdj hxa
  have hbyAdj : G.Adj b y := by
    have hbN : b ∈ G.neighborSet y := by
      rw [hNy]
      simp
    simpa [SimpleGraph.mem_neighborSet] using hbN.symm
  let right : SimplePath G b y :=
    SimplePath.ofAdj hbyAdj
  have hleftDisjoint :
      ∀ i, left.walk.support.Disjoint
        (mapped.path i).walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvLeft hvTail
    have hvClass : v = x ∨ v = a := by
      simpa [left] using hvLeft
    rcases hvClass with hvx | hva
    · have hxSupport :
          x ∈ (mapped.path i).walk.support := by
        apply List.mem_of_mem_tail
        simpa [hvx] using hvTail
      change
        x ∈ ((F.path i).mapInjectiveHom
          (embedding G x y).toHom
          (embedding G x y).injective).walk.support at hxSupport
      have hxRange :=
        SimplePath.mem_range_of_mem_mapInjectiveHom_support
          (P := F.path i)
          (f := (embedding G x y).toHom)
          (hinj := (embedding G x y).injective)
          hxSupport
      obtain ⟨v, hv⟩ := hxRange
      exact v.2.1 hv
    · exact (mapped.path i).start_not_mem_tail
        (by simpa [hva] using hvTail)
  let prep :=
    mapped.prependFixed left hleftDisjoint
  have hrightDisjoint :
      ∀ i, (prep.path i).walk.support.Disjoint
        right.walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvPrep hvRight
    have hvy : v = y := by
      simpa [right] using hvRight
    subst v
    have hvParts :
        y ∈ left.walk.support ∨
          y ∈ (mapped.path i).walk.support := by
      simpa [prep, SimplePath.appendDisjoint] using hvPrep
    rcases hvParts with hyLeft | hyMapped
    · have hyClass : y = x ∨ y = a := by
        simpa [left] using hyLeft
      exact hyClass.elim
        (fun hyx => M.roots_ne hyx.symm)
        (fun hya => hay hya.symm)
    · have hyRange :=
        have hyMapped' :
            y ∈ ((F.path i).mapInjectiveHom
              (embedding G x y).toHom
              (embedding G x y).injective).walk.support := by
          change y ∈ (mapped.path i).walk.support
          exact hyMapped
        SimplePath.mem_range_of_mem_mapInjectiveHom_support
          (P := F.path i)
          (f := (embedding G x y).toHom)
          (hinj := (embedding G x y).injective)
          hyMapped'
      obtain ⟨v, hv⟩ := hyRange
      exact v.2.2 hv
  exact M.no_paths
    ⟨prep.appendFixed right hrightDisjoint⟩

end SingletonTwinDeletion

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
COY Case 1.3 in the selected-core interface.  Claims 3.5--3.7 force a
two-element common neighborhood for the original roots and provide an
ordinary vertex surviving their deletion.  Recursive minimality then
produces the forbidden path family.
-/
theorem false_of_natural_singleton_typeThree
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty
        (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (htype : D.chosen.rooted.core.typeNumber = 3) :
    False := by
  classical
  cases hcore : D.chosen.rooted.core with
  | typeOne C =>
      simp [hcore, Core.typeNumber] at htype
  | typeTwo C =>
      simp [hcore, Core.typeNumber] at htype
  | typeThree C =>
      obtain ⟨W⟩ :=
        D.exists_typeThreeOtherComponentWitness_of_natural_singleton
          M hnot hregion C hcore
      have hsizes :=
        D.typeThree_singleton_cardinalities
          M hnot hregion C hcore W
      obtain ⟨a, b, hab, hT⟩ :=
        Finset.card_eq_two.mp hsizes.1
      have haT : a ∈ C.T := by
        rw [hT]
        simp
      have hbT : b ∈ C.T := by
        rw [hT]
        simp
      have hyT : y ∉ C.T := by
        intro hy
        apply D.chosen.rooted.other_root_not_mem
        rw [hcore]
        exact (Core.typeThree C).T_subset_carrier
          (by simpa [Core.T] using hy)
      have hax : a ≠ x := by
        intro h
        exact C.root_not_mem_T (h ▸ haT)
      have hay : a ≠ y := by
        intro h
        exact hyT (h ▸ haT)
      have hbx : b ≠ x := by
        intro h
        exact C.root_not_mem_T (h ▸ hbT)
      have hby : b ≠ y := by
        intro h
        exact hyT (h ▸ hbT)
      have hneighbors :=
        D.neighborSets_eq_T_of_natural_singleton
          M hnot hregion (Or.inr htype)
      have hNy :
          G.neighborSet y = ({a, b} : Set V) := by
        simpa [hcore, Core.T, hT] using hneighbors.2
      have hNx :
          G.neighborSet x = ({a, b} : Set V) :=
        hneighbors.1.trans hNy
      let Q :=
        componentVertices G
          D.chosen.rooted.core.carrier W.component
      have hQ :
          ComponentRegion G
            D.chosen.rooted.core.carrier Q :=
        componentRegion_componentVertices
          G D.chosen.rooted.core.carrier W.component
      have hwCarrier :
          W.ordinary ∉ D.chosen.rooted.core.carrier :=
        hQ.not_mem_separator W.ordinary_mem
      have hwx : W.ordinary ≠ x := by
        intro h
        apply hwCarrier
        simp [h]
      have hwy : W.ordinary ≠ y := by
        intro h
        have hyW :
            y ∈ componentVertices G
              D.chosen.rooted.core.carrier W.component := by
          simpa [h] using W.ordinary_mem
        exact Finset.disjoint_left.mp
          (componentVertices_disjoint_of_ne
            G D.chosen.rooted.core.carrier
              W.component_ne_other)
          hyW
          D.chosen.rooted.other_root_mem_otherRegion
      have haCarrier :
          a ∈ D.chosen.rooted.core.carrier := by
        rw [hcore]
        exact (Core.typeThree C).T_subset_carrier
          (by simpa [Core.T] using haT)
      have hbCarrier :
          b ∈ D.chosen.rooted.core.carrier := by
        rw [hcore]
        exact (Core.typeThree C).T_subset_carrier
          (by simpa [Core.T] using hbT)
      have hwa : W.ordinary ≠ a := by
        intro h
        exact hwCarrier (h.symm ▸ haCarrier)
      have hwb : W.ordinary ≠ b := by
        intro h
        exact hwCarrier (h.symm ▸ hbCarrier)
      exact SingletonTwinDeletion.contradiction
        M hab hax hay hbx hby hNx hNy
        hwx hwy hwa hwb W.ordinary_ne_exception

end MinimalCounterexample

end COY

end DeanK5
