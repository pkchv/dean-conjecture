import DeanK5.COYExteriorZEndBlock

/-!
# The balanced modified-core case of COY Claim 3.9(4)

In modification (M1), both `t₀` and `s₀` are removed from the selected
type-3 core.  The edge `t₀s₀` therefore pulls `s₀` into the new exterior
component.  The attachment chosen in the old second component enters the
same exterior through `t₀`, while the other root `y` is already there.

Thus, if the source vertex `b'_z` were `t₀`, it would have the three
distinct exterior neighbours `y`, `s₀`, and the old-component attachment.
This contradicts the degree-at-most-two hypothesis in Claim 3.9(4).
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

namespace ExteriorZEndBlock

/--
The old attachment component is different from the old component
containing `y`, so its selected attachment is not `y`.
-/
private theorem attachment_ne_other_root
    (T : TypeThreeModificationTrigger
      (z := z) P.orientation.chosen) :
    T.attachment ≠ y := by
  intro h
  have hyOld :
      y ∈ P.orientation.chosen.rooted.otherRegion :=
    P.orientation.chosen.rooted.other_root_mem_otherRegion
  have haOld :
      T.attachment ∈
        P.orientation.chosen.rooted.otherRegion := by
    simpa only [h] using hyOld
  exact
    Finset.disjoint_left.mp
      (componentVertices_disjoint_of_ne
        G P.orientation.chosen.rooted.core.carrier
        T.component_ne_other)
      T.attachment_mem haOld

/--
COY Claim 3.9(4), balanced modification (M1): if `b'_z` has exterior
degree at most two, then it is not the removed vertex `t₀`.
-/
theorem bPrime_ne_t₀_of_balanced
    (T : TypeThreeModificationTrigger
      (z := z) P.orientation.chosen)
    (s₀ : V) (hs₀ : s₀ ∈ T.core.S)
    (hbalance : T.core.T.card = T.core.S.card + 1)
    (hworking :
      P.working =
        .modified T (.balanced s₀ hs₀ hbalance))
    (E : P.ExteriorZEndBlock)
    (hdegree :
      finiteDegree P.exteriorGraph E.certificate.bPrime ≤ 2) :
    E.bPrime ≠ T.t₀ := by
  classical
  let K : TypeThreeModificationChoice T :=
    .balanced s₀ hs₀ hbalance
  have hs₀NotOldT : s₀ ∉ T.core.T := by
    intro hs₀T
    exact
      Finset.disjoint_left.mp T.core.disjoint
        hs₀ hs₀T
  have hs₀NeRoot : s₀ ≠ x := by
    intro h
    exact T.core.root_not_mem_S (h ▸ hs₀)
  have hs₀NotCarrierK :
      s₀ ∉ K.rooted.core.carrier := by
    simp [K, TypeThreeModificationChoice.rooted,
      TypeThreeModificationChoice.core,
      TypeThreeModificationChoice.rank,
      TypeThreeCore.eraseBalanced,
      Core.carrier, Core.S, Core.T,
      hs₀NeRoot, hs₀NotOldT]
  have hs₀NotCarrier :
      s₀ ∉ P.working.rooted.core.carrier := by
    rw [hworking]
    exact hs₀NotCarrierK
  have hattachmentNotCarrier :
      T.attachment ∉ P.working.rooted.core.carrier := by
    rw [hworking]
    exact K.attachment_not_mem_carrier
  have ht₀Region :
      T.t₀ ∈ P.working.rooted.otherRegion := by
    rw [hworking]
    exact K.t₀_mem_otherRegion
  have hs₀Adj : G.Adj T.t₀ s₀ :=
    T.core.cross_adj T.t₀ T.t₀_mem s₀ hs₀
  have hs₀Region :
      s₀ ∈ P.working.rooted.otherRegion :=
    P.working.rooted.otherRegion_componentRegion.closed
      ht₀Region hs₀Adj hs₀NotCarrier
  have hattachmentRegion :
      T.attachment ∈ P.working.rooted.otherRegion :=
    P.working.rooted.otherRegion_componentRegion.closed
      ht₀Region T.t₀_adj_attachment hattachmentNotCarrier
  have hs₀OldCarrier :
      s₀ ∈ P.orientation.chosen.rooted.core.carrier := by
    rw [T.core_eq]
    simp [Core.carrier, Core.S, Core.T, hs₀]
  have hs₀NeY : s₀ ≠ y := by
    intro h
    exact P.orientation.chosen.rooted.other_root_not_mem
      (h ▸ hs₀OldCarrier)
  have hs₀NeAttachment : s₀ ≠ T.attachment := by
    intro h
    exact
      TypeThreeModificationChoice.attachment_not_mem_original_carrier
        (T := T)
        (h ▸ hs₀OldCarrier)
  have hattachmentNeY : T.attachment ≠ y :=
    attachment_ne_other_root T
  let yE : P.ExteriorVertex :=
    ⟨y, P.working.rooted.other_root_mem_otherRegion⟩
  let sE : P.ExteriorVertex :=
    ⟨s₀, hs₀Region⟩
  let aE : P.ExteriorVertex :=
    ⟨T.attachment, hattachmentRegion⟩
  have hyS : yE ≠ sE := by
    intro h
    exact hs₀NeY (congrArg Subtype.val h).symm
  have hyA : yE ≠ aE := by
    intro h
    exact hattachmentNeY (congrArg Subtype.val h).symm
  have hsA : sE ≠ aE := by
    intro h
    exact hs₀NeAttachment (congrArg Subtype.val h)
  intro hPrime
  have hPrimeY :
      P.exteriorGraph.Adj E.certificate.bPrime yE := by
    change G.Adj E.bPrime y
    rw [hPrime]
    exact T.other_root_adj_t₀.symm
  have hPrimeS :
      P.exteriorGraph.Adj E.certificate.bPrime sE := by
    change G.Adj E.bPrime s₀
    rw [hPrime]
    exact hs₀Adj
  have hPrimeA :
      P.exteriorGraph.Adj E.certificate.bPrime aE := by
    change G.Adj E.bPrime T.attachment
    rw [hPrime]
    exact T.t₀_adj_attachment
  let witnesses : Finset P.ExteriorVertex :=
    {yE, sE, aE}
  have hwitnessesCard : witnesses.card = 3 := by
    simp [witnesses, hyS, hyA, hsA]
  have hwitnessesSubset :
      (↑witnesses : Set P.ExteriorVertex) ⊆
        P.exteriorGraph.neighborSet E.certificate.bPrime := by
    intro v hv
    simp only [witnesses, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact hPrimeY
    · exact hPrimeS
    · exact hPrimeA
  have hdegreeLower :
      3 ≤ finiteDegree P.exteriorGraph E.certificate.bPrime := by
    change
      3 ≤
        (P.exteriorGraph.neighborSet
          E.certificate.bPrime).ncard
    calc
      3 = (↑witnesses : Set P.ExteriorVertex).ncard := by
        rw [Set.ncard_coe_finset, hwitnessesCard]
      _ ≤
          (P.exteriorGraph.neighborSet
            E.certificate.bPrime).ncard :=
        Set.ncard_le_ncard hwitnessesSubset
  omega

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
