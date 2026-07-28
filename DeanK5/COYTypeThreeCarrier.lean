import DeanK5.COYTypeThreeAnchor

/-!
# The singleton-side type-3 carrier

For a type-3 COY core with singleton `S`, the induced carrier itself is
2-connected.  This is the unrooted anchor used when Claim 3.14 deletes the
distinguished exterior component except for `y`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace TypeThreeCore

variable [DecidableEq V]
  {G : SimpleGraph V} {x s : V} {ℓ : ℕ}

/--
The carrier of a type-3 core with singleton `S` is 2-connected.

The two vertices `x,s` have at least two common neighbours in `T`.  Thus
deleting either of them leaves a star, while deleting one vertex of `T`
leaves another common neighbour joining `s` back to `x`.
-/
theorem carrierGraph_two_connected
    (C : TypeThreeCore G x ℓ)
    (hS : C.S = {s}) :
    IsTwoConnected C.carrierGraph := by
  classical
  let hs : s ∈ C.S := by
    rw [hS]
    simp
  let xC : C.Carrier := C.rootVertex
  let sC : C.Carrier := C.sideVertex s hs
  have hxs : x ≠ s := by
    intro h
    exact C.root_not_mem_S (h ▸ hs)
  have hxCsC : xC ≠ sC := by
    intro h
    exact hxs (congrArg Subtype.val h)
  have hrootT :
      ∀ (v : C.Carrier), v.1 ∈ C.T →
        C.carrierGraph.Adj xC v := by
    intro v hvT
    exact C.root_adj_T v.1 hvT
  have hsideT :
      ∀ (v : C.Carrier), v.1 ∈ C.T →
        C.carrierGraph.Adj sC v := by
    intro v hvT
    exact (C.cross_adj v.1 hvT s hs).symm
  have hclassify :
      ∀ v : C.Carrier,
        v = xC ∨ v = sC ∨ v.1 ∈ C.T := by
    intro v
    have hv := v.2
    change v.1 ∈ insert x (C.S ∪ C.T) at hv
    simp only [Finset.mem_insert, Finset.mem_union] at hv
    rcases hv with hvx | hvS | hvT
    · exact Or.inl (Subtype.ext hvx)
    · have hvs : v.1 = s := by
        rw [hS] at hvS
        simpa using hvS
      exact Or.inr (Or.inl (Subtype.ext hvs))
    · exact Or.inr (Or.inr hvT)
  have hTtwo : 2 ≤ C.T.card :=
    (Nat.le_max_right (ℓ + 1) 2).trans C.card_T_lower
  obtain ⟨t₀, ht₀T⟩ := C.T.nonempty_of_ne_empty (by
    intro h
    rw [h] at hTtwo
    simp at hTtwo)
  have ht₀Carrier :
      t₀ ∈ (Core.typeThree C).carrier :=
    (Core.typeThree C).T_subset_carrier
      (by simpa [Core.T] using ht₀T)
  let t₀C : C.Carrier := ⟨t₀, ht₀Carrier⟩
  have horder : 3 ≤ Fintype.card C.Carrier := by
    have hcard :
        Fintype.card C.Carrier =
          (insert x (C.S ∪ C.T)).card := by
      simp [Carrier, Core.carrier, Core.S, Core.T]
    rw [hcard, Finset.card_insert_of_notMem]
    · rw [Finset.card_union_of_disjoint C.disjoint, hS]
      simp only [Finset.card_singleton]
      omega
    · simp only [Finset.mem_union]
      exact not_or_intro C.root_not_mem_S C.root_not_mem_T
  apply isTwoConnected_of_connected_delete_one
      C.carrierGraph horder
  · rw [connected_iff_exists_forall_reachable]
    refine ⟨xC, ?_⟩
    intro v
    rcases hclassify v with hv | hv | hvT
    · subst v
      exact .rfl
    · subst v
      exact
        (hrootT t₀C ht₀T).reachable.trans
          ((hsideT t₀C ht₀T).symm.reachable)
    · exact (hrootT v hvT).reachable
  · intro r
    rcases hclassify r with hrx | hrs | hrT
    · have hsCr : sC ≠ r := by
        intro h
        exact hxCsC (hrx.symm.trans h.symm)
      let sD : {v : C.Carrier // v ≠ r} := ⟨sC, hsCr⟩
      rw [connected_iff_exists_forall_reachable]
      refine ⟨sD, ?_⟩
      intro v
      rcases hclassify v.1 with hvx | hvs | hvT
      · exact False.elim (v.2 (hvx.trans hrx.symm))
      · have hvEq : v = sD := by
          apply Subtype.ext
          exact hvs
        subst v
        exact .rfl
      · exact
          (show
            (C.carrierGraph.induce {w | w ≠ r}).Adj sD v
            from hsideT v.1 hvT).reachable
    · have hxCr : xC ≠ r := by
        intro h
        exact hxCsC (h.trans hrs)
      let xD : {v : C.Carrier // v ≠ r} := ⟨xC, hxCr⟩
      rw [connected_iff_exists_forall_reachable]
      refine ⟨xD, ?_⟩
      intro v
      rcases hclassify v.1 with hvx | hvs | hvT
      · have hvEq : v = xD := by
          apply Subtype.ext
          exact hvx
        subst v
        exact .rfl
      · exact False.elim (v.2 (hvs.trans hrs.symm))
      · exact
          (show
            (C.carrierGraph.induce {w | w ≠ r}).Adj xD v
            from hrootT v.1 hvT).reachable
    · have hTwithout : (C.T.erase r.1).Nonempty := by
        rw [← Finset.card_pos]
        rw [Finset.card_erase_of_mem hrT]
        omega
      obtain ⟨t₁, ht₁Erase⟩ := hTwithout
      have ht₁T : t₁ ∈ C.T :=
        Finset.mem_of_mem_erase ht₁Erase
      have ht₁Ne : t₁ ≠ r.1 :=
        (Finset.mem_erase.mp ht₁Erase).1
      have ht₁Carrier :
          t₁ ∈ (Core.typeThree C).carrier :=
        (Core.typeThree C).T_subset_carrier
          (by simpa [Core.T] using ht₁T)
      let t₁C : C.Carrier := ⟨t₁, ht₁Carrier⟩
      have ht₁Cr : t₁C ≠ r := by
        intro h
        exact ht₁Ne (congrArg Subtype.val h)
      have hxCr : xC ≠ r := by
        intro h
        have hval : x = r.1 :=
          congrArg Subtype.val h
        have hxT : x ∈ C.T := by
          simpa [hval] using hrT
        exact C.root_not_mem_T hxT
      let xD : {v : C.Carrier // v ≠ r} := ⟨xC, hxCr⟩
      let t₁D : {v : C.Carrier // v ≠ r} := ⟨t₁C, ht₁Cr⟩
      rw [connected_iff_exists_forall_reachable]
      refine ⟨xD, ?_⟩
      intro v
      rcases hclassify v.1 with hvx | hvs | hvT
      · have hvEq : v = xD := by
          apply Subtype.ext
          exact hvx
        subst v
        exact .rfl
      · have hxt₁ :
            (C.carrierGraph.induce {w | w ≠ r}).Adj xD t₁D :=
          hrootT t₁C ht₁T
        have ht₁s :
            (C.carrierGraph.induce {w | w ≠ r}).Adj t₁D v := by
          change C.carrierGraph.Adj t₁C v.1
          simpa [hvs] using (hsideT t₁C ht₁T).symm
        exact hxt₁.reachable.trans ht₁s.reachable
      · exact
          (show
            (C.carrierGraph.induce {w | w ≠ r}).Adj xD v
            from hrootT v.1 hvT).reachable

end TypeThreeCore

end COY

end DeanK5
