import DeanK5.COYSingletonExteriorOtherComponents

/-!
# The type-three singleton-exterior endgame

This file formalizes COY Case 1.3.  We first isolate the numerical
consequence of Fact 3 that drives Claim 3.7: in the singleton-exterior
case, the selected type-3 core has a `T`-attachment through the other root,
so its rank is at most two below the requested path-family size.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace BoundaryCompression

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Q T : Finset V} {t : V}

/-- A lifted two-edge outer family together with its exact support classes. -/
structure LiftedOuterTwoEdgeData
    (G : SimpleGraph V) (Q T : Finset V)
    (t m y : V) (s : ℕ) where
  /-- The lifted family after adjoining the fixed connector `t-m-y`. -/
  family :
    SemiAdmissibleSetPathFamily G
      (↑(T.erase t) : Set V) y s
  /-- Every used vertex belongs to one of the five advertised classes. -/
  support_class :
    ∀ i v, v ∈ (family.path i).walk.support →
      v = family.endpoint i ∨ v = t ∨
        v ∈ Q ∨ v = m ∨ v = y

/--
Lift a recursive compression family and append a fixed two-edge connector
`t-m-y`.  This is the outer family used in COY Claim 3.7.
-/
theorem exists_lifted_outer_twoEdgeData
    (hQT : Disjoint Q T) (ht : t ∈ T)
    {m y : V}
    (hmQ : m ∉ Q) (hmT : m ∉ T)
    (hyQ : y ∉ Q) (hyT : y ∉ T)
    (htm : G.Adj t m) (hmy : G.Adj m y)
    {s : ℕ}
    (F : AdmissiblePathFamily
      (graph G Q T t)
      (collapsedRoot : BoundaryCompressionVertex Q)
      retainedRoot s) :
    Nonempty
      (LiftedOuterTwoEdgeData G Q T t m y s) := by
  classical
  have hty : t ≠ y := by
    intro h
    exact hyT (h ▸ ht)
  let connector : SimplePath G t y :=
    SimplePath.ofVertexList [m]
      (by simp [htm, hmy])
      (by simp [htm.ne, hmy.ne, hty])
  let L (i : Fin s) :
      PathLift G Q T t (F.path i) :=
    Classical.choice
      (exists_pathLift hQT ht (F.path i))
  have hmLift (i : Fin s) :
      m ∉ (L i).path.walk.support := by
    intro hm
    rcases (L i).support_class m hm with
      hEndpoint | hretained | hmQ'
    · exact hmT
        (Finset.mem_of_mem_erase
          (hEndpoint ▸ (L i).endpoint_mem))
    · exact hmT (hretained ▸ ht)
    · exact hmQ hmQ'
  have hyLift (i : Fin s) :
      y ∉ (L i).path.walk.support := by
    intro hy
    rcases (L i).support_class y hy with
      hEndpoint | hretained | hyQ'
    · exact hyT
        (Finset.mem_of_mem_erase
          (hEndpoint ▸ (L i).endpoint_mem))
    · exact hyT (hretained ▸ ht)
    · exact hyQ hyQ'
  have hdisjoint (i : Fin s) :
      (L i).path.walk.support.Disjoint
        connector.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvLift hvConnector
    have hv : v = m ∨ v = y := by
      simpa [connector] using hvConnector
    rcases hv with rfl | rfl
    · exact hmLift i hvLift
    · exact hyLift i hvLift
  let P (i : Fin s) :
      SimplePath G (L i).endpoint y :=
    (L i).path.appendDisjoint connector (hdisjoint i)
  let outer :
      SemiAdmissibleSetPathFamily G
        (↑(T.erase t) : Set V) y s := {
    start := F.start + 2
    step := F.step
    admissible_step := F.admissible_step
    start_ge_one := by
      have := F.start_ge_two
      omega
    endpoint := fun i => (L i).endpoint
    endpoint_mem := fun i => (L i).endpoint_mem
    path := P
    length_path := by
      intro i
      calc
        (P i).length =
            (L i).path.length + connector.length := by
          simp [P, SimplePath.appendDisjoint_length]
        _ = (F.path i).length + 2 := by
          rw [(L i).length_eq]
          simp [connector]
        _ = (F.start + i.val * F.step) + 2 := by
          rw [F.length_path i]
        _ = F.start + 2 + i.val * F.step := by
          omega
    unique_endpoint := by
      intro i v hvPath hvErase
      have hvParts :
          v ∈ (L i).path.walk.support ∨
            v ∈ connector.walk.support.tail := by
        change v ∈
          (((L i).path.appendDisjoint
            connector (hdisjoint i)).walk.support) at hvPath
        rw [SimplePath.appendDisjoint,
          SimpleGraph.Walk.support_append] at hvPath
        exact List.mem_append.mp hvPath
      rcases hvParts with hvLift | hvConnector
      · rcases (L i).support_meets_T v hvLift
            (Finset.mem_of_mem_erase hvErase) with
          hvEndpoint | hvt
        · exact hvEndpoint
        · exact False.elim
            ((Finset.mem_erase.mp hvErase).1 hvt)
      · have hv : v = m ∨ v = y := by
          simpa [connector] using hvConnector
        rcases hv with rfl | rfl
        · exact False.elim
            (hmT (Finset.mem_of_mem_erase hvErase))
        · exact False.elim
            (hyT (Finset.mem_of_mem_erase hvErase))
  }
  refine ⟨{
    family := outer
    support_class := ?_
  }⟩
  intro i v hvPath
  have hvPath' :
      v ∈ (P i).walk.support := by
    simpa [outer] using hvPath
  have hvParts :
      v ∈ (L i).path.walk.support ∨
        v ∈ connector.walk.support.tail := by
    change v ∈
      (((L i).path.appendDisjoint
        connector (hdisjoint i)).walk.support) at hvPath'
    rw [SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hvPath'
    exact List.mem_append.mp hvPath'
  rcases hvParts with hvLift | hvConnector
  · rcases (L i).support_class v hvLift with
      hvEndpoint | hvt | hvQ
    · exact Or.inl (by simpa [outer] using hvEndpoint)
    · exact Or.inr (Or.inl hvt)
    · exact Or.inr (Or.inr (Or.inl hvQ))
  · have hv : v = m ∨ v = y := by
      simpa [connector] using hvConnector
    rcases hv with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- Forget the support certificate when only the two-edge family is needed. -/
theorem exists_lifted_outer_family_two_edges
    (hQT : Disjoint Q T) (ht : t ∈ T)
    {m y : V}
    (hmQ : m ∉ Q) (hmT : m ∉ T)
    (hyQ : y ∉ Q) (hyT : y ∉ T)
    (htm : G.Adj t m) (hmy : G.Adj m y)
    {s : ℕ}
    (F : AdmissiblePathFamily
      (graph G Q T t)
      (collapsedRoot : BoundaryCompressionVertex Q)
      retainedRoot s) :
    Nonempty
      (SemiAdmissibleSetPathFamily G
        (↑(T.erase t) : Set V) y s) := by
  obtain ⟨L⟩ :=
    exists_lifted_outer_twoEdgeData
      hQT ht hmQ hmT hyQ hyT htm hmy F
  exact ⟨L.family⟩

end BoundaryCompression

namespace PreferredOrientationData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
In a type-3 optimal core the root has no neighbor in `S`.  Such a neighbor,
together with any vertex of the nonempty set `T`, would form a rooted
type-1 core and contradict type minimality.
-/
theorem not_adj_root_S_of_typeThree
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    {s : V} (hs : s ∈ C.S) :
    ¬G.Adj x s := by
  intro hxs
  have hTNonempty : C.T.Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.lt_of_lt_of_le (by omega)
      ((Nat.le_max_right (D.chosen.rank + 1) 2).trans
        C.card_T_lower)
  obtain ⟨t, ht⟩ := hTNonempty
  have hxt : G.Adj x t :=
    C.root_adj_T t ht
  have hst : G.Adj s t :=
    (C.cross_adj t ht s hs).symm
  have hxsNe : x ≠ s := by
    intro h
    exact C.root_not_mem_S (h ▸ hs)
  have hxtNe : x ≠ t := by
    intro h
    exact C.root_not_mem_T (h ▸ ht)
  have hstNe : s ≠ t := by
    intro h
    exact Finset.disjoint_left.mp C.disjoint
      hs (h ▸ ht)
  have hyx : y ≠ x := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    exact h.symm ▸ D.chosen.rooted.core.root_mem_carrier
  have hys : y ≠ s := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    have hsCarrier :
        s ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).S_subset_carrier
        (by simpa [Core.S] using hs)
    exact h.symm ▸ hsCarrier
  have hyt : y ≠ t := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    have htCarrier :
        t ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using ht)
    exact h.symm ▸ htCarrier
  let C₁ : TypeOneCore G x 1 := {
    T := {s, t}
    rank_pos := le_rfl
    card_T := by simp [hstNe]
    root_not_mem := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxsNe, hxtNe⟩
    root_adj := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxs
      · exact hxt
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show s ≠ t → G.Adj s t from fun _ => hst)
  }
  let R₁ : RootedCore G x y 1 := {
    core := .typeOne C₁
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C₁,
        hyx, hys, hyt]
  }
  have hminimal := D.chosen.type_minimal R₁
  rw [hcore] at hminimal
  change 3 ≤ 1 at hminimal
  omega

/--
The strong half of COY Fact 3 in the natural type-3 singleton-exterior
case.  The singleton `{y}` has a `T`-attachment because Claim 3.5
identifies `N(y)` with `T`.
-/
theorem rank_add_one_lt_of_typeThree_singleton
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C) :
    D.chosen.rank + 1 < q := by
  have hneighbors :=
    D.neighborSets_eq_T_of_natural_singleton
      M hnot hregion (Or.inr (by
        rw [hcore]
        rfl))
  have hTNonempty : C.T.Nonempty := by
    rw [← Finset.card_pos]
    have htwo :
        2 ≤ C.T.card :=
      (Nat.le_max_right (D.chosen.rank + 1) 2).trans
        C.card_T_lower
    omega
  obtain ⟨t, htT⟩ := hTNonempty
  have htCoreT :
      t ∈ D.chosen.rooted.core.T := by
    rw [hcore]
    exact htT
  have hyt : G.Adj y t := by
    have htNeighbor :
        t ∈ G.neighborSet y := by
      rw [hneighbors.2]
      simpa using htCoreT
    simpa [SimpleGraph.mem_neighborSet] using htNeighbor
  have hregion' :
      D.chosen.rooted.otherRegion = {y} := by
    exact hregion
  have hattach :
      D.chosen.rooted.core.HasTAttachment
        D.chosen.rooted.otherRegion := by
    refine ⟨y, ?_, t, htCoreT, hyt.symm⟩
    rw [hregion']
    simp
  exact
    (M.rootedCore_factThree D.chosen.rooted).2 hattach

/--
The equality calculation in the first half of COY Claim 3.7, localized at
one `T`-vertex distinct from the exception.
-/
private theorem closed_boundary_data_at_T
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (hstrong : D.chosen.rank + 1 < q)
    (hclosed :
      ∀ t ∈ C.T, ∀ v, G.Adj t v →
        v ∈ D.chosen.rooted.core.carrier ∨ v = y ∨ v = z)
    {t : V} (ht : t ∈ C.T) (htz : t ≠ z) :
    D.chosen.rank + 2 = q ∧
      z ≠ x ∧ z ≠ y ∧ z ∉ C.S ∧ z ∉ C.T ∧
        G.Adj t z := by
  classical
  let A : Finset V := C.S ∪ {x, y, z}
  have htx : t ≠ x := by
    intro h
    exact C.root_not_mem_T (h ▸ ht)
  have hty : t ≠ y := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    have htCarrier :
        t ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using ht)
    exact h.symm ▸ htCarrier
  have hneighborSubset :
      G.neighborSet t ⊆ (↑A : Set V) := by
    intro v hv
    have htv : G.Adj t v := by
      simpa [SimpleGraph.mem_neighborSet] using hv
    rcases hclosed t ht v htv with
      hvCarrier | rfl | rfl
    · have hvClass :
          v = x ∨ v ∈ C.S ∨ v ∈ C.T := by
        rw [hcore] at hvCarrier
        simpa [Core.carrier, Core.S, Core.T] using hvCarrier
      rcases hvClass with rfl | hvS | hvT
      · simp [A]
      · simp [A, hvS]
      · have hne : t ≠ v := htv.ne
        exact False.elim
          ((C.independent_T
              (by simpa using ht)
              (by simpa using hvT) hne) htv)
    · simp [A]
    · simp [A]
  have hdegreeUpper :
      finiteDegree G t ≤ A.card := by
    unfold finiteDegree
    calc
      (G.neighborSet t).ncard ≤ (↑A : Set V).ncard :=
        Set.ncard_le_ncard hneighborSubset
      _ = A.card := Set.ncard_coe_finset A
  have hdegreeLower :
      q + 1 ≤ finiteDegree G t :=
    M.degree_lower t htx hty htz
  have htripleCard :
      ({x, y, z} : Finset V).card ≤ 3 := by
    calc
      ({x, y, z} : Finset V).card ≤
          ({y, z} : Finset V).card + 1 :=
        Finset.card_insert_le x {y, z}
      _ ≤ ({z} : Finset V).card + 2 := by
        have h := Finset.card_insert_le y {z}
        omega
      _ = 3 := by simp
  have hAcardUpper :
      A.card ≤ D.chosen.rank + 3 := by
    calc
      A.card ≤ C.S.card + ({x, y, z} : Finset V).card :=
        Finset.card_union_le C.S {x, y, z}
      _ ≤ D.chosen.rank + 3 := by
        rw [C.card_S]
        omega
  have hrankEq :
      D.chosen.rank + 2 = q := by
    omega
  have hAcard :
      A.card = D.chosen.rank + 3 := by
    omega
  have hneighborEq :
      G.neighborSet t = (↑A : Set V) := by
    apply Set.eq_of_subset_of_ncard_le hneighborSubset
    rw [Set.ncard_coe_finset, hAcard]
    unfold finiteDegree at hdegreeLower hdegreeUpper
    omega
  have htzAdj : G.Adj t z := by
    have hzNeighbor :
        z ∈ G.neighborSet t := by
      rw [hneighborEq]
      simp [A]
    simpa [SimpleGraph.mem_neighborSet] using hzNeighbor
  have htripleCardEq :
      ({x, y, z} : Finset V).card = 3 := by
    have hUnion :=
      Finset.card_union_le C.S ({x, y, z} : Finset V)
    dsimp [A] at hAcard
    rw [C.card_S] at hUnion
    omega
  have hzx : z ≠ x := by
    intro h
    have hsubset :
        ({x, y, z} : Finset V) ⊆ {x, y} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hpair :
        ({x, y} : Finset V).card ≤ 2 := by
      calc
        ({x, y} : Finset V).card ≤
            ({y} : Finset V).card + 1 :=
          Finset.card_insert_le x {y}
        _ = 2 := by simp
    have := Finset.card_le_card hsubset
    omega
  have hzy : z ≠ y := by
    intro h
    have hsubset :
        ({x, y, z} : Finset V) ⊆ {x, y} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hpair :
        ({x, y} : Finset V).card ≤ 2 := by
      calc
        ({x, y} : Finset V).card ≤
            ({y} : Finset V).card + 1 :=
          Finset.card_insert_le x {y}
        _ = 2 := by simp
    have := Finset.card_le_card hsubset
    omega
  have hzS : z ∉ C.S := by
    intro hzS
    have hsubset :
        A ⊆ C.S ∪ {x, y} := by
      intro v hv
      change v ∈ C.S ∪ {x, y, z} at hv
      simp only [Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hv ⊢
      aesop
    have hsmall :
        (C.S ∪ {x, y}).card ≤ D.chosen.rank + 2 := by
      calc
        (C.S ∪ {x, y}).card ≤
            C.S.card + ({x, y} : Finset V).card :=
          Finset.card_union_le C.S {x, y}
        _ ≤ D.chosen.rank + 2 := by
          rw [C.card_S]
          have hpair := Finset.card_insert_le x {y}
          simp only [Finset.card_singleton] at hpair
          omega
    have := Finset.card_le_card hsubset
    omega
  have hzT : z ∉ C.T := by
    intro hzT
    exact
      (C.independent_T
        (by simpa using ht)
        (by simpa using hzT) htz) htzAdj
  exact ⟨hrankEq, hzx, hzy, hzS, hzT, htzAdj⟩

/--
The rigidity forced when no vertex of `T` sees an ordinary vertex outside
the core.  This packages the equality case used in COY Claim 3.7.
-/
structure TypeThreeClosedBoundaryRigidity
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank) : Prop where
  rank_add_two_eq : D.chosen.rank + 2 = q
  exception_ne_left : z ≠ x
  exception_ne_right : z ≠ y
  exception_not_mem_S : z ∉ C.S
  exception_not_mem_T : z ∉ C.T
  exception_not_mem_carrier :
    z ∉ D.chosen.rooted.core.carrier
  exception_adj_T :
    ∀ t ∈ C.T, G.Adj t z

namespace TypeThreeClosedBoundaryRigidity

variable
  {D : PreferredOrientationData G x y z}
  {C : TypeThreeCore G x D.chosen.rank}

/--
The two inner paths used at the end of COY Claim 3.7.  In the bounded
case the preceding equalities force rank two.  After deleting one vertex
from each side, the exception replaces the deleted `S`-vertex in the
four-edge alternating path.
-/
noncomputable def innerPathsForClaim37
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C)
    (hrank : D.chosen.rank = 2)
    (hcardT : C.T.card = 3)
    (s₀ target t₀ : V)
    (htarget : target ∈ C.S.erase s₀)
    (ht₀ : t₀ ∈ C.T) :
    AdmissiblePathFamily G x target 2 := by
  classical
  have hremaining :
      (C.T.erase t₀).card = 2 := by
    rw [Finset.card_erase_of_mem ht₀, hcardT]
  let t : Fin 2 ↪ V :=
    finsetEmbeddingOfCardEq
      (C.T.erase t₀) hremaining
  have ht (i : Fin 2) :
      t i ∈ C.T.erase t₀ :=
    finsetEmbeddingOfCardEq_mem
      (C.T.erase t₀) hremaining i
  have htT (i : Fin 2) : t i ∈ C.T :=
    Finset.mem_of_mem_erase (ht i)
  have htargetS : target ∈ C.S :=
    Finset.mem_of_mem_erase htarget
  have hxt (i : Fin 2) : G.Adj x (t i) :=
    C.root_adj_T (t i) (htT i)
  have httarget (i : Fin 2) :
      G.Adj (t i) target :=
    C.cross_adj (t i) (htT i) target htargetS
  have htz (i : Fin 2) :
      G.Adj (t i) z :=
    R.exception_adj_T (t i) (htT i)
  have ht01 : t (0 : Fin 2) ≠ t (1 : Fin 2) :=
    t.injective.ne (by decide)
  have hxTarget : x ≠ target := by
    intro h
    exact C.root_not_mem_S (h ▸ htargetS)
  have hxT (i : Fin 2) : x ≠ t i :=
    (hxt i).ne
  have hTtarget (i : Fin 2) :
      t i ≠ target :=
    (httarget i).ne
  have htargetT (i : Fin 2) :
      target ≠ t i :=
    (hTtarget i).symm
  have hzTarget : z ≠ target := by
    intro h
    exact R.exception_not_mem_S (h ▸ htargetS)
  have hTz (i : Fin 2) : t i ≠ z :=
    (htz i).ne
  have hzT (i : Fin 2) : z ≠ t i :=
    (hTz i).symm
  have hxz : x ≠ z :=
    R.exception_ne_left.symm
  let p₂ : SimplePath G x target :=
    SimplePath.ofVertexList [t 0]
      (by simp [hxt, httarget])
      (by simp [hxTarget, hxT, hTtarget])
  let p₄ : SimplePath G x target :=
    SimplePath.ofVertexList [t 0, z, t 1]
      (by
        simp [hxt, htz, httarget, Adj.symm])
      (by
        simp [hxTarget, hxz, hxT, hTz, hzT,
          hzTarget, hTtarget, ht01])
  exact {
    start := 2
    step := 2
    admissible_step := Or.inr rfl
    start_ge_two := le_rfl
    path := ![p₂, p₄]
    length_path := by
      intro i
      fin_cases i <;> simp [p₂, p₄]
  }

/-- Every inner path above stays in the advertised reduced support. -/
theorem innerPathsForClaim37_support
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C)
    (hrank : D.chosen.rank = 2)
    (hcardT : C.T.card = 3)
    (s₀ target t₀ : V)
    (htarget : target ∈ C.S.erase s₀)
    (ht₀ : t₀ ∈ C.T)
    (i : Fin 2) {v : V}
    (hv :
      v ∈ ((R.innerPathsForClaim37
        hrank hcardT s₀ target t₀ htarget ht₀).path i
          ).walk.support) :
    v = x ∨ v = target ∨ v = z ∨
      v ∈ C.T.erase t₀ := by
  classical
  have hremaining :
      (C.T.erase t₀).card = 2 := by
    rw [Finset.card_erase_of_mem ht₀, hcardT]
  let e : Fin 2 ↪ V :=
    finsetEmbeddingOfCardEq
      (C.T.erase t₀) hremaining
  have he (j : Fin 2) :
      e j ∈ C.T.erase t₀ :=
    finsetEmbeddingOfCardEq_mem
      (C.T.erase t₀) hremaining j
  fin_cases i
  · have hv' :
        v = x ∨ v = e 0 ∨ v = target := by
      simpa [innerPathsForClaim37, e,
        SimplePath.ofVertexList_support] using hv
    rcases hv' with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (he 0)))
    · exact Or.inr (Or.inl rfl)
  · have hv' :
        v = x ∨ v = e 0 ∨ v = z ∨
          v = e 1 ∨ v = target := by
      simpa [innerPathsForClaim37, e,
        SimplePath.ofVertexList_support] using hv
    rcases hv' with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (he 0)))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (he 1)))
    · exact Or.inr (Or.inl rfl)

end TypeThreeClosedBoundaryRigidity

/--
The exact component asserted by COY Claim 3.7: it differs from the
singleton component containing `y`, contains an ordinary vertex, and has
an attachment in the type-3 core's `T`-side.
-/
structure TypeThreeOtherComponentWitness
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank) where
  /-- The deletion component distinct from the one containing `y`. -/
  component :
    (deleteVertices G
      D.chosen.rooted.core.carrier).ConnectedComponent
  /-- The selected component is not the distinguished exterior component. -/
  component_ne_other :
    component ≠ D.chosen.rooted.otherComponent
  /-- A nonexceptional vertex certifying that the component is ordinary. -/
  ordinary : V
  /-- The ordinary witness lies in the selected component. -/
  ordinary_mem :
    ordinary ∈ componentVertices G
      D.chosen.rooted.core.carrier component
  /-- The ordinary witness is not the exceptional vertex. -/
  ordinary_ne_exception : ordinary ≠ z
  /-- The component vertex incident with the certified `T`-attachment. -/
  attachment : V
  /-- The attachment endpoint lies in the selected component. -/
  attachment_mem :
    attachment ∈ componentVertices G
      D.chosen.rooted.core.carrier component
  /-- The core endpoint of the attachment edge. -/
  terminal : V
  /-- The core endpoint belongs to the type-3 side `T`. -/
  terminal_mem : terminal ∈ C.T
  /-- The terminal and component endpoints form the attachment edge. -/
  terminal_adj_attachment : G.Adj terminal attachment

/--
The `S`-attached component produced in the second half of the contradiction
argument for Claim 3.7.
-/
structure TypeThreeSComponentWitness
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank) where
  /-- The deletion component carrying the `S`-attachment. -/
  component :
    (deleteVertices G
      D.chosen.rooted.core.carrier).ConnectedComponent
  /-- The component differs from the one containing `y`. -/
  component_ne_other :
    component ≠ D.chosen.rooted.otherComponent
  /-- A nonexceptional vertex in the selected component. -/
  ordinary : V
  /-- The ordinary witness lies in the selected component. -/
  ordinary_mem :
    ordinary ∈ componentVertices G
      D.chosen.rooted.core.carrier component
  /-- The ordinary witness is not the exceptional vertex. -/
  ordinary_ne_exception : ordinary ≠ z
  /-- The component endpoint of the `S`-attachment edge. -/
  attachment : V
  /-- The attachment endpoint lies in the selected component. -/
  attachment_mem :
    attachment ∈ componentVertices G
      D.chosen.rooted.core.carrier component
  /-- The core endpoint of the attachment edge. -/
  initial : V
  /-- The core endpoint belongs to the type-3 side `S`. -/
  initial_mem : initial ∈ C.S
  /-- The initial and component endpoints form the attachment edge. -/
  initial_adj_attachment : G.Adj initial attachment

/--
A nonprotected `T`-neighbor outside the core immediately gives the
component required by Claim 3.7.
-/
noncomputable def typeThreeOtherComponentWitnessOfTNeighbor
    (D : PreferredOrientationData G x y z)
    (hregion : D.chosen.rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    {t v : V}
    (ht : t ∈ C.T)
    (htv : G.Adj t v)
    (hvCarrier : v ∉ D.chosen.rooted.core.carrier)
    (hvy : v ≠ y) (hvz : v ≠ z) :
    TypeThreeOtherComponentWitness D C := by
  classical
  let vD :
      {w : V // w ∉ D.chosen.rooted.core.carrier} :=
    ⟨v, hvCarrier⟩
  let K :=
    (deleteVertices G
      D.chosen.rooted.core.carrier).connectedComponentMk vD
  have hvK :
      v ∈ componentVertices G
        D.chosen.rooted.core.carrier K := by
    apply (mem_componentVertices_iff
      G D.chosen.rooted.core.carrier K v).2
    exact ⟨hvCarrier,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hKne :
      K ≠ D.chosen.rooted.otherComponent := by
    intro hK
    have hvOther :
        v ∈ D.chosen.rooted.otherRegion := by
      change v ∈ componentVertices G
        D.chosen.rooted.core.carrier
          D.chosen.rooted.otherComponent
      exact hK ▸ hvK
    rw [hregion] at hvOther
    exact hvy (by simpa using hvOther)
  exact {
    component := K
    component_ne_other := hKne
    ordinary := v
    ordinary_mem := hvK
    ordinary_ne_exception := hvz
    attachment := v
    attachment_mem := hvK
    terminal := t
    terminal_mem := ht
    terminal_adj_attachment := htv
  }

/--
Negating the component conclusion of Claim 3.7 says precisely that every
`T`-neighbor outside the core is one of the two protected exterior
vertices.
-/
theorem closed_T_boundary_of_no_otherComponentWitness
    (D : PreferredOrientationData G x y z)
    (hregion : D.chosen.rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hno :
      ¬Nonempty (TypeThreeOtherComponentWitness D C)) :
    ∀ t ∈ C.T, ∀ v, G.Adj t v →
      v ∈ D.chosen.rooted.core.carrier ∨ v = y ∨ v = z := by
  intro t ht v htv
  by_cases hvCarrier :
      v ∈ D.chosen.rooted.core.carrier
  · exact Or.inl hvCarrier
  by_cases hvy : v = y
  · exact Or.inr (Or.inl hvy)
  by_cases hvz : v = z
  · exact Or.inr (Or.inr hvz)
  exact False.elim
    (hno ⟨D.typeThreeOtherComponentWitnessOfTNeighbor
      hregion C ht htv hvCarrier hvy hvz⟩)

/--
Once the exception lies outside the core and is adjacent to `T`, any edge
from it to another exterior vertex also yields the component in Claim 3.7.
The ordinary witness is the other endpoint, while the exception itself is
the certified `T`-attachment vertex.
-/
noncomputable def typeThreeOtherComponentWitnessOfExceptionEdge
    (D : PreferredOrientationData G x y z)
    (hregion : D.chosen.rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C)
    {t v : V}
    (ht : t ∈ C.T)
    (hzv : G.Adj z v)
    (hvCarrier : v ∉ D.chosen.rooted.core.carrier) :
    TypeThreeOtherComponentWitness D C := by
  classical
  let zD :
      {w : V // w ∉ D.chosen.rooted.core.carrier} :=
    ⟨z, R.exception_not_mem_carrier⟩
  let vD :
      {w : V // w ∉ D.chosen.rooted.core.carrier} :=
    ⟨v, hvCarrier⟩
  let K :=
    (deleteVertices G
      D.chosen.rooted.core.carrier).connectedComponentMk zD
  have hzK :
      z ∈ componentVertices G
        D.chosen.rooted.core.carrier K := by
    apply (mem_componentVertices_iff
      G D.chosen.rooted.core.carrier K z).2
    exact ⟨R.exception_not_mem_carrier,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hzSupp :
      zD ∈ K.supp := by
    exact
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hzvD :
      (deleteVertices G
        D.chosen.rooted.core.carrier).Adj zD vD :=
    hzv
  have hvSupp :
      vD ∈ K.supp :=
    K.mem_supp_of_adj_mem_supp hzSupp hzvD
  have hvK :
      v ∈ componentVertices G
        D.chosen.rooted.core.carrier K := by
    apply (mem_componentVertices_iff
      G D.chosen.rooted.core.carrier K v).2
    exact ⟨hvCarrier, by simpa [vD] using hvSupp⟩
  have hKne :
      K ≠ D.chosen.rooted.otherComponent := by
    intro hK
    have hzOther :
        z ∈ D.chosen.rooted.otherRegion := by
      change z ∈ componentVertices G
        D.chosen.rooted.core.carrier
          D.chosen.rooted.otherComponent
      exact hK ▸ hzK
    rw [hregion] at hzOther
    exact R.exception_ne_right
      (by simpa using hzOther)
  exact {
    component := K
    component_ne_other := hKne
    ordinary := v
    ordinary_mem := hvK
    ordinary_ne_exception := hzv.ne.symm
    attachment := z
    attachment_mem := hzK
    terminal := t
    terminal_mem := ht
    terminal_adj_attachment :=
      R.exception_adj_T t ht
  }

/--
If every neighbor of every `T`-vertex lies in the core or is protected,
the degree bound is sharp: `rank=q-2`, the exception lies outside the
core, and it is adjacent to all of `T`.
-/
theorem typeThree_closed_boundary_rigidity
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (hclosed :
      ∀ t ∈ C.T, ∀ v, G.Adj t v →
        v ∈ D.chosen.rooted.core.carrier ∨ v = y ∨ v = z) :
    TypeThreeClosedBoundaryRigidity
      (q := q) D C := by
  classical
  have hstrong :=
    D.rank_add_one_lt_of_typeThree_singleton
      M hnot hregion C hcore
  have htwo :
      2 ≤ C.T.card :=
    (Nat.le_max_right (D.chosen.rank + 1) 2).trans
      C.card_T_lower
  obtain ⟨t, ht, htz⟩ :
      ∃ t, t ∈ C.T ∧ t ≠ z := by
    by_contra hnone
    push Not at hnone
    have hsubset :
        C.T ⊆ {z} := by
      intro v hv
      simp [hnone v hv]
    have hcard :=
      Finset.card_le_card hsubset
    simp only [Finset.card_singleton] at hcard
    omega
  have hdata :=
    D.closed_boundary_data_at_T
      M C hcore hstrong hclosed ht htz
  have hzCarrier :
      z ∉ D.chosen.rooted.core.carrier := by
    rw [hcore]
    simp only [Core.carrier, Core.S, Core.T,
      Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hdata.2.1, hdata.2.2.2.1,
      hdata.2.2.2.2.1⟩
  have hAdjAll :
      ∀ u ∈ C.T, G.Adj u z := by
    intro u hu
    have huz : u ≠ z := by
      intro h
      exact hdata.2.2.2.2.1 (h ▸ hu)
    exact
      (D.closed_boundary_data_at_T
        M C hcore hstrong hclosed hu huz).2.2.2.2.2
  exact {
    rank_add_two_eq := hdata.1
    exception_ne_left := hdata.2.1
    exception_ne_right := hdata.2.2.1
    exception_not_mem_S := hdata.2.2.2.1
    exception_not_mem_T := hdata.2.2.2.2.1
    exception_not_mem_carrier := hzCarrier
    exception_adj_T := hAdjAll
  }

/--
Under the closed-boundary equality, the exception is nonadjacent to `S`.
Otherwise two vertices of `T`, together with the edge from the exception
to `S`, form a rooted type-2 core, contradicting type minimality.
-/
theorem not_adj_exception_S_of_closed_boundary
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C)
    {s : V} (hs : s ∈ C.S) :
    ¬G.Adj z s := by
  intro hzs
  have htwo :
      1 < C.T.card := by
    exact Nat.lt_of_lt_of_le (by omega)
      ((Nat.le_max_right (D.chosen.rank + 1) 2).trans
        C.card_T_lower)
  obtain ⟨t₁, ht₁, t₂, ht₂, htne⟩ :=
    Finset.one_lt_card.mp htwo
  have hxt₁ : G.Adj x t₁ :=
    C.root_adj_T t₁ ht₁
  have hxt₂ : G.Adj x t₂ :=
    C.root_adj_T t₂ ht₂
  have ht₁z : G.Adj t₁ z :=
    R.exception_adj_T t₁ ht₁
  have ht₂z : G.Adj t₂ z :=
    R.exception_adj_T t₂ ht₂
  have ht₁s : G.Adj t₁ s :=
    C.cross_adj t₁ ht₁ s hs
  have ht₂s : G.Adj t₂ s :=
    C.cross_adj t₂ ht₂ s hs
  have hzsNe : z ≠ s := hzs.ne
  have ht₁zNe : t₁ ≠ z := ht₁z.ne
  have ht₂zNe : t₂ ≠ z := ht₂z.ne
  have ht₁sNe : t₁ ≠ s := ht₁s.ne
  have ht₂sNe : t₂ ≠ s := ht₂s.ne
  let C₂ : TypeTwoCore G x 2 := {
    S := {t₁, t₂}
    T := {z, s}
    rank_ge_two := le_rfl
    card_S := by simp [htne]
    card_T := by simp [hzsNe]
    disjoint := by
      rw [Finset.disjoint_left]
      intro v hvS hvT
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hvS hvT
      rcases hvS with rfl | rfl <;>
        rcases hvT with rfl | rfl
      · exact ht₁zNe rfl
      · exact ht₁sNe rfl
      · exact ht₂zNe rfl
      · exact ht₂sNe rfl
    root_not_mem_S := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨
        fun h => C.root_not_mem_T (h ▸ ht₁),
        fun h => C.root_not_mem_T (h ▸ ht₂)⟩
    root_not_mem_T := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨R.exception_ne_left.symm,
        fun h => C.root_not_mem_S (h ▸ hs)⟩
    independent_S := by
      intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;>
        rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact C.independent_T
          (by simpa using ht₁)
          (by simpa using ht₂) htne
      · intro hadj
        exact C.independent_T
          (by simpa using ht₁)
          (by simpa using ht₂) htne hadj.symm
      · exact False.elim (hab rfl)
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show z ≠ s → G.Adj z s from fun _ => hzs)
    root_adj_S := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hxt₁
      · exact hxt₂
    cross_adj := by
      intro t ht v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht hv
      rcases ht with rfl | rfl <;>
        rcases hv with rfl | rfl
      · exact ht₁z
      · exact ht₁s
      · exact ht₂z
      · exact ht₂s
  }
  have hyt₁ : y ≠ t₁ := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    have htCarrier :
        t₁ ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using ht₁)
    exact h.symm ▸ htCarrier
  have hyt₂ : y ≠ t₂ := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    have htCarrier :
        t₂ ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using ht₂)
    exact h.symm ▸ htCarrier
  have hys : y ≠ s := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    have hsCarrier :
        s ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).S_subset_carrier
        (by simpa [Core.S] using hs)
    exact h.symm ▸ hsCarrier
  have hyx : y ≠ x := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    exact h.symm ▸
      D.chosen.rooted.core.root_mem_carrier
  let R₂ : RootedCore G x y 2 := {
    core := .typeTwo C₂
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C₂,
        hyx, hyt₁, hyt₂, R.exception_ne_right.symm, hys]
  }
  have hminimal := D.chosen.type_minimal R₂
  rw [hcore] at hminimal
  change 3 ≤ 2 at hminimal
  omega

/--
The closed-boundary equality also forces the root-adjacent side to have
its minimum possible order.  If `T` had one further vertex, adjoining the
exception to `S` would enlarge the selected type-3 core.
-/
theorem card_T_eq_rank_add_one_of_closed_boundary
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C) :
    C.T.card = D.chosen.rank + 1 := by
  by_contra hcard
  have hlarge :
      D.chosen.rank + 2 ≤ C.T.card := by
    have hlower := C.card_T_lower
    omega
  have hnonadjS :
      ∀ s ∈ C.S, ¬G.Adj z s :=
    fun s hs =>
      D.not_adj_exception_S_of_closed_boundary
        C hcore R hs
  let C' : TypeThreeCore G x (D.chosen.rank + 1) :=
    C.insertInitial z C.T
      (by rfl)
      (by
        have htwo : 2 ≤ C.T.card :=
          (Nat.le_max_right
            (D.chosen.rank + 2) 2).trans
            (by omega)
        omega)
      R.exception_ne_left
      R.exception_not_mem_S
      R.exception_not_mem_T
      hnonadjS
      (fun t ht => (R.exception_adj_T t ht).symm)
  have hyx : y ≠ x := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    exact h.symm ▸
      D.chosen.rooted.core.root_mem_carrier
  have hyS : y ∉ C.S := by
    intro hy
    apply D.chosen.rooted.other_root_not_mem
    have hyCarrier :
        y ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).S_subset_carrier
        (by simpa [Core.S] using hy)
    exact hyCarrier
  have hyT : y ∉ C.T := by
    intro hy
    apply D.chosen.rooted.other_root_not_mem
    have hyCarrier :
        y ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using hy)
    exact hyCarrier
  let R' : RootedCore G x y (D.chosen.rank + 1) := {
    core := .typeThree C'
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C',
        TypeThreeCore.insertInitial,
        hyx, R.exception_ne_right.symm, hyS, hyT]
  }
  have htype :
      R'.core.typeNumber =
        D.chosen.rooted.core.typeNumber := by
    rw [hcore]
    rfl
  have hmax :=
    D.chosen.S_maximal R' htype
  have hnew :
      R'.core.S.card = D.chosen.rank + 1 := by
    simp [R', C', Core.S,
      TypeThreeCore.insertInitial,
      R.exception_not_mem_S, C.card_S]
  have hold :
      D.chosen.rooted.core.S.card =
        D.chosen.rank := by
    rw [hcore]
    exact C.card_S
  rw [hnew, hold] at hmax
  omega

/--
If Claim 3.7 has no witness, the exception has no neighbor outside the
core.  The protected nonedge at the root and the preceding type-2
obstruction then identify its full neighborhood with `T`.
-/
theorem neighborSet_exception_eq_T_of_no_otherComponentWitness
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hregion : D.chosen.rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C)
    (hno :
      ¬Nonempty (TypeThreeOtherComponentWitness D C)) :
    G.neighborSet z = (↑C.T : Set V) := by
  classical
  have hTNonempty : C.T.Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.lt_of_lt_of_le (by omega)
      ((Nat.le_max_right (D.chosen.rank + 1) 2).trans
        C.card_T_lower)
  obtain ⟨t₀, ht₀⟩ := hTNonempty
  have hzSubsetCarrier :
      G.neighborSet z ⊆
        (↑D.chosen.rooted.core.carrier : Set V) := by
    intro v hv
    by_contra hvCarrier
    have hzv : G.Adj z v := by
      simpa [SimpleGraph.mem_neighborSet] using hv
    exact hno
      ⟨D.typeThreeOtherComponentWitnessOfExceptionEdge
        hregion C R ht₀ hzv hvCarrier⟩
  apply Set.Subset.antisymm
  · intro v hv
    have hvCarrier := hzSubsetCarrier hv
    have hzv : G.Adj z v := by
      simpa [SimpleGraph.mem_neighborSet] using hv
    have hvClass :
        v = x ∨ v ∈ C.S ∨ v ∈ C.T := by
      rw [hcore] at hvCarrier
      simpa [Core.carrier, Core.S, Core.T] using hvCarrier
    rcases hvClass with rfl | hvS | hvT
    · exact False.elim
        (M.left_root_not_adj_exception hzv.symm)
    · exact False.elim
        ((D.not_adj_exception_S_of_closed_boundary
          C hcore R hvS) hzv)
    · simpa using hvT
  · intro t ht
    have htT : t ∈ C.T := by
      simpa using ht
    have hzt : G.Adj z t :=
      (R.exception_adj_T t htT).symm
    simpa [SimpleGraph.mem_neighborSet] using hzt

/--
Under the negation of Claim 3.7, an `S`-vertex still has two more required
neighbors than the whole set `T` can contain.  One such neighbor therefore
lies in another deletion component and supplies an `S`-attachment.
-/
theorem exists_typeThreeSComponentWitness_of_no_otherComponentWitness
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C)
    (hno :
      ¬Nonempty (TypeThreeOtherComponentWitness D C)) :
    Nonempty (TypeThreeSComponentWitness D C) := by
  classical
  have hregion' :
      D.chosen.rooted.otherRegion = {y} :=
    hregion
  have hcardT :=
    D.card_T_eq_rank_add_one_of_closed_boundary
      C hcore R
  have hSNonempty : C.S.Nonempty := by
    rw [← Finset.card_pos, C.card_S]
    have hTtwo :
        2 ≤ C.T.card :=
      (Nat.le_max_right
        (D.chosen.rank + 1) 2).trans
        C.card_T_lower
    omega
  obtain ⟨s, hs⟩ := hSNonempty
  have hsx : s ≠ x := by
    intro h
    exact C.root_not_mem_S (h ▸ hs)
  have hsy : s ≠ y := by
    intro h
    apply D.chosen.rooted.other_root_not_mem
    have hsCarrier :
        s ∈ D.chosen.rooted.core.carrier := by
      rw [hcore]
      exact (Core.typeThree C).S_subset_carrier
        (by simpa [Core.S] using hs)
    exact h.symm ▸ hsCarrier
  have hsz : s ≠ z := by
    intro h
    exact R.exception_not_mem_S (h ▸ hs)
  have hdegree :
      q + 1 ≤ finiteDegree G s :=
    M.degree_lower s hsx hsy hsz
  have hnotSubset :
      ¬G.neighborSet s ⊆ (↑C.T : Set V) := by
    intro hsubset
    have hcard :=
      Set.ncard_le_ncard hsubset
    rw [Set.ncard_coe_finset, hcardT] at hcard
    unfold finiteDegree at hdegree
    have hrank := R.rank_add_two_eq
    omega
  obtain ⟨v, hvNeighbor, hvNotT⟩ :=
    Set.not_subset.mp hnotSubset
  have hsv : G.Adj s v := by
    simpa [SimpleGraph.mem_neighborSet] using hvNeighbor
  have hvCarrier :
      v ∉ D.chosen.rooted.core.carrier := by
    intro hvCarrier
    have hvClass :
        v = x ∨ v ∈ C.S ∨ v ∈ C.T := by
      rw [hcore] at hvCarrier
      simpa [Core.carrier, Core.S, Core.T] using hvCarrier
    rcases hvClass with rfl | hvS | hvT
    · exact
        (D.not_adj_root_S_of_typeThree C hcore hs)
          hsv.symm
    · exact
        (C.independent_S
          (by simpa using hs)
          (by simpa using hvS) hsv.ne) hsv
    · exact hvNotT (by simpa using hvT)
  have hneighbors :=
    D.neighborSets_eq_T_of_natural_singleton
      M hnot hregion (Or.inr (by
        rw [hcore]
        rfl))
  have hvy : v ≠ y := by
    intro h
    subst v
    have hsNeighbor :
        s ∈ G.neighborSet y := by
      simpa [SimpleGraph.mem_neighborSet] using hsv.symm
    rw [hneighbors.2] at hsNeighbor
    have hsT :
        s ∈ C.T := by
      simpa [hcore, Core.T] using hsNeighbor
    exact Finset.disjoint_left.mp C.disjoint hs hsT
  have hvz : v ≠ z := by
    intro h
    subst v
    exact
      (D.not_adj_exception_S_of_closed_boundary
        C hcore R hs) hsv.symm
  let vD :
      {w : V // w ∉ D.chosen.rooted.core.carrier} :=
    ⟨v, hvCarrier⟩
  let K :=
    (deleteVertices G
      D.chosen.rooted.core.carrier).connectedComponentMk vD
  have hvK :
      v ∈ componentVertices G
        D.chosen.rooted.core.carrier K := by
    apply (mem_componentVertices_iff
      G D.chosen.rooted.core.carrier K v).2
    exact ⟨hvCarrier,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hKne :
      K ≠ D.chosen.rooted.otherComponent := by
    intro hK
    have hvOther :
        v ∈ D.chosen.rooted.otherRegion := by
      change v ∈ componentVertices G
        D.chosen.rooted.core.carrier
          D.chosen.rooted.otherComponent
      exact hK ▸ hvK
    rw [hregion'] at hvOther
    exact hvy (by simpa using hvOther)
  exact ⟨{
    component := K
    component_ne_other := hKne
    ordinary := v
    ordinary_mem := hvK
    ordinary_ne_exception := hvz
    attachment := v
    attachment_mem := hvK
    initial := s
    initial_mem := hs
    initial_adj_attachment := hsv
  }⟩

/--
For the `S`-attached component obtained above, every core endpoint of a
boundary edge lies in `S`.  A `T`-endpoint would already be a Claim 3.7
witness; the root is excluded by the exact root neighborhood from Claim
3.5.
-/
theorem boundary_mem_S_of_no_otherComponentWitness
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (hno :
      ¬Nonempty (TypeThreeOtherComponentWitness D C))
    (W : TypeThreeSComponentWitness D C)
    {d a : V}
    (hd :
      d ∈ componentVertices G
        D.chosen.rooted.core.carrier W.component)
    (hda : G.Adj d a)
    (ha : a ∈ D.chosen.rooted.core.carrier) :
    a ∈ C.S := by
  have hneighbors :=
    D.neighborSets_eq_T_of_natural_singleton
      M hnot hregion (Or.inr (by
        rw [hcore]
        rfl))
  have hQ :
      ComponentRegion G D.chosen.rooted.core.carrier
        (componentVertices G
          D.chosen.rooted.core.carrier W.component) :=
    componentRegion_componentVertices
      G D.chosen.rooted.core.carrier W.component
  have hax : a ≠ x := by
    intro h
    subst a
    have hdNeighbor :
        d ∈ G.neighborSet x := by
      simpa [SimpleGraph.mem_neighborSet] using hda.symm
    rw [hneighbors.1, hneighbors.2] at hdNeighbor
    have hdT :
        d ∈ D.chosen.rooted.core.T := by
      simpa using hdNeighbor
    exact hQ.not_mem_separator hd
      (D.chosen.rooted.core.T_subset_carrier hdT)
  rcases
      D.chosen.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
        ha hax with haS | haT
  · simpa [hcore, Core.S] using haS
  · have haT' : a ∈ C.T := by
      simpa [hcore, Core.T] using haT
    exact False.elim
      (hno ⟨{
        component := W.component
        component_ne_other := W.component_ne_other
        ordinary := W.ordinary
        ordinary_mem := W.ordinary_mem
        ordinary_ne_exception := W.ordinary_ne_exception
        attachment := d
        attachment_mem := hd
        terminal := a
        terminal_mem := haT'
        terminal_adj_attachment := hda.symm
      }⟩)

/--
The two distinct `S`-attachments needed for the recursive compression.
Their existence also collapses the bounded numerical range to
`rank=2` and `q=4`.
-/
structure TypeThreeSCompressionData
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank)
    (W : TypeThreeSComponentWitness D C) where
  /-- A component endpoint for the second boundary edge. -/
  secondAttachment : V
  /-- The second attachment endpoint lies in the selected component. -/
  secondAttachment_mem :
    secondAttachment ∈ componentVertices G
      D.chosen.rooted.core.carrier W.component
  /-- The second, distinct boundary vertex in `S`. -/
  secondInitial : V
  /-- The second boundary vertex belongs to `S`. -/
  secondInitial_mem : secondInitial ∈ C.S
  /-- The two boundary vertices are distinct. -/
  secondInitial_ne : secondInitial ≠ W.initial
  /-- The second boundary and component endpoints are adjacent. -/
  secondInitial_adj :
    G.Adj secondInitial secondAttachment
  /-- The bounded equality case forces rank two. -/
  rank_eq_two : D.chosen.rank = 2
  /-- The bounded equality case forces four requested paths. -/
  q_eq_four : q = 4

/--
Two-connectivity supplies a second boundary vertex distinct from the
already selected `S`-attachment.  The source rank and the requested
bounded family size are then forced to be two and four.
-/
theorem exists_typeThreeSCompressionData
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C)
    (hno :
      ¬Nonempty (TypeThreeOtherComponentWitness D C))
    (W : TypeThreeSComponentWitness D C) :
    Nonempty (TypeThreeSCompressionData
      (q := q) D C W) := by
  let Q :=
    componentVertices G
      D.chosen.rooted.core.carrier W.component
  have hQ :
      ComponentRegion G
        D.chosen.rooted.core.carrier Q :=
    componentRegion_componentVertices
      G D.chosen.rooted.core.carrier W.component
  have hs₀Carrier :
      W.initial ∈ D.chosen.rooted.core.carrier := by
    rw [hcore]
    exact (Core.typeThree C).S_subset_carrier
      (by simpa [Core.S] using W.initial_mem)
  have hs₀x : W.initial ≠ x := by
    intro h
    have hs : W.initial ∈ C.S :=
      W.initial_mem
    apply C.root_not_mem_S
    simpa only [h] using hs
  obtain
      ⟨d₁, hd₁, s₁, hs₁Carrier, hs₁s₀, hd₁s₁⟩ :=
    hQ.exists_attachment_avoiding_boundary_vertex
      M.underlying_two_connected
      hs₀Carrier
      D.chosen.rooted.core.root_mem_carrier
      hs₀x
  have hs₁S :
      s₁ ∈ C.S :=
    D.boundary_mem_S_of_no_otherComponentWitness
      M hnot hregion C hcore hno W
      hd₁ hd₁s₁ hs₁Carrier
  have htwoS : 2 ≤ C.S.card := by
    have hone : 1 < C.S.card :=
      Finset.one_lt_card.mpr
        ⟨W.initial, W.initial_mem,
          s₁, hs₁S, hs₁s₀.symm⟩
    omega
  have hrank : D.chosen.rank = 2 := by
    rw [C.card_S] at htwoS
    have hq := R.rank_add_two_eq
    have hqFour := M.q_le_four
    omega
  have hq : q = 4 := by
    have := R.rank_add_two_eq
    omega
  exact ⟨{
    secondAttachment := d₁
    secondAttachment_mem := hd₁
    secondInitial := s₁
    secondInitial_mem := hs₁S
    secondInitial_ne := hs₁s₀
    secondInitial_adj := hd₁s₁.symm
    rank_eq_two := hrank
    q_eq_four := hq
  }⟩

/--
Under the negation of Claim 3.7, the exceptional vertex cannot belong to
the auxiliary `S`-attached component.  Its full neighborhood is `T`, while
the component is disjoint from the core.  If the exception belonged to the
component, connectivity to its certified ordinary vertex would therefore
give an impossible neighbor inside the component.
-/
theorem exception_not_mem_typeThreeSComponent
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hregion : D.chosen.rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C)
    (hno :
      ¬Nonempty (TypeThreeOtherComponentWitness D C))
    (W : TypeThreeSComponentWitness D C) :
    z ∉ componentVertices G
      D.chosen.rooted.core.carrier W.component := by
  classical
  let Q :=
    componentVertices G
      D.chosen.rooted.core.carrier W.component
  have hQ :
      ComponentRegion G
        D.chosen.rooted.core.carrier Q :=
    componentRegion_componentVertices
      G D.chosen.rooted.core.carrier W.component
  have hneighbors :
      G.neighborSet z = (↑C.T : Set V) :=
    D.neighborSet_exception_eq_T_of_no_otherComponentWitness
      M hregion C hcore R hno
  intro hzQ
  let zQ : (↑Q : Set V) := ⟨z, hzQ⟩
  let wQ : (↑Q : Set V) :=
    ⟨W.ordinary, W.ordinary_mem⟩
  have hzw : zQ ≠ wQ := by
    intro h
    exact W.ordinary_ne_exception
      (congrArg Subtype.val h).symm
  have hreach :
      (G.induce (↑Q : Set V)).Reachable zQ wQ :=
    hQ.connected zQ wQ
  have hzSupport :
      zQ ∈ (G.induce (↑Q : Set V)).support :=
    SimpleGraph.mem_support_of_reachable hzw hreach
  obtain ⟨v, hzv⟩ :=
    (G.induce (↑Q : Set V)).mem_support.mp hzSupport
  have hvT : v.1 ∈ C.T := by
    have hvNeighbor : v.1 ∈ G.neighborSet z := by
      simpa [SimpleGraph.mem_neighborSet] using hzv
    rw [hneighbors] at hvNeighbor
    simpa using hvNeighbor
  exact hQ.not_mem_separator v.2
    (by
      rw [hcore]
      exact (Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using hvT))

/--
COY Claim 3.7.  A natural singleton exterior around a selected type-3
core has a different deletion component containing an ordinary vertex and
attached to the `T`-side of the core.
-/
theorem exists_typeThreeOtherComponentWitness_of_natural_singleton
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C) :
    Nonempty (TypeThreeOtherComponentWitness D C) := by
  classical
  by_contra hno
  have hclosed :=
    D.closed_T_boundary_of_no_otherComponentWitness
      hregion C hno
  let R :
      TypeThreeClosedBoundaryRigidity
        (q := q) D C :=
    D.typeThree_closed_boundary_rigidity
      M hnot hregion C hcore hclosed
  obtain ⟨W⟩ :=
    D.exists_typeThreeSComponentWitness_of_no_otherComponentWitness
      M hnot hregion C hcore R hno
  obtain ⟨X⟩ :=
    D.exists_typeThreeSCompressionData
      M hnot hregion C hcore R hno W
  let Q :=
    componentVertices G
      D.chosen.rooted.core.carrier W.component
  have hQ :
      ComponentRegion G
        D.chosen.rooted.core.carrier Q :=
    componentRegion_componentVertices
      G D.chosen.rooted.core.carrier W.component
  have hQCarrier :
      Disjoint Q D.chosen.rooted.core.carrier :=
    hQ.disjoint
  have hQS : Disjoint Q C.S := by
    apply hQCarrier.mono_right
    intro s hs
    rw [hcore]
    exact (Core.typeThree C).S_subset_carrier
      (by simpa [Core.S] using hs)
  have hxQ : x ∉ Q := by
    intro hx
    exact hQ.not_mem_separator hx
      D.chosen.rooted.core.root_mem_carrier
  have hyQ : y ∉ Q := by
    intro hy
    have hdisjoint :=
      componentVertices_disjoint_of_ne
        G D.chosen.rooted.core.carrier
          W.component_ne_other
    apply Finset.disjoint_left.mp hdisjoint hy
    exact D.chosen.rooted.other_root_mem_otherRegion
  have hzQ : z ∉ Q := by
    simpa only [Q] using
      D.exception_not_mem_typeThreeSComponent
        M hregion C hcore R hno W
  have hboundary :
      ∀ {d a : V}, d ∈ Q → G.Adj d a →
        a ∈ D.chosen.rooted.core.carrier → a ∈ C.S := by
    intro d a hd hda ha
    exact D.boundary_mem_S_of_no_otherComponentWitness
      M hnot hregion C hcore hno W hd hda ha
  have hall (d : V) (hd : d ∈ Q) :
      ∀ ⦃v : V⦄, G.Adj d v → v ∈ Q ∪ C.S := by
    intro v hdv
    by_cases hvCarrier :
        v ∈ D.chosen.rooted.core.carrier
    · exact Finset.mem_union_right Q
        (hboundary hd hdv hvCarrier)
    · exact Finset.mem_union_left C.S
        (hQ.closed hd hdv hvCarrier)
  have hSbound (d : V) :
      (G.neighborSet d ∩ (↑C.S : Set V)).ncard ≤ 2 := by
    calc
      (G.neighborSet d ∩ (↑C.S : Set V)).ncard
          ≤ (↑C.S : Set V).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right
      _ = C.S.card := Set.ncard_coe_finset C.S
      _ = 2 := by rw [C.card_S, X.rank_eq_two]
  have hledger :
      ∀ d (hd : d ∈ Q),
        finiteDegree G d + 1 ≤
          finiteDegree
              (BoundaryCompression.graph
                G Q C.S W.initial)
              (BoundaryCompression.inner ⟨d, hd⟩) + 2 := by
    intro d hd
    have hstrong :=
      BoundaryCompression.finiteDegree_add_one_le_compressed_add
        (G := G) (Q := Q) (T := C.S)
        (t := W.initial)
        hQS W.initial_mem hd
        (fun {_} hdv => hall d hd hdv)
        1 (by omega)
        (by rw [C.card_S, X.rank_eq_two])
        (by simpa using hSbound d)
    omega
  have hrecursive :
      Nonempty
        (AdmissiblePathFamily
          (BoundaryCompression.graph G Q C.S W.initial)
          (BoundaryCompression.collapsedRoot :
            BoundaryCompressionVertex Q)
          BoundaryCompression.retainedRoot 3) := by
    have hfamily :=
      BoundaryCompression.exists_recursive_family
        (G := G)
        (C := D.chosen.rooted.core.carrier)
        (Q := Q) (T := C.S)
        M hQ hQCarrier
        D.chosen.rooted.core.three_le_carrier_card_claim36
        hQS hboundary
        W.initial W.initial_mem
        W.attachment_mem W.initial_adj_attachment
        X.secondAttachment_mem X.secondInitial_mem
        X.secondInitial_ne X.secondInitial_adj
        hxQ hyQ
        ⟨W.ordinary, W.ordinary_mem,
          W.ordinary_ne_exception⟩
        2 1
        (by rw [X.q_eq_four]; norm_num)
        (by omega)
        hledger
    simpa [X.q_eq_four] using hfamily
  obtain ⟨recursive⟩ := hrecursive
  have hTNonempty : C.T.Nonempty := by
    rw [← Finset.card_pos]
    have htwo :
        2 ≤ C.T.card :=
      (Nat.le_max_right
        (D.chosen.rank + 1) 2).trans
        C.card_T_lower
    omega
  obtain ⟨t₀, ht₀⟩ := hTNonempty
  have hcardT : C.T.card = 3 := by
    rw [D.card_T_eq_rank_add_one_of_closed_boundary
      C hcore R, X.rank_eq_two]
  have ht₀Q : t₀ ∉ Q := by
    intro htQ
    exact hQ.not_mem_separator htQ
      (by
        rw [hcore]
        exact (Core.typeThree C).T_subset_carrier
          (by simpa [Core.T] using ht₀))
  have ht₀S : t₀ ∉ C.S := by
    exact Finset.disjoint_right.mp C.disjoint
      ht₀
  have hyS : y ∉ C.S := by
    intro hy
    apply D.chosen.rooted.other_root_not_mem
    rw [hcore]
    exact (Core.typeThree C).S_subset_carrier
      (by simpa [Core.S] using hy)
  have hst₀ : G.Adj W.initial t₀ :=
    (C.cross_adj t₀ ht₀ W.initial W.initial_mem).symm
  have ht₀y : G.Adj t₀ y := by
    have hneighbors :=
      D.neighborSets_eq_T_of_natural_singleton
        M hnot hregion (Or.inr (by
          rw [hcore]
          rfl))
    have hyt₀ : G.Adj y t₀ := by
      rw [← SimpleGraph.mem_neighborSet,
        hneighbors.2]
      rw [hcore]
      simpa [Core.T] using ht₀
    exact hyt₀.symm
  obtain ⟨outer⟩ :=
    BoundaryCompression.exists_lifted_outer_twoEdgeData
      hQS W.initial_mem
      ht₀Q ht₀S hyQ hyS hst₀ ht₀y recursive
  let inner (i : Fin 3) :
      SemiAdmissiblePathFamily G x
        (outer.family.endpoint i) 2 :=
    SemiAdmissiblePathFamily.ofAdmissible
      (R.innerPathsForClaim37
        X.rank_eq_two hcardT W.initial
        (outer.family.endpoint i) t₀
        (outer.family.endpoint_mem i) ht₀)
  let certificate :
      FactOneCertificate G x y
        (↑(C.S.erase W.initial) : Set V) 3 2 := {
    hs := by omega
    ht := by omega
    x_ne_y := M.roots_ne
    x_not_mem := by
      intro hx
      exact C.root_not_mem_S
        (Finset.mem_of_mem_erase hx)
    y_not_mem := by
      intro hy
      exact hyS (Finset.mem_of_mem_erase hy)
    outer := outer.family
    inner := inner
    equal_inner_length := by
      intro i j
      rw [(inner i).length_path j,
        (inner (firstFin (by omega : 1 ≤ 3))).length_path j]
      change 2 + j.val * 2 = 2 + j.val * 2
      rfl
    avoid_outer := by
      intro i j
      apply List.disjoint_left.mpr
      intro v hvInner hvOuterTail
      have hvInnerClass :=
        R.innerPathsForClaim37_support
          X.rank_eq_two hcardT W.initial
          (outer.family.endpoint i) t₀
          (outer.family.endpoint_mem i) ht₀ j hvInner
      have hvOuterClass :=
        outer.support_class i v
          (List.mem_of_mem_tail hvOuterTail)
      rcases hvOuterClass with
          hvEndpoint | hvInitial | hvQ | hvt₀ | hvy
      · subst v
        exact (outer.family.path i).start_not_mem_tail
          hvOuterTail
      · rcases hvInnerClass with
          hvx | hvEndpoint | hvz | hvT
        · exact C.root_not_mem_S
            (by
              apply (congrArg (fun a => a ∈ C.S) hvx).mp
              apply (congrArg (fun a => a ∈ C.S) hvInitial).mpr
              exact W.initial_mem)
        · exact (Finset.mem_erase.mp
            (outer.family.endpoint_mem i)).1
              (hvEndpoint.symm.trans hvInitial)
        · exact R.exception_not_mem_S
            (by
              apply (congrArg (fun a => a ∈ C.S) hvz).mp
              apply (congrArg (fun a => a ∈ C.S) hvInitial).mpr
              exact W.initial_mem)
        · rw [hvInitial] at hvT
          exact Finset.disjoint_left.mp C.disjoint
            W.initial_mem
            (Finset.mem_of_mem_erase hvT)
      · rcases hvInnerClass with
          hvx | hvEndpoint | hvz | hvT
        · subst v
          exact hxQ hvQ
        · subst v
          exact Finset.disjoint_left.mp hQS
            hvQ
            (Finset.mem_of_mem_erase
              (outer.family.endpoint_mem i))
        · subst v
          exact hzQ hvQ
        · exact Finset.disjoint_left.mp hQCarrier
            hvQ
            (by
              rw [hcore]
              exact (Core.typeThree C).T_subset_carrier
                (by simpa [Core.T] using
                  Finset.mem_of_mem_erase hvT))
      · rcases hvInnerClass with
          hvx | hvEndpoint | hvz | hvT
        · exact C.root_not_mem_T
            ((hvt₀.symm.trans hvx) ▸ ht₀)
        · rw [hvt₀] at hvEndpoint
          exact Finset.disjoint_left.mp C.disjoint
            (Finset.mem_of_mem_erase
              (outer.family.endpoint_mem i))
            (hvEndpoint ▸ ht₀)
        · exact R.exception_not_mem_T
            ((hvt₀.symm.trans hvz) ▸ ht₀)
        · rw [hvt₀] at hvT
          exact (Finset.mem_erase.mp hvT).1 rfl
      · rcases hvInnerClass with
          hvx | hvEndpoint | hvz | hvT
        · exact M.roots_ne
            (hvx.symm.trans hvy)
        · apply hyS
          apply (congrArg (fun a => a ∈ C.S) hvy).mp
          apply (congrArg (fun a => a ∈ C.S) hvEndpoint).mpr
          exact Finset.mem_of_mem_erase
            (outer.family.endpoint_mem i)
        · exact R.exception_ne_right
            (hvz.symm.trans hvy)
        · rw [hvy] at hvT
          apply D.chosen.rooted.other_root_not_mem
          rw [hcore]
          exact (Core.typeThree C).T_subset_carrier
            (by simpa [Core.T] using
              Finset.mem_of_mem_erase hvT)
  }
  have hpaths := fact_one certificate
  apply M.no_paths
  simpa [RootedInstance.Solvable, X.q_eq_four] using hpaths

end PreferredOrientationData

end COY

end DeanK5
