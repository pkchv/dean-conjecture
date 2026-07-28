import DeanK5.COYExteriorClaimThreeFifteenSingleton

/-!
# The multiple-neighbour branch of COY Claim 3.15(1)

Assume the unique type-three `S`-vertex `s` has at least two neighbours in
the selected block.  The source recursive graph is
`B' = G[B ∪ {s,x}]`, rooted at `x,b`, with exceptional vertex `s`.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/-- The intermediate graph `G[B ∪ {s}]`. -/
noncomputable def sideBPrime
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    SimpleGraph (Option C.BPrimeBlockVertex) :=
  adjoinRoot C.bPrimeBlockGraph
    (C.bPrimeAttachments s)

/-- The canonical homomorphism `G[B ∪ {s}] → G`. -/
noncomputable def sideBPrimeHom
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    C.sideBPrime s →g G :=
  adjoinRootHom C.bPrimeBlockGraph
    (C.bPrimeAttachments s)
    C.bPrimeBlockEmbedding.toHom s
    (by
      intro d hd
      exact C.mem_bPrimeAttachments.mp hd)

@[simp] theorem sideBPrimeHom_none
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    C.sideBPrimeHom s none = s :=
  rfl

@[simp] theorem sideBPrimeHom_some
    (C : P.ExteriorFeasibleBlockChoice) (s : V)
    (d : C.BPrimeBlockVertex) :
    C.sideBPrimeHom s (some d) = d.1 :=
  rfl

/-- Actual `x`-neighbours in `G[B ∪ {s}]`. -/
noncomputable def doubleRootAttachments
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    Finset (Option C.BPrimeBlockVertex) := by
  classical
  exact Finset.univ.filter fun d =>
    G.Adj x (C.sideBPrimeHom s d)

@[simp] theorem mem_doubleRootAttachments
    (C : P.ExteriorFeasibleBlockChoice)
    (s : V) {d : Option C.BPrimeBlockVertex} :
    d ∈ C.doubleRootAttachments s ↔
      G.Adj x (C.sideBPrimeHom s d) := by
  classical
  simp [doubleRootAttachments]

/-- The source graph `G[B ∪ {s,x}]`. -/
noncomputable def doubleBPrime
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    SimpleGraph
      (Option (Option C.BPrimeBlockVertex)) :=
  adjoinRoot (C.sideBPrime s)
    (C.doubleRootAttachments s)

/-- Its left root, representing `x`. -/
abbrev doubleBPrimeRoot
    (C : P.ExteriorFeasibleBlockChoice) :
    Option (Option C.BPrimeBlockVertex) :=
  none

/-- Its right root, representing `b`. -/
def doubleBPrimeAnchor
    (C : P.ExteriorFeasibleBlockChoice) :
    Option (Option C.BPrimeBlockVertex) :=
  some (some C.bPrimeAnchor)

/-- Its recursive exceptional vertex, representing `s`. -/
def doubleBPrimeException
    (C : P.ExteriorFeasibleBlockChoice) :
    Option (Option C.BPrimeBlockVertex) :=
  some none

/-- The canonical homomorphism `G[B ∪ {s,x}] → G`. -/
noncomputable def doubleBPrimeHom
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    C.doubleBPrime s →g G :=
  adjoinRootHom (C.sideBPrime s)
    (C.doubleRootAttachments s)
    (C.sideBPrimeHom s) x
    (by
      intro d hd
      exact C.mem_doubleRootAttachments s |>.mp hd)

@[simp] theorem doubleBPrimeHom_root
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    C.doubleBPrimeHom s C.doubleBPrimeRoot = x :=
  rfl

@[simp] theorem doubleBPrimeHom_anchor
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    C.doubleBPrimeHom s C.doubleBPrimeAnchor = C.b :=
  rfl

@[simp] theorem doubleBPrimeHom_exception
    (C : P.ExteriorFeasibleBlockChoice) (s : V) :
    C.doubleBPrimeHom s C.doubleBPrimeException = s :=
  rfl

/-- The intermediate homomorphism is injective when `s` is in the core. -/
theorem sideBPrimeHom_injective
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V}
    (hsCore : s ∈ P.working.rooted.core.carrier) :
    Function.Injective (C.sideBPrimeHom s) := by
  apply adjoinRootHom_injective
  · exact C.bPrimeBlockEmbedding.injective
  · rintro ⟨d, hd⟩
    change d.1 = s at hd
    exact Finset.disjoint_left.mp
      C.ambientCarrier_disjoint_core d.2
      (Eq.mp
        (congrArg
          (fun a =>
            a ∈ P.working.rooted.core.carrier)
          hd.symm)
        hsCore)

/-- The canonical homomorphism for `G[B ∪ {s,x}]` is injective. -/
theorem doubleBPrimeHom_injective
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V} (hs : s ∈ D.core.S) :
    Function.Injective (C.doubleBPrimeHom s) := by
  have hsCore :
      s ∈ P.working.rooted.core.carrier := by
    rw [D.core_eq]
    exact (Core.typeThree D.core).S_subset_carrier
      (by simpa [Core.S] using hs)
  apply adjoinRootHom_injective
  · exact C.sideBPrimeHom_injective hsCore
  · rintro ⟨d, hd⟩
    cases d with
    | none =>
        change s = x at hd
        apply D.core.root_not_mem_S
        exact
          Eq.mp
            (congrArg
              (fun a => a ∈ D.core.S)
              hd)
            hs
    | some d =>
        change d.1 = x at hd
        exact Finset.disjoint_left.mp
          C.ambientCarrier_disjoint_core d.2
          (Eq.mp
            (congrArg
              (fun a =>
                a ∈ P.working.rooted.core.carrier)
              hd.symm)
            P.working.rooted.core.root_mem_carrier)

/-- Two block neighbours of `s` make `G[B ∪ {s}]` 2-connected. -/
theorem sideBPrime_twoConnected
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V}
    (hside : 2 ≤ (C.blockNeighbors s).card) :
    IsTwoConnected (C.sideBPrime s) := by
  apply
    C.ambientCarrier_nonseparable.isTwoConnected_adjoinRoot
  rw [C.card_bPrimeAttachments]
  exact hside

/-- Adding the artificial edge `xb` enlarges the outer attachment set by
the block anchor. -/
theorem doubleBPrime_sup_rootEdge
    (C : P.ExteriorFeasibleBlockChoice)
    (s : V) :
    C.doubleBPrime s ⊔
        edge C.doubleBPrimeRoot C.doubleBPrimeAnchor =
      adjoinRoot (C.sideBPrime s)
        (insert (some C.bPrimeAnchor)
          (C.doubleRootAttachments s)) := by
  ext a b
  cases a <;> cases b <;>
    simp [doubleBPrime, doubleBPrimeAnchor,
      adjoinRoot, edge, or_comm]

/-- The rooted outer attachment set contains `b` and an actual distinct
`x`-neighbour in `B-b`. -/
theorem two_le_insert_anchor_doubleRootAttachments
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V}
    (hboundary : C.coreAttachments = {x, s}) :
    2 ≤
      (insert (some C.bPrimeAnchor)
        (C.doubleRootAttachments s)).card := by
  obtain ⟨d, hd, hxd⟩ :=
    C.exists_root_attachment_in_compressionInterior
      hboundary
  let dB : C.BPrimeBlockVertex :=
    ⟨d, Finset.mem_of_mem_erase hd⟩
  have hdAttach :
      some dB ∈ C.doubleRootAttachments s := by
    exact C.mem_doubleRootAttachments s |>.mpr hxd
  have hne :
      (some C.bPrimeAnchor :
        Option C.BPrimeBlockVertex) ≠ some dB := by
    intro h
    have h' : C.bPrimeAnchor = dB :=
      Option.some.inj h
    exact (Finset.mem_erase.mp hd).1
      (congrArg Subtype.val h').symm
  have hpair :
      ({some C.bPrimeAnchor, some dB} :
        Finset (Option C.BPrimeBlockVertex)) ⊆
        insert (some C.bPrimeAnchor)
          (C.doubleRootAttachments s) := by
    intro w hw
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hdAttach
  have hpairCard :
      ({some C.bPrimeAnchor, some dB} :
        Finset (Option C.BPrimeBlockVertex)).card = 2 := by
    simp [hne]
  rw [← hpairCard]
  exact Finset.card_le_card hpair

/-- The multiple-neighbour recursive graph is rooted 2-connected. -/
theorem doubleBPrime_rooted_twoConnected
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V}
    (hboundary : C.coreAttachments = {x, s})
    (hside : 2 ≤ (C.blockNeighbors s).card) :
    IsTwoConnected
      (C.doubleBPrime s ⊔
        edge C.doubleBPrimeRoot
          C.doubleBPrimeAnchor) := by
  rw [C.doubleBPrime_sup_rootEdge]
  exact isTwoConnected_adjoinRoot
    (C.sideBPrime s)
    (insert (some C.bPrimeAnchor)
      (C.doubleRootAttachments s))
    (C.sideBPrime_twoConnected hside)
    (C.two_le_insert_anchor_doubleRootAttachments
      hboundary)

/--
Every nonanchor block vertex retains its ambient degree in
`G[B ∪ {s,x}]`.
-/
theorem finiteDegree_le_doubleBPrime
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V}
    (hzPrime : C.zPrime = C.b)
    (hboundary : C.coreAttachments = {x, s})
    {d : V} (hd : d ∈ C.compressionInterior) :
    finiteDegree G d ≤
      finiteDegree (C.doubleBPrime s)
        (some (some
          (⟨d, Finset.mem_of_mem_erase hd⟩ :
            C.BPrimeBlockVertex))) := by
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
        (adjoinRoot (C.sideBPrime s)
          (C.doubleRootAttachments s))
        (some (some
          (⟨d, hdB⟩ :
            C.BPrimeBlockVertex)))
  rw [finiteDegree_adjoinRoot_some]
  change
    finiteDegree G d ≤
      finiteDegree
          (adjoinRoot C.bPrimeBlockGraph
            (C.bPrimeAttachments s))
          (some
            (⟨d, hdB⟩ :
              C.BPrimeBlockVertex)) +
        (if some
            (⟨d, hdB⟩ :
              C.BPrimeBlockVertex) ∈
              C.doubleRootAttachments s
          then 1 else 0)
  rw [finiteDegree_adjoinRoot_some]
  by_cases hds : G.Adj d s
  · have hsAttach :
        (⟨d, hdB⟩ :
          C.BPrimeBlockVertex) ∈
            C.bPrimeAttachments s :=
      C.mem_bPrimeAttachments.mpr hds.symm
    rw [if_pos hsAttach]
    omega
  · have hsNotAttach :
        (⟨d, hdB⟩ :
          C.BPrimeBlockVertex) ∉
            C.bPrimeAttachments s := by
      intro h
      exact hds
        (C.mem_bPrimeAttachments.mp h).symm
    rw [if_neg hsNotAttach, add_zero]
    by_cases hdx : G.Adj d x
    · have hxAttach :
          some
              (⟨d, hdB⟩ :
                C.BPrimeBlockVertex) ∈
            C.doubleRootAttachments s := by
        exact C.mem_doubleRootAttachments s |>.mpr
          hdx.symm
      rw [if_pos hxAttach]
      omega
    · have hxNotAttach :
          some
              (⟨d, hdB⟩ :
                C.BPrimeBlockVertex) ∉
            C.doubleRootAttachments s := by
        intro h
        exact hdx
          (C.mem_doubleRootAttachments s |>.mp h).symm
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
        · exact hds hw.1
      rw [hcoreEmpty] at hsplit
      simp at hsplit
      omega

/-- The doubly adjoined graph has fewer vertices than the ambient graph. -/
theorem doubleBPrime_vertex_card_lt
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V} (hs : s ∈ D.core.S) :
    Fintype.card
        (Option (Option C.BPrimeBlockVertex)) <
      Fintype.card V := by
  have hTnonempty : D.core.T.Nonempty := by
    have htwo : 2 ≤ D.core.T.card :=
      (Nat.le_max_right
        (P.working.rank + 1) 2).trans
        D.core.card_T_lower
    exact Finset.card_pos.mp (by omega)
  obtain ⟨t, ht⟩ := hTnonempty
  have htWorkingCore :
      t ∈ P.working.rooted.core.carrier := by
    rw [D.core_eq]
    exact (Core.typeThree D.core).T_subset_carrier
      (by simpa [Core.T] using ht)
  refine
    Fintype.card_lt_of_injective_of_notMem
      (b := t) (C.doubleBPrimeHom s)
      (C.doubleBPrimeHom_injective D hs) ?_
  rintro ⟨w, hw⟩
  cases w with
  | none =>
      change x = t at hw
      apply D.core.root_not_mem_T
      exact
        Eq.mp
          (congrArg
            (fun a => a ∈ D.core.T)
            hw).symm
          ht
  | some w =>
      cases w with
      | none =>
          change s = t at hw
          have hsT : s ∈ D.core.T :=
            Eq.mp
              (congrArg
                (fun a => a ∈ D.core.T)
                hw).symm
              ht
          exact Finset.disjoint_left.mp
            D.core.disjoint hs hsT
      | some d =>
          change d.1 = t at hw
          exact Finset.disjoint_left.mp
            C.ambientCarrier_disjoint_core d.2
            (Eq.mp
              (congrArg
                (fun a =>
                  a ∈ P.working.rooted.core.carrier)
                hw.symm)
              htWorkingCore)

/-- The injective ambient homomorphism bounds the recursive edge count. -/
theorem doubleBPrime_edgeSet_ncard_le
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V} (hs : s ∈ D.core.S) :
    (C.doubleBPrime s).edgeSet.ncard ≤
      G.edgeSet.ncard := by
  let f := C.doubleBPrimeHom s
  have hsubset :
      Sym2.map f '' (C.doubleBPrime s).edgeSet ⊆
        G.edgeSet :=
    f.image_edgeSet_subset
  calc
    (C.doubleBPrime s).edgeSet.ncard =
        (Sym2.map f ''
          (C.doubleBPrime s).edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective
          (C.doubleBPrimeHom_injective D hs))]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

/-- The multiple-neighbour recursive graph is strictly smaller. -/
theorem doubleBPrime_complexity_lt
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V} (hs : s ∈ D.core.S) :
    rootedComplexity (C.doubleBPrime s) <
      rootedComplexity G :=
  rootedComplexity_lt_of_card_lt_of_edgeCount_le
    (C.doubleBPrime_vertex_card_lt D hs)
    (C.doubleBPrime_edgeSet_ncard_le D hs)

/--
Mapped `x`--`b` paths in `G[B ∪ {s,x}]` avoid the connector tail.
-/
theorem doubleBPrime_path_disjoint_pathToY
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V} (hs : s ∈ D.core.S)
    (Q : SimplePath (C.doubleBPrime s)
      C.doubleBPrimeRoot C.doubleBPrimeAnchor) :
    (Q.mapInjectiveHom (C.doubleBPrimeHom s)
        (C.doubleBPrimeHom_injective D hs)).walk.support.Disjoint
      C.pathToY.walk.support.tail := by
  have hsWorkingCore :
      s ∈ P.working.rooted.core.carrier := by
    rw [D.core_eq]
    exact (Core.typeThree D.core).S_subset_carrier
      (by simpa [Core.S] using hs)
  apply List.disjoint_left.mpr
  intro a haMapped haTail
  have haConnector :
      a ∈ C.pathToY.walk.support :=
    List.mem_of_mem_tail haTail
  change
    a ∈ (Q.walk.map (C.doubleBPrimeHom s)).support
      at haMapped
  rw [SimpleGraph.Walk.support_map] at haMapped
  obtain ⟨w, hwQ, hwValue⟩ :=
    List.mem_map.mp haMapped
  cases w with
  | none =>
      change x = a at hwValue
      exact
        P.working.rooted.otherRegion_componentRegion.not_mem_separator
          (C.pathToY_support_mem_otherRegion
            haConnector)
          (Eq.mp
            (congrArg
              (fun u =>
                u ∈ P.working.rooted.core.carrier)
              hwValue)
            P.working.rooted.core.root_mem_carrier)
  | some w =>
      cases w with
      | none =>
          change s = a at hwValue
          exact
            P.working.rooted.otherRegion_componentRegion.not_mem_separator
              (C.pathToY_support_mem_otherRegion
                haConnector)
              (Eq.mp
                (congrArg
                  (fun u =>
                    u ∈ P.working.rooted.core.carrier)
                  hwValue)
                hsWorkingCore)
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

/-- A certified ordinary block vertex is ordinary in the recursive graph. -/
theorem exists_doubleBPrime_ordinary
    (C : P.ExteriorFeasibleBlockChoice) :
    ∃ w : Option (Option C.BPrimeBlockVertex),
      w ≠ C.doubleBPrimeRoot ∧
        w ≠ C.doubleBPrimeAnchor ∧
          w ≠ C.doubleBPrimeException := by
  let ordinaryB : C.BPrimeBlockVertex :=
    ⟨C.ordinary, C.ordinary_mem_ambientCarrier⟩
  refine
    ⟨some (some ordinaryB),
      (by simp [doubleBPrimeRoot]),
      ?_, (by simp [doubleBPrimeException])⟩
  intro h
  have h' :
      ordinaryB = C.bPrimeAnchor :=
    Option.some.inj (Option.some.inj h)
  have hvalue :
      C.ordinary = C.b :=
    congrArg
      (fun w : C.BPrimeBlockVertex => w.1) h'
  exact C.ordinary_ne_b hvalue

/-- The complete rooted instance in the multiple-neighbour branch. -/
theorem doubleBPrime_recursiveInstance
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V}
    (hzPrime : C.zPrime = C.b)
    (hboundary : C.coreAttachments = {x, s})
    (hside : 2 ≤ (C.blockNeighbors s).card) :
    RootedInstance q (C.doubleBPrime s)
      C.doubleBPrimeRoot C.doubleBPrimeAnchor
      C.doubleBPrimeException where
  q_pos := M.q_pos
  q_le_four := M.q_le_four
  roots_ne := by
    simp [doubleBPrimeRoot, doubleBPrimeAnchor]
  rooted_two_connected :=
    C.doubleBPrime_rooted_twoConnected
      hboundary hside
  ordinary_nonempty :=
    C.exists_doubleBPrime_ordinary
  degree_lower := by
    intro w hwRoot hwAnchor hwException
    cases w with
    | none =>
        exact False.elim (hwRoot rfl)
    | some w =>
        cases w with
        | none =>
            exact False.elim (hwException rfl)
        | some d =>
            have hdb : d.1 ≠ C.b := by
              intro h
              apply hwAnchor
              apply congrArg some
              apply congrArg some
              apply Subtype.ext
              exact h
            have hdInterior :
                d.1 ∈ C.compressionInterior :=
              Finset.mem_erase.mpr ⟨hdb, d.2⟩
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
                d.2 hdb
                (by simpa [hzPrime] using hdb)
            have hdNotZ :
                d.1 ≠ z :=
              C.ordinary_block_vertex_ne_z
                d.2 hdb
                (by simpa [hzPrime] using hdb)
            have hambient :=
              M.degree_lower d.1
                hdNotX hdNotY hdNotZ
            have hpreserved :=
              C.finiteDegree_le_doubleBPrime
                M D hzPrime hboundary hdInterior
            exact hambient.trans hpreserved

/-- The multiple-neighbour alternative proves Claim 3.15(1). -/
theorem meetsProtectedInterior_of_two_le_sideBlockNeighbors
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    {s : V}
    (hS : D.core.S = {s})
    (hboundary : C.coreAttachments = {x, s})
    (hside : 2 ≤ (C.blockNeighbors s).card) :
    C.MeetsProtectedInterior := by
  by_contra hnot
  have hzPrimeNot :
      C.zPrime ∉ C.compressionInterior := by
    intro hz
    exact hnot (Or.inr hz)
  have hzPrime :
      C.zPrime = C.b :=
    C.zPrime_eq_b_of_not_mem_compressionInterior
      hzPrimeNot
  have hs : s ∈ D.core.S := by
    rw [hS]
    simp
  let I :=
    C.doubleBPrime_recursiveInstance
      M D hzPrime hboundary hside
  exact
    false_of_claimThreeFifteen_recursiveInstance
      M I
      (C.doubleBPrime_complexity_lt D hs)
      (C.doubleBPrimeHom s)
      (C.doubleBPrimeHom_injective D hs)
      rfl
      C.pathToY
      (C.doubleBPrime_path_disjoint_pathToY
        D hs)

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
