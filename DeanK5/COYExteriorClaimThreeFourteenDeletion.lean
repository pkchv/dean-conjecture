import DeanK5.COYExteriorClaimThreeTwelve
import DeanK5.COYExteriorClaimThreeEight
import DeanK5.COYTypeThreeCarrier
import DeanK5.Graph.ComponentPruning
import DeanK5.Graph.RootAdjunction

/-!
# The deletion recursion in COY Claim 3.14

Suppose the selected exterior component has no `T`-attachment away from
`y`.  Claim 3.8 then gives an edge from `y` to `T`.  Delete every other
vertex of that exterior component.  The remaining rooted graph is
2-connected, preserves every required degree, and is strictly smaller.

The source permits the exceptional vertex `z` to coincide with `y`.
Accordingly, the degree proof below does not silently infer
`z ∈ C - y` from `z ∈ C`: if `z = y`, it is already a recursive root; if
`z ≠ y`, it is deleted.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s : V}
  {P : PreferredWorkingCoreData G x y z}
  {C : TypeThreeCore G x P.working.rank}

/-- A `T`-attachment to the selected exterior at a vertex other than `y`. -/
def HasTAttachmentAwayFromY
    (P : PreferredWorkingCoreData G x y z)
    (C : TypeThreeCore G x P.working.rank) : Prop :=
  ∃ a ∈ P.working.rooted.otherRegion, a ≠ y ∧
    ∃ t ∈ C.T, G.Adj t a

/--
Data for the source deletion `G' = G - (C-y)` under the negation of
Claim 3.14(2).
-/
structure TypeThreeExteriorDeletion
    (P : PreferredWorkingCoreData G x y z)
    (C : TypeThreeCore G x P.working.rank)
    (s : V) where
  /-- The selected working core is this type-3 core. -/
  core_eq : P.working.rooted.core = .typeThree C
  /-- The `S`-side is the singleton used as recursive exception. -/
  side_eq : C.S = {s}
  /-- Claim 3.14(2) is invoked only when `z` lies in this component. -/
  exception_mem_region : z ∈ P.working.rooted.otherRegion
  /-- This is the nonsingleton-exterior case of the source proof. -/
  region_ne_singleton : P.working.rooted.otherRegion ≠ {y}
  /-- The contradictory assumption: no `T`-attachment occurs away from `y`. -/
  no_away_attachment : ¬P.HasTAttachmentAwayFromY C
  /-- Claim 3.8 nevertheless supplies a `T`-vertex adjacent to `y`. -/
  terminal : V
  terminal_mem : terminal ∈ C.T
  terminal_adj_y : G.Adj terminal y

namespace TypeThreeExteriorDeletion

variable {P : PreferredWorkingCoreData G x y z}
  {C : TypeThreeCore G x P.working.rank}

/--
Claim 3.8 turns the absence of an attachment away from `y` into a genuine
edge from `y` to a vertex of `T`.
-/
theorem exists_data
    (M : MinimalCounterexample q G x y z)
    (C : TypeThreeCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeThree C)
    (s : V) (hS : C.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hz : z ∈ P.working.rooted.otherRegion)
    (hno : ¬P.HasTAttachmentAwayFromY C) :
    Nonempty (TypeThreeExteriorDeletion P C s) := by
  have hScard : C.S.card = 1 := by
    rw [hS]
    simp
  obtain ⟨a, haQ, t, htT, hta⟩ :
      ∃ a ∈ P.working.rooted.otherRegion,
        ∃ t ∈ C.T, G.Adj t a := by
    simpa [hcore, Core.HasTAttachment, Core.T] using
      hasTAttachment_of_typeThree_card_S_one
        M P C hcore hScard hregion
  have hay : a = y := by
    by_contra hne
    exact hno ⟨a, haQ, hne, t, htT, hta⟩
  exact ⟨{
    core_eq := hcore
    side_eq := hS
    exception_mem_region := hz
    region_ne_singleton := hregion
    no_away_attachment := hno
    terminal := t
    terminal_mem := htT
    terminal_adj_y := by simpa [hay] using hta
  }⟩

/-- The exterior component removed by the recursive call, except for `y`. -/
noncomputable abbrev removed
    (_D : TypeThreeExteriorDeletion P C s) : Finset V :=
  P.working.rooted.otherRegion.erase y

/-- Ambient vertices surviving the deletion `C-y`. -/
abbrev SurvivingSet
    (D : TypeThreeExteriorDeletion P C s) : Set V :=
  {v | v ∉ D.removed}

/-- The vertex type of the recursive graph. -/
abbrev Vertex
    (D : TypeThreeExteriorDeletion P C s) :=
  D.SurvivingSet

/-- The recursive graph `G - (C-y)`. -/
def graph
    (D : TypeThreeExteriorDeletion P C s) :
    SimpleGraph D.Vertex :=
  G.induce D.SurvivingSet

/-- The exterior is a component region behind the type-3 carrier. -/
theorem componentRegion
    (D : TypeThreeExteriorDeletion P C s) :
    ComponentRegion G (Core.typeThree C).carrier
      P.working.rooted.otherRegion := by
  have h :=
    P.working.rooted.otherRegion_componentRegion
  rw [D.core_eq] at h
  exact h

/-- Every core vertex lies outside the selected exterior component. -/
theorem core_not_mem_region
    (D : TypeThreeExteriorDeletion P C s)
    {v : V} (hv : v ∈ (Core.typeThree C).carrier) :
    v ∉ P.working.rooted.otherRegion :=
  fun hvQ => D.componentRegion.not_mem_separator hvQ hv

/-- The original root survives the deletion. -/
theorem root_not_mem_removed
    (D : TypeThreeExteriorDeletion P C s) :
    x ∉ D.removed := by
  intro hx
  exact D.core_not_mem_region
    (Core.typeThree C).root_mem_carrier
    (Finset.mem_of_mem_erase hx)

/-- The retained exterior root survives the deletion. -/
theorem otherRoot_not_mem_removed
    (D : TypeThreeExteriorDeletion P C s) :
    y ∉ D.removed := by
  simp [removed]

/-- The singleton `S`-vertex survives the deletion. -/
theorem side_not_mem_removed
    (D : TypeThreeExteriorDeletion P C s) :
    s ∉ D.removed := by
  have hsS : s ∈ C.S := by
    rw [D.side_eq]
    simp
  intro hs
  exact D.core_not_mem_region
    ((Core.typeThree C).S_subset_carrier
      (by simpa [Core.S] using hsS))
    (Finset.mem_of_mem_erase hs)

/-- The selected `T`-vertex survives the deletion. -/
theorem terminal_not_mem_removed
    (D : TypeThreeExteriorDeletion P C s) :
    D.terminal ∉ D.removed := by
  intro ht
  exact D.core_not_mem_region
    ((Core.typeThree C).T_subset_carrier
      (by simpa [Core.T] using D.terminal_mem))
    (Finset.mem_of_mem_erase ht)

/-- The left root of the recursive graph. -/
def leftRoot
    (D : TypeThreeExteriorDeletion P C s) : D.Vertex :=
  ⟨x, D.root_not_mem_removed⟩

/-- The right root of the recursive graph. -/
def rightRoot
    (D : TypeThreeExteriorDeletion P C s) : D.Vertex :=
  ⟨y, D.otherRoot_not_mem_removed⟩

/-- The recursive exceptional vertex. -/
def sideException
    (D : TypeThreeExteriorDeletion P C s) : D.Vertex :=
  ⟨s, D.side_not_mem_removed⟩

/-- A nonexceptional witness in the recursive graph. -/
def terminalVertex
    (D : TypeThreeExteriorDeletion P C s) : D.Vertex :=
  ⟨D.terminal, D.terminal_not_mem_removed⟩

/-- The recursive roots remain distinct. -/
theorem leftRoot_ne_rightRoot
    (M : MinimalCounterexample q G x y z)
    (D : TypeThreeExteriorDeletion P C s) :
    D.leftRoot ≠ D.rightRoot := by
  intro h
  exact M.roots_ne (congrArg Subtype.val h)

/-- The induced recursive graph embeds canonically in the ambient graph. -/
def embedding
    (D : TypeThreeExteriorDeletion P C s) :
    D.graph ↪g G :=
  Embedding.induce D.SurvivingSet

@[simp] theorem embedding_apply
    (D : TypeThreeExteriorDeletion P C s)
    (v : D.Vertex) :
    D.embedding v = v.1 :=
  rfl

/-- Vertices outside the entire selected exterior component. -/
abbrev BaseVertex
    (_D : TypeThreeExteriorDeletion P C s) :=
  ComponentPruning.Outside P.working.rooted.otherRegion

/-- The induced graph obtained by pruning the entire selected component. -/
def baseGraph
    (_D : TypeThreeExteriorDeletion P C s) :
    SimpleGraph (ComponentPruning.Outside
      P.working.rooted.otherRegion) :=
  G.induce {v | v ∉ P.working.rooted.otherRegion}

/-- The core root in the fully pruned graph. -/
noncomputable def baseRoot
    (D : TypeThreeExteriorDeletion P C s) :
    D.BaseVertex :=
  ComponentPruning.boundaryVertex D.componentRegion x
    (Core.typeThree C).root_mem_carrier

/-- The selected `T`-vertex in the fully pruned graph. -/
noncomputable def baseTerminal
    (D : TypeThreeExteriorDeletion P C s) :
    D.BaseVertex :=
  ComponentPruning.boundaryVertex D.componentRegion D.terminal
    ((Core.typeThree C).T_subset_carrier
      (by simpa [Core.T] using D.terminal_mem))

/-- The two selected base vertices are distinct. -/
theorem baseRoot_ne_baseTerminal
    (D : TypeThreeExteriorDeletion P C s) :
    D.baseRoot ≠ D.baseTerminal := by
  intro h
  have hval : x = D.terminal :=
    congrArg Subtype.val h
  apply C.root_not_mem_T
  simpa [hval] using D.terminal_mem

/--
The fully pruned graph is 2-connected.  Component pruning is applied with
the type-3 carrier as its 2-connected anchor.  The nominal root edge
`x-terminal` is already a genuine type-3 core edge and can therefore be
removed from the conclusion.
-/
theorem baseGraph_two_connected
    (M : MinimalCounterexample q G x y z)
    (D : TypeThreeExteriorDeletion P C s) :
    IsTwoConnected D.baseGraph := by
  let xC : C.Carrier := C.rootVertex
  let tC : C.Carrier :=
    ⟨D.terminal,
      (Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using D.terminal_mem)⟩
  have hanchor :
      IsTwoConnected
        (C.carrierGraph ⊔ edge xC tC) :=
    (C.carrierGraph_two_connected D.side_eq).mono
      le_sup_left
  have hrooted :
      IsTwoConnected
        (D.baseGraph ⊔
          edge D.baseRoot D.baseTerminal) := by
    exact ComponentPruning.rooted_two_connected
      M.underlying_two_connected D.componentRegion
      (Core.typeThree C).root_mem_carrier
      ((Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using D.terminal_mem))
      hanchor
  have hxt :
      D.baseGraph.Adj D.baseRoot D.baseTerminal := by
    change G.Adj x D.terminal
    exact C.root_adj_T D.terminal D.terminal_mem
  have hedge :
      edge D.baseRoot D.baseTerminal ≤ D.baseGraph :=
    (edge_le_iff D.baseGraph).2 (Or.inr hxt)
  simpa [sup_eq_left.mpr hedge] using hrooted

/-- The singleton-side type-3 carrier has at least four vertices. -/
theorem four_le_core_carrier_card
    (D : TypeThreeExteriorDeletion P C s) :
    4 ≤ (Core.typeThree C).carrier.card := by
  have hTtwo : 2 ≤ C.T.card :=
    (Nat.le_max_right (P.working.rank + 1) 2).trans
      C.card_T_lower
  have hxNot :
      x ∉ C.S ∪ C.T := by
    simp [C.root_not_mem_S, C.root_not_mem_T]
  rw [Core.carrier, Core.S, Core.T,
    Finset.card_insert_of_notMem hxNot,
    Finset.card_union_of_disjoint C.disjoint,
    D.side_eq]
  simp only [Finset.card_singleton]
  omega

/--
Every surviving vertex other than `y` lies outside the entire selected
exterior component.
-/
theorem not_mem_region_of_survives_of_ne_y
    (D : TypeThreeExteriorDeletion P C s)
    {v : V} (hv : v ∉ D.removed) (hvy : v ≠ y) :
    v ∉ P.working.rooted.otherRegion := by
  intro hvQ
  apply hv
  exact Finset.mem_erase.mpr ⟨hvy, hvQ⟩

/--
The carrier after deleting `C-y` is canonically `Option` of the carrier
outside all of `C`: `none` represents the retained vertex `y`.
-/
noncomputable def optionBaseEquiv
    (D : TypeThreeExteriorDeletion P C s) :
    Option D.BaseVertex ≃ D.Vertex where
  toFun
    | none => D.rightRoot
    | some v =>
        ⟨v.1, fun hv =>
          v.2 (Finset.mem_of_mem_erase hv)⟩
  invFun v :=
    if h : v.1 = y then none
    else some
      ⟨v.1, D.not_mem_region_of_survives_of_ne_y v.2 h⟩
  left_inv v := by
    cases v with
    | none =>
        simp [rightRoot]
    | some v =>
        have hvy : v.1 ≠ y := by
          intro h
          apply v.2
          simpa [h] using
            P.working.rooted.other_root_mem_otherRegion
        simp [hvy]
  right_inv v := by
    by_cases h : v.1 = y
    · apply Subtype.ext
      simp [h, rightRoot]
    · apply Subtype.ext
      simp [h]

@[simp] theorem optionBaseEquiv_none
    (D : TypeThreeExteriorDeletion P C s) :
    D.optionBaseEquiv none = D.rightRoot :=
  rfl

@[simp] theorem optionBaseEquiv_some
    (D : TypeThreeExteriorDeletion P C s)
    (v : D.BaseVertex) :
    (D.optionBaseEquiv (some v) : V) = v.1 :=
  rfl

@[simp] theorem optionBaseEquiv_baseRoot
    (D : TypeThreeExteriorDeletion P C s) :
    D.optionBaseEquiv (some D.baseRoot) = D.leftRoot := by
  apply Subtype.ext
  rfl

@[simp] theorem optionBaseEquiv_baseTerminal
    (D : TypeThreeExteriorDeletion P C s) :
    D.optionBaseEquiv (some D.baseTerminal) =
      D.terminalVertex := by
  apply Subtype.ext
  rfl

/-- The two neighbours used to adjoin the retained vertex `y`. -/
noncomputable def baseAttachments
    (D : TypeThreeExteriorDeletion P C s) :
    Finset D.BaseVertex :=
  {D.baseRoot, D.baseTerminal}

/-- The retained vertex is adjoined through two distinct base vertices. -/
theorem two_le_baseAttachments_card
    (D : TypeThreeExteriorDeletion P C s) :
    2 ≤ D.baseAttachments.card := by
  simp [baseAttachments, D.baseRoot_ne_baseTerminal]

/--
The recursive graph is rooted 2-connected.

First prune the whole exterior component.  Then reinsert `y` through the
genuine edge to `terminal` and the rooted edge to `x`.  The explicit
equivalence `optionBaseEquiv` identifies this root-adjoined graph with a
spanning subgraph of `graph ⊔ xy`.
-/
theorem rootedGraph_two_connected
    (M : MinimalCounterexample q G x y z)
    (D : TypeThreeExteriorDeletion P C s) :
    IsTwoConnected
      (D.graph ⊔ edge D.leftRoot D.rightRoot) := by
  let A : SimpleGraph (Option D.BaseVertex) :=
    adjoinRoot D.baseGraph D.baseAttachments
  have hA : IsTwoConnected A :=
    isTwoConnected_adjoinRoot
      D.baseGraph D.baseAttachments
      (D.baseGraph_two_connected M)
      D.two_le_baseAttachments_card
  let e := D.optionBaseEquiv
  have hmap :
      IsTwoConnected (A.map e) :=
    hA.map_iso (SimpleGraph.Iso.map e A)
  apply hmap.mono
  intro u v huv
  rw [SimpleGraph.map_adj'] at huv
  obtain ⟨_, a, b, hab, rfl, rfl⟩ := huv
  cases a with
  | none =>
      cases b with
      | none =>
          exact False.elim hab
      | some b =>
          have hb :
              b = D.baseRoot ∨ b = D.baseTerminal := by
            simpa [A, baseAttachments] using hab
          rcases hb with rfl | rfl
          · right
            simp [e, SimpleGraph.edge_adj,
              (D.leftRoot_ne_rightRoot M).symm]
          · left
            change G.Adj y D.terminal
            exact D.terminal_adj_y.symm
  | some a =>
      cases b with
      | none =>
          have ha :
              a = D.baseRoot ∨ a = D.baseTerminal := by
            simpa [A, baseAttachments] using hab
          rcases ha with rfl | rfl
          · right
            simp [e, SimpleGraph.edge_adj,
              D.leftRoot_ne_rightRoot M]
          · left
            change G.Adj D.terminal y
            exact D.terminal_adj_y
      | some b =>
          left
          exact hab

/--
A recursive ordinary vertex is distinct from the original exception.

If `z = y`, this follows from avoidance of the recursive right root.  If
`z ≠ y`, membership of `z` in the selected exterior means that `z` was
deleted.
-/
theorem ambient_ne_exception
    (D : TypeThreeExteriorDeletion P C s)
    (v : D.Vertex)
    (_hvx : v ≠ D.leftRoot)
    (hvy : v ≠ D.rightRoot)
    (_hvs : v ≠ D.sideException) :
    v.1 ≠ z := by
  by_cases hzy : z = y
  · intro hvz
    apply hvy
    apply Subtype.ext
    exact hvz.trans hzy
  · intro hvz
    apply v.2
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · exact fun h => hzy (hvz.symm.trans h)
    · simpa [hvz] using D.exception_mem_region

/--
Every ambient neighbour of a recursive ordinary vertex survives deletion.
The only possible lost neighbours of a core vertex lie in the selected
exterior.  The root and singleton `S`-vertex are excluded, while the
negated Claim 3.14 conclusion excludes such neighbours for `T`.
-/
theorem neighbor_not_mem_removed
    (D : TypeThreeExteriorDeletion P C s)
    (v : D.Vertex)
    (hvx : v ≠ D.leftRoot)
    (hvy : v ≠ D.rightRoot)
    (hvs : v ≠ D.sideException)
    {w : V} (hvw : G.Adj v.1 w) :
    w ∉ D.removed := by
  intro hwRemoved
  have hwErase := Finset.mem_erase.mp hwRemoved
  have hwNeY : w ≠ y := hwErase.1
  have hwQ :
      w ∈ P.working.rooted.otherRegion :=
    hwErase.2
  have hvx' : v.1 ≠ x := by
    intro h
    apply hvx
    apply Subtype.ext
    exact h
  have hvy' : v.1 ≠ y := by
    intro h
    apply hvy
    apply Subtype.ext
    exact h
  have hvs' : v.1 ≠ s := by
    intro h
    apply hvs
    apply Subtype.ext
    exact h
  by_cases hvCore :
      v.1 ∈ (Core.typeThree C).carrier
  · rcases
        (Core.typeThree C
          ).mem_S_or_mem_T_of_mem_carrier_of_ne_root
            hvCore hvx' with hvS | hvT
    · have hvEqS : v.1 = s := by
        have hvS' : v.1 ∈ C.S := by
          simpa [Core.S] using hvS
        rw [D.side_eq] at hvS'
        simpa using hvS'
      exact hvs' hvEqS
    · apply D.no_away_attachment
      exact ⟨w, hwQ, hwNeY, v.1, hvT, hvw⟩
  · have hvQ :
        v.1 ∈ P.working.rooted.otherRegion :=
      D.componentRegion.closed hwQ hvw.symm hvCore
    exact v.2 (Finset.mem_erase.mpr ⟨hvy', hvQ⟩)

/-- Recursive ordinary vertices retain their exact ambient degree. -/
theorem finiteDegree_graph_eq
    (D : TypeThreeExteriorDeletion P C s)
    (v : D.Vertex)
    (hvx : v ≠ D.leftRoot)
    (hvy : v ≠ D.rightRoot)
    (hvs : v ≠ D.sideException) :
    finiteDegree D.graph v = finiteDegree G v.1 := by
  let N : Set V := G.neighborSet v.1
  let NI : Set D.Vertex := D.graph.neighborSet v
  have himage : Subtype.val '' NI = N := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hw
      have hwSurvives :
          w ∉ D.removed :=
        D.neighbor_not_mem_removed v hvx hvy hvs hw
      exact ⟨⟨w, hwSurvives⟩, hw, rfl⟩
  unfold finiteDegree
  change NI.ncard = N.ncard
  rw [← himage,
    Set.ncard_image_of_injective _ Subtype.val_injective]

/-- The selected terminal vertex is different from the recursive roots and exception. -/
theorem terminalVertex_ordinary
    (D : TypeThreeExteriorDeletion P C s) :
    D.terminalVertex ≠ D.leftRoot ∧
      D.terminalVertex ≠ D.rightRoot ∧
        D.terminalVertex ≠ D.sideException := by
  have htNeX : D.terminal ≠ x := by
    intro h
    apply C.root_not_mem_T
    simpa [h] using D.terminal_mem
  have htNeY : D.terminal ≠ y := by
    intro h
    apply D.core_not_mem_region
      ((Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using D.terminal_mem))
    simpa [h] using
      P.working.rooted.other_root_mem_otherRegion
  have hsS : s ∈ C.S := by
    rw [D.side_eq]
    simp
  have htNeS : D.terminal ≠ s := by
    intro h
    exact Finset.disjoint_left.mp C.disjoint
      hsS (by simpa [h] using D.terminal_mem)
  exact ⟨by
      intro h
      exact htNeX (congrArg Subtype.val h),
    by
      intro h
      exact htNeY (congrArg Subtype.val h),
    by
      intro h
      exact htNeS (congrArg Subtype.val h)⟩

/-- The recursive degree condition is at least the ambient one. -/
theorem degree_lower
    (M : MinimalCounterexample q G x y z)
    (D : TypeThreeExteriorDeletion P C s)
    (v : D.Vertex)
    (hvx : v ≠ D.leftRoot)
    (hvy : v ≠ D.rightRoot)
    (hvs : v ≠ D.sideException) :
    q + 1 ≤ finiteDegree D.graph v := by
  rw [D.finiteDegree_graph_eq v hvx hvy hvs]
  exact M.degree_lower v.1
    (fun h => hvx (Subtype.ext h))
    (fun h => hvy (Subtype.ext h))
    (D.ambient_ne_exception v hvx hvy hvs)

/-- The nonsingleton exterior has a vertex other than `y`. -/
theorem exists_removed_vertex
    (D : TypeThreeExteriorDeletion P C s) :
    ∃ w : V, w ∈ D.removed := by
  have hyQ :
      y ∈ P.working.rooted.otherRegion :=
    P.working.rooted.other_root_mem_otherRegion
  have hother :
      ∃ w ∈ P.working.rooted.otherRegion, w ≠ y := by
    by_contra h
    push Not at h
    apply D.region_ne_singleton
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hyQ, fun w hw => h w hw⟩
  obtain ⟨w, hwQ, hwy⟩ := hother
  exact ⟨w, Finset.mem_erase.mpr ⟨hwy, hwQ⟩⟩

/-- Deleting the nonempty set `C-y` strictly reduces the carrier. -/
theorem vertex_card_lt
    (D : TypeThreeExteriorDeletion P C s) :
    Fintype.card D.Vertex < Fintype.card V := by
  obtain ⟨w, hwRemoved⟩ := D.exists_removed_vertex
  apply Fintype.card_subtype_lt
  exact fun hw => hw hwRemoved

/-- The induced recursive graph has no more edges than the ambient graph. -/
theorem graph_edgeSet_ncard_le
    (D : TypeThreeExteriorDeletion P C s) :
    D.graph.edgeSet.ncard ≤ G.edgeSet.ncard := by
  let e := D.embedding
  have hsubset :
      Sym2.map e '' D.graph.edgeSet ⊆ G.edgeSet :=
    e.toHom.image_edgeSet_subset
  calc
    D.graph.edgeSet.ncard =
        (Sym2.map e '' D.graph.edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective e.injective)]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

/-- The deletion graph is strictly smaller in the COY induction measure. -/
theorem complexity_lt
    (D : TypeThreeExteriorDeletion P C s) :
    rootedComplexity D.graph < rootedComplexity G :=
  rootedComplexity_lt_of_card_lt_of_edgeCount_le
    D.vertex_card_lt D.graph_edgeSet_ncard_le

/-- The deletion graph, rooted at `x,y` with exception `s`, is a valid recursive instance. -/
theorem recursiveInstance
    (M : MinimalCounterexample q G x y z)
    (D : TypeThreeExteriorDeletion P C s) :
    RootedInstance q D.graph D.leftRoot D.rightRoot
      D.sideException where
  q_pos := M.q_pos
  q_le_four := M.q_le_four
  roots_ne := D.leftRoot_ne_rightRoot M
  rooted_two_connected := D.rootedGraph_two_connected M
  ordinary_nonempty :=
    ⟨D.terminalVertex,
      D.terminalVertex_ordinary.1,
      D.terminalVertex_ordinary.2.1,
      D.terminalVertex_ordinary.2.2⟩
  degree_lower := D.degree_lower M

/-- Minimality solves the recursive deletion instance. -/
theorem recursiveFamily
    (M : MinimalCounterexample q G x y z)
    (D : TypeThreeExteriorDeletion P C s) :
    Nonempty
      (AdmissiblePathFamily D.graph D.leftRoot D.rightRoot q) :=
  M.smaller_solvable (D.recursiveInstance M) D.complexity_lt

/--
The recursive family maps directly back to an ambient `x-y` family,
contradicting minimality.
-/
theorem false_of_data
    (M : MinimalCounterexample q G x y z)
    (D : TypeThreeExteriorDeletion P C s) :
    False := by
  obtain ⟨F⟩ := D.recursiveFamily M
  let mapped :=
    F.mapInjectiveHom D.embedding.toHom D.embedding.injective
  apply M.no_paths
  exact ⟨by simpa [mapped, leftRoot, rightRoot] using mapped⟩

end TypeThreeExteriorDeletion

end PreferredWorkingCoreData

end COY

end DeanK5
