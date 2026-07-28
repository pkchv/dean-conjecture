import DeanK5.Graph.Connectivity
import DeanK5.Graph.Separation

/-!
# Boundary auxiliary graphs

This module contains the generic represented-endpoint, boundary-degree,
two-root auxiliary-graph, connectivity, and root-deleted-carrier machinery
used by the boundary lifting arguments.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {W : Type u}

/-- The old vertices in a represented boundary set adjacent to `w`. -/
noncomputable def boundaryEndsIn
    (J : SimpleGraph W) (Q R : Finset W)
    (w : (↑Q : Set W)) : Finset W :=
  by
    classical
    exact R.filter fun x => J.Adj w.1 x

@[simp] theorem mem_boundaryEndsIn
    (J : SimpleGraph W) (Q R : Finset W)
    (w : (↑Q : Set W)) (x : W) :
    x ∈ boundaryEndsIn J Q R w ↔
      x ∈ R ∧ J.Adj w.1 x := by
  classical
  simp [boundaryEndsIn]

theorem boundaryEndsIn_nonempty_of_adj
    (J : SimpleGraph W) (Q R : Finset W)
    (w : (↑Q : Set W)) {x : W}
    (hxR : x ∈ R) (hwx : J.Adj w.1 x) :
    (boundaryEndsIn J Q R w).Nonempty :=
  by
    classical
    exact ⟨x, by simp [hxR, hwx]⟩
/--
The number of neighbors of `w` in a finite boundary set.  This is the
paper's `d_F(w)` when the boundary is the core carrier.
-/
noncomputable def finiteBoundaryDegree
    (J : SimpleGraph W) (S : Finset W) (w : W) : ℕ :=
  (J.neighborSet w ∩ (↑S : Set W)).ncard

/-- Boundary degree is monotone in the boundary set. -/
theorem finiteBoundaryDegree_mono
    (J : SimpleGraph W) {S T : Finset W}
    (hST : S ⊆ T) (w : W) :
    finiteBoundaryDegree J S w ≤
      finiteBoundaryDegree J T w := by
  unfold finiteBoundaryDegree
  apply Set.ncard_le_ncard
    (ht := Set.toFinite _)
  intro z hz
  exact ⟨hz.1, hST hz.2⟩
theorem finiteBoundaryDegree_pos_iff
    (J : SimpleGraph W) (S : Finset W) (w : W) :
    0 < finiteBoundaryDegree J S w ↔
      ∃ x ∈ S, J.Adj w x := by
  classical
  unfold finiteBoundaryDegree
  rw [Set.ncard_pos]
  constructor
  · rintro ⟨x, hxAdj, hxS⟩
    exact ⟨x, hxS, hxAdj⟩
  · rintro ⟨x, hxS, hxAdj⟩
    exact ⟨x, hxAdj, hxS⟩

/--
Two distinct boundary incidences cannot both be concentrated at one
specified boundary vertex.
-/
theorem exists_boundary_neighbor_ne_of_two_le
    (J : SimpleGraph W) (S : Finset W) (w y : W)
    (hdegree : 2 ≤ finiteBoundaryDegree J S w) :
    ∃ x ∈ S, J.Adj w x ∧ x ≠ y := by
  by_contra hnone
  push Not at hnone
  have hsub :
      J.neighborSet w ∩ (↑S : Set W) ⊆ ({y} : Set W) := by
    intro x hx
    have hxy := hnone x hx.2 hx.1
    simpa using hxy
  have hcard :=
    Set.ncard_le_ncard hsub
  unfold finiteBoundaryDegree at hdegree
  have hone : ({y} : Set W).ncard = 1 :=
    Set.ncard_singleton y
  rw [hone] at hcard
  omega

/--
For a component region outside `S`, every neighbor of an old vertex is
either another old vertex or lies in `S`.  Thus inducing onto the region
loses at most exactly the number of boundary neighbors.
-/
theorem finiteDegree_le_induced_region_add_boundary
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (S Q : Finset W)
    (hQ : ComponentRegion J S Q)
    (w : (↑Q : Set W)) :
    finiteDegree J w.1 ≤
      finiteDegree (J.induce (↑Q : Set W)) w +
        finiteBoundaryDegree J S w.1 := by
  let NQ : Set W :=
    Subtype.val ''
      (J.induce (↑Q : Set W)).neighborSet w
  let NS : Set W :=
    J.neighborSet w.1 ∩ (↑S : Set W)
  have hsub : J.neighborSet w.1 ⊆ NQ ∪ NS := by
    intro v hwv
    by_cases hvS : v ∈ S
    · exact Or.inr ⟨hwv, hvS⟩
    · have hvQ : v ∈ Q :=
        hQ.closed w.2 hwv hvS
      exact Or.inl ⟨⟨v, hvQ⟩, hwv, rfl⟩
  unfold finiteDegree finiteBoundaryDegree
  calc
    (J.neighborSet w.1).ncard
        ≤ (NQ ∪ NS).ncard :=
      Set.ncard_le_ncard hsub
    _ ≤ NQ.ncard + NS.ncard :=
      Set.ncard_union_le NQ NS
    _ =
        ((J.induce (↑Q : Set W)).neighborSet w).ncard +
          (J.neighborSet w.1 ∩ (↑S : Set W)).ncard := by
      rw [Set.ncard_image_of_injective _
        Subtype.val_injective]
/-- Carrier used for the two artificial boundary roots and the old region. -/
abbrev BoundaryAuxVertex (Q : Finset W) :=
  Option (Option (↑Q : Set W))

/-- The left artificial root in the two-root auxiliary carrier. -/
def boundaryLeftRoot (Q : Finset W) : BoundaryAuxVertex Q := none

/-- The right artificial root in the two-root auxiliary carrier. -/
def boundaryRightRoot (Q : Finset W) : BoundaryAuxVertex Q := some none

/-- Embed an old region vertex into the two-root auxiliary carrier. -/
def boundaryOldVertex (Q : Finset W) (w : (↑Q : Set W)) :
    BoundaryAuxVertex Q := some (some w)

/--
The generic two-root auxiliary graph used in all cases of Lemma 6.3.
A root is adjacent to an old vertex exactly when its represented endpoint
set is nonempty.
-/
def boundaryAuxGraph
    (J : SimpleGraph W) (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W) :
    SimpleGraph (BoundaryAuxVertex Q) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some none => False
    | some none, none => False
    | some none, some none => False
    | none, some (some w) => (leftEnds w).Nonempty
    | some (some w), none => (leftEnds w).Nonempty
    | some none, some (some w) => (rightEnds w).Nonempty
    | some (some w), some none => (rightEnds w).Nonempty
    | some (some u), some (some v) => J.Adj u.1 v.1
  symm := by
    constructor
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact hab
        | some b =>
            cases b with
            | none => exact hab
            | some v => exact hab
    | some a =>
        cases b with
        | none =>
            cases a with
            | none => exact hab
            | some u => exact hab
        | some b =>
            cases a with
            | none =>
                cases b with
                | none => exact hab
                | some v => exact hab
            | some u =>
                cases b with
                | none => exact hab
                | some v => exact hab.symm
  loopless := by
    constructor
    intro a
    cases a with
    | none => simp
    | some a =>
        cases a with
        | none => simp
        | some w => exact J.loopless.irrefl w.1

@[simp] theorem boundaryAuxGraph_roots_not_adjacent
    (J : SimpleGraph W) (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W) :
    ¬(boundaryAuxGraph J Q leftEnds rightEnds).Adj
      (boundaryLeftRoot Q) (boundaryRightRoot Q) :=
  id

theorem finiteDegree_boundaryAuxGraph_old
    [Fintype W]
    (J : SimpleGraph W) (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (w : (↑Q : Set W)) :
    finiteDegree (boundaryAuxGraph J Q leftEnds rightEnds)
        (boundaryOldVertex Q w) =
      finiteDegree (J.induce (↑Q : Set W)) w +
        (if (leftEnds w).Nonempty then 1 else 0) +
        (if (rightEnds w).Nonempty then 1 else 0) := by
  classical
  let N : Set (BoundaryAuxVertex Q) :=
    boundaryOldVertex Q ''
      (J.induce (↑Q : Set W)).neighborSet w
  have hNcard :
      N.ncard =
        ((J.induce (↑Q : Set W)).neighborSet w).ncard := by
    exact Set.ncard_image_of_injective _
      (fun _ _ h => Option.some.inj (Option.some.inj h))
  have hleftNotN : boundaryLeftRoot Q ∉ N := by
    simp [N, boundaryLeftRoot, boundaryOldVertex]
  have hrightNotN : boundaryRightRoot Q ∉ N := by
    simp [N, boundaryRightRoot, boundaryOldVertex]
  have hrootsNe :
      boundaryLeftRoot Q ≠ boundaryRightRoot Q := by
    simp [boundaryLeftRoot, boundaryRightRoot]
  by_cases hleft : (leftEnds w).Nonempty <;>
    by_cases hright : (rightEnds w).Nonempty
  · have hneighbors :
        (boundaryAuxGraph J Q leftEnds rightEnds).neighborSet
            (boundaryOldVertex Q w) =
          insert (boundaryLeftRoot Q)
            (insert (boundaryRightRoot Q) N) := by
      ext z
      cases z with
      | none =>
          simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
            boundaryLeftRoot, boundaryRightRoot, boundaryOldVertex,
            hleft]
      | some z =>
          cases z with
          | none =>
              simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
                boundaryLeftRoot, boundaryRightRoot, boundaryOldVertex,
                N, hright]
          | some z =>
              simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
                boundaryLeftRoot, boundaryRightRoot, boundaryOldVertex,
                N]
    unfold finiteDegree
    rw [hneighbors,
      Set.ncard_insert_of_notMem (by
        simp [hrootsNe, hleftNotN]),
      Set.ncard_insert_of_notMem hrightNotN,
      hNcard]
    simp [hleft, hright]
  · have hneighbors :
        (boundaryAuxGraph J Q leftEnds rightEnds).neighborSet
            (boundaryOldVertex Q w) =
          insert (boundaryLeftRoot Q) N := by
      ext z
      cases z with
      | none =>
          simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
            boundaryLeftRoot, boundaryOldVertex, N, hleft]
      | some z =>
          cases z with
          | none =>
              simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
                boundaryLeftRoot, boundaryOldVertex,
                hright]
              exact hrightNotN
          | some z =>
              simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
                boundaryLeftRoot, boundaryOldVertex, N]
    unfold finiteDegree
    rw [hneighbors,
      Set.ncard_insert_of_notMem hleftNotN,
      hNcard]
    simp [hleft, hright]
  · have hneighbors :
        (boundaryAuxGraph J Q leftEnds rightEnds).neighborSet
            (boundaryOldVertex Q w) =
          insert (boundaryRightRoot Q) N := by
      ext z
      cases z with
      | none =>
          simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
            boundaryOldVertex, N, hleft]
          simp [boundaryRightRoot]
      | some z =>
          cases z with
          | none =>
              simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
                boundaryRightRoot, boundaryOldVertex, N, hright]
          | some z =>
              simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
                boundaryRightRoot, boundaryOldVertex, N]
    unfold finiteDegree
    rw [hneighbors,
      Set.ncard_insert_of_notMem hrightNotN,
      hNcard]
    simp [hleft, hright]
  · have hneighbors :
        (boundaryAuxGraph J Q leftEnds rightEnds).neighborSet
            (boundaryOldVertex Q w) = N := by
      ext z
      cases z with
      | none =>
          simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
            boundaryOldVertex, hleft]
          exact hleftNotN
      | some z =>
          cases z with
          | none =>
              simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
                boundaryOldVertex, hright]
              exact hrightNotN
          | some z =>
              simp [SimpleGraph.mem_neighborSet, boundaryAuxGraph,
                boundaryOldVertex, N]
    unfold finiteDegree
    rw [hneighbors, hNcard]
    simp [hleft, hright]

/--
Degree bookkeeping for all auxiliary graphs in Lemma 6.3.  If `k` root
edges are certified at `w`, then the auxiliary degree plus the number of
deleted core neighbors is at least the old degree plus `k`.
-/
theorem ambientDegree_add_le_auxDegree_add_boundary
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (S Q : Finset W)
    (hQ : ComponentRegion J S Q)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (w : (↑Q : Set W)) (k : ℕ)
    (hroots :
      k ≤ (if (leftEnds w).Nonempty then 1 else 0) +
        (if (rightEnds w).Nonempty then 1 else 0)) :
    finiteDegree J w.1 + k ≤
      finiteDegree
          (boundaryAuxGraph J Q leftEnds rightEnds)
          (boundaryOldVertex Q w) +
        finiteBoundaryDegree J S w.1 := by
  have hpartition :=
    finiteDegree_le_induced_region_add_boundary
      J S Q hQ w
  rw [finiteDegree_boundaryAuxGraph_old]
  omega
/--
Cut-component form of the end-block hypothesis in Lemma 6.1.  After any
old vertex is deleted, every surviving old vertex can reach an old vertex
attached to at least one boundary root.
-/
structure BoundaryAuxConnectivityData
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W) where
  /-- An old vertex attached to the left artificial root. -/
  leftWitness : (↑Q : Set W)
  /-- A distinct old vertex attached to the right artificial root. -/
  rightWitness : (↑Q : Set W)
  witnesses_ne : leftWitness ≠ rightWitness
  left_attached : (leftEnds leftWitness).Nonempty
  right_attached : (rightEnds rightWitness).Nonempty
  old_connected : (J.induce (↑Q : Set W)).Connected
  reaches_attachment_after_delete :
    ∀ (w z : (↑Q : Set W)) (hzw : z ≠ w),
      ∃ (a : (↑Q : Set W)) (haw : a ≠ w),
        ((leftEnds a).Nonempty ∨ (rightEnds a).Nonempty) ∧
        ((J.induce (↑Q : Set W)).induce
          {t | t.1 ≠ w.1}).Reachable
          ⟨z, fun h => hzw (Subtype.ext h)⟩
          ⟨a, fun h => haw (Subtype.ext h)⟩

theorem BoundaryAuxConnectivityData.two_le_card
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {Q : Finset W}
    {leftEnds rightEnds : (↑Q : Set W) → Finset W}
    (data :
      BoundaryAuxConnectivityData J Q leftEnds rightEnds) :
    2 ≤ Q.card := by
  have hpair :
      ({data.leftWitness, data.rightWitness} :
        Finset (↑Q : Set W)).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr data.witnesses_ne
  have hsub :
      ({data.leftWitness, data.rightWitness} :
        Finset (↑Q : Set W)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [hpair] at hcard
  change 2 ≤ Fintype.card (↑Q : Set W) at hcard
  simpa using hcard

/--
Construct the cut-component form of Lemma 6.1 directly from connectivity
after deleting one old vertex and every unrepresented boundary vertex.
This avoids treating the paper's end-block sentence as an axiom.
-/
noncomputable def boundaryAuxConnectivityDataOfDeletedConnected
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (S Q R : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (hQ : ComponentRegion J S Q)
    (hRS : R ⊆ S)
    (hR : R.Nonempty)
    (leftWitness rightWitness : (↑Q : Set W))
    (hwitnesses : leftWitness ≠ rightWitness)
    (hleft : (leftEnds leftWitness).Nonempty)
    (hright : (rightEnds rightWitness).Nonempty)
    (hdeleted :
      ∀ w : (↑Q : Set W),
        (J.induce
          {z | z ∉ insert w.1 (S \ R)}).Connected)
    (hrepresented :
      ∀ (a : (↑Q : Set W)) s,
        s ∈ R → J.Adj a.1 s →
          (leftEnds a).Nonempty ∨
            (rightEnds a).Nonempty) :
    BoundaryAuxConnectivityData
      J Q leftEnds rightEnds := by
  classical
  refine {
    leftWitness := leftWitness
    rightWitness := rightWitness
    witnesses_ne := hwitnesses
    left_attached := hleft
    right_attached := hright
    old_connected := hQ.connected
    reaches_attachment_after_delete := ?_
  }
  intro w z hzw
  obtain ⟨t, htR⟩ := hR
  have hwS : w.1 ∉ S :=
    hQ.not_mem_separator w.2
  have hzS : z.1 ∉ S :=
    hQ.not_mem_separator z.2
  have hzDeleted :
      z.1 ∉ insert w.1 (S \ R) := by
    intro hz
    simp only [Finset.mem_insert, Finset.mem_sdiff] at hz
    rcases hz with hzwVal | ⟨hzS', -⟩
    · exact hzw (Subtype.ext hzwVal)
    · exact hzS hzS'
  have htS : t ∈ S := hRS htR
  have htDeleted :
      t ∉ insert w.1 (S \ R) := by
    intro ht
    simp only [Finset.mem_insert, Finset.mem_sdiff] at ht
    rcases ht with htw | ⟨-, htNotR⟩
    · exact hwS (htw ▸ htS)
    · exact htNotR htR
  obtain ⟨p⟩ :=
    (hdeleted w).preconnected
      ⟨z.1, hzDeleted⟩ ⟨t, htDeleted⟩
  let pJ : J.Walk z.1 t :=
    p.map (Embedding.induce
      {z | z ∉ insert w.1 (S \ R)}).toHom
  have hwavoid : w.1 ∉ pJ.support := by
    intro hw
    change w.1 ∈
      (p.map (Embedding.induce
        {z | z ∉ insert w.1 (S \ R)}).toHom).support at hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨a, ha, haw⟩ := List.mem_map.mp hw
    apply a.2
    exact Finset.mem_insert.mpr (Or.inl haw)
  obtain ⟨a, haw, s, hsS, hsSupport, has, hreach⟩ :=
    hQ.reaches_boundary_of_walk_avoiding_vertex
      w z hzw
        (fun htQ => hQ.not_mem_separator htQ htS)
        pJ hwavoid
  have hsR : s ∈ R := by
    change s ∈
      (p.map (Embedding.induce
        {z | z ∉ insert w.1 (S \ R)}).toHom).support at hsSupport
    rw [SimpleGraph.Walk.support_map] at hsSupport
    obtain ⟨b, hb, hbs⟩ := List.mem_map.mp hsSupport
    by_contra hsNotR
    apply b.2
    have hsDiff : s ∈ S \ R :=
      Finset.mem_sdiff.mpr ⟨hsS, hsNotR⟩
    apply Finset.mem_insert_of_mem
    have hbsVal : b.1 = s := hbs
    rw [hbsVal]
    exact hsDiff
  exact ⟨a, haw, hrepresented a s hsR has, hreach⟩

/-- Connectivity supplies the deletion hypothesis above whenever the
unrepresented boundary together with one old vertex has size below `k`. -/
theorem deleted_boundary_connected_of_kConnected
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (S Q R : Finset W)
    (k : ℕ) (hconn : IsKConnected J k)
    (hcard : (S \ R).card + 1 < k) :
    ∀ w : (↑Q : Set W),
      (J.induce
        {z | z ∉ insert w.1 (S \ R)}).Connected := by
  intro w
  apply hconn.2
  calc
    (insert w.1 (S \ R)).card
        ≤ (S \ R).card + 1 :=
      Finset.card_insert_le _ _
    _ < k := hcard

/--
Lemma 6.1 in the cut-component form actually consumed by the proof.
The added root edge is used only to join components after an old vertex
is deleted.
-/
theorem boundaryAuxGraph_add_roots_two_connected
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (data : BoundaryAuxConnectivityData J Q leftEnds rightEnds) :
    IsTwoConnected
      (boundaryAuxGraph J Q leftEnds rightEnds ⊔
        edge (boundaryLeftRoot Q) (boundaryRightRoot Q)) := by
  let H :=
    boundaryAuxGraph J Q leftEnds rightEnds ⊔
      edge (boundaryLeftRoot Q) (boundaryRightRoot Q)
  let oldHom :
      J.induce (↑Q : Set W) →g H := {
    toFun := boundaryOldVertex Q
    map_rel' := by
      intro u v huv
      exact Or.inl huv
  }
  have hrootEdge :
      H.Adj (boundaryLeftRoot Q) (boundaryRightRoot Q) := by
    apply Or.inr
    simp [SimpleGraph.edge_adj, boundaryLeftRoot, boundaryRightRoot]
  have hleftEdge :
      H.Adj (boundaryLeftRoot Q)
        (boundaryOldVertex Q data.leftWitness) := by
    exact Or.inl data.left_attached
  have hrightEdge :
      H.Adj (boundaryRightRoot Q)
        (boundaryOldVertex Q data.rightWitness) := by
    exact Or.inl data.right_attached
  have hconnected : H.Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨boundaryLeftRoot Q, ?_⟩
    intro z
    cases z with
    | none => exact .rfl
    | some z =>
        cases z with
        | none => exact hrootEdge.reachable
        | some w =>
            exact hleftEdge.reachable.trans
              ((data.old_connected data.leftWitness w).map oldHom)
  have hdelete :
      ∀ x : BoundaryAuxVertex Q,
        (H.induce {z | z ≠ x}).Connected := by
    intro x
    cases x with
    | none =>
        let oldDel :
            J.induce (↑Q : Set W) →g
              H.induce {z | z ≠ boundaryLeftRoot Q} := {
          toFun w := ⟨boundaryOldVertex Q w, by
            simp [boundaryLeftRoot, boundaryOldVertex]⟩
          map_rel' := by
            intro u v huv
            exact Or.inl huv
        }
        have hrightDel :
            (H.induce {z | z ≠ boundaryLeftRoot Q}).Adj
              ⟨boundaryRightRoot Q, by
                simp [boundaryLeftRoot, boundaryRightRoot]⟩
              (oldDel data.rightWitness) := by
          exact hrightEdge
        rw [connected_iff_exists_forall_reachable]
        refine ⟨⟨boundaryRightRoot Q, by
          simp [boundaryRightRoot]⟩, ?_⟩
        rintro ⟨z, hz⟩
        cases z with
        | none => exact False.elim (hz rfl)
        | some z =>
            cases z with
            | none => exact .rfl
            | some w =>
                exact hrightDel.reachable.trans
                  ((data.old_connected data.rightWitness w).map oldDel)
    | some x =>
        cases x with
        | none =>
            let oldDel :
                J.induce (↑Q : Set W) →g
                  H.induce {z | z ≠ boundaryRightRoot Q} := {
              toFun w := ⟨boundaryOldVertex Q w, by
                simp [boundaryRightRoot, boundaryOldVertex]⟩
              map_rel' := by
                intro u v huv
                exact Or.inl huv
            }
            have hleftDel :
                (H.induce {z | z ≠ boundaryRightRoot Q}).Adj
                  ⟨boundaryLeftRoot Q, by
                    simp [boundaryLeftRoot, boundaryRightRoot]⟩
                  (oldDel data.leftWitness) := by
              exact hleftEdge
            rw [connected_iff_exists_forall_reachable]
            refine ⟨⟨boundaryLeftRoot Q, by
              simp [boundaryLeftRoot]⟩, ?_⟩
            rintro ⟨z, hz⟩
            cases z with
            | none => exact .rfl
            | some z =>
                cases z with
                | none => exact False.elim (hz rfl)
                | some w =>
                    exact hleftDel.reachable.trans
                      ((data.old_connected data.leftWitness w).map oldDel)
        | some w =>
            let oldDel :
                (J.induce (↑Q : Set W)).induce
                    {z | z.1 ≠ w.1} →g
                  H.induce {z | z ≠ boundaryOldVertex Q w} := {
              toFun z := ⟨boundaryOldVertex Q z.1, by
                intro h
                exact z.2 (by
                  simpa [boundaryOldVertex] using h)⟩
              map_rel' := by
                intro u v huv
                exact Or.inl huv
            }
            have hrootDel :
                (H.induce {z | z ≠ boundaryOldVertex Q w}).Adj
                  ⟨boundaryLeftRoot Q, by
                    simp [boundaryLeftRoot, boundaryOldVertex]⟩
                  ⟨boundaryRightRoot Q, by
                    simp [boundaryRightRoot, boundaryOldVertex]⟩ :=
              hrootEdge
            rw [connected_iff_exists_forall_reachable]
            refine ⟨⟨boundaryLeftRoot Q, by
              simp [boundaryLeftRoot]⟩, ?_⟩
            rintro ⟨z, hz⟩
            cases z with
            | none => exact .rfl
            | some z =>
                cases z with
                | none => exact hrootDel.reachable
                | some v =>
                    have hvw : v ≠ w := by
                      intro hvw
                      apply hz
                      simp [hvw]
                    obtain ⟨a, haw, haAttach, hva⟩ :=
                      data.reaches_attachment_after_delete w v hvw
                    have haOldNe :
                        boundaryOldVertex Q a ≠
                          boundaryOldVertex Q w := by
                      intro h
                      exact haw (by
                        simpa [boundaryOldVertex] using h)
                    have hrootToA :
                        (H.induce
                          {z | z ≠ boundaryOldVertex Q w}).Reachable
                          ⟨boundaryLeftRoot Q, by
                            simp [boundaryLeftRoot,
                              boundaryOldVertex]⟩
                          ⟨boundaryOldVertex Q a, haOldNe⟩ := by
                      rcases haAttach with haLeft | haRight
                      · exact (show
                          (H.induce
                            {z | z ≠ boundaryOldVertex Q w}).Adj
                            ⟨boundaryLeftRoot Q, by
                              simp [boundaryLeftRoot,
                                boundaryOldVertex]⟩
                            ⟨boundaryOldVertex Q a, haOldNe⟩ by
                              exact Or.inl haLeft).reachable
                      · have hrightToA :
                            (H.induce
                              {z | z ≠ boundaryOldVertex Q w}).Adj
                              ⟨boundaryRightRoot Q, by
                                simp [boundaryRightRoot,
                                  boundaryOldVertex]⟩
                              ⟨boundaryOldVertex Q a, haOldNe⟩ := by
                          exact Or.inl haRight
                        exact hrootDel.reachable.trans
                          hrightToA.reachable
                    have hvaMapped := hva.map oldDel
                    exact hrootToA.trans hvaMapped.symm
  have hQcard : 2 ≤ Q.card := by
    have hpair :
        ({data.leftWitness, data.rightWitness} :
          Finset (↑Q : Set W)).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr data.witnesses_ne
    have hsub :
        ({data.leftWitness, data.rightWitness} :
          Finset (↑Q : Set W)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have := Finset.card_le_card hsub
    rw [hpair] at this
    change 2 ≤ Fintype.card (↑Q : Set W) at this
    simpa using this
  have horder :
      3 ≤ Fintype.card (BoundaryAuxVertex Q) := by
    have hQtype :
        Fintype.card (↑Q : Set W) = Q.card := by
      simp
    simp only [BoundaryAuxVertex, Fintype.card_option]
    rw [hQtype]
    omega
  exact isTwoConnected_of_connected_delete_one H horder
    hconnected hdelete

/-- Recover the unique old region vertex from a non-root auxiliary vertex. -/
def boundaryInteriorOld
    (Q : Finset W)
    (z : {u : BoundaryAuxVertex Q //
      u ≠ boundaryLeftRoot Q ∧ u ≠ boundaryRightRoot Q}) :
    (↑Q : Set W) :=
  match h : z.1 with
  | none => False.elim (z.2.1 (by
      simpa [boundaryLeftRoot] using h))
  | some none => False.elim (z.2.2 (by
      simpa [boundaryRightRoot] using h))
  | some (some w) => w

@[simp] theorem boundaryInteriorOld_old
    (Q : Finset W) (w : (↑Q : Set W)) :
    boundaryInteriorOld Q
      ⟨boundaryOldVertex Q w, by
        simp [boundaryOldVertex, boundaryLeftRoot,
          boundaryRightRoot]⟩ = w :=
  by
    simp [boundaryInteriorOld, boundaryOldVertex]

theorem boundaryOldVertex_interior
    (Q : Finset W)
    (z : {u : BoundaryAuxVertex Q //
      u ≠ boundaryLeftRoot Q ∧ u ≠ boundaryRightRoot Q}) :
    boundaryOldVertex Q (boundaryInteriorOld Q z) = z.1 := by
  rcases z with ⟨z, hz⟩
  cases z with
  | none =>
      exact False.elim (hz.1 (by
        simp [boundaryLeftRoot]))
  | some z =>
      cases z with
      | none =>
          exact False.elim (hz.2 (by
            simp [boundaryRightRoot]))
      | some w =>
          simp [boundaryInteriorOld, boundaryOldVertex]

/-- The embedding of the old component carrier into its auxiliary graph. -/
def boundaryOldEmbedding (Q : Finset W) :
    (↑Q : Set W) ↪ BoundaryAuxVertex Q where
  toFun := boundaryOldVertex Q
  inj' := by
    intro u v huv
    simpa [boundaryOldVertex] using huv

/-- Deficient old vertices, represented on the auxiliary carrier. -/
def boundaryDeficient
    [DecidableEq W]
    (D Q : Finset W) : Finset (BoundaryAuxVertex Q) :=
  (Finset.univ.filter fun w : (↑Q : Set W) => w.1 ∈ D).map
    (boundaryOldEmbedding Q)

@[simp] theorem mem_boundaryDeficient_old
    [DecidableEq W]
    (D Q : Finset W) (w : (↑Q : Set W)) :
    boundaryOldVertex Q w ∈ boundaryDeficient D Q ↔ w.1 ∈ D := by
  simp [boundaryDeficient, boundaryOldEmbedding]

theorem mem_boundaryDeficient_iff
    [DecidableEq W]
    (D Q : Finset W) (z : BoundaryAuxVertex Q) :
    z ∈ boundaryDeficient D Q ↔
      ∃ w : (↑Q : Set W),
        w.1 ∈ D ∧ z = boundaryOldVertex Q w := by
  simp [boundaryDeficient, boundaryOldEmbedding, eq_comm]

@[simp] theorem leftRoot_not_mem_boundaryDeficient
    [DecidableEq W]
    (D Q : Finset W) :
    boundaryLeftRoot Q ∉ boundaryDeficient D Q := by
  simp [boundaryDeficient, boundaryOldEmbedding,
    boundaryLeftRoot, boundaryOldVertex]

@[simp] theorem rightRoot_not_mem_boundaryDeficient
    [DecidableEq W]
    (D Q : Finset W) :
    boundaryRightRoot Q ∉ boundaryDeficient D Q := by
  simp [boundaryDeficient, boundaryOldEmbedding,
    boundaryRightRoot, boundaryOldVertex]

end DeanK5
