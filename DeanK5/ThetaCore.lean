import DeanK5.ThetaResidue
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Intrinsic properties of theta graphs

This file proves ordinary theta-graph facts internally.  It first controls
degrees in an induced theta by embedding its neighbor set into the disjoint
union of the three path-neighbor sets.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace SimplePath

/--
From any surviving vertex of a simple path, one of the two endpoint
segments avoids a prescribed deleted vertex.  The returned segment also
records that it uses only vertices of the original path.
-/
theorem exists_endpoint_segment_avoiding
    (P : SimplePath G x y) {z d : V}
    (hz : z ∈ P.walk.support) (hzd : z ≠ d) :
    (∃ Q : SimplePath G z x,
        (∀ w ∈ Q.walk.support, w ∈ P.walk.support) ∧
        d ∉ Q.walk.support) ∨
      (∃ Q : SimplePath G z y,
        (∀ w ∈ Q.walk.support, w ∈ P.walk.support) ∧
        d ∉ Q.walk.support) := by
  obtain ⟨n, hnz, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  by_cases hd : d ∈ P.walk.support
  · obtain ⟨m, hmd, hmle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hd
    have hnm : n ≠ m := by
      intro h
      subst m
      exact hzd (hnz.symm.trans hmd)
    rcases Nat.lt_or_gt_of_ne hnm with hnm | hmn
    · left
      let Q : SimplePath G z x :=
        (P.take n).reverse.castStart hnz
      refine ⟨Q, ?_, ?_⟩
      · intro w hw
        have hwTake :
            w ∈ (P.take n).walk.support := by
          simpa [Q, SimplePath.reverse] using hw
        exact P.mem_support_of_mem_take n hwTake
      · intro hdQ
        have hdTake :
            d ∈ (P.take n).walk.support := by
          simpa [Q, SimplePath.reverse] using hdQ
        obtain ⟨q, hqd, hqle⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
            hdTake
        have hqleN : q ≤ n := by
          have hqmin :
              q ≤ min n P.length := by
            simpa [SimplePath.take,
              SimplePath.length] using hqle
          exact (le_min_iff.mp hqmin).1
        have hqleP : q ≤ P.walk.length := by
          simpa [SimplePath.length] using hqleN.trans hnle
        have hqdP : P.walk.getVert q = d := by
          simpa [SimplePath.take,
            Nat.min_eq_right hqleN] using hqd
        have hqm : q = m :=
          P.isPath.getVert_injOn
            (by simpa using hqleP)
            (by simpa using hmle)
            (hqdP.trans hmd.symm)
        omega
    · right
      let Q : SimplePath G z y :=
        (P.drop n).castStart hnz
      refine ⟨Q, ?_, ?_⟩
      · intro w hw
        exact P.mem_support_of_mem_drop n
          (by simpa [Q] using hw)
      · intro hdQ
        have hdDrop :
            d ∈ (P.drop n).walk.support := by
          simpa [Q] using hdQ
        obtain ⟨q, hqd, hqle⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
            hdDrop
        have hsumle : n + q ≤ P.walk.length := by
          simp only [SimplePath.drop,
            SimpleGraph.Walk.drop_length] at hqle
          omega
        have hqdP : P.walk.getVert (n + q) = d := by
          simpa [SimplePath.drop] using hqd
        have hmq : m = n + q :=
          P.isPath.getVert_injOn
            (by simpa using hmle)
            (by simpa using hsumle)
            (hmd.trans hqdP.symm)
        omega
  · left
    let Q : SimplePath G z x :=
      (P.take n).reverse.castStart hnz
    refine ⟨Q, ?_, ?_⟩
    · intro w hw
      have hwTake :
          w ∈ (P.take n).walk.support := by
        simpa [Q, SimplePath.reverse] using hw
      exact P.mem_support_of_mem_take n hwTake
    · intro hdQ
      apply hd
      have hdTake :
          d ∈ (P.take n).walk.support := by
        simpa [Q, SimplePath.reverse] using hdQ
      exact P.mem_support_of_mem_take n hdTake

end SimplePath

namespace Theta

theorem x_mem_verts_basic
    [DecidableEq V] (T : Theta G) :
    T.x ∈ T.verts := by
  simp only [Theta.verts, Finset.mem_biUnion]
  exact ⟨0, Finset.mem_univ _, by
    simp⟩

theorem y_mem_verts_basic
    [DecidableEq V] (T : Theta G) :
    T.y ∈ T.verts := by
  simp only [Theta.verts, Finset.mem_biUnion]
  exact ⟨0, Finset.mem_univ _, by
    simp⟩

/-- A theta has at least its two roots and one internal vertex. -/
theorem three_le_card_verts
    [DecidableEq V]
    (T : Theta G) :
    3 ≤ T.verts.card := by
  have hlong :
      2 ≤ (T.path 0).length ∨
        2 ≤ (T.path 1).length := by
    by_contra h
    push Not at h
    exact T.paths_ne 0 1 (by decide)
      (SimpleGraph.Walk.eq_of_length_le_one
        (by simpa [SimplePath.length] using h.1)
        (by simpa [SimplePath.length] using h.2))
  rcases hlong with hlong | hlong
  · let z := (T.path 0).walk.getVert 1
    have hzx : z ≠ T.x := by
      intro h
      have :
          (1 : ℕ) = 0 :=
        ((T.path 0).isPath.getVert_eq_start_iff
          (by
            change 1 ≤ (T.path 0).length
            omega)).1 h
      omega
    have hzy : z ≠ T.y := by
      intro h
      have :
          (1 : ℕ) = (T.path 0).walk.length :=
        ((T.path 0).isPath.getVert_eq_end_iff
          (by
            change 1 ≤ (T.path 0).length
            omega)).1 h
      simp only [SimplePath.length] at hlong
      omega
    have hz : z ∈ T.verts := by
      simp only [Theta.verts, Finset.mem_biUnion]
      exact ⟨0, Finset.mem_univ _,
        by simp [z]⟩
    have hsub :
        ({T.x, T.y, z} : Finset V) ⊆ T.verts := by
      intro w hw
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact T.x_mem_verts_basic
      · exact T.y_mem_verts_basic
      · exact hz
    have hcard :
        ({T.x, T.y, z} : Finset V).card = 3 := by
      have hxz : T.x ≠ z := fun h => hzx h.symm
      have hyz : T.y ≠ z := fun h => hzy h.symm
      simp [T.roots_ne, hxz, hyz]
    rw [← hcard]
    exact Finset.card_le_card hsub
  · let z := (T.path 1).walk.getVert 1
    have hzx : z ≠ T.x := by
      intro h
      have :
          (1 : ℕ) = 0 :=
        ((T.path 1).isPath.getVert_eq_start_iff
          (by
            change 1 ≤ (T.path 1).length
            omega)).1 h
      omega
    have hzy : z ≠ T.y := by
      intro h
      have :
          (1 : ℕ) = (T.path 1).walk.length :=
        ((T.path 1).isPath.getVert_eq_end_iff
          (by
            change 1 ≤ (T.path 1).length
            omega)).1 h
      simp only [SimplePath.length] at hlong
      omega
    have hz : z ∈ T.verts := by
      simp only [Theta.verts, Finset.mem_biUnion]
      exact ⟨1, Finset.mem_univ _,
        by simp [z]⟩
    have hsub :
        ({T.x, T.y, z} : Finset V) ⊆ T.verts := by
      intro w hw
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact T.x_mem_verts_basic
      · exact T.y_mem_verts_basic
      · exact hz
    have hcard :
        ({T.x, T.y, z} : Finset V).card = 3 := by
      have hxz : T.x ≠ z := fun h => hzx h.symm
      have hyz : T.y ≠ z := fun h => hzy h.symm
      simp [T.roots_ne, hxz, hyz]
    rw [← hcard]
    exact Finset.card_le_card hsub

/--
Lift an ambient path contained in the theta carrier and avoiding a deleted
finite set to reachability in the twice-induced graph.
-/
theorem exists_reachable_lift_avoiding
    [DecidableEq V]
    (T : Theta G)
    (S : Finset (↑T.verts : Set V))
    {a b : V} (Q : SimplePath G a b)
    (hverts :
      ∀ z ∈ Q.walk.support, z ∈ T.verts)
    (havoid :
      ∀ z : (↑T.verts : Set V),
        z.1 ∈ Q.walk.support → z ∉ S) :
    ∃ a' b' :
        {z : (↑T.verts : Set V) // z ∉ S},
      a'.1.1 = a ∧ b'.1.1 = b ∧
        ((G.induce (↑T.verts : Set V)).induce
          {z | z ∉ S}).Reachable a' b' := by
  let QH :=
    Q.walk.induce (↑T.verts : Set V)
      (fun z hz => hverts z hz)
  have hQHavoid :
      ∀ z ∈ QH.support, z ∉ S := by
    intro z hz
    have hzMapped :
        z.1 ∈
          (QH.map
            (SimpleGraph.Embedding.induce
              (G := G) (↑T.verts : Set V)).toHom).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    have hmap :
        QH.map
            (SimpleGraph.Embedding.induce
              (G := G) (↑T.verts : Set V)).toHom =
          Q.walk := by
      dsimp only [QH]
      apply SimpleGraph.Walk.map_induce
    have hzQ : z.1 ∈ Q.walk.support := by
      rw [hmap] at hzMapped
      exact hzMapped
    exact havoid z hzQ
  let QD :=
    QH.induce {z | z ∉ S} hQHavoid
  refine ⟨_, _, rfl, rfl, ⟨QD⟩⟩

theorem path_support_subset_verts_basic
    [DecidableEq V] (T : Theta G) (i : Fin 3) :
    ∀ z ∈ (T.path i).walk.support, z ∈ T.verts := by
  intro z hz
  simp only [Theta.verts, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, by simpa using hz⟩

theorem reachable_lift_avoiding
    [DecidableEq V]
    (T : Theta G)
    (S : Finset (↑T.verts : Set V))
    {a b : V} (Q : SimplePath G a b)
    (ha : a ∈ T.verts) (hb : b ∈ T.verts)
    (haS : (⟨a, ha⟩ :
      (↑T.verts : Set V)) ∉ S)
    (hbS : (⟨b, hb⟩ :
      (↑T.verts : Set V)) ∉ S)
    (hverts :
      ∀ z ∈ Q.walk.support, z ∈ T.verts)
    (havoid :
      ∀ z : (↑T.verts : Set V),
        z.1 ∈ Q.walk.support → z ∉ S) :
    ((G.induce (↑T.verts : Set V)).induce
      {z | z ∉ S}).Reachable
        ⟨⟨a, ha⟩, haS⟩
        ⟨⟨b, hb⟩, hbS⟩ := by
  obtain ⟨a', b', ha', hb', hab⟩ :=
    T.exists_reachable_lift_avoiding
      S Q hverts havoid
  have hea :
      a' = (⟨⟨a, ha⟩, haS⟩ :
        {z : (↑T.verts : Set V) // z ∉ S}) := by
    apply Subtype.ext
    apply Subtype.ext
    exact ha'
  have heb :
      b' = (⟨⟨b, hb⟩, hbS⟩ :
        {z : (↑T.verts : Set V) // z ∉ S}) := by
    apply Subtype.ext
    apply Subtype.ext
    exact hb'
  rwa [hea, heb] at hab

theorem connected_delete_empty
    [DecidableEq V]
    (T : Theta G) :
    ((G.induce (↑T.verts : Set V)).induce
      {z | z ∉ (∅ :
        Finset (↑T.verts : Set V))}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  let xT : (↑T.verts : Set V) :=
    ⟨T.x, T.x_mem_verts_basic⟩
  let xD :
      {z : (↑T.verts : Set V) //
        z ∉ (∅ : Finset (↑T.verts : Set V))} :=
    ⟨xT, by simp⟩
  refine ⟨xD, ?_⟩
  intro w
  have hwSome :
      ∃ i : Fin 3,
        w.1.1 ∈ (T.path i).walk.support := by
    simpa [Theta.verts] using w.1.2
  obtain ⟨i, hwi⟩ := hwSome
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwi
  let Q : SimplePath G T.x w.1.1 :=
    ((T.path i).take n).castEnd hn
  have hQverts :
      ∀ z ∈ Q.walk.support, z ∈ T.verts := by
    intro z hz
    have hzTake :
        z ∈ ((T.path i).take n).walk.support := by
      simpa [Q] using hz
    exact T.path_support_subset_verts_basic i z
      ((T.path i).mem_support_of_mem_take n hzTake)
  have hreach :=
    T.reachable_lift_avoiding
      (∅ : Finset (↑T.verts : Set V))
      Q T.x_mem_verts_basic w.1.2
      (by simp) (by simp) hQverts
      (by simp)
  simpa [xD, xT] using hreach

theorem connected_delete_singleton
    [DecidableEq V]
    (T : Theta G)
    (d : (↑T.verts : Set V)) :
    ((G.induce (↑T.verts : Set V)).induce
      {z | z ∉ ({d} :
        Finset (↑T.verts : Set V))}).Connected := by
  let S : Finset (↑T.verts : Set V) := {d}
  have segmentData :
      ∀ w :
          {z : (↑T.verts : Set V) // z ∉ S},
        ∃ i : Fin 3,
          w.1.1 ∈ (T.path i).walk.support := by
    intro w
    simpa [Theta.verts] using w.1.2
  have liftSegment :
      ∀ {w :
          {z : (↑T.verts : Set V) // z ∉ S}}
        {i : Fin 3}
        (hwi : w.1.1 ∈ (T.path i).walk.support)
        {e : V} (Q : SimplePath G w.1.1 e)
        (hQsub :
          ∀ z ∈ Q.walk.support,
            z ∈ (T.path i).walk.support)
        (hdQ : d.1 ∉ Q.walk.support)
        (he : e ∈ T.verts)
        (heS :
          (⟨e, he⟩ :
            (↑T.verts : Set V)) ∉ S),
        ((G.induce (↑T.verts : Set V)).induce
          {z | z ∉ S}).Reachable
            w ⟨⟨e, he⟩, heS⟩ := by
    intro w i hwi e Q hQsub hdQ he heS
    have hQverts :
        ∀ z ∈ Q.walk.support, z ∈ T.verts := by
      intro z hz
      exact T.path_support_subset_verts_basic i z
        (hQsub z hz)
    have hQavoid :
        ∀ z : (↑T.verts : Set V),
          z.1 ∈ Q.walk.support → z ∉ S := by
      intro z hz hzd
      have hzdEq : z = d := by
        simpa [S] using hzd
      subst z
      exact hdQ hz
    have hreach :=
      T.reachable_lift_avoiding
        S Q w.1.2 he w.2 heS
        hQverts hQavoid
    simpa using hreach
  by_cases hdx : d.1 = T.x
  · have hyS :
        (⟨T.y, T.y_mem_verts_basic⟩ :
          (↑T.verts : Set V)) ∉ S := by
      simp only [S, Finset.mem_singleton]
      intro h
      have hyx : T.y = T.x :=
        (congrArg Subtype.val h).trans hdx
      exact T.roots_ne hyx.symm
    let yD :
        {z : (↑T.verts : Set V) // z ∉ S} :=
      ⟨⟨T.y, T.y_mem_verts_basic⟩, hyS⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨yD, ?_⟩
    intro w
    obtain ⟨i, hwi⟩ := segmentData w
    have hwd : w.1.1 ≠ d.1 := by
      intro h
      apply w.2
      simp only [Finset.mem_singleton]
      apply Subtype.ext
      exact h
    rcases (T.path i).exists_endpoint_segment_avoiding
        hwi hwd with ⟨Q, hQsub, hdQ⟩ |
          ⟨Q, hQsub, hdQ⟩
    · exfalso
      apply hdQ
      have hxQ : T.x ∈ Q.walk.support :=
        Q.walk.end_mem_support
      simp [hdx]
    · have hreach :=
        liftSegment hwi Q hQsub hdQ
          T.y_mem_verts_basic hyS
      simpa [yD] using hreach.symm
  · by_cases hdy : d.1 = T.y
    · have hxS :
          (⟨T.x, T.x_mem_verts_basic⟩ :
            (↑T.verts : Set V)) ∉ S := by
        simp only [S, Finset.mem_singleton]
        intro h
        have hxy : T.x = T.y :=
          (congrArg Subtype.val h).trans hdy
        exact T.roots_ne hxy
      let xD :
          {z : (↑T.verts : Set V) // z ∉ S} :=
        ⟨⟨T.x, T.x_mem_verts_basic⟩, hxS⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨xD, ?_⟩
      intro w
      obtain ⟨i, hwi⟩ := segmentData w
      have hwd : w.1.1 ≠ d.1 := by
        intro h
        apply w.2
        simp only [Finset.mem_singleton]
        apply Subtype.ext
        exact h
      rcases (T.path i).exists_endpoint_segment_avoiding
          hwi hwd with ⟨Q, hQsub, hdQ⟩ |
            ⟨Q, hQsub, hdQ⟩
      · have hreach :=
          liftSegment hwi Q hQsub hdQ
            T.x_mem_verts_basic hxS
        simpa [xD] using hreach.symm
      · exfalso
        apply hdQ
        have hyQ : T.y ∈ Q.walk.support :=
          Q.walk.end_mem_support
        simp [hdy]
    · have hxS :
          (⟨T.x, T.x_mem_verts_basic⟩ :
            (↑T.verts : Set V)) ∉ S := by
        simp only [S, Finset.mem_singleton]
        intro h
        exact hdx (congrArg Subtype.val h).symm
      have hyS :
          (⟨T.y, T.y_mem_verts_basic⟩ :
            (↑T.verts : Set V)) ∉ S := by
        simp only [S, Finset.mem_singleton]
        intro h
        exact hdy (congrArg Subtype.val h).symm
      have hdSome :
          ∃ i : Fin 3,
            d.1 ∈ (T.path i).walk.support := by
        simpa [Theta.verts] using d.2
      obtain ⟨i, hdi⟩ := hdSome
      obtain ⟨j, hji⟩ := exists_ne i
      have hdj :
          d.1 ∉ (T.path j).walk.support := by
        intro hdj
        rcases T.eq_root_of_mem_two_paths
            (fun h => hji h.symm) hdi hdj with hx | hy
        · exact hdx hx
        · exact hdy hy
      have hbridgeAvoid :
          ∀ z : (↑T.verts : Set V),
            z.1 ∈ (T.path j).walk.support → z ∉ S := by
        intro z hz hzd
        have hzdEq : z = d := by
          simpa [S] using hzd
        subst z
        exact hdj hz
      have hbridge :=
        T.reachable_lift_avoiding
          S (T.path j)
          T.x_mem_verts_basic T.y_mem_verts_basic
          hxS hyS
          (T.path_support_subset_verts_basic j)
          hbridgeAvoid
      let xD :
          {z : (↑T.verts : Set V) // z ∉ S} :=
        ⟨⟨T.x, T.x_mem_verts_basic⟩, hxS⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨xD, ?_⟩
      intro w
      obtain ⟨k, hwk⟩ := segmentData w
      have hwd : w.1.1 ≠ d.1 := by
        intro h
        apply w.2
        simp only [Finset.mem_singleton]
        apply Subtype.ext
        exact h
      rcases (T.path k).exists_endpoint_segment_avoiding
          hwk hwd with ⟨Q, hQsub, hdQ⟩ |
            ⟨Q, hQsub, hdQ⟩
      · have hreach :=
          liftSegment hwk Q hQsub hdQ
            T.x_mem_verts_basic hxS
        simpa [xD] using hreach.symm
      · have hreach :=
          liftSegment hwk Q hQsub hdQ
            T.y_mem_verts_basic hyS
        simpa [xD] using hbridge.trans hreach.symm

/--
The graph induced by the vertices of a theta is 2-connected. Extra ambient
edges can only help: the proof uses just the three constituent paths.
-/
theorem induced_isTwoConnected
    [DecidableEq V]
    (T : Theta G) :
    IsTwoConnected (G.induce (↑T.verts : Set V)) := by
  constructor
  · simpa using T.three_le_card_verts
  · intro S hScard
    by_cases hSempty : S = ∅
    · subst S
      exact T.connected_delete_empty
    · have hSnonempty : S.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hSempty
      have hScardOne : S.card = 1 := by
        have hpos := Finset.card_pos.mpr hSnonempty
        omega
      obtain ⟨d, rfl⟩ :=
        Finset.card_eq_one.mp hScardOne
      exact T.connected_delete_singleton d

theorem exists_path_toSubgraph_adj_of_induced_adj
    [DecidableEq V]
    (T : Theta G) (hinduced : T.IsInduced)
    {v w : (↑T.verts : Set V)}
    (hvw : (G.induce (↑T.verts : Set V)).Adj v w) :
    ∃ i : Fin 3,
      (T.path i).walk.toSubgraph.Adj v.1 w.1 := by
  have hvwG : G.Adj v.1 w.1 :=
    SimpleGraph.induce_adj.mp hvw
  have hedge : s(v.1, w.1) ∈ T.edges :=
    hinduced v.2 w.2 hvwG
  simp only [Theta.edges, Finset.mem_biUnion] at hedge
  obtain ⟨i, -, hi⟩ := hedge
  exact ⟨i,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
      (by simpa using hi)⟩

/--
Every neighbor in an induced theta is assigned to one constituent path
which supplies its edge.  Retaining the neighbor itself in the codomain
makes this assignment injective even when an edge belongs to more than one
leg at a root.
-/
noncomputable def neighborEmbedding
    [DecidableEq V]
    (T : Theta G) (hinduced : T.IsInduced)
    (v : (↑T.verts : Set V)) :
    (G.induce (↑T.verts : Set V)).neighborSet v ↪
      (Σ i : Fin 3,
        (T.path i).walk.toSubgraph.neighborSet v.1) where
  toFun w :=
    let h :=
      T.exists_path_toSubgraph_adj_of_induced_adj
        hinduced w.2
    ⟨Classical.choose h,
      ⟨w.1.1, Classical.choose_spec h⟩⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.2.1) hab

theorem finiteDegree_induced_le_sigma_path_neighbors
    [Fintype V] [DecidableEq V]
    (T : Theta G) (hinduced : T.IsInduced)
    (v : (↑T.verts : Set V)) :
    finiteDegree (G.induce (↑T.verts : Set V)) v ≤
      Nat.card
        (Σ i : Fin 3,
          (T.path i).walk.toSubgraph.neighborSet v.1) := by
  letI pathNeighborFintype (i : Fin 3) :
      Fintype
        ((T.path i).walk.toSubgraph.neighborSet v.1) :=
    (SimpleGraph.Walk.finite_neighborSet_toSubgraph
      (T.path i).walk).fintype
  letI inducedNeighborFintype :
      Fintype
        ((G.induce (↑T.verts : Set V)).neighborSet v) :=
    (Set.toFinite _).fintype
  have hcard :=
    Nat.card_le_card_of_injective
      (T.neighborEmbedding hinduced v)
      (T.neighborEmbedding hinduced v).injective
  simpa [finiteDegree, Nat.card_coe_set_eq] using hcard

theorem natCard_path_neighbors_start
    {x y : V} (P : SimplePath G x y) (hxy : x ≠ y) :
    Nat.card (P.walk.toSubgraph.neighborSet x) = 1 := by
  rw [Nat.card_coe_set_eq,
    P.isPath.neighborSet_toSubgraph_startpoint
      (SimpleGraph.Walk.not_nil_of_ne hxy)]
  simp

theorem natCard_path_neighbors_end
    {x y : V} (P : SimplePath G x y) (hxy : x ≠ y) :
    Nat.card (P.walk.toSubgraph.neighborSet y) = 1 := by
  rw [Nat.card_coe_set_eq,
    P.isPath.neighborSet_toSubgraph_endpoint
      (SimpleGraph.Walk.not_nil_of_ne hxy)]
  simp

theorem natCard_path_neighbors_internal
    {x y z : V} (P : SimplePath G x y)
    (hz : z ∈ P.walk.support)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    Nat.card (P.walk.toSubgraph.neighborSet z) = 2 := by
  obtain ⟨n, hnz, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    simp at hnz
    exact hzx hnz.symm
  have hnlt : n < P.walk.length := by
    by_contra hnot
    have hn : n = P.walk.length := by omega
    subst n
    simp at hnz
    exact hzy hnz.symm
  rw [← hnz, Nat.card_coe_set_eq,
    P.isPath.ncard_neighborSet_toSubgraph_internal_eq_two
      hn0 hnlt]

theorem natCard_path_neighbors_of_not_mem
    {x y z : V} (P : SimplePath G x y)
    (hz : z ∉ P.walk.support) :
    Nat.card (P.walk.toSubgraph.neighborSet z) = 0 := by
  have hempty :
      P.walk.toSubgraph.neighborSet z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hzw
    exact hz
      (SimpleGraph.Walk.mem_support_of_adj_toSubgraph hzw)
  rw [hempty]
  simp

/--
Inducedness rules out every chord not supplied by a theta leg. At a root,
each leg supplies at most one neighbor; at an internal vertex, exactly one
leg can supply neighbors and a simple path supplies at most two.
-/
theorem induced_finiteDegree_le_three
    [Fintype V] [DecidableEq V]
    (T : Theta G) (hinduced : T.IsInduced)
    (v : (↑T.verts : Set V)) :
    finiteDegree (G.induce (↑T.verts : Set V)) v ≤ 3 := by
  apply (T.finiteDegree_induced_le_sigma_path_neighbors
    hinduced v).trans
  rw [Nat.card_sigma]
  by_cases hvx : v.1 = T.x
  · calc
      (∑ i : Fin 3,
          Nat.card
            ((T.path i).walk.toSubgraph.neighborSet v.1)) =
          ∑ _i : Fin 3, 1 := by
            apply Finset.sum_congr rfl
            intro i _
            simpa [hvx] using
              natCard_path_neighbors_start
                (T.path i) T.roots_ne
      _ = 3 := by decide
      _ ≤ 3 := le_rfl
  by_cases hvy : v.1 = T.y
  · calc
      (∑ i : Fin 3,
          Nat.card
            ((T.path i).walk.toSubgraph.neighborSet v.1)) =
          ∑ _i : Fin 3, 1 := by
            apply Finset.sum_congr rfl
            intro i _
            simpa [hvy] using
              natCard_path_neighbors_end
                (T.path i) T.roots_ne
      _ = 3 := by decide
      _ ≤ 3 := le_rfl
  · have hvSome :
        ∃ i : Fin 3, v.1 ∈ (T.path i).walk.support := by
      simpa [Theta.verts] using v.2
    obtain ⟨i, hvi⟩ := hvSome
    have hfiber :
        ∀ j : Fin 3,
          Nat.card
              ((T.path j).walk.toSubgraph.neighborSet v.1) =
            if j = i then 2 else 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp [natCard_path_neighbors_internal
          (P := T.path i) hvi hvx hvy]
      · have hvj :
            v.1 ∉ (T.path j).walk.support := by
          intro hvj
          rcases T.eq_root_of_mem_two_paths
              (fun h => hji h.symm) hvi hvj with hroot | hroot
          · exact hvx hroot
          · exact hvy hroot
        simp [hji,
          natCard_path_neighbors_of_not_mem
            (P := T.path j) hvj]
    simp [hfiber]

end Theta

namespace ClassicalGraphTheory

/--
The path representation of a theta has its standard intrinsic properties.
Both conclusions are proved from the three certified simple paths; inducedness
is needed only for the degree bound.
-/
theorem induced_theta_core_properties
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Theta G)
    (hinduced : T.IsInduced) :
    IsTwoConnected (G.induce (↑T.verts : Set V)) ∧
      ∀ v : (↑T.verts : Set V),
        finiteDegree
          (G.induce (↑T.verts : Set V)) v ≤ 3 :=
  ⟨T.induced_isTwoConnected,
    T.induced_finiteDegree_le_three hinduced⟩

end ClassicalGraphTheory

end DeanK5
