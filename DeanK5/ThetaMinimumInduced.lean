import DeanK5.ThetaResidue

/-!
# Inducedness of a minimum theta

This file proves the first conclusion of GHLM Lemma 5.10 without using any
published input: in a graph of girth at least six, a theta with the fewest
vertices is induced.
-/

open SimpleGraph
open scoped Sym2

namespace DeanK5

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace Theta

private theorem mem_verts_of_mem_path
    [DecidableEq V] (T : Theta G) (i : Fin 3) {z : V}
    (hz : z ∈ (T.path i).walk.support) :
    z ∈ T.verts := by
  simp only [Theta.verts, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, by simpa using hz⟩

private theorem exists_path_of_mem_verts
    [DecidableEq V] (T : Theta G) {z : V}
    (hz : z ∈ T.verts) :
    ∃ i : Fin 3, z ∈ (T.path i).walk.support := by
  simp only [Theta.verts, Finset.mem_biUnion] at hz
  obtain ⟨i, -, hi⟩ := hz
  exact ⟨i, by simpa using hi⟩

private theorem getVert_ne_start
    {a b : V} (P : SimplePath G a b) {n : ℕ}
    (hnpos : 0 < n) (hn : n ≤ P.length) :
    P.walk.getVert n ≠ a := by
  intro h
  have hnzero :=
    (P.isPath.getVert_eq_start_iff (by
      simpa [SimplePath.length] using hn)).1 h
  omega

private theorem getVert_ne_end
    {a b : V} (P : SimplePath G a b) {n : ℕ}
    (hnlt : n < P.length) :
    P.walk.getVert n ≠ b := by
  intro h
  have hnend :=
    (P.isPath.getVert_eq_end_iff (by
      simpa [SimplePath.length] using hnlt.le)).1 h
  apply (Nat.ne_of_lt hnlt)
  simpa [SimplePath.length] using hnend

private theorem getVert_eq_iff
    {a b : V} (P : SimplePath G a b) {m n : ℕ}
    (hm : m ≤ P.length) (hn : n ≤ P.length) :
    P.walk.getVert m = P.walk.getVert n ↔ m = n := by
  constructor
  · intro h
    exact P.isPath.getVert_injOn
      (by simpa [SimplePath.length] using hm)
      (by simpa [SimplePath.length] using hn) h
  · exact fun h => h ▸ rfl

private theorem internal_mem_of_getVert
    {a b : V} (P : SimplePath G a b) {n : ℕ}
    (hnpos : 0 < n) (hnlt : n < P.length) :
    P.walk.getVert n ∈ P.internalSupport := by
  apply P.mem_internalSupport_of_mem_support
    (P.walk.getVert_mem_support n)
  · exact getVert_ne_start P hnpos hnlt.le
  · exact getVert_ne_end P hnlt

private theorem mem_take_support_position
    {a b z : V} (P : SimplePath G a b) (r : ℕ)
    (hr : r ≤ P.length)
    (hz : z ∈ (P.take r).walk.support) :
    ∃ n, n ≤ r ∧ n ≤ P.length ∧ P.walk.getVert n = z := by
  obtain ⟨n, hnz, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hnR : n ≤ r := by
    have : n ≤ min r P.length := by
      simpa [SimplePath.take, SimplePath.length] using hnle
    exact (le_min_iff.mp this).1
  refine ⟨n, hnR, hnR.trans hr, ?_⟩
  simpa [SimplePath.take,
    SimpleGraph.Walk.take_getVert,
    Nat.min_eq_right hnR] using hnz

private theorem mem_drop_tail_position
    {a b z : V} (P : SimplePath G a b) (s : ℕ)
    (hs : s ≤ P.length)
    (hz : z ∈ (P.drop s).walk.support.tail) :
    ∃ n, s < n ∧ n ≤ P.length ∧ P.walk.getVert n = z := by
  have hzSupport :
      z ∈ (P.drop s).walk.support :=
    List.mem_of_mem_tail hz
  obtain ⟨m, hmz, hmle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      hzSupport
  have hstartNotTail :
      (P.drop s).walk.getVert 0 ∉
        (P.drop s).walk.support.tail := by
    have hnodup :=
      (P.drop s).isPath.support_nodup
    rw [← (P.drop s).walk.cons_tail_support] at hnodup
    simpa using (List.nodup_cons.mp hnodup).1
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    exact hstartNotTail (hmz ▸ hz)
  have hsum : s + m ≤ P.length := by
    have hmle' : m ≤ P.length - s := by
      simpa [SimplePath.drop, SimplePath.length] using hmle
    omega
  refine ⟨s + m, by omega, hsum, ?_⟩
  simpa [SimplePath.drop,
    SimpleGraph.Walk.drop_getVert] using hmz

private def shortcut
    {a b : V} (P : SimplePath G a b)
    (r s : ℕ) (hrs : r < s) (hs : s ≤ P.length)
    (hchord : G.Adj (P.walk.getVert r) (P.walk.getVert s)) :
    SimplePath G a b := by
  have hr : r ≤ P.length := hrs.le.trans hs
  let first :
      SimplePath G a (P.walk.getVert s) :=
    (P.take r).appendDisjoint
      (SimplePath.ofAdj hchord) (by
        apply List.disjoint_left.mpr
        intro z hzTake hzEdge
        simp only [SimplePath.ofAdj_support,
          List.tail_cons, List.mem_singleton] at hzEdge
        subst z
        obtain ⟨n, hnR, hnLength, hnEq⟩ :=
          mem_take_support_position P r hr hzTake
        have hnS :
            n = s :=
          (getVert_eq_iff P hnLength hs).1 hnEq
        omega)
  exact first.appendDisjoint (P.drop s) (by
    apply List.disjoint_left.mpr
    intro z hzFirst hzDrop
    obtain ⟨n, hsN, hnLength, hnEq⟩ :=
      mem_drop_tail_position P s hs hzDrop
    have hzCases :
        z ∈ (P.take r).walk.support ∨
          z = P.walk.getVert s := by
      change z ∈
        ((P.take r).walk.append
          (SimplePath.ofAdj hchord).walk).support at hzFirst
      rw [SimpleGraph.Walk.support_append] at hzFirst
      simp only [SimplePath.ofAdj_support,
        List.tail_cons, List.mem_append,
        List.mem_singleton] at hzFirst
      exact hzFirst
    rcases hzCases with hzTake | rfl
    · obtain ⟨m, hmR, hmLength, hmEq⟩ :=
        mem_take_support_position P r hr hzTake
      have hmn :
          m = n :=
        (getVert_eq_iff P hmLength hnLength).1
          (hmEq.trans hnEq.symm)
      omega
    · have hsn :
          s = n :=
        (getVert_eq_iff P hs hnLength).1 hnEq.symm
      omega)

private theorem shortcut_support_subset
    {a b : V} (P : SimplePath G a b)
    (r s : ℕ) (hrs : r < s) (hs : s ≤ P.length)
    (hchord : G.Adj (P.walk.getVert r) (P.walk.getVert s)) :
    ∀ z ∈ (shortcut P r s hrs hs hchord).walk.support,
      z ∈ P.walk.support := by
  intro z hz
  change z ∈
    (((P.take r).appendDisjoint
      (SimplePath.ofAdj hchord) _).walk.append
        (P.drop s).walk).support at hz
  rw [SimpleGraph.Walk.support_append] at hz
  rcases List.mem_append.mp hz with hzFirst | hzDrop
  · change z ∈
      ((P.take r).walk.append
        (SimplePath.ofAdj hchord).walk).support at hzFirst
    rw [SimpleGraph.Walk.support_append] at hzFirst
    rcases List.mem_append.mp hzFirst with hzTake | hzEdge
    · exact P.mem_support_of_mem_take r hzTake
    · simp only [SimplePath.ofAdj_support,
        List.tail_cons, List.mem_singleton] at hzEdge
      subst z
      exact P.walk.getVert_mem_support s
  · exact P.mem_support_of_mem_drop s
      (List.mem_of_mem_tail hzDrop)

private theorem shortcut_chord_mem_edges
    {a b : V} (P : SimplePath G a b)
    (r s : ℕ) (hrs : r < s) (hs : s ≤ P.length)
    (hchord : G.Adj (P.walk.getVert r) (P.walk.getVert s)) :
    s(P.walk.getVert r, P.walk.getVert s) ∈
      (shortcut P r s hrs hs hchord).walk.edges := by
  change s(P.walk.getVert r, P.walk.getVert s) ∈
    (((P.take r).walk.append
      (SimplePath.ofAdj hchord).walk).append
        (P.drop s).walk).edges
  simp [SimpleGraph.Walk.edges_append,
    SimplePath.ofAdj]

private theorem internal_support_data
    {a b z : V} (P : SimplePath G a b) (hab : a ≠ b)
    (hz : z ∈ P.internalSupport) :
    z ∈ P.walk.support ∧ z ≠ a ∧ z ≠ b := by
  have hzTail :
      z ∈ P.walk.support.tail :=
    List.mem_of_mem_dropLast hz
  have hzSupport :
      z ∈ P.walk.support :=
    List.mem_of_mem_tail hzTail
  have hza : z ≠ a := by
    intro h
    subst z
    exact P.start_not_mem_tail hzTail
  have htail :
      P.walk.support.tail ≠ [] := by
    have hbSupport : b ∈ P.walk.support :=
      P.walk.end_mem_support
    have hbCases :=
      (P.walk.mem_support_iff).1 hbSupport
    exact List.ne_nil_of_mem
      (hbCases.resolve_left hab.symm)
  have hbNotDrop :
      b ∉ P.walk.support.dropLast := by
    intro hb
    have hnodup := P.isPath.support_nodup
    rw [← P.walk.dropLast_support_concat,
      List.nodup_append] at hnodup
    exact (hnodup.2.2 b hb b (by simp)) rfl
  have hzb : z ≠ b := by
    intro h
    subst z
    apply hbNotDrop
    rw [← P.walk.cons_tail_support,
      List.dropLast_cons_of_ne_nil htail]
    exact List.mem_cons_of_mem _ hz
  exact ⟨hzSupport, hza, hzb⟩

private theorem getVert_succ_edge_mem
    {a b : V} (P : SimplePath G a b) {r : ℕ}
    (hr : r < P.length) :
    s(P.walk.getVert r, P.walk.getVert (r + 1)) ∈
      P.walk.edges := by
  have hrDarts : r < P.walk.darts.length := by
    simpa [SimplePath.length] using hr
  have hdart :
      P.walk.darts[r] ∈ P.walk.darts :=
    List.getElem_mem hrDarts
  rw [show P.walk.edges =
      P.walk.darts.map SimpleGraph.Dart.edge by rfl]
  apply List.mem_map.mpr
  refine ⟨P.walk.darts[r], hdart, ?_⟩
  rw [P.walk.darts_getElem_eq_getVert r hrDarts]
  rfl

private theorem shortcut_omits_between
    {a b : V} (P : SimplePath G a b)
    (r s n : ℕ) (hrn : r < n) (hns : n < s)
    (hs : s ≤ P.length)
    (hchord : G.Adj (P.walk.getVert r) (P.walk.getVert s)) :
    P.walk.getVert n ∉
      (shortcut P r s (hrn.trans hns) hs hchord).walk.support := by
  intro hnMem
  change P.walk.getVert n ∈
    (((P.take r).appendDisjoint
      (SimplePath.ofAdj hchord) _).walk.append
        (P.drop s).walk).support at hnMem
  rw [SimpleGraph.Walk.support_append] at hnMem
  rcases List.mem_append.mp hnMem with hnFirst | hnDrop
  · change P.walk.getVert n ∈
      ((P.take r).walk.append
        (SimplePath.ofAdj hchord).walk).support at hnFirst
    rw [SimpleGraph.Walk.support_append] at hnFirst
    rcases List.mem_append.mp hnFirst with hnTake | hnEdge
    · obtain ⟨m, hmR, hmLength, hmEq⟩ :=
        mem_take_support_position P r
          ((hrn.trans hns).le.trans hs) hnTake
      have hmn :
          m = n :=
        (getVert_eq_iff P hmLength
          (hns.le.trans hs)).1 hmEq
      omega
    · simp only [SimplePath.ofAdj_support,
        List.tail_cons, List.mem_singleton] at hnEdge
      have hnsEq :
          n = s :=
        (getVert_eq_iff P (hns.le.trans hs) hs).1
          hnEdge
      omega
  · obtain ⟨m, hsM, hmLength, hmEq⟩ :=
      mem_drop_tail_position P s hs hnDrop
    have hnm :
        n = m :=
      (getVert_eq_iff P (hns.le.trans hs) hmLength).1
        hmEq.symm
    omega

private theorem path_edges_subset_theta
    [DecidableEq V] (T : Theta G) (i : Fin 3)
    {e : Sym2 V} (he : e ∈ (T.path i).walk.edges) :
    e ∈ T.edges := by
  simp only [Theta.edges, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, by simpa using he⟩

private theorem exists_smaller_theta_of_replacement
    [DecidableEq V] (T : Theta G) (i : Fin 3)
    (Q : SimplePath G T.x T.y)
    {e : Sym2 V}
    (heQ : e ∈ Q.walk.edges)
    (heT : e ∉ T.edges)
    (hQsupport :
      ∀ z ∈ Q.walk.support,
        z ∈ (T.path i).walk.support)
    (w : V)
    (hwInternal : w ∈ (T.path i).internalSupport)
    (hwQ : w ∉ Q.walk.support) :
    ∃ U : Theta G, U.verts.card < T.verts.card := by
  let paths : Fin 3 → SimplePath G T.x T.y :=
    fun j => if h : j = i then Q else T.path j
  have hQinternal :
      ∀ z ∈ Q.internalSupport,
        z ∈ (T.path i).internalSupport := by
    intro z hz
    obtain ⟨hzSupport, hzx, hzy⟩ :=
      internal_support_data Q T.roots_ne hz
    exact (T.path i).mem_internalSupport_of_mem_support
      (hQsupport z hzSupport) hzx hzy
  let U : Theta G := {
    x := T.x
    y := T.y
    roots_ne := T.roots_ne
    path := paths
    paths_ne := by
      intro j k hjk
      by_cases hji : j = i
      · by_cases hki : k = i
        · exact False.elim (hjk (hji.trans hki.symm))
        · simp only [paths, dif_pos hji, dif_neg hki]
          intro heq
          apply heT
          apply path_edges_subset_theta T k
          rw [← heq]
          exact heQ
      · by_cases hki : k = i
        · simp only [paths, dif_neg hji, dif_pos hki]
          intro heq
          apply heT
          apply path_edges_subset_theta T j
          rw [heq]
          exact heQ
        · simp only [paths, dif_neg hji, dif_neg hki]
          exact T.paths_ne j k hjk
    internal_disjoint := by
      intro j k hjk
      by_cases hji : j = i
      · by_cases hki : k = i
        · exact False.elim (hjk (hji.trans hki.symm))
        · simp only [paths, dif_pos hji, dif_neg hki]
          apply List.disjoint_left.mpr
          intro z hzQ hzK
          have hzI := hQinternal z hzQ
          exact (List.disjoint_left.mp
            (T.internal_disjoint i k
              (fun hik => hki hik.symm)) hzI) hzK
      · by_cases hki : k = i
        · simp only [paths, dif_neg hji, dif_pos hki]
          apply List.disjoint_left.mpr
          intro z hzJ hzQ
          have hzI := hQinternal z hzQ
          exact (List.disjoint_left.mp
            (T.internal_disjoint j i hji) hzJ) hzI
        · simp only [paths, dif_neg hji, dif_neg hki]
          exact T.internal_disjoint j k hjk
  }
  have hsubset : U.verts ⊆ T.verts := by
    intro z hzU
    simp only [Theta.verts, Finset.mem_biUnion] at hzU ⊢
    obtain ⟨j, -, hzj⟩ := hzU
    by_cases hji : j = i
    · subst j
      simp only [U, paths, dif_pos rfl] at hzj
      exact ⟨i, Finset.mem_univ _, by
        simpa using hQsupport z (by simpa using hzj)⟩
    · simp only [U, paths, dif_neg hji] at hzj
      exact ⟨j, Finset.mem_univ _, hzj⟩
  have hwT : w ∈ T.verts :=
    T.mem_verts_of_mem_path i
      (internal_support_data
        (T.path i) T.roots_ne hwInternal).1
  have hwNotU : w ∉ U.verts := by
    intro hwU
    simp only [Theta.verts, Finset.mem_biUnion] at hwU
    obtain ⟨j, -, hwj⟩ := hwU
    by_cases hji : j = i
    · subst j
      simp only [U, paths, dif_pos rfl] at hwj
      exact hwQ (by simpa using hwj)
    · simp only [U, paths, dif_neg hji] at hwj
      have hwOldJ :
          w ∈ (T.path j).walk.support := by
        simpa using hwj
      have hwOldI :=
        (internal_support_data
          (T.path i) T.roots_ne hwInternal).1
      rcases T.eq_root_of_mem_two_paths
          (fun hij => hji hij.symm) hwOldI hwOldJ with
        hwx | hwy
      · exact
          (internal_support_data
            (T.path i) T.roots_ne hwInternal).2.1 hwx
      · exact
          (internal_support_data
            (T.path i) T.roots_ne hwInternal).2.2 hwy
  refine ⟨U, Finset.card_lt_card ?_⟩
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨hsubset, fun heq => hwNotU (heq ▸ hwT)⟩

private theorem exists_smaller_theta_of_same_leg_chord
    [DecidableEq V] (T : Theta G) (i : Fin 3)
    {u v : V}
    (hu : u ∈ (T.path i).walk.support)
    (hv : v ∈ (T.path i).walk.support)
    (huv : G.Adj u v)
    (heT : s(u, v) ∉ T.edges) :
    ∃ U : Theta G, U.verts.card < T.verts.card := by
  let P := T.path i
  obtain ⟨r, hru, hrle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu
  obtain ⟨s, hsv, hsle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  have hrs : r ≠ s := by
    intro hrs
    subst s
    exact huv.ne (hru.symm.trans hsv)
  rcases Nat.lt_or_gt_of_ne hrs with hrs | hsr
  · have hchord :
        G.Adj (P.walk.getVert r) (P.walk.getVert s) := by
      simpa [P, hru, hsv] using huv
    have hgap : r + 1 < s := by
      by_contra h
      have hsucc : s = r + 1 := by omega
      apply heT
      have hrlt : r < P.length := by
        simpa [P] using hrs.trans_le
          (by simpa [P, SimplePath.length] using hsle)
      have hedge :=
        getVert_succ_edge_mem P hrlt
      have hedgeT :=
        path_edges_subset_theta T i hedge
      rw [hsucc] at hsv
      simpa [P, hru, hsv] using hedgeT
    let Q :=
      shortcut P r s hrs
        (by simpa [P, SimplePath.length] using hsle)
        hchord
    let w := P.walk.getVert (r + 1)
    have hwInternal :
        w ∈ P.internalSupport :=
      internal_mem_of_getVert P (by omega)
        (hgap.trans_le
          (by simpa [P, SimplePath.length] using hsle))
    have hwQ : w ∉ Q.walk.support := by
      exact shortcut_omits_between P r s (r + 1)
        (by omega) hgap
        (by simpa [P, SimplePath.length] using hsle)
        hchord
    refine exists_smaller_theta_of_replacement
      T i Q
      (e := s(P.walk.getVert r, P.walk.getVert s))
      ?_ ?_ ?_ w ?_ ?_
    · exact shortcut_chord_mem_edges P r s hrs
        (by simpa [P, SimplePath.length] using hsle)
        hchord
    · simpa [P, hru, hsv] using heT
    · exact shortcut_support_subset P r s hrs
        (by simpa [P, SimplePath.length] using hsle)
        hchord
    · simpa [P] using hwInternal
    · exact hwQ
  · have hchord :
        G.Adj (P.walk.getVert s) (P.walk.getVert r) := by
      simpa [P, hru, hsv] using huv.symm
    have hgap : s + 1 < r := by
      by_contra h
      have hsucc : r = s + 1 := by omega
      apply heT
      have hslt : s < P.length := by
        simpa [P] using hsr.trans_le
          (by simpa [P, SimplePath.length] using hrle)
      have hedge :=
        getVert_succ_edge_mem P hslt
      have hedgeT :=
        path_edges_subset_theta T i hedge
      rw [hsucc] at hru
      simpa [P, hru, hsv, Sym2.eq_swap] using
        hedgeT
    let Q :=
      shortcut P s r hsr
        (by simpa [P, SimplePath.length] using hrle)
        hchord
    let w := P.walk.getVert (s + 1)
    have hwInternal :
        w ∈ P.internalSupport :=
      internal_mem_of_getVert P (by omega)
        (hgap.trans_le
          (by simpa [P, SimplePath.length] using hrle))
    have hwQ : w ∉ Q.walk.support := by
      exact shortcut_omits_between P s r (s + 1)
        (by omega) hgap
        (by simpa [P, SimplePath.length] using hrle)
        hchord
    refine exists_smaller_theta_of_replacement
      T i Q
      (e := s(P.walk.getVert s, P.walk.getVert r))
      ?_ ?_ ?_ w ?_ ?_
    · exact shortcut_chord_mem_edges P s r hsr
        (by simpa [P, SimplePath.length] using hrle)
        hchord
    · simpa [P, hru, hsv, Sym2.eq_swap] using heT
    · exact shortcut_support_subset P s r hsr
        (by simpa [P, SimplePath.length] using hrle)
        hchord
    · simpa [P] using hwInternal
    · exact hwQ

private theorem mem_drop_support_position
    {a b z : V} (P : SimplePath G a b) (s : ℕ)
    (hs : s ≤ P.length)
    (hz : z ∈ (P.drop s).walk.support) :
    ∃ n, s ≤ n ∧ n ≤ P.length ∧ P.walk.getVert n = z := by
  obtain ⟨m, hmz, hmle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hsum : s + m ≤ P.length := by
    have hmle' : m ≤ P.length - s := by
      simpa [SimplePath.drop, SimplePath.length] using hmle
    omega
  refine ⟨s + m, by omega, hsum, ?_⟩
  simpa [SimplePath.drop,
    SimpleGraph.Walk.drop_getVert] using hmz

private def crossTail
    (T : Theta G) (j : Fin 3) (s : ℕ) :
    SimplePath G T.y ((T.path j).walk.getVert s) :=
  ((T.path j).drop s).reverse

private def crossViaThird
    (T : Theta G) (j k : Fin 3) (hkj : k ≠ j)
    (s : ℕ) (hs : s < (T.path j).length) :
    SimplePath G T.y ((T.path j).walk.getVert s) :=
  (T.path k).reverse.appendDisjoint
    ((T.path j).take s) (by
      apply List.disjoint_left.mpr
      intro z hzK hzJ
      have hzK' :
          z ∈ (T.path k).walk.support := by
        simpa [SimplePath.reverse] using hzK
      have hzJTake :
          z ∈ ((T.path j).take s).walk.support :=
        List.mem_of_mem_tail hzJ
      have hzJ' :
          z ∈ (T.path j).walk.support :=
        (T.path j).mem_support_of_mem_take s hzJTake
      rcases T.eq_root_of_mem_two_paths hkj
          hzK' hzJ' with rfl | rfl
      · exact ((T.path j).take s).start_not_mem_tail hzJ
      · exact (T.path j).end_not_mem_take hs hzJTake)

private def crossViaChord
    (T : Theta G) (i j : Fin 3) (hij : i ≠ j)
    (r s : ℕ)
    (_hrpos : 0 < r) (_hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s < (T.path j).length)
    (hchord :
      G.Adj ((T.path i).walk.getVert r)
        ((T.path j).walk.getVert s)) :
    SimplePath G T.y ((T.path j).walk.getVert s) :=
  ((T.path i).drop r).reverse.appendDisjoint
    (SimplePath.ofAdj hchord) (by
      apply List.disjoint_left.mpr
      intro z hzI hzEdge
      simp only [SimplePath.ofAdj_support,
        List.tail_cons, List.mem_singleton] at hzEdge
      subst z
      have hzI' :
          (T.path j).walk.getVert s ∈
            (T.path i).walk.support := by
        have hzDrop :
            (T.path j).walk.getVert s ∈
              ((T.path i).drop r).walk.support := by
          simpa [SimplePath.reverse] using hzI
        exact (T.path i).mem_support_of_mem_drop r hzDrop
      have hzJ' :
          (T.path j).walk.getVert s ∈
            (T.path j).walk.support :=
        (T.path j).walk.getVert_mem_support s
      rcases T.eq_root_of_mem_two_paths hij
          hzI' hzJ' with hx | hy
      · exact (getVert_ne_start
          (T.path j) hspos hs.le) hx
      · exact (getVert_ne_end
          (T.path j) hs) hy)

private theorem exists_smaller_theta_of_cross_chord
    [DecidableEq V] (T : Theta G)
    (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s < (T.path j).length)
    (hrlarge : 1 < r)
    (hchord :
      G.Adj ((T.path i).walk.getVert r)
        ((T.path j).walk.getVert s))
    (heT :
      s((T.path i).walk.getVert r,
        (T.path j).walk.getVert s) ∉ T.edges) :
    ∃ U : Theta G, U.verts.card < T.verts.card := by
  let v := (T.path j).walk.getVert s
  let A := crossTail T j s
  let B := crossViaThird T j k
    (fun h => hjk h.symm) s hs
  let C := crossViaChord T i j hij
    r s hrpos hr hspos hs hchord
  have hyv : T.y ≠ v :=
    (getVert_ne_end (T.path j) hs).symm
  have hAcontains : T.ContainsPath A := by
    exact (T.containsPath_path j |>.drop s |>.reverse)
  have hBcontains : T.ContainsPath B := by
    exact ((T.containsPath_path k).reverse.appendDisjoint
      ((T.containsPath_path j).take s) _)
  have hCchord :
      s((T.path i).walk.getVert r,
        (T.path j).walk.getVert s) ∈ C.walk.edges := by
    change s((T.path i).walk.getVert r,
        (T.path j).walk.getVert s) ∈
      (((T.path i).drop r).reverse.walk.append
        (SimplePath.ofAdj hchord).walk).edges
    simp [SimpleGraph.Walk.edges_append,
      SimplePath.ofAdj]
  have hA_support :
      ∀ z ∈ A.walk.support,
        z ∈ (T.path j).walk.support := by
    intro z hz
    have hzDrop :
        z ∈ ((T.path j).drop s).walk.support := by
      simpa [A, crossTail, SimplePath.reverse] using hz
    exact (T.path j).mem_support_of_mem_drop s hzDrop
  have hA_drop :
      ∀ z ∈ A.walk.support,
        z ∈ ((T.path j).drop s).walk.support := by
    intro z hz
    simpa [A, crossTail, SimplePath.reverse] using hz
  have hB_support :
      ∀ z ∈ B.walk.support,
        z ∈ (T.path k).walk.support ∨
          z ∈ ((T.path j).take s).walk.support := by
    intro z hz
    change z ∈
      ((T.path k).reverse.walk.append
        ((T.path j).take s).walk).support at hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzK | hzJ
    · exact Or.inl (by
        simpa [SimplePath.reverse] using hzK)
    · exact Or.inr (List.mem_of_mem_tail hzJ)
  have hC_support :
      ∀ z ∈ C.walk.support,
        z ∈ ((T.path i).drop r).walk.support ∨ z = v := by
    intro z hz
    change z ∈
      (((T.path i).drop r).reverse.walk.append
        (SimplePath.ofAdj hchord).walk).support at hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzI | hzEdge
    · exact Or.inl (by
        simpa [SimplePath.reverse] using hzI)
    · simp only [SimplePath.ofAdj_support,
        List.tail_cons, List.mem_singleton] at hzEdge
      exact Or.inr hzEdge
  have hxA : T.x ∉ A.walk.support := by
    intro hx
    exact (T.path j).start_not_mem_drop
      hspos hs.le (hA_drop T.x hx)
  have hxB : T.x ∈ B.walk.support := by
    change T.x ∈
      ((T.path k).reverse.walk.append
        ((T.path j).take s).walk).support
    rw [SimpleGraph.Walk.support_append]
    apply List.mem_append_left
    simp [SimplePath.reverse]
  have hABne : A.walk ≠ B.walk := by
    intro h
    apply hxA
    rw [h]
    exact hxB
  have hACne : A.walk ≠ C.walk := by
    intro h
    apply heT
    apply hAcontains
    rw [h]
    exact hCchord
  have hBCne : B.walk ≠ C.walk := by
    intro h
    apply heT
    apply hBcontains
    rw [h]
    exact hCchord
  have hBAne : B.walk ≠ A.walk := Ne.symm hABne
  have hCAne : C.walk ≠ A.walk := Ne.symm hACne
  have hCBne : C.walk ≠ B.walk := Ne.symm hBCne
  have hABdisjoint :
      A.internalSupport.Disjoint B.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzA hzB
    obtain ⟨hzASupport, hzAy, hzAv⟩ :=
      internal_support_data A hyv hzA
    obtain ⟨hzBSupport, hzBy, hzBv⟩ :=
      internal_support_data B hyv hzB
    have hzADrop := hA_drop z hzASupport
    have hzAJ := hA_support z hzASupport
    rcases hB_support z hzBSupport with hzK | hzJTake
    · have hzKOld :
          z ∈ (T.path k).walk.support := hzK
      rcases T.eq_root_of_mem_two_paths
          (fun h => hjk h.symm) hzKOld hzAJ with
        hzx | hzy
      · exact hxA (hzx ▸ hzASupport)
      · exact hzAy hzy
    · obtain ⟨n, hsN, hnLength, hnEq⟩ :=
        mem_drop_support_position (T.path j) s hs.le hzADrop
      have hsStrict : s < n := by
        by_contra h
        have hns : n = s := by omega
        subst n
        exact hzAv hnEq.symm
      obtain ⟨m, hmS, hmLength, hmEq⟩ :=
        mem_take_support_position (T.path j) s hs.le hzJTake
      have hnm :
          n = m :=
        (getVert_eq_iff (T.path j) hnLength hmLength).1
          (hnEq.trans hmEq.symm)
      omega
  have hACdisjoint :
      A.internalSupport.Disjoint C.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzA hzC
    obtain ⟨hzASupport, hzAy, hzAv⟩ :=
      internal_support_data A hyv hzA
    obtain ⟨hzCSupport, hzCy, hzCv⟩ :=
      internal_support_data C hyv hzC
    have hzAJ := hA_support z hzASupport
    rcases hC_support z hzCSupport with hzIDrop | hzv
    · have hzI :
          z ∈ (T.path i).walk.support :=
        (T.path i).mem_support_of_mem_drop r hzIDrop
      rcases T.eq_root_of_mem_two_paths
          hij.symm hzAJ hzI with hzx | hzy
      · exact hxA (hzx ▸ hzASupport)
      · exact hzAy hzy
    · exact hzCv hzv
  have hBCdisjoint :
      B.internalSupport.Disjoint C.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzB hzC
    obtain ⟨hzBSupport, hzBy, hzBv⟩ :=
      internal_support_data B hyv hzB
    obtain ⟨hzCSupport, hzCy, hzCv⟩ :=
      internal_support_data C hyv hzC
    rcases hC_support z hzCSupport with hzIDrop | hzv
    · have hzI :
          z ∈ (T.path i).walk.support :=
        (T.path i).mem_support_of_mem_drop r hzIDrop
      rcases hB_support z hzBSupport with hzK | hzJTake
      · rcases T.eq_root_of_mem_two_paths
            (fun h => hik h.symm) hzK hzI with
          hzx | hzy
        · exact (T.path i).start_not_mem_drop
            hrpos hr.le (hzx ▸ hzIDrop)
        · exact hzBy hzy
      · have hzJ :
            z ∈ (T.path j).walk.support :=
          (T.path j).mem_support_of_mem_take s hzJTake
        rcases T.eq_root_of_mem_two_paths
            hij.symm hzJ hzI with hzx | hzy
        · exact (T.path i).start_not_mem_drop
            hrpos hr.le (hzx ▸ hzIDrop)
        · exact (T.path j).end_not_mem_take
            hs (hzy ▸ hzJTake)
    · exact hzCv hzv
  let U : Theta G := {
    x := T.y
    y := v
    roots_ne := hyv
    path := ![A, B, C]
    paths_ne := by
      intro p q hpq
      fin_cases p <;> fin_cases q <;>
        simp_all
    internal_disjoint := by
      intro p q hpq
      fin_cases p <;> fin_cases q <;>
        simp_all [List.Disjoint.symm]
  }
  have hPathSupport :
      ∀ (p : Fin 3) z,
        z ∈ (U.path p).walk.support →
          z ∈ T.verts := by
    intro p z hz
    fin_cases p
    · exact T.mem_verts_of_mem_path j
        (hA_support z (by simpa [U] using hz))
    · rcases hB_support z (by simpa [U] using hz) with
        hzK | hzJ
      · exact T.mem_verts_of_mem_path k hzK
      · exact T.mem_verts_of_mem_path j
          ((T.path j).mem_support_of_mem_take s hzJ)
    · rcases hC_support z (by simpa [U] using hz) with
        hzI | rfl
      · exact T.mem_verts_of_mem_path i
          ((T.path i).mem_support_of_mem_drop r hzI)
      · exact T.mem_verts_of_mem_path j
          ((T.path j).walk.getVert_mem_support s)
  have hsubset : U.verts ⊆ T.verts := by
    intro z hz
    simp only [Theta.verts, Finset.mem_biUnion] at hz
    obtain ⟨p, -, hp⟩ := hz
    exact hPathSupport p z (by simpa using hp)
  let w := (T.path i).walk.getVert 1
  have hwInternal :
      w ∈ (T.path i).internalSupport :=
    internal_mem_of_getVert (T.path i) (by omega)
      (hrlarge.trans hr)
  have hwData :=
    internal_support_data (T.path i) T.roots_ne hwInternal
  have hwT : w ∈ T.verts :=
    T.mem_verts_of_mem_path i hwData.1
  have hwNotA : w ∉ A.walk.support := by
    intro hwA
    have hwJ := hA_support w hwA
    rcases T.eq_root_of_mem_two_paths hij
        hwData.1 hwJ with hwx | hwy
    · exact hwData.2.1 hwx
    · exact hwData.2.2 hwy
  have hwNotB : w ∉ B.walk.support := by
    intro hwB
    rcases hB_support w hwB with hwK | hwJTake
    · rcases T.eq_root_of_mem_two_paths hik
          hwData.1 hwK with hwx | hwy
      · exact hwData.2.1 hwx
      · exact hwData.2.2 hwy
    · have hwJ :
          w ∈ (T.path j).walk.support :=
        (T.path j).mem_support_of_mem_take s hwJTake
      rcases T.eq_root_of_mem_two_paths hij
          hwData.1 hwJ with hwx | hwy
      · exact hwData.2.1 hwx
      · exact hwData.2.2 hwy
  have hwNotC : w ∉ C.walk.support := by
    intro hwC
    rcases hC_support w hwC with hwIDrop | hwv
    · obtain ⟨n, hrN, hnLength, hnEq⟩ :=
        mem_drop_support_position (T.path i) r hr.le hwIDrop
      have hOneN :
          1 = n :=
        (getVert_eq_iff (T.path i)
          (hrlarge.le.trans hr.le) hnLength).1
          (by simpa [w] using hnEq.symm)
      omega
    · have hvJ :
          v ∈ (T.path j).walk.support := by
        exact (T.path j).walk.getVert_mem_support s
      have hwJ : w ∈ (T.path j).walk.support := by
        simpa [hwv] using hvJ
      rcases T.eq_root_of_mem_two_paths hij
          hwData.1 hwJ with hwx | hwy
      · exact hwData.2.1 hwx
      · exact hwData.2.2 hwy
  have hwNotU : w ∉ U.verts := by
    intro hwU
    simp only [Theta.verts, Finset.mem_biUnion] at hwU
    obtain ⟨p, -, hp⟩ := hwU
    fin_cases p
    · exact hwNotA (by simpa [U] using hp)
    · exact hwNotB (by simpa [U] using hp)
    · exact hwNotC (by simpa [U] using hp)
  refine ⟨U, Finset.card_lt_card ?_⟩
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨hsubset, fun heq => hwNotU (heq ▸ hwT)⟩

/--
A theta of minimum order in a graph of girth at least six is induced.

An omitted ambient edge is either a chord of one constituent path, in which
case that path can be shortened, or joins internal vertices of two different
constituent paths.  In the latter case the chord and the three theta paths
form a subdivided `K₄`; the short cycle through the first branch vertex
forces one of its two incident segments to have an internal vertex, and
deleting that segment gives a smaller theta.
-/
theorem minimumOrder_isInduced
    [DecidableEq V]
    (T : Theta G)
    (hminimum : T.IsMinimumOrder)
    (hgirth : GirthAtLeast G 6) :
    T.IsInduced := by
  intro u v hu hv huv
  by_contra heT
  by_cases hcommon :
      ∃ i : Fin 3,
        u ∈ (T.path i).walk.support ∧
          v ∈ (T.path i).walk.support
  · obtain ⟨i, hui, hvi⟩ := hcommon
    obtain ⟨U, hU⟩ :=
      exists_smaller_theta_of_same_leg_chord
        T i hui hvi huv heT
    exact (Nat.not_lt_of_ge (hminimum U)) hU
  · obtain ⟨i, hui⟩ := T.exists_path_of_mem_verts hu
    obtain ⟨j, hvj⟩ := T.exists_path_of_mem_verts hv
    have hij : i ≠ j := by
      intro h
      subst j
      exact hcommon ⟨i, hui, hvj⟩
    have hux : u ≠ T.x := by
      intro h
      subst u
      apply hcommon
      exact ⟨j, (T.path j).walk.start_mem_support, hvj⟩
    have huy : u ≠ T.y := by
      intro h
      subst u
      apply hcommon
      exact ⟨j, (T.path j).walk.end_mem_support, hvj⟩
    have hvx : v ≠ T.x := by
      intro h
      subst v
      apply hcommon
      exact ⟨i, hui, (T.path i).walk.start_mem_support⟩
    have hvy : v ≠ T.y := by
      intro h
      subst v
      apply hcommon
      exact ⟨i, hui, (T.path i).walk.end_mem_support⟩
    obtain ⟨r, hru, hrle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hui
    obtain ⟨s, hsv, hsle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvj
    have hrle' : r ≤ (T.path i).length := by
      simpa [SimplePath.length] using hrle
    have hsle' : s ≤ (T.path j).length := by
      simpa [SimplePath.length] using hsle
    have hrpos : 0 < r := by
      by_contra h
      have hrzero : r = 0 := Nat.eq_zero_of_not_pos h
      subst r
      apply hux
      simpa using hru.symm
    have hspos : 0 < s := by
      by_contra h
      have hszero : s = 0 := Nat.eq_zero_of_not_pos h
      subst s
      apply hvx
      simpa using hsv.symm
    have hrlt : r < (T.path i).length := by
      by_contra h
      have hre :
          r = (T.path i).length := by omega
      apply huy
      rw [← hru]
      simp [SimplePath.length, hre]
    have hslt : s < (T.path j).length := by
      by_contra h
      have hse :
          s = (T.path j).length := by omega
      apply hvy
      rw [← hsv]
      simp [SimplePath.length, hse]
    have hchord :
        G.Adj ((T.path i).walk.getVert r)
          ((T.path j).walk.getVert s) := by
      simpa [hru, hsv] using huv
    have heT' :
        s((T.path i).walk.getVert r,
          (T.path j).walk.getVert s) ∉ T.edges := by
      simpa [hru, hsv] using heT
    have hk :
        ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      have hfinite :
          ∀ a b : Fin 3, a ≠ b →
            ∃ k : Fin 3, a ≠ k ∧ b ≠ k := by
        decide
      exact hfinite i j hij
    obtain ⟨k, hik, hjk⟩ := hk
    let P := T.viaFirstRoot hij r s hrlt
    let Q :=
      SimplePath.ofAdj hchord.symm
    have hdisjoint :
        P.walk.support.tail.Disjoint
          Q.walk.support.tail := by
      apply List.disjoint_left.mpr
      intro z hzP hzQ
      simp only [Q, SimplePath.ofAdj_support,
        List.tail_cons, List.mem_singleton] at hzQ
      subst z
      exact P.start_not_mem_tail hzP
    have hlong : 1 < P.length ∨ 1 < Q.length := by
      left
      rw [show P.length = r + s by
        exact T.viaFirstRoot_length hij r s hrlt hsle']
      omega
    let C :=
      cycleOfDisjointPaths P Q hdisjoint hlong
    have hcycleLength : 6 ≤ r + s + 1 := by
      have h := hgirth C
      simpa [C, P, Q,
        T.viaFirstRoot_length hij r s hrlt hsle'] using h
    by_cases hrlarge : 1 < r
    · obtain ⟨U, hU⟩ :=
        exists_smaller_theta_of_cross_chord
          T i j k hij hik hjk r s
          hrpos hrlt hspos hslt hrlarge
          hchord heT'
      exact (Nat.not_lt_of_ge (hminimum U)) hU
    · have hslarge : 1 < s := by omega
      obtain ⟨U, hU⟩ :=
        exists_smaller_theta_of_cross_chord
          T j i k hij.symm hjk hik s r
          hspos hslt hrpos hrlt hslarge
          hchord.symm (by
            simpa [Sym2.eq_swap] using heT')
      exact (Nat.not_lt_of_ge (hminimum U)) hU

/-- The two-edge path through an outside vertex. -/
private def viaOutside
    {a b : V} (P : SimplePath G a b)
    (r s : ℕ) (hrs : r < s) (hs : s ≤ P.length)
    (v : V) (hvP : v ∉ P.walk.support)
    (hvr : G.Adj v (P.walk.getVert r))
    (hvs : G.Adj v (P.walk.getVert s)) :
    SimplePath G (P.walk.getVert r) (P.walk.getVert s) := {
  walk := .cons hvr.symm (.cons hvs .nil)
  isPath := by
    have hr : r ≤ P.length := hrs.le.trans hs
    have hrv : P.walk.getVert r ≠ v := by
      intro h
      exact hvP (h ▸ P.walk.getVert_mem_support r)
    have hsv : P.walk.getVert s ≠ v := by
      intro h
      exact hvP (h ▸ P.walk.getVert_mem_support s)
    have hrsVert :
        P.walk.getVert r ≠ P.walk.getVert s := by
      intro h
      exact (Nat.ne_of_lt hrs)
        ((getVert_eq_iff P hr hs).1 h)
    simp [hrv, hsv.symm, hrsVert]
}

@[simp] private theorem viaOutside_length
    {a b : V} (P : SimplePath G a b)
    (r s : ℕ) (hrs : r < s) (hs : s ≤ P.length)
    (v : V) (hvP : v ∉ P.walk.support)
    (hvr : G.Adj v (P.walk.getVert r))
    (hvs : G.Adj v (P.walk.getVert s)) :
    (viaOutside P r s hrs hs v hvP hvr hvs).length = 2 := by
  simp [viaOutside, SimplePath.length]

/--
Replace the portion of `P` strictly between positions `r` and `s` by the
two-edge route through `v`.
-/
private def shortcutViaOutside
    {a b : V} (P : SimplePath G a b)
    (r s : ℕ) (hrs : r < s) (hs : s ≤ P.length)
    (v : V) (hvP : v ∉ P.walk.support)
    (hvr : G.Adj v (P.walk.getVert r))
    (hvs : G.Adj v (P.walk.getVert s)) :
    SimplePath G a b := by
  have hr : r ≤ P.length := hrs.le.trans hs
  let R := viaOutside P r s hrs hs v hvP hvr hvs
  let first :=
    (P.take r).appendDisjoint R (by
      apply List.disjoint_left.mpr
      intro z hzTake hzR
      have hzR' :
          z = v ∨ z = P.walk.getVert s := by
        simpa [R, viaOutside] using hzR
      rcases hzR' with rfl | rfl
      · exact hvP (P.mem_support_of_mem_take r hzTake)
      · obtain ⟨n, hnR, hnLength, hnEq⟩ :=
          mem_take_support_position P r hr hzTake
        have hnS :
            n = s :=
          (getVert_eq_iff P hnLength hs).1 hnEq
        omega)
  exact first.appendDisjoint (P.drop s) (by
    apply List.disjoint_left.mpr
    intro z hzFirst hzDrop
    obtain ⟨n, hsN, hnLength, hnEq⟩ :=
      mem_drop_tail_position P s hs hzDrop
    have hzCases :
        z ∈ (P.take r).walk.support ∨
          z = v ∨ z = P.walk.getVert s := by
      change z ∈
        ((P.take r).walk.append R.walk).support at hzFirst
      rw [SimpleGraph.Walk.support_append] at hzFirst
      rcases List.mem_append.mp hzFirst with hzTake | hzR
      · exact Or.inl hzTake
      · have hzR' :
            z = v ∨ z = P.walk.getVert s := by
          simpa [R, viaOutside] using hzR
        exact Or.inr hzR'
    rcases hzCases with hzTake | hzOther
    · obtain ⟨m, hmR, hmLength, hmEq⟩ :=
        mem_take_support_position P r hr hzTake
      have hmn :
          m = n :=
        (getVert_eq_iff P hmLength hnLength).1
          (hmEq.trans hnEq.symm)
      omega
    · rcases hzOther with hzv | hzs
      · apply hvP
        rw [← hzv, ← hnEq]
        exact P.walk.getVert_mem_support n
      ·
        have hsn :
            s = n :=
          ((getVert_eq_iff P hnLength hs).1
            (hnEq.trans hzs)).symm
        omega)

private theorem shortcutViaOutside_support
    {a b : V} (P : SimplePath G a b)
    (r s : ℕ) (hrs : r < s) (hs : s ≤ P.length)
    (v : V) (hvP : v ∉ P.walk.support)
    (hvr : G.Adj v (P.walk.getVert r))
    (hvs : G.Adj v (P.walk.getVert s)) :
    ∀ z ∈
        (shortcutViaOutside P r s hrs hs v hvP hvr hvs).walk.support,
      z ∈ P.walk.support ∨ z = v := by
  intro z hz
  change z ∈
    (((P.take r).walk.append
      (viaOutside P r s hrs hs v hvP hvr hvs).walk).append
        (P.drop s).walk).support at hz
  rw [SimpleGraph.Walk.support_append] at hz
  rcases List.mem_append.mp hz with hzFirst | hzDrop
  · rw [SimpleGraph.Walk.support_append] at hzFirst
    rcases List.mem_append.mp hzFirst with hzTake | hzR
    · exact Or.inl (P.mem_support_of_mem_take r hzTake)
    · have hzR' :
          z = v ∨ z = P.walk.getVert s := by
        simpa [viaOutside] using hzR
      rcases hzR' with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (P.walk.getVert_mem_support s)
  · exact Or.inl
      (P.mem_support_of_mem_drop s
        (List.mem_of_mem_tail hzDrop))

private theorem shortcutViaOutside_omits_between
    {a b : V} (P : SimplePath G a b)
    (r s n : ℕ) (hrn : r < n) (hns : n < s)
    (hs : s ≤ P.length)
    (v : V) (hvP : v ∉ P.walk.support)
    (hvr : G.Adj v (P.walk.getVert r))
    (hvs : G.Adj v (P.walk.getVert s)) :
    P.walk.getVert n ∉
      (shortcutViaOutside P r s
        (hrn.trans hns) hs v hvP hvr hvs).walk.support := by
  intro hnMem
  change P.walk.getVert n ∈
    (((P.take r).walk.append
      (viaOutside P r s (hrn.trans hns) hs
        v hvP hvr hvs).walk).append
          (P.drop s).walk).support at hnMem
  rw [SimpleGraph.Walk.support_append] at hnMem
  rcases List.mem_append.mp hnMem with hnFirst | hnDrop
  · rw [SimpleGraph.Walk.support_append] at hnFirst
    rcases List.mem_append.mp hnFirst with hnTake | hnR
    · obtain ⟨m, hmR, hmLength, hmEq⟩ :=
        mem_take_support_position P r
          ((hrn.trans hns).le.trans hs) hnTake
      have hmn :
          m = n :=
        (getVert_eq_iff P hmLength
          (hns.le.trans hs)).1 hmEq
      omega
    · have hnR' :
          P.walk.getVert n = v ∨
            P.walk.getVert n = P.walk.getVert s := by
        simpa [viaOutside] using hnR
      rcases hnR' with hnv | hnsEq
      · apply hvP
        rw [← hnv]
        exact P.walk.getVert_mem_support n
      · have :
            n = s :=
          (getVert_eq_iff P (hns.le.trans hs) hs).1 hnsEq
        omega
  · obtain ⟨m, hsM, hmLength, hmEq⟩ :=
      mem_drop_tail_position P s hs hnDrop
    have hnm :
        n = m :=
      (getVert_eq_iff P (hns.le.trans hs) hmLength).1
        hmEq.symm
    omega

/--
In a minimum-order theta of girth at least six, an outside vertex cannot
have two distinct neighbors on the same constituent path.
-/
theorem minimumOrder_outside_atMostOneNeighbor_on_path
    [DecidableEq V]
    (T : Theta G)
    (hminimum : T.IsMinimumOrder)
    (hgirth : GirthAtLeast G 6)
    (v : V) (hv : v ∉ T.verts)
    (i : Fin 3) {u w : V}
    (huw : u ≠ w)
    (hu : u ∈ (T.path i).walk.support)
    (hw : w ∈ (T.path i).walk.support)
    (hvu : G.Adj v u) (hvw : G.Adj v w) :
    False := by
  let P := T.path i
  have hvP : v ∉ P.walk.support := by
    intro hvSupport
    exact hv (T.mem_verts_of_mem_path i hvSupport)
  obtain ⟨r, hru, hrleWalk⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu
  obtain ⟨s, hsw, hsleWalk⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  have hrle : r ≤ P.length := by
    simpa [P, SimplePath.length] using hrleWalk
  have hsle : s ≤ P.length := by
    simpa [P, SimplePath.length] using hsleWalk
  have hrsne : r ≠ s := by
    intro hrs
    subst s
    exact huw (hru.symm.trans hsw)
  wlog hrs : r < s generalizing u w r s
  · have hsr : s < r := Nat.lt_of_le_of_ne
        (Nat.le_of_not_gt hrs) (Ne.symm hrsne)
    exact this
      huw.symm hw hu hvw hvu
      s hsw hsleWalk r hru hrleWalk
      hsle hrle (Ne.symm hrsne) hsr
  have hvr :
      G.Adj v (P.walk.getVert r) := by
    simpa [P, hru] using hvu
  have hvs :
      G.Adj v (P.walk.getVert s) := by
    simpa [P, hsw] using hvw
  let A : SimplePath G
      (P.walk.getVert r) (P.walk.getVert s) :=
    ((P.drop r).take (s - r)).castEnd (by
      simp only [SimplePath.drop,
        SimpleGraph.Walk.drop_getVert]
      congr 1
      omega)
  let R :=
    (viaOutside P r s hrs hsle v hvP hvr hvs).reverse
  have hA_support :
      ∀ z ∈ A.walk.support, z ∈ P.walk.support := by
    intro z hz
    have hzTake :
        z ∈ ((P.drop r).take (s - r)).walk.support := by
      simpa only [A, SimplePath.castEnd_support] using hz
    exact P.mem_support_of_mem_drop r
      ((P.drop r).mem_support_of_mem_take
        (s - r) hzTake)
  have hdisjoint :
      A.walk.support.tail.Disjoint R.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzA hzR
    have hzR' :
        z = v ∨ z = P.walk.getVert r := by
      simpa [R, viaOutside, SimplePath.reverse] using hzR
    rcases hzR' with hzv | hzr
    · apply hvP
      rw [← hzv]
      exact hA_support z (List.mem_of_mem_tail hzA)
    · apply A.start_not_mem_tail
      simpa [A, hzr] using hzA
  have hAlong : A.length = s - r := by
    rw [show A.length =
        ((P.drop r).take (s - r)).length by
      simp [A]]
    rw [SimplePath.take_length,
      SimplePath.drop_length]
    omega
  have hlong : 1 < A.length ∨ 1 < R.length := by
    right
    simp [R]
  let C := cycleOfDisjointPaths A R hdisjoint hlong
  have hgap : r + 4 ≤ s := by
    have hC := hgirth C
    rw [cycleOfDisjointPaths_length,
      hAlong] at hC
    have hR : R.length = 2 := by simp [R]
    omega
  let Q :=
    shortcutViaOutside P r s hrs hsle v hvP hvr hvs
  have hQedge :
      s(P.walk.getVert r, v) ∈ Q.walk.edges := by
    change s(P.walk.getVert r, v) ∈
      (((P.take r).walk.append
        (viaOutside P r s hrs hsle v hvP hvr hvs).walk).append
          (P.drop s).walk).edges
    simp [SimpleGraph.Walk.edges_append,
      viaOutside]
  have hQsupport :
      ∀ z ∈ Q.walk.support,
        z ∈ P.walk.support ∨ z = v := by
    exact shortcutViaOutside_support
      P r s hrs hsle v hvP hvr hvs
  let paths : Fin 3 → SimplePath G T.x T.y :=
    fun j => if h : j = i then Q else T.path j
  let U : Theta G := {
    x := T.x
    y := T.y
    roots_ne := T.roots_ne
    path := paths
    paths_ne := by
      intro j k hjk
      by_cases hji : j = i
      · by_cases hki : k = i
        · exact False.elim (hjk (hji.trans hki.symm))
        · simp only [paths, dif_pos hji, dif_neg hki]
          intro heq
          have hedgeOld :
              s(P.walk.getVert r, v) ∈
                (T.path k).walk.edges := by
            rw [← heq]
            exact hQedge
          have hvSupport :
              v ∈ (T.path k).walk.support :=
            (T.path k).walk.snd_mem_support_of_mem_edges
              hedgeOld
          exact hv (T.mem_verts_of_mem_path k hvSupport)
      · by_cases hki : k = i
        · simp only [paths, dif_neg hji, dif_pos hki]
          intro heq
          have hedgeOld :
              s(P.walk.getVert r, v) ∈
                (T.path j).walk.edges := by
            rw [heq]
            exact hQedge
          have hvSupport :
              v ∈ (T.path j).walk.support :=
            (T.path j).walk.snd_mem_support_of_mem_edges
              hedgeOld
          exact hv (T.mem_verts_of_mem_path j hvSupport)
        · simp only [paths, dif_neg hji, dif_neg hki]
          exact T.paths_ne j k hjk
    internal_disjoint := by
      intro j k hjk
      by_cases hji : j = i
      · by_cases hki : k = i
        · exact False.elim (hjk (hji.trans hki.symm))
        · simp only [paths, dif_pos hji, dif_neg hki]
          apply List.disjoint_left.mpr
          intro z hzQ hzK
          have hzQdata :=
            internal_support_data Q T.roots_ne hzQ
          rcases hQsupport z
              hzQdata.1 with hzP | rfl
          · have hzx : z ≠ T.x := hzQdata.2.1
            have hzy : z ≠ T.y := hzQdata.2.2
            have hzI :=
              P.mem_internalSupport_of_mem_support
                hzP hzx hzy
            exact (List.disjoint_left.mp
              (T.internal_disjoint i k
                (fun hik => hki hik.symm)) hzI) hzK
          · exact hv (T.mem_verts_of_mem_path k
              (internal_support_data
                (T.path k) T.roots_ne hzK).1)
      · by_cases hki : k = i
        · simp only [paths, dif_neg hji, dif_pos hki]
          exact List.Disjoint.symm (by
            apply List.disjoint_left.mpr
            intro z hzQ hzJ
            have hzQdata :=
              internal_support_data Q T.roots_ne hzQ
            rcases hQsupport z
                hzQdata.1 with hzP | rfl
            · have hzx : z ≠ T.x := hzQdata.2.1
              have hzy : z ≠ T.y := hzQdata.2.2
              have hzI :=
                P.mem_internalSupport_of_mem_support
                  hzP hzx hzy
              exact (List.disjoint_left.mp
                (T.internal_disjoint i j
                  (fun hij => hji hij.symm)) hzI) hzJ
            · exact hv (T.mem_verts_of_mem_path j
                (internal_support_data
                  (T.path j) T.roots_ne hzJ).1))
        · simp only [paths, dif_neg hji, dif_neg hki]
          exact T.internal_disjoint j k hjk
  }
  have hsubset :
      U.verts ⊆ insert v T.verts := by
    intro z hzU
    simp only [Theta.verts, Finset.mem_biUnion] at hzU
    obtain ⟨j, -, hzj⟩ := hzU
    by_cases hji : j = i
    · subst j
      simp only [U, paths, dif_pos rfl] at hzj
      rcases hQsupport z (by simpa using hzj) with hzP | rfl
      · exact Finset.mem_insert_of_mem
          (T.mem_verts_of_mem_path i hzP)
      · exact Finset.mem_insert_self _ _
    · simp only [U, paths, dif_neg hji] at hzj
      exact Finset.mem_insert_of_mem
        (T.mem_verts_of_mem_path j (by simpa using hzj))
  let q₁ := P.walk.getVert (r + 1)
  let q₂ := P.walk.getVert (r + 2)
  have hq₁Internal :
      q₁ ∈ P.internalSupport :=
    internal_mem_of_getVert P (by omega)
      (by omega)
  have hq₂Internal :
      q₂ ∈ P.internalSupport :=
    internal_mem_of_getVert P (by omega)
      (by omega)
  have hq₁T :
      q₁ ∈ T.verts :=
    T.mem_verts_of_mem_path i
      (internal_support_data P T.roots_ne hq₁Internal).1
  have hq₂T :
      q₂ ∈ T.verts :=
    T.mem_verts_of_mem_path i
      (internal_support_data P T.roots_ne hq₂Internal).1
  have hq₁NotQ : q₁ ∉ Q.walk.support := by
    exact shortcutViaOutside_omits_between
      P r s (r + 1) (by omega) (by omega)
      hsle v hvP hvr hvs
  have hq₂NotQ : q₂ ∉ Q.walk.support := by
    exact shortcutViaOutside_omits_between
      P r s (r + 2) (by omega) (by omega)
      hsle v hvP hvr hvs
  have hq₁NotU : q₁ ∉ U.verts := by
    intro hqU
    simp only [Theta.verts, Finset.mem_biUnion] at hqU
    obtain ⟨j, -, hqj⟩ := hqU
    by_cases hji : j = i
    · subst j
      simp only [U, paths, dif_pos rfl] at hqj
      exact hq₁NotQ (by simpa using hqj)
    · simp only [U, paths, dif_neg hji] at hqj
      have hqj' :
          q₁ ∈ (T.path j).walk.support := by simpa using hqj
      rcases T.eq_root_of_mem_two_paths
          (fun hij => hji hij.symm)
          (internal_support_data P T.roots_ne hq₁Internal).1
          hqj' with hroot | hroot
      · exact (internal_support_data
          P T.roots_ne hq₁Internal).2.1 hroot
      · exact (internal_support_data
          P T.roots_ne hq₁Internal).2.2 hroot
  have hq₂NotU : q₂ ∉ U.verts := by
    intro hqU
    simp only [Theta.verts, Finset.mem_biUnion] at hqU
    obtain ⟨j, -, hqj⟩ := hqU
    by_cases hji : j = i
    · subst j
      simp only [U, paths, dif_pos rfl] at hqj
      exact hq₂NotQ (by simpa using hqj)
    · simp only [U, paths, dif_neg hji] at hqj
      have hqj' :
          q₂ ∈ (T.path j).walk.support := by simpa using hqj
      rcases T.eq_root_of_mem_two_paths
          (fun hij => hji hij.symm)
          (internal_support_data P T.roots_ne hq₂Internal).1
          hqj' with hroot | hroot
      · exact (internal_support_data
          P T.roots_ne hq₂Internal).2.1 hroot
      · exact (internal_support_data
          P T.roots_ne hq₂Internal).2.2 hroot
  have hq₁q₂ : q₁ ≠ q₂ := by
    intro h
    have :
        r + 1 = r + 2 :=
      (getVert_eq_iff P (by omega) (by omega)).1 h
    omega
  have hlargeSubset :
      insert q₁ (insert q₂ U.verts) ⊆
        insert v T.verts := by
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hzU
    · exact Finset.mem_insert_of_mem hq₁T
    · exact Finset.mem_insert_of_mem hq₂T
    · exact hsubset hzU
  have hcardLarge :
      (insert q₁ (insert q₂ U.verts)).card =
        U.verts.card + 2 := by
    have hq₁NotInsert :
        q₁ ∉ insert q₂ U.verts := by
      simp [hq₁q₂, hq₁NotU]
    rw [Finset.card_insert_of_notMem hq₁NotInsert,
      Finset.card_insert_of_notMem hq₂NotU]
  have hcardAmbient :
      (insert v T.verts).card =
        T.verts.card + 1 :=
    Finset.card_insert_of_notMem hv
  have hcardIneq :=
    Finset.card_le_card hlargeSubset
  rw [hcardLarge, hcardAmbient] at hcardIneq
  exact (Nat.not_lt_of_ge (hminimum U)) (by omega)

end Theta

end DeanK5
