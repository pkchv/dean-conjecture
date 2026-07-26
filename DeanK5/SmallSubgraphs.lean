import DeanK5.StandingSetup
import DeanK5.Contraction

/-!
# First local exclusions (paper Section 5)

This module begins with the exact labelled `K₄⁻` configuration used by the
paper.  The possible sixth edge is deliberately not constrained.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {W : Type u} {V : Type v}

/-- A labelled copy of the five required edges of `K₄⁻`. -/
structure K4MinusConfig (G : SimpleGraph W) where
  /-- First endpoint of the omitted edge `xb`. -/
  x : W
  /-- First vertex incident to all three other labelled vertices. -/
  y : W
  /-- Second vertex incident to all three other labelled vertices. -/
  a : W
  /-- Second endpoint of the omitted edge `xb`. -/
  b : W
  x_ne_y : x ≠ y
  x_ne_a : x ≠ a
  x_ne_b : x ≠ b
  y_ne_a : y ≠ a
  y_ne_b : y ≠ b
  a_ne_b : a ≠ b
  xy : G.Adj x y
  xa : G.Adj x a
  ya : G.Adj y a
  yb : G.Adj y b
  ab : G.Adj a b

/-- A labelled triangle. -/
structure TriangleConfig (G : SimpleGraph W) where
  /-- First labelled triangle vertex. -/
  p : W
  /-- Second labelled triangle vertex. -/
  q : W
  /-- Third labelled triangle vertex. -/
  r : W
  p_ne_q : p ≠ q
  p_ne_r : p ≠ r
  q_ne_r : q ≠ r
  pq : G.Adj p q
  qr : G.Adj q r
  rp : G.Adj r p

namespace TriangleConfig

variable {G : SimpleGraph W}

theorem adj_s_p
    (T : TriangleConfig G) {s other : W}
    (h : (s = T.q ∧ other = T.r) ∨
      (s = T.r ∧ other = T.q)) :
    G.Adj s T.p := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact T.pq.symm
  · exact T.rp

theorem adj_s_other
    (T : TriangleConfig G) {s other : W}
    (h : (s = T.q ∧ other = T.r) ∨
      (s = T.r ∧ other = T.q)) :
    G.Adj s other := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact T.qr
  · exact T.qr.symm

theorem adj_other_p
    (T : TriangleConfig G) {s other : W}
    (h : (s = T.q ∧ other = T.r) ∨
      (s = T.r ∧ other = T.q)) :
    G.Adj other T.p := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact T.rp
  · exact T.pq.symm

theorem s_ne_p
    (T : TriangleConfig G) {s other : W}
    (h : (s = T.q ∧ other = T.r) ∨
      (s = T.r ∧ other = T.q)) :
    s ≠ T.p := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact T.p_ne_q.symm
  · exact T.p_ne_r.symm

theorem other_ne_p
    (T : TriangleConfig G) {s other : W}
    (h : (s = T.q ∧ other = T.r) ∨
      (s = T.r ∧ other = T.q)) :
    other ≠ T.p := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact T.p_ne_r.symm
  · exact T.p_ne_q.symm

theorem s_ne_other
    (T : TriangleConfig G) {s other : W}
    (h : (s = T.q ∧ other = T.r) ∨
      (s = T.r ∧ other = T.q)) :
    s ≠ other := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact T.q_ne_r
  · exact T.q_ne_r.symm

/-- Cyclically relabel the triangle so that the edge `rp` becomes the
next contraction edge. -/
def rotate (T : TriangleConfig G) : TriangleConfig G where
  p := T.q
  q := T.r
  r := T.p
  p_ne_q := T.q_ne_r
  p_ne_r := T.p_ne_q.symm
  q_ne_r := T.p_ne_r.symm
  pq := T.qr
  qr := T.rp
  rp := T.pq

end TriangleConfig

/--
The cycle output of lifting one contracted admissible path through a
triangle: one closure adds one edge and the other adds two.
-/
structure TriangleLiftCycleGrid
    {U : Type*} (A : SimpleGraph U) (G : SimpleGraph W) {p t : U}
    (paths : AdmissiblePathFamily A p t 4) where
  /-- Cycles obtained by closing each lifted path with one edge. -/
  short : Fin 4 → SimpleCycle G
  /-- Cycles obtained by closing each lifted path with two edges. -/
  long : Fin 4 → SimpleCycle G
  length_short : ∀ i, (short i).length = (paths.path i).length + 1
  length_long : ∀ i, (long i).length = (paths.path i).length + 2

/--
The modular calculation at the end of Lemma 5.2.  It consumes actual
simple-cycle witnesses, not merely claimed walk lengths.
-/
theorem four_paths_two_triangle_closures_force_divisible_cycle
    {U : Type*} (A : SimpleGraph U) (G : SimpleGraph W) {p t : U}
    (paths : AdmissiblePathFamily A p t 4)
    (grid : TriangleLiftCycleGrid A G paths) :
    HasCycleDivisibleBy G 5 := by
  rcases paths.admissible_step with hstep | hstep
  · let pi : Fin 5 → Fin 4 := ![0, 0, 1, 2, 3]
    let useLong : Fin 5 → Bool := ![false, true, true, true, true]
    let F : AdmissibleCycleFamily G 5 := {
      start := paths.start + 1
      step := 1
      admissible_step := Or.inl rfl
      cycle i := if useLong i then grid.long (pi i) else grid.short (pi i)
      length_cycle := by
        intro i
        fin_cases i <;>
          simp [pi, useLong, grid.length_short, grid.length_long,
            paths.length_path, hstep]
    }
    exact F.hasCycleDivisibleByFive
  · let pi : Fin 5 → Fin 4 := ![0, 0, 1, 1, 2]
    let useLong : Fin 5 → Bool := ![false, true, false, true, false]
    let F : AdmissibleCycleFamily G 5 := {
      start := paths.start + 1
      step := 1
      admissible_step := Or.inl rfl
      cycle i := if useLong i then grid.long (pi i) else grid.short (pi i)
      length_cycle := by
        intro i
        fin_cases i <;>
          simp [pi, useLong, grid.length_short, grid.length_long,
            paths.length_path, hstep]
    }
    exact F.hasCycleDivisibleByFive

namespace StandingSetup

variable [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}

/--
A fifth vertex adjacent to both `a` and `b` in the labelled configuration
creates the explicit cycle `x-y-b-v-a-x`.
-/
theorem k4minus_common_neighbor_gives_five_cycle
    (setup : StandingSetup J B c D)
    (K : K4MinusConfig J) (w : W)
    (hwx : w ≠ K.x) (hwy : w ≠ K.y)
    (hwa : w ≠ K.a) (hwb : w ≠ K.b)
    (hwaAdj : J.Adj w K.a) (hwbAdj : J.Adj w K.b) :
    HasCycleDivisibleBy B 5 := by
  let vertices : Fin 5 → W :=
    ![K.x, K.y, K.b, w, K.a]
  let f : SimpleGraph.cycleGraph 5 →g B := {
    toFun i := setup.inclusion (vertices i)
    map_rel' := by
      intro i j hij
      apply setup.inclusion.toHom.map_rel'
      have hj : j = i - 1 ∨ j = i + 1 := by
        have hjmem : j ∈ (SimpleGraph.cycleGraph 5).neighborSet i :=
          hij
        simpa [SimpleGraph.cycleGraph_neighborSet] using hjmem
      rcases hj with rfl | rfl <;> fin_cases i
      all_goals simp [vertices]
      all_goals first
        | exact K.xy
        | exact K.xy.symm
        | exact K.yb
        | exact K.yb.symm
        | exact hwbAdj
        | exact hwbAdj.symm
        | exact hwaAdj
        | exact hwaAdj.symm
        | exact K.xa
        | exact K.xa.symm
  }
  have hxw : K.x ≠ w := hwx.symm
  have hyw : K.y ≠ w := hwy.symm
  have hbw : K.b ≠ w := hwb.symm
  have hba : K.b ≠ K.a := K.a_ne_b.symm
  have hvertices : Function.Injective vertices := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [vertices] at hij ⊢
    all_goals
      first
      | exact False.elim (K.x_ne_y hij)
      | exact False.elim (K.x_ne_b hij)
      | exact False.elim (hxw hij)
      | exact False.elim (K.x_ne_a hij)
      | exact False.elim (K.x_ne_y hij.symm)
      | exact False.elim (K.y_ne_b hij)
      | exact False.elim (hyw hij)
      | exact False.elim (K.y_ne_a hij)
      | exact False.elim (K.x_ne_b hij.symm)
      | exact False.elim (K.y_ne_b hij.symm)
      | exact False.elim (hbw hij)
      | exact False.elim (hba hij)
      | exact False.elim (hxw hij.symm)
      | exact False.elim (hyw hij.symm)
      | exact False.elim (hbw hij.symm)
      | exact False.elim (hwa hij)
      | exact False.elim (K.x_ne_a hij.symm)
      | exact False.elim (K.y_ne_a hij.symm)
      | exact False.elim (hba hij.symm)
      | exact False.elim (hwa hij.symm)
  have hf : Function.Injective f := by
    intro i j hij
    exact hvertices (setup.inclusion.injective hij)
  exact hasCycleDivisibleByFive_of_injective_cycleHom f hf

/--
Under the no-divisible-cycle standing assumption, any other vertex has at
most one neighbour in the pair `{a,b}`.
-/
theorem k4minus_at_most_one_pair_neighbor
    (setup : StandingSetup J B c D)
    (K : K4MinusConfig J) (w : W)
    (hwx : w ≠ K.x) (hwy : w ≠ K.y)
    (hwa : w ≠ K.a) (hwb : w ≠ K.b) :
    ¬(J.Adj w K.a ∧ J.Adj w K.b) := by
  rintro ⟨hwaAdj, hwbAdj⟩
  exact setup.no_divisible_cycle
    (setup.k4minus_common_neighbor_gives_five_cycle
      K w hwx hwy hwa hwb hwaAdj hwbAdj)

omit [DecidableEq W] in
/-- In a five-vertex graph, degree at least four forces every possible edge. -/
theorem adjacent_of_card_five_of_degree_at_least_four
    (G : SimpleGraph W) (hcard : Fintype.card W = 5)
    (u v : W) (huv : u ≠ v)
    (hdegree : 4 ≤ finiteDegree G u) :
    G.Adj u v := by
  classical
  let N := G.neighborSet u
  have huN : u ∉ N := G.loopless.irrefl u
  have hinsertCard :
      (insert u N).ncard = N.ncard + 1 :=
    Set.ncard_insert_of_notMem huN
  have hsub : insert u N ⊆ (Set.univ : Set W) :=
    Set.subset_univ _
  have hunivLe : (Set.univ : Set W).ncard ≤ (insert u N).ncard := by
    simp only [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    rw [hinsertCard]
    change 5 ≤ finiteDegree G u + 1
    omega
  have heq : insert u N = (Set.univ : Set W) :=
    Set.eq_of_subset_of_ncard_le hsub hunivLe
  have hvInsert : v ∈ insert u N := by
    rw [heq]
    trivial
  rcases Set.mem_insert_iff.mp hvInsert with hvu | hvN
  · exact False.elim (huv hvu.symm)
  · exact hvN

/-- Paper Lemma 5.1: the standing graph contains no `K₄⁻`. -/
theorem no_k4minus
    (setup : StandingSetup J B c D) :
    ¬ Nonempty (K4MinusConfig J) := by
  rintro ⟨K⟩
  let S : Finset W := {K.a, K.b}
  let U : Set W := {w | w ∉ S}
  let A₀ := J.induce U
  let rx : U := ⟨K.x, by
    simp [U, S, K.x_ne_a, K.x_ne_b]⟩
  let ry : U := ⟨K.y, by
    simp [U, S, K.y_ne_a, K.y_ne_b]⟩
  let A := A₀ \ edge rx ry
  let DU : Finset U :=
    Finset.univ.filter fun w => w.1 ∈ D
  let Z : Finset U :=
    DU.filter fun w => w ≠ rx ∧ w ≠ ry
  have hroots : rx ≠ ry := by
    intro h
    exact K.x_ne_y (congrArg Subtype.val h)
  have hA₀two : IsTwoConnected A₀ := by
    have h :=
      isKConnected_deleteVertices J 2 2 setup.four_connected S (by
        norm_num [S, K.a_ne_b])
    simpa [A₀, U, S, deleteVertices] using h
  have hrootAdj : A₀.Adj rx ry := by
    exact K.xy
  have hAedge : A ⊔ edge rx ry = A₀ := by
    ext p q
    simp only [A, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
    constructor
    · rintro (⟨hpq, -⟩ | hpq)
      · exact hpq
      · simp only [SimpleGraph.edge_adj] at hpq
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hrootAdj
        · exact hrootAdj.symm
    · intro hpq
      by_cases hedge : (edge rx ry).Adj p q
      · exact Or.inr hedge
      · exact Or.inl ⟨hpq, hedge⟩
  have hnotadj : ¬ A.Adj rx ry := by
    intro h
    exact h.2 (by
      simpa [SimpleGraph.edge_adj] using hroots)
  have hloss :
      ∀ w : U, w ≠ rx → w ≠ ry →
        finiteDegree J w.1 ≤ finiteDegree A w + 1 := by
    intro w hwrx hwry
    have hwx : w.1 ≠ K.x := by
      intro h
      exact hwrx (by apply Subtype.ext; exact h)
    have hwy : w.1 ≠ K.y := by
      intro h
      exact hwry (by apply Subtype.ext; exact h)
    have hwa : w.1 ≠ K.a := by
      intro h
      exact w.2 (by simp [S, h])
    have hwb : w.1 ≠ K.b := by
      intro h
      exact w.2 (by simp [S, h])
    have hone :=
      setup.k4minus_at_most_one_pair_neighbor
        K w.1 hwx hwy hwa hwb
    have hInduce :
        finiteDegree J w.1 ≤ finiteDegree A₀ w + 1 := by
      by_cases hwaAdj : J.Adj w.1 K.a
      · apply finiteDegree_le_induce_add_one J U w K.a
        intro t hwt htU
        have htPair : t = K.a ∨ t = K.b := by
          have htS : t ∈ S := by
            by_contra htNotS
            exact htU htNotS
          simpa [S] using htS
        rcases htPair with hta | htb
        · exact hta
        · subst t
          exact False.elim (hone ⟨hwaAdj, hwt⟩)
      · apply finiteDegree_le_induce_add_one J U w K.b
        intro t hwt htU
        have htPair : t = K.a ∨ t = K.b := by
          have htS : t ∈ S := by
            by_contra htNotS
            exact htU htNotS
          simpa [S] using htS
        rcases htPair with hta | htb
        · subst t
          exact False.elim (hwaAdj hwt)
        · exact htb
    rw [finiteDegree_sdiff_edge_of_ne A₀ rx ry w hwrx hwry]
    exact hInduce
  have horderA : 4 ≤ Fintype.card U := by
    by_contra hsmall
    have hUcard : Fintype.card U = 3 := by
      have := hA₀two.1
      omega
    have hexists : ∃ w : U, w ≠ rx ∧ w ≠ ry := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset U) ⊆ {rx, ry} := by
        intro w _hw
        by_cases hwrx : w = rx
        · simp [hwrx]
        · simp [h w hwrx]
      have hcardle := Finset.card_le_card hsub
      have hpaircard : ({rx, ry} : Finset U).card = 2 :=
        Finset.card_pair_eq_two_iff.mpr hroots
      rw [hpaircard] at hcardle
      have hunivcard :
          (Finset.univ : Finset U).card = 3 := by
        simpa using hUcard
      omega
    obtain ⟨w, hwrx, hwry⟩ := hexists
    have hmemberCard :
        Fintype.card {v : W // v ∈ S} = 2 := by
      change Fintype.card ↥S = 2
      rw [Fintype.card_coe]
      exact Finset.card_pair_eq_two_iff.mpr K.a_ne_b
    have hUcardFormula :
        Fintype.card U = Fintype.card W - 2 := by
      change Fintype.card {v : W // ¬v ∈ S} =
        Fintype.card W - 2
      rw [Fintype.card_subtype_compl, hmemberCard]
    have hWcard : Fintype.card W = 5 := by
      have hWlower := setup.four_connected.1
      omega
    have hwx : w.1 ≠ K.x := by
      intro h
      exact hwrx (by apply Subtype.ext; exact h)
    have hwy : w.1 ≠ K.y := by
      intro h
      exact hwry (by apply Subtype.ext; exact h)
    have hwa : w.1 ≠ K.a := by
      intro h
      exact w.2 (by simp [S, h])
    have hwb : w.1 ≠ K.b := by
      intro h
      exact w.2 (by simp [S, h])
    have hwaAdj : J.Adj w.1 K.a :=
      adjacent_of_card_five_of_degree_at_least_four
        J hWcard w.1 K.a hwa (setup.degree_at_least_four w.1)
    have hwbAdj : J.Adj w.1 K.b :=
      adjacent_of_card_five_of_degree_at_least_four
        J hWcard w.1 K.b hwb (setup.degree_at_least_four w.1)
    exact setup.no_divisible_cycle
      (setup.k4minus_common_neighbor_gives_five_cycle
        K w.1 hwx hwy hwa hwb hwaAdj hwbAdj)
  have hxZ : rx ∉ Z := by
    simp [Z]
  have hyZ : ry ∉ Z := by
    simp [Z]
  have hZDU : Z ⊆ DU := by
    intro w hw
    exact (Finset.mem_filter.mp hw).1
  have hdeg :
      ∀ w, w ≠ rx → w ≠ ry → w ∉ Z →
        3 + 1 ≤ finiteDegree A w := by
    intro w hwrx hwry hwZ
    have hwD : w.1 ∉ D := by
      intro hwD
      apply hwZ
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwD⟩,
        hwrx, hwry⟩
    have hJdeg := setup.degree_regular w.1 hwD
    have hl := hloss w hwrx hwry
    omega
  have hdegZ :
      ∀ w ∈ Z, 3 ≤ finiteDegree A w := by
    intro w hwZ
    have hwFilter := Finset.mem_filter.mp hwZ
    have hwD := (Finset.mem_filter.mp hwFilter.1).2
    have hJdeg := setup.degree_deficient w.1 hwD
    have hl := hloss w hwFilter.2.1 hwFilter.2.2
    omega
  have lifted : RootLiftResult A Z rx ry 3 :=
    root_lifting 3 A DU Z rx ry
      (by omega) hroots hnotadj (hAedge ▸ hA₀two)
      hZDU hxZ hyZ hdeg hdegZ (fun _ => horderA)
  let φ : A →g B := {
    toFun w := setup.inclusion w.1
    map_rel' := by
      intro p q hpq
      exact setup.inclusion.toHom.map_rel' hpq.1
  }
  have hφ : Function.Injective φ := by
    intro p q hpq
    apply Subtype.ext
    exact setup.inclusion.injective hpq
  have hcφ : c ∉ Set.range φ := by
    rintro ⟨w, hw⟩
    exact setup.c_not_old ⟨w.1, by
      simpa [φ] using hw⟩
  have hZadj : ∀ z ∈ Z, B.Adj c (φ z) := by
    intro z hz
    have hzD := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hz).1).2
    exact setup.deficient_adjacent_to_c z.1 hzD
  obtain ⟨F, hsupp, -⟩ :=
    lifted.mapToAmbient φ c hZadj hφ hcφ
  change AdmissiblePathFamily B
    (setup.inclusion K.x) (setup.inclusion K.y) 3 at F
  change ∀ i v, v ∈ (F.path i).walk.support →
    v = c ∨ v ∈ Set.range φ at hsupp
  have hxyB := setup.inclusion.toHom.map_rel' K.xy
  have hxaB := setup.inclusion.toHom.map_rel' K.xa
  have hyaB := setup.inclusion.toHom.map_rel' K.ya
  have hybB := setup.inclusion.toHom.map_rel' K.yb
  have habB := setup.inclusion.toHom.map_rel' K.ab
  let P₁ : SimplePath B
      (setup.inclusion K.y) (setup.inclusion K.x) := {
    walk := .cons hxyB.symm .nil
    isPath := by
      simp [K.x_ne_y.symm, setup.inclusion.injective.eq_iff]
  }
  let P₂ : SimplePath B
      (setup.inclusion K.y) (setup.inclusion K.x) := {
    walk := .cons hyaB (.cons hxaB.symm .nil)
    isPath := by
      simp [K.y_ne_a, K.x_ne_a.symm, K.x_ne_y.symm,
        setup.inclusion.injective.eq_iff]
  }
  let P₃ : SimplePath B
      (setup.inclusion K.y) (setup.inclusion K.x) := {
    walk := .cons hybB (.cons habB.symm (.cons hxaB.symm .nil))
    isPath := by
      simp [K.y_ne_b, K.y_ne_a, K.x_ne_a.symm,
        K.a_ne_b.symm, K.x_ne_b.symm,
        K.x_ne_y.symm, setup.inclusion.injective.eq_iff]
  }
  let core : ConsecutivePathTriple B
      (setup.inclusion K.y) (setup.inclusion K.x) := {
    start := 1
    path := ![P₁, P₂, P₃]
    length_path := by
      intro i
      fin_cases i <;>
        simp [P₁, P₂, P₃, SimplePath.length]
  }
  have hcoreSupport :
      ∀ j v, v ∈ (core.path j).walk.support.tail →
        v = setup.inclusion K.x ∨
        v = setup.inclusion K.a ∨
        v = setup.inclusion K.b := by
    intro j v hv
    fin_cases j <;>
      simp [core, P₁, P₂, P₃] at hv
    all_goals tauto
  have hdisj :
      ∀ i j,
        (F.path i).walk.support.tail.Disjoint
          (core.path j).walk.support.tail := by
    intro i j
    rw [List.disjoint_left]
    intro v hvF hvCore
    have hvFfull : v ∈ (F.path i).walk.support :=
      List.mem_of_mem_tail hvF
    have hvAllowed := hsupp i v hvFfull
    have hvCoreClass := hcoreSupport j v hvCore
    rcases hvAllowed with hvc | hvrange
    · rcases hvCoreClass with hvx | hva | hvb
      · exact setup.c_not_old ⟨K.x, hvx.symm.trans hvc⟩
      · exact setup.c_not_old ⟨K.a, hva.symm.trans hvc⟩
      · exact setup.c_not_old ⟨K.b, hvb.symm.trans hvc⟩
    · obtain ⟨w, rfl⟩ := hvrange
      rcases hvCoreClass with hvx | hva | hvb
      · have hwx : w.1 = K.x :=
          setup.inclusion.injective hvx
        exact (F.path i).start_not_mem_tail (by
          simpa [φ, hwx] using hvF)
      · have hwa : w.1 = K.a :=
          setup.inclusion.injective hva
        exact w.2 (by simp [U, S, hwa])
      · have hwb : w.1 = K.b :=
          setup.inclusion.injective hvb
        exact w.2 (by simp [U, S, hwb])
  exact setup.no_divisible_cycle
    (admissible_three_plus_consecutive_three_forces_divisible_cycle
      B F core hdisj)

/--
After Lemma 5.1, a vertex outside a triangle has at most one neighbour in
that triangle.
-/
theorem triangle_external_vertex_at_most_one_neighbor
    (setup : StandingSetup J B c D)
    (T : TriangleConfig J) (w : W)
    (hwp : w ≠ T.p) (hwq : w ≠ T.q) (hwr : w ≠ T.r) :
    ¬((J.Adj w T.p ∧ J.Adj w T.q) ∨
      (J.Adj w T.q ∧ J.Adj w T.r) ∨
      (J.Adj w T.r ∧ J.Adj w T.p)) := by
  intro htwo
  apply setup.no_k4minus
  rcases htwo with hpq | hqr | hrp
  · refine ⟨{
      x := T.r
      y := T.p
      a := T.q
      b := w
      x_ne_y := T.p_ne_r.symm
      x_ne_a := T.q_ne_r.symm
      x_ne_b := hwr.symm
      y_ne_a := T.p_ne_q
      y_ne_b := hwp.symm
      a_ne_b := hwq.symm
      xy := T.rp
      xa := T.qr.symm
      ya := T.pq
      yb := hpq.1.symm
      ab := hpq.2.symm
    }⟩
  · refine ⟨{
      x := T.p
      y := T.q
      a := T.r
      b := w
      x_ne_y := T.p_ne_q
      x_ne_a := T.p_ne_r
      x_ne_b := hwp.symm
      y_ne_a := T.q_ne_r
      y_ne_b := hwq.symm
      a_ne_b := hwr.symm
      xy := T.pq
      xa := T.rp.symm
      ya := T.qr
      yb := hqr.1.symm
      ab := hqr.2.symm
    }⟩
  · refine ⟨{
      x := T.q
      y := T.r
      a := T.p
      b := w
      x_ne_y := T.q_ne_r
      x_ne_a := T.p_ne_q.symm
      x_ne_b := hwq.symm
      y_ne_a := T.p_ne_r.symm
      y_ne_b := hwr.symm
      a_ne_b := hwp.symm
      xy := T.qr
      xa := T.pq.symm
      ya := T.rp
      yb := hrp.1.symm
      ab := hrp.2.symm
    }⟩

/-- Distinct images of the neighbours of `c` after contracting `qr`. -/
noncomputable def contractedCNeighbors
    (setup : StandingSetup J B c D) (q r : W) :
    Finset (ContractPairVertex W q r) := by
  classical
  exact Finset.univ.filter fun z =>
    ∃ w : W, contractVertex q r w = z ∧
      B.Adj c (setup.inclusion w)

@[simp] theorem mem_contractedCNeighbors
    (setup : StandingSetup J B c D) (q r : W)
    (z : ContractPairVertex W q r) :
    z ∈ setup.contractedCNeighbors q r ↔
      ∃ w : W, contractVertex q r w = z ∧
        B.Adj c (setup.inclusion w) := by
  classical
  simp [contractedCNeighbors]

/--
The auxiliary graph obtained by contracting `q` and `r` in `J` and
adjoining a root for the contracted images of the neighbors of `c`.
-/
noncomputable def triangleContractionGraph
    (setup : StandingSetup J B c D) (q r : W) :
    SimpleGraph (Option (ContractPairVertex W q r)) :=
  adjoinRoot (contractPair J q r) (setup.contractedCNeighbors q r)

/-- The image of `p` in the rooted contraction graph. -/
def triangleContractP (q r p : W) :
    Option (ContractPairVertex W q r) :=
  some (contractVertex q r p)

/-- The vertex representing the contracted pair `q, r`. -/
def triangleContractT (q r : W) :
    Option (ContractPairVertex W q r) :=
  some none

/--
The rooted contraction graph with the edge from the image of `p` to the
contracted vertex removed.
-/
noncomputable def triangleContractionBase
    (setup : StandingSetup J B c D) (p q r : W) :
    SimpleGraph (Option (ContractPairVertex W q r)) :=
  setup.triangleContractionGraph q r \
    edge (triangleContractP q r p) (triangleContractT q r)

/-- Map every non-contracted vertex of the auxiliary graph back to `B`. -/
def triangleNonTVertex
    (setup : StandingSetup J B c D) (q r : W) :
    {z : Option (ContractPairVertex W q r) //
      z ≠ triangleContractT q r} → V
  | ⟨none, _⟩ => c
  | ⟨some none, h⟩ => False.elim (h rfl)
  | ⟨some (some w), _⟩ => setup.inclusion w.1

/--
Embed the auxiliary graph away from the contracted vertex back into the
ambient graph `B`.
-/
noncomputable def triangleNonTHom
    (setup : StandingSetup J B c D) (p q r : W) :
    (setup.triangleContractionBase p q r).induce
      {z | z ≠ triangleContractT q r} →g B where
  toFun := setup.triangleNonTVertex q r
  map_rel' := by
    classical
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have habH' :
        (setup.triangleContractionGraph q r).Adj a b := hab.1
    cases a with
    | none =>
        cases b with
        | none => exact False.elim habH'
        | some z =>
            cases z with
            | none => exact False.elim (hb rfl)
            | some w =>
                have hwZ :
                    (some w : ContractPairVertex W q r) ∈
                      setup.contractedCNeighbors q r := habH'
                obtain ⟨x, hxContract, hcx⟩ :=
                  (mem_contractedCNeighbors setup q r _).1 hwZ
                have hxw : x = w.1 := by
                  have hnot : ¬(x = q ∨ x = r) := by
                    intro hx
                    have : contractVertex q r x = none :=
                      (contractVertex_eq_none_iff q r x).2 hx
                    rw [this] at hxContract
                    contradiction
                  have := (contractVertex_eq_iff q r x w.1).1 (by
                    simpa [contractVertex, w.2.1, w.2.2] using hxContract)
                  rcases this with hxw | ⟨hx, hw⟩
                  · exact hxw
                  · exact False.elim (hnot hx)
                simpa [triangleNonTVertex, hxw] using hcx
    | some z =>
        cases b with
        | none =>
            cases z with
            | none => exact False.elim (ha rfl)
            | some w =>
                have hwZ :
                    (some w : ContractPairVertex W q r) ∈
                      setup.contractedCNeighbors q r := habH'
                obtain ⟨x, hxContract, hcx⟩ :=
                  (mem_contractedCNeighbors setup q r _).1 hwZ
                have hxw : x = w.1 := by
                  have hnot : ¬(x = q ∨ x = r) := by
                    intro hx
                    have : contractVertex q r x = none :=
                      (contractVertex_eq_none_iff q r x).2 hx
                    rw [this] at hxContract
                    contradiction
                  have := (contractVertex_eq_iff q r x w.1).1 (by
                    simpa [contractVertex, w.2.1, w.2.2] using hxContract)
                  rcases this with hxw | ⟨hx, hw⟩
                  · exact hxw
                  · exact False.elim (hnot hx)
                simpa [triangleNonTVertex, hxw] using hcx.symm
        | some z' =>
            cases z with
            | none => exact False.elim (ha rfl)
            | some w =>
                cases z' with
                | none => exact False.elim (hb rfl)
                | some w' =>
                    apply setup.inclusion.toHom.map_rel'
                    exact habH'

theorem triangleNonTHom_injective
    (setup : StandingSetup J B c D) (p q r : W) :
    Function.Injective (setup.triangleNonTHom p q r) := by
  intro a b hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some z =>
          cases z with
          | none => exact False.elim (hb rfl)
          | some w =>
              exact False.elim (setup.c_not_old ⟨w.1, by
                simpa [triangleNonTHom, triangleNonTVertex] using hab.symm⟩)
  | some z =>
      cases b with
      | none =>
          cases z with
          | none => exact False.elim (ha rfl)
          | some w =>
              exact False.elim (setup.c_not_old ⟨w.1, by
                simpa [triangleNonTHom, triangleNonTVertex] using hab⟩)
      | some z' =>
          cases z with
          | none => exact False.elim (ha rfl)
          | some w =>
              cases z' with
              | none => exact False.elim (hb rfl)
              | some w' =>
                  apply Subtype.ext
                  apply congrArg some
                  apply congrArg some
                  apply Subtype.ext
                  exact setup.inclusion.injective hab

/-- One contracted path lifted to one of the two endpoints of `qr`. -/
structure TrianglePathLift
    (setup : StandingSetup J B c D)
    (p q r : W)
    (P : SimplePath (setup.triangleContractionBase p q r)
      (triangleContractP q r p) (triangleContractT q r)) where
  /-- Endpoint of `qr` at which the lifted path terminates. -/
  s : W
  /-- The other endpoint of `qr`, avoided by the lifted path. -/
  other : W
  endpoints : (s = q ∧ other = r) ∨ (s = r ∧ other = q)
  /-- The simple path in `B` obtained by lifting `P`. -/
  path : SimplePath B (setup.inclusion p) (setup.inclusion s)
  length_path : path.length = P.length
  avoids_other : setup.inclusion other ∉ path.walk.support

/-- The direct edge from the selected lift endpoint back to `p`. -/
def triangleShortClosure
    (setup : StandingSetup J B c D)
    (T : TriangleConfig J)
    {P : SimplePath (setup.triangleContractionBase T.p T.q T.r)
      (triangleContractP T.q T.r T.p) (triangleContractT T.q T.r)}
    (L : TrianglePathLift setup T.p T.q T.r P) :
    SimplePath B (setup.inclusion L.s) (setup.inclusion T.p) := {
  walk := .cons
    (setup.inclusion.toHom.map_rel' (T.adj_s_p L.endpoints))
    .nil
  isPath := by
    simp [T.s_ne_p L.endpoints,
      setup.inclusion.injective.eq_iff]
}

/-- The two-edge route from the selected endpoint through the other
triangle vertex and back to `p`. -/
def triangleLongClosure
    (setup : StandingSetup J B c D)
    (T : TriangleConfig J)
    {P : SimplePath (setup.triangleContractionBase T.p T.q T.r)
      (triangleContractP T.q T.r T.p) (triangleContractT T.q T.r)}
    (L : TrianglePathLift setup T.p T.q T.r P) :
    SimplePath B (setup.inclusion L.s) (setup.inclusion T.p) := {
  walk := .cons
    (setup.inclusion.toHom.map_rel' (T.adj_s_other L.endpoints))
    (.cons
      (setup.inclusion.toHom.map_rel' (T.adj_other_p L.endpoints))
      .nil)
  isPath := by
    simp [T.s_ne_other L.endpoints, T.s_ne_p L.endpoints,
      T.other_ne_p L.endpoints,
      setup.inclusion.injective.eq_iff]
}

@[simp] theorem triangleShortClosure_length
    (setup : StandingSetup J B c D)
    (T : TriangleConfig J)
    {P : SimplePath (setup.triangleContractionBase T.p T.q T.r)
      (triangleContractP T.q T.r T.p) (triangleContractT T.q T.r)}
    (L : TrianglePathLift setup T.p T.q T.r P) :
    (triangleShortClosure setup T L).length = 1 := by
  simp [triangleShortClosure, SimplePath.length]

@[simp] theorem triangleLongClosure_length
    (setup : StandingSetup J B c D)
    (T : TriangleConfig J)
    {P : SimplePath (setup.triangleContractionBase T.p T.q T.r)
      (triangleContractP T.q T.r T.p) (triangleContractT T.q T.r)}
    (L : TrianglePathLift setup T.p T.q T.r P) :
    (triangleLongClosure setup T L).length = 2 := by
  simp [triangleLongClosure, SimplePath.length]

/-- The explicit path lift through the contracted endpoint. -/
theorem lift_triangle_contracted_path
    (setup : StandingSetup J B c D)
    (p q r : W)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (P : SimplePath (setup.triangleContractionBase p q r)
      (triangleContractP q r p) (triangleContractT q r)) :
    Nonempty (TrianglePathLift setup p q r P) := by
  let rp := triangleContractP q r p
  let rt := triangleContractT q r
  let R := P.reverse
  have hroots : rp ≠ rt := by
    simp [rp, rt, triangleContractP, triangleContractT,
      contractVertex, hpq, hpr]
  obtain ⟨a, hta, tail, hwalk⟩ :=
    R.walk.exists_eq_cons_of_ne hroots.symm
  have hRpath : (SimpleGraph.Walk.cons hta tail).IsPath := by
        have h := R.isPath
        rw [hwalk] at h
        exact h
  have htailPath : tail.IsPath := hRpath.of_cons
  have hrtTail : rt ∉ tail.support :=
    (SimpleGraph.Walk.cons_isPath_iff hta tail).1 hRpath |>.2
  have haRT : a ≠ rt := by
    intro ha
    subst a
    exact (setup.triangleContractionBase p q r).loopless.irrefl rt hta
  have hrpRT : rp ≠ rt := hroots
  have htailAvoid :
      ∀ z ∈ tail.support, z ∈ {z | z ≠ rt} := by
    intro z hz hzr
    exact hrtTail (hzr ▸ hz)
  let tailI :=
    tail.induce {z | z ≠ rt} htailAvoid
  let Q : SimplePath
      ((setup.triangleContractionBase p q r).induce
        {z | z ≠ rt})
      ⟨a, haRT⟩ ⟨rp, hrpRT⟩ := {
    walk := tailI
    isPath := by
      apply SimpleGraph.Walk.IsPath.of_map
        (f := (Embedding.induce {z | z ≠ rt}).toHom)
      rw [SimpleGraph.Walk.map_induce]
      exact htailPath
  }
  let hom := setup.triangleNonTHom p q r
  let QB := Q.mapInjectiveHom hom
    (setup.triangleNonTHom_injective p q r)
  have hQBend :
      hom (⟨rp, hrpRT⟩ :
        {z | z ≠ rt}) = setup.inclusion p := by
    change setup.triangleNonTVertex q r ⟨rp, hrpRT⟩ =
      setup.inclusion p
    simp [triangleNonTVertex,
      rp, triangleContractP, triangleContractT,
      contractVertex, hpq, hpr]
  let QB' : SimplePath B
      (hom ⟨a, haRT⟩) (setup.inclusion p) := by
    exact QB.castEnd hQBend
  have hsChoice :
      ∃ s other : W,
        ((s = q ∧ other = r) ∨ (s = r ∧ other = q)) ∧
        B.Adj (setup.inclusion s) (hom ⟨a, haRT⟩) := by
    have htaH := hta.1
    cases a with
    | none =>
        have htZ :
            (none : ContractPairVertex W q r) ∈
              setup.contractedCNeighbors q r := htaH
        obtain ⟨s, hsContract, hcs⟩ :=
          (mem_contractedCNeighbors setup q r _).1 htZ
        have hsPair : s = q ∨ s = r :=
          (contractVertex_eq_none_iff q r s).1 hsContract
        rcases hsPair with hs | hs
        · exact ⟨q, r, Or.inl ⟨rfl, rfl⟩, by
            simpa [hom, triangleNonTHom, triangleNonTVertex, hs] using hcs.symm⟩
        · exact ⟨r, q, Or.inr ⟨rfl, rfl⟩, by
            simpa [hom, triangleNonTHom, triangleNonTVertex, hs] using hcs.symm⟩
    | some z =>
        cases z with
        | none => exact False.elim (haRT rfl)
        | some w =>
            have htAdj :
                (contractPair J q r).Adj none (some w) := htaH
            rcases htAdj with hqw | hrw
            · exact ⟨q, r, Or.inl ⟨rfl, rfl⟩, by
                simpa [hom, triangleNonTHom, triangleNonTVertex] using
                  setup.inclusion.toHom.map_rel' hqw⟩
            · exact ⟨r, q, Or.inr ⟨rfl, rfl⟩, by
                simpa [hom, triangleNonTHom, triangleNonTVertex] using
                  setup.inclusion.toHom.map_rel' hrw⟩
  obtain ⟨s, other, hends, hsa⟩ := hsChoice
  have endpoint_not_in_QB
      (e : W) (he : e = q ∨ e = r) :
      setup.inclusion e ∉ QB.walk.support := by
    intro heSupp
    change setup.inclusion e ∈
      (Q.walk.map hom).support at heSupp
    rw [SimpleGraph.Walk.support_map] at heSupp
    obtain ⟨z, hz, hzEq⟩ := List.mem_map.mp heSupp
    rcases z with ⟨z, hzRT⟩
    cases z with
    | none =>
        exact setup.c_not_old ⟨e, by
          simpa [hom, triangleNonTHom, triangleNonTVertex] using hzEq.symm⟩
    | some z =>
        cases z with
        | none => exact False.elim (hzRT rfl)
        | some w =>
            have hew : e = w.1 :=
              (setup.inclusion.injective (by
                simpa [hom, triangleNonTHom, triangleNonTVertex] using hzEq)).symm
            rcases he with rfl | rfl
            · exact w.2.1 hew.symm
            · exact w.2.2 hew.symm
  have hsPair : s = q ∨ s = r := by
    rcases hends with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hotherPair : other = q ∨ other = r := by
    rcases hends with h | h
    · exact Or.inr h.2
    · exact Or.inl h.2
  have hsNotQB := endpoint_not_in_QB s hsPair
  have hsNotQB' : setup.inclusion s ∉ QB'.walk.support := by
    simpa [QB'] using hsNotQB
  let liftedReverse : SimplePath B
      (setup.inclusion s) (setup.inclusion p) := {
    walk := .cons hsa QB'.walk
    isPath := QB'.isPath.cons hsNotQB'
  }
  let lifted := liftedReverse.reverse
  have hlength : lifted.length = P.length := by
    have htailILen : tailI.length = tail.length := by
      have h := congrArg SimpleGraph.Walk.length
        (SimpleGraph.Walk.map_induce tail htailAvoid)
      rw [SimpleGraph.Walk.length_map] at h
      change
        (tail.induce {z | z ≠ rt} htailAvoid).length =
          tail.length
      exact h
    have hQBlen : QB'.length = tail.length := by
      calc
        QB'.length = QB.length := by simp [QB']
        _ = Q.length := by simp [QB]
        _ = tailI.length := rfl
        _ = tail.length := htailILen
    have hliftLen : lifted.length = QB'.length + 1 := by
      calc
        lifted.length = liftedReverse.length := by
          simp [lifted]
        _ = QB'.length + 1 := by
          simp [liftedReverse, SimplePath.length, Nat.add_comm]
    have hRlen : R.length = tail.length + 1 := by
      change R.walk.length = tail.length + 1
      rw [hwalk]
      simp
    have hRPeq : R.length = P.length := by
      simp [R]
    omega
  have hotherNeS : other ≠ s := by
    rcases hends with h | h
    · simpa [h.1, h.2] using hqr.symm
    · simpa [h.1, h.2] using hqr
  have hotherAvoid : setup.inclusion other ∉ lifted.walk.support := by
    intro hmem
    have hmem' :
        setup.inclusion other ∈ liftedReverse.walk.support := by
      simpa [lifted, SimplePath.reverse,
        SimpleGraph.Walk.support_reverse] using hmem
    simp only [liftedReverse, SimpleGraph.Walk.support_cons,
      List.mem_cons] at hmem'
    rcases hmem' with hEq | htail
    · exact hotherNeS (setup.inclusion.injective hEq)
    · exact endpoint_not_in_QB other hotherPair (by
        simpa [QB'] using htail)
  exact ⟨{
    s := s
    other := other
    endpoints := hends
    path := lifted
    length_path := hlength
    avoids_other := hotherAvoid
  }⟩

/--
Every one of the four contracted paths has two certified simple-cycle
closures after lifting.  The support arguments here are the formal
content behind the paper's phrase "closing ... in the two possible
ways": neither closure is merely a closed walk.
-/
theorem triangle_lift_cycle_grid
    (setup : StandingSetup J B c D)
    (T : TriangleConfig J)
    (paths : AdmissiblePathFamily
      (setup.triangleContractionBase T.p T.q T.r)
      (triangleContractP T.q T.r T.p)
      (triangleContractT T.q T.r) 4) :
    Nonempty (TriangleLiftCycleGrid
      (setup.triangleContractionBase T.p T.q T.r) B paths) := by
  classical
  let lift (i : Fin 4) : TrianglePathLift
      setup T.p T.q T.r (paths.path i) :=
    Classical.choice (setup.lift_triangle_contracted_path
      T.p T.q T.r T.p_ne_q T.p_ne_r T.q_ne_r (paths.path i))
  have hshortDisjoint :
      ∀ i,
        (lift i).path.walk.support.tail.Disjoint
          (triangleShortClosure setup T (lift i)).walk.support.tail := by
    intro i
    rw [List.disjoint_left]
    intro z hzLift hzClose
    have hzP : z = setup.inclusion T.p := by
      simpa [triangleShortClosure] using hzClose
    subst z
    exact (lift i).path.start_not_mem_tail hzLift
  have hlongDisjoint :
      ∀ i,
        (lift i).path.walk.support.tail.Disjoint
          (triangleLongClosure setup T (lift i)).walk.support.tail := by
    intro i
    rw [List.disjoint_left]
    intro z hzLift hzClose
    have hzEnds :
        z = setup.inclusion (lift i).other ∨
          z = setup.inclusion T.p := by
      simpa [triangleLongClosure] using hzClose
    rcases hzEnds with hzOther | hzP
    · exact (lift i).avoids_other
        (List.mem_of_mem_tail (hzOther ▸ hzLift))
    · subst z
      exact (lift i).path.start_not_mem_tail hzLift
  refine ⟨{
    short := fun i =>
      cycleOfDisjointPaths (lift i).path
        (triangleShortClosure setup T (lift i))
        (hshortDisjoint i)
        (Or.inl (by
          rw [(lift i).length_path, paths.length_path]
          exact paths.start_ge_two.trans
            (Nat.le_add_right paths.start
              (i.val * paths.step))))
    long := fun i =>
      cycleOfDisjointPaths (lift i).path
        (triangleLongClosure setup T (lift i))
        (hlongDisjoint i)
        (Or.inr (by simp))
    length_short := ?_
    length_long := ?_
  }⟩
  · intro i
    rw [cycleOfDisjointPaths_length]
    simp [(lift i).length_path]
  · intro i
    rw [cycleOfDisjointPaths_length]
    simp [(lift i).length_path]

/--
The edge-selection bookkeeping at the start of Lemma 5.2.  Two distinct
neighbours of `c` exist by the standing lower degree bound.  If contracting
`qr` merges them, they must be exactly `q,r`, so the cyclically next edge
`rp` cannot merge them.
-/
theorem triangle_contraction_preserves_two_c_neighbors
    (setup : StandingSetup J B c D)
    (T : TriangleConfig J) :
    ∃ T' : TriangleConfig J, ∃ u v : W,
      B.Adj c (setup.inclusion u) ∧
      B.Adj c (setup.inclusion v) ∧
      contractVertex T'.q T'.r u ≠
        contractVertex T'.q T'.r v := by
  have hneighborCard : 1 < (B.neighborSet c).ncard := by
    change 1 < finiteDegree B c
    exact setup.degree_c_lower
  obtain ⟨uB, huB, vB, hvB, huvB⟩ :=
    (Set.one_lt_ncard (s := B.neighborSet c)).1 hneighborCard
  have hcuB : B.Adj c uB :=
    (B.mem_neighborSet c uB).1 huB
  have hcvB : B.Adj c vB :=
    (B.mem_neighborSet c vB).1 hvB
  rcases setup.vertex_decomposition uB with huc | ⟨u, hu⟩
  · subst uB
    exact False.elim (B.loopless.irrefl c hcuB)
  rcases setup.vertex_decomposition vB with hvc | ⟨v, hv⟩
  · subst vB
    exact False.elim (B.loopless.irrefl c hcvB)
  have hcu : B.Adj c (setup.inclusion u) := by
    simpa [hu] using hcuB
  have hcv : B.Adj c (setup.inclusion v) := by
    simpa [hv] using hcvB
  have huv : u ≠ v := by
    intro huv
    apply huvB
    rw [← hu, ← hv, huv]
  by_cases hsurvive :
      contractVertex T.q T.r u ≠ contractVertex T.q T.r v
  · exact ⟨T, u, v, hcu, hcv, hsurvive⟩
  · have hmerged :
        contractVertex T.q T.r u =
          contractVertex T.q T.r v := not_ne_iff.mp hsurvive
    rcases (contractVertex_eq_iff T.q T.r u v).1 hmerged with
      huvEq | ⟨huQR, hvQR⟩
    · exact False.elim (huv huvEq)
    · let T' := T.rotate
      refine ⟨T', u, v, hcu, hcv, ?_⟩
      intro hmerged'
      have hmergedRP :
          contractVertex T.r T.p u =
            contractVertex T.r T.p v := by
        simpa [T', TriangleConfig.rotate] using hmerged'
      rcases (contractVertex_eq_iff T.r T.p u v).1 hmergedRP with
        huvEq | ⟨huRP, hvRP⟩
      · exact huv huvEq
      · have huR : u = T.r := by
          rcases huQR with huQ | huR
          · rcases huRP with huR | huP
            · exact False.elim
                (T.q_ne_r (huQ.symm.trans huR))
            · exact False.elim
                (T.p_ne_q (huP.symm.trans huQ))
          · exact huR
        have hvR : v = T.r := by
          rcases hvQR with hvQ | hvR
          · rcases hvRP with hvR | hvP
            · exact False.elim
                (T.q_ne_r (hvQ.symm.trans hvR))
            · exact False.elim
                (T.p_ne_q (hvP.symm.trans hvQ))
          · exact hvR
        exact huv (huR.trans hvR.symm)

/--
The COY output in the contracted graph, conditional on two distinct
surviving neighbours of `c`.  This contains all connectivity and degree
bookkeeping in the first half of Lemma 5.2.
-/
theorem triangle_contraction_admissible_paths
    (setup : StandingSetup J B c D)
    (T : TriangleConfig J)
    (u v : W)
    (hcu : B.Adj c (setup.inclusion u))
    (hcv : B.Adj c (setup.inclusion v))
    (huvContract :
      contractVertex T.q T.r u ≠ contractVertex T.q T.r v) :
    Nonempty (AdmissiblePathFamily
      (setup.triangleContractionBase T.p T.q T.r)
      (triangleContractP T.q T.r T.p)
      (triangleContractT T.q T.r) 4) := by
  let C := contractPair J T.q T.r
  let Zc := setup.contractedCNeighbors T.q T.r
  let H := setup.triangleContractionGraph T.q T.r
  let rp := triangleContractP T.q T.r T.p
  let rt := triangleContractT T.q T.r
  let L := setup.triangleContractionBase T.p T.q T.r
  have huZ :
      contractVertex T.q T.r u ∈ Zc :=
    (mem_contractedCNeighbors setup T.q T.r _).2
      ⟨u, rfl, hcu⟩
  have hvZ :
      contractVertex T.q T.r v ∈ Zc :=
    (mem_contractedCNeighbors setup T.q T.r _).2
      ⟨v, rfl, hcv⟩
  have hZcard : 2 ≤ Zc.card := by
    have hsub :
        ({contractVertex T.q T.r u,
          contractVertex T.q T.r v} :
          Finset (ContractPairVertex W T.q T.r)) ⊆ Zc := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact huZ
      · exact hvZ
    have hcard :=
      Finset.card_le_card hsub
    rw [Finset.card_pair_eq_two_iff.mpr huvContract] at hcard
    exact hcard
  have hCthree : IsKConnected C 3 :=
    isThreeConnected_contractPair J T.q T.r
      T.q_ne_r T.qr setup.four_connected
  have hCtwo : IsTwoConnected C := by
    constructor
    · have := hCthree.1
      omega
    · intro S hS
      exact hCthree.2 S (by omega)
  have hHtwo : IsTwoConnected H := by
    exact isTwoConnected_adjoinRoot C Zc hCtwo hZcard
  have hpContract :
      contractVertex T.q T.r T.p =
        some ⟨T.p, T.p_ne_q, T.p_ne_r⟩ := by
    simp [contractVertex, T.p_ne_q, T.p_ne_r]
  have hrootAdjC :
      C.Adj (contractVertex T.q T.r T.p) none := by
    rw [hpContract]
    exact Or.inl T.pq
  have hrootAdjH : H.Adj rp rt := by
    exact hrootAdjC
  have hroots : rp ≠ rt := by
    simp [rp, rt, triangleContractP, triangleContractT,
      hpContract]
  have hLedge : L ⊔ edge rp rt = H := by
    ext a b
    simp only [L, triangleContractionBase,
      SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
    constructor
    · rintro (⟨hab, -⟩ | hab)
      · exact hab
      · simp only [SimpleGraph.edge_adj] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hrootAdjH
        · exact hrootAdjH.symm
    · intro hab
      by_cases hedge : (edge rp rt).Adj a b
      · exact Or.inr hedge
      · exact Or.inl ⟨hab, hedge⟩
  have horder :
      4 ≤ Fintype.card (Option (ContractPairVertex W T.q T.r)) := by
    rw [Fintype.card_option]
    have := hCthree.1
    omega
  have hdeg :
      ∀ z, z ≠ rp → z ≠ rt → z ≠ none →
        4 + 1 ≤ finiteDegree L z := by
    intro z hzrp hzrt hzc
    cases z with
    | none => exact False.elim (hzc rfl)
    | some z =>
        have hzNone : z ≠ none := by
          intro hz
          exact hzrt (by simp [rt, triangleContractT, hz])
        cases z with
        | none => exact False.elim (hzNone rfl)
        | some w =>
            have hwp : w.1 ≠ T.p := by
              intro hwp
              exact hzrp (by
                apply congrArg some
                rw [hpContract]
                apply congrArg some
                apply Subtype.ext
                exact hwp)
            have hwq : w.1 ≠ T.q := w.2.1
            have hwr : w.1 ≠ T.r := w.2.2
            have hone :
                ¬(J.Adj w.1 T.q ∧ J.Adj w.1 T.r) := by
              intro hboth
              exact setup.triangle_external_vertex_at_most_one_neighbor
                T w.1 hwp hwq hwr (Or.inr (Or.inl hboth))
            have hCdegree :
                finiteDegree C (some w) = finiteDegree J w.1 := by
              simpa [C, contractVertex, hwq, hwr] using
                finiteDegree_contractPair_eq J T.q T.r w.1 hwq hwr hone
            have hLdegree :
                finiteDegree L (some (some w)) =
                  finiteDegree H (some (some w)) := by
              exact finiteDegree_sdiff_edge_of_ne H rp rt
                (some (some w)) hzrp hzrt
            rw [hLdegree, show H =
                adjoinRoot C Zc by rfl,
              finiteDegree_adjoinRoot_some, hCdegree]
            by_cases hwD : w.1 ∈ D
            · have hwZ : (some w : ContractPairVertex W T.q T.r) ∈ Zc := by
                apply (mem_contractedCNeighbors setup T.q T.r _).2
                refine ⟨w.1, ?_, setup.deficient_adjacent_to_c w.1 hwD⟩
                simp [contractVertex, hwq, hwr]
              rw [if_pos hwZ, setup.degree_deficient w.1 hwD]
            · have hwdegree := setup.degree_regular w.1 hwD
              by_cases hwZ :
                  (some w : ContractPairVertex W T.q T.r) ∈ Zc
              · rw [if_pos hwZ]
                omega
              · rw [if_neg hwZ, add_zero]
                exact hwdegree
  have result :=
    COY.one_exception_rooted_paths 4 L rp rt none
      (by omega) horder hroots (hLedge ▸ hHtwo) hdeg
  simpa [L, rp, rt] using result

/--
Lemma 5.2: the standing graph has no triangle.  All path production is
conditional only on the named COY axiom; contraction, degree preservation,
path lifting, simplicity of the two closures, and the modular contradiction
are proved internally.
-/
theorem no_triangle
    (setup : StandingSetup J B c D) :
    ¬ Nonempty (TriangleConfig J) := by
  rintro ⟨T⟩
  obtain ⟨T', u, v, hcu, hcv, huv⟩ :=
    setup.triangle_contraction_preserves_two_c_neighbors T
  obtain ⟨paths⟩ :=
    setup.triangle_contraction_admissible_paths
      T' u v hcu hcv huv
  obtain ⟨grid⟩ :=
    setup.triangle_lift_cycle_grid T' paths
  exact setup.no_divisible_cycle
    (four_paths_two_triangle_closures_force_divisible_cycle
      (setup.triangleContractionBase T'.p T'.q T'.r)
      B paths grid)

end StandingSetup

end DeanK5
