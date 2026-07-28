import DeanK5.ThetaCore

/-!
# A minimum-theta consequence for an outside two-edge chord

An outside vertex adjacent to internal points of two distinct legs of a
minimum-order theta supplies a third path between those points.  Together
with the routes through the two theta roots, this is another theta.  Its
minimality forces the unused original leg to have length at most two.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace Theta

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

private theorem getVert_eq_iff
    {a b : V} (P : SimplePath G a b) {m n : ℕ}
    (hm : m ≤ P.length) (hn : n ≤ P.length) :
    P.walk.getVert m = P.walk.getVert n ↔ m = n := by
  constructor
  · intro h
    exact P.isPath.getVert_injOn
      (by simpa [SimplePath.length] using hm)
      (by simpa [SimplePath.length] using hn) h
  · exact congrArg P.walk.getVert

private theorem mem_take_support_position
    {a b : V} (P : SimplePath G a b) (r : ℕ)
    (hr : r ≤ P.length) {z : V}
    (hz : z ∈ (P.take r).walk.support) :
    ∃ n, n ≤ r ∧ n ≤ P.length ∧
      P.walk.getVert n = z := by
  obtain ⟨n, hnEq, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hnR : n ≤ r := by
    have hnmin : n ≤ min r P.length := by
      simpa [SimplePath.take, SimplePath.length] using hnle
    exact (le_min_iff.mp hnmin).1
  refine ⟨n, hnR, hnR.trans hr, ?_⟩
  simpa [SimplePath.take,
    SimpleGraph.Walk.take_getVert,
    Nat.min_eq_right hnR] using hnEq

private theorem mem_drop_support_position
    {a b : V} (P : SimplePath G a b) (s : ℕ)
    (hs : s ≤ P.length) {z : V}
    (hz : z ∈ (P.drop s).walk.support) :
    ∃ n, s ≤ n ∧ n ≤ P.length ∧
      P.walk.getVert n = z := by
  obtain ⟨m, hmEq, hmle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hmle' : m ≤ P.length - s := by
    simpa [SimplePath.drop, SimplePath.length] using hmle
  refine ⟨s + m, by omega, by omega, ?_⟩
  simpa [SimplePath.drop,
    SimpleGraph.Walk.drop_getVert] using hmEq

/-- The two-edge route between two theta legs through an outside vertex. -/
private def viaOutside
    [DecidableEq V]
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r < (T.path i).length)
    (_hspos : 0 < s) (_hs : s < (T.path j).length)
    (v : V) (hv : v ∉ T.verts)
    (hvr : G.Adj v ((T.path i).walk.getVert r))
    (hvs : G.Adj v ((T.path j).walk.getVert s)) :
    SimplePath G ((T.path i).walk.getVert r)
      ((T.path j).walk.getVert s) := by
  let a := (T.path i).walk.getVert r
  let b := (T.path j).walk.getVert s
  have haT : a ∈ T.verts :=
    T.path_support_subset_verts_basic i a
      ((T.path i).walk.getVert_mem_support r)
  have hbT : b ∈ T.verts :=
    T.path_support_subset_verts_basic j b
      ((T.path j).walk.getVert_mem_support s)
  have hav : a ≠ v := fun h => hv (h ▸ haT)
  have hbv : b ≠ v := fun h => hv (h ▸ hbT)
  have hab : a ≠ b := by
    intro hab
    have haJ : a ∈ (T.path j).walk.support := by
      rw [hab]
      exact (T.path j).walk.getVert_mem_support s
    rcases T.eq_root_of_mem_two_paths hij
        ((T.path i).walk.getVert_mem_support r) haJ with
      hax | hay
    · have : r = 0 :=
        ((T.path i).isPath.getVert_eq_start_iff
          (by
            simpa [SimplePath.length] using hr.le)).1 hax
      omega
    · have :
          r = (T.path i).walk.length :=
        ((T.path i).isPath.getVert_eq_end_iff
          (by
            simpa [SimplePath.length] using hr.le)).1 hay
      simpa [SimplePath.length] using hr.ne this
  exact {
    walk := .cons hvr.symm (.cons hvs .nil)
    isPath := by
      simp [a, b, hav, hbv.symm, hab]
  }

@[simp] private theorem viaOutside_length
    [DecidableEq V]
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s < (T.path j).length)
    (v : V) (hv : v ∉ T.verts)
    (hvr : G.Adj v ((T.path i).walk.getVert r))
    (hvs : G.Adj v ((T.path j).walk.getVert s)) :
    (viaOutside T hij r s hrpos hr hspos hs
      v hv hvr hvs).length = 2 := by
  simp [viaOutside, SimplePath.length]

/-- Reverse all three legs and interchange the roots of a theta. -/
private def reverseRoots (T : Theta G) : Theta G where
  x := T.y
  y := T.x
  roots_ne := T.roots_ne.symm
  path i := (T.path i).reverse
  paths_ne := by
    intro i j hij h
    exact T.paths_ne i j hij
      (SimpleGraph.Walk.reverse_injective h)
  internal_disjoint := by
    intro i j hij
    apply List.disjoint_left.mpr
    intro z hzi hzj
    have hziData :=
      internal_support_data
        (T.path i).reverse T.roots_ne.symm hzi
    have hzjData :=
      internal_support_data
        (T.path j).reverse T.roots_ne.symm hzj
    have hziSupport :
        z ∈ (T.path i).walk.support := by
      simpa [SimplePath.reverse,
        SimpleGraph.Walk.support_reverse] using hziData.1
    have hzjSupport :
        z ∈ (T.path j).walk.support := by
      simpa [SimplePath.reverse,
        SimpleGraph.Walk.support_reverse] using hzjData.1
    have hziInternal :
        z ∈ (T.path i).internalSupport :=
      (T.path i).mem_internalSupport_of_mem_support
        hziSupport hziData.2.2 hziData.2.1
    have hzjInternal :
        z ∈ (T.path j).internalSupport :=
      (T.path j).mem_internalSupport_of_mem_support
        hzjSupport hzjData.2.2 hzjData.2.1
    exact (List.disjoint_left.mp
      (T.internal_disjoint i j hij) hziInternal) hzjInternal

@[simp] private theorem reverseRoots_path_length
    (T : Theta G) (i : Fin 3) :
    ((reverseRoots T).path i).length =
      (T.path i).length := by
  simp [reverseRoots]

@[simp] private theorem reverseRoots_verts
    [DecidableEq V] (T : Theta G) :
    (reverseRoots T).verts = T.verts := by
  simp [reverseRoots, Theta.verts, SimplePath.reverse,
    SimpleGraph.Walk.support_reverse]

private theorem reverseRoots_minimumOrder
    [DecidableEq V] (T : Theta G)
    (hminimum : T.IsMinimumOrder) :
    (reverseRoots T).IsMinimumOrder := by
  intro U
  simpa using hminimum U

private theorem reverseRoots_getVert_sub
    (T : Theta G) (i : Fin 3) (r : ℕ)
    (hr : r ≤ (T.path i).length) :
    ((reverseRoots T).path i).walk.getVert
        ((T.path i).length - r) =
      (T.path i).walk.getVert r := by
  simp only [reverseRoots, SimplePath.reverse,
    SimpleGraph.Walk.getVert_reverse]
  have hrWalk : r ≤ (T.path i).walk.length := by
    simpa [SimplePath.length] using hr
  change
    (T.path i).walk.getVert
        ((T.path i).walk.length -
          ((T.path i).walk.length - r)) =
      (T.path i).walk.getVert r
  rw [Nat.sub_sub_self hrWalk]

/--
Minimality forbids a comparison theta, contained in the old theta plus one
outside vertex, from omitting two distinct old vertices.
-/
private theorem minimumOrder_no_two_omitted
    [DecidableEq V]
    (T : Theta G) (hminimum : T.IsMinimumOrder)
    (v : V) (hv : v ∉ T.verts)
    (U : Theta G)
    (hsubset : U.verts ⊆ insert v T.verts)
    {q₁ q₂ : V} (hqne : q₁ ≠ q₂)
    (hq₁T : q₁ ∈ T.verts) (hq₂T : q₂ ∈ T.verts)
    (hq₁NotU : q₁ ∉ U.verts) (hq₂NotU : q₂ ∉ U.verts) :
    False := by
  have hq₁NotInsert :
      q₁ ∉ insert q₂ U.verts := by
    simp [hqne, hq₁NotU]
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

private def outsideCrossTail
    (T : Theta G) (j : Fin 3) (s : ℕ) :
    SimplePath G T.y ((T.path j).walk.getVert s) :=
  ((T.path j).drop s).reverse

private def outsideCrossViaThird
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

private def outsideCrossViaOutside
    [DecidableEq V]
    (T : Theta G) (i j : Fin 3) (hij : i ≠ j)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s < (T.path j).length)
    (v : V) (hv : v ∉ T.verts)
    (hvr : G.Adj v ((T.path i).walk.getVert r))
    (hvs : G.Adj v ((T.path j).walk.getVert s)) :
    SimplePath G T.y ((T.path j).walk.getVert s) :=
  ((T.path i).drop r).reverse.appendDisjoint
    (viaOutside T hij r s hrpos hr hspos hs
      v hv hvr hvs) (by
      apply List.disjoint_left.mpr
      intro z hzI hzOutside
      have hzDrop :
          z ∈ ((T.path i).drop r).walk.support := by
        simpa [SimplePath.reverse] using hzI
      have hzI' :
          z ∈ (T.path i).walk.support :=
        (T.path i).mem_support_of_mem_drop r hzDrop
      have hzCases :
          z = v ∨
            z = (T.path j).walk.getVert s := by
        simpa [viaOutside] using hzOutside
      rcases hzCases with hzv | hzb
      · apply hv
        rw [← hzv]
        exact T.path_support_subset_verts_basic i z hzI'
      · have hzJ' :
            z ∈ (T.path j).walk.support := by
          rw [hzb]
          exact (T.path j).walk.getVert_mem_support s
        rcases T.eq_root_of_mem_two_paths hij
            hzI' hzJ' with hzx | hzy
        · have :
              s = 0 :=
            ((T.path j).isPath.getVert_eq_start_iff
              (by
                simpa [SimplePath.length] using hs.le)).1 (by
              exact hzb.symm.trans hzx)
          omega
        · have :
              s = (T.path j).walk.length :=
            ((T.path j).isPath.getVert_eq_end_iff
              (by
                simpa [SimplePath.length] using hs.le)).1 (by
              exact hzb.symm.trans hzy)
          simpa [SimplePath.length] using hs.ne this)

/--
The initial segment from the first root to an outside attachment point has
length at most two in a minimum-order theta.
-/
private theorem minimumOrder_prefix_length_le_two_of_outside_chord
    [DecidableEq V]
    (T : Theta G)
    (hminimum : T.IsMinimumOrder)
    (v : V) (hv : v ∉ T.verts)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s < (T.path j).length)
    (hvr : G.Adj v ((T.path i).walk.getVert r))
    (hvs : G.Adj v ((T.path j).walk.getVert s)) :
    r ≤ 2 := by
  by_contra hrBound
  have hrlarge : 3 ≤ r := by omega
  let b := (T.path j).walk.getVert s
  let A := outsideCrossTail T j s
  let B := outsideCrossViaThird T j k
    (fun h => hjk h.symm) s hs
  let C := outsideCrossViaOutside T i j hij
    r s hrpos hr hspos hs v hv hvr hvs
  have hyb : T.y ≠ b := by
    intro h
    have :
        s = (T.path j).walk.length :=
      ((T.path j).isPath.getVert_eq_end_iff
        (by
          simpa [SimplePath.length] using hs.le)).1 h.symm
    simpa [SimplePath.length] using hs.ne this
  have hA_support :
      ∀ z ∈ A.walk.support,
        z ∈ (T.path j).walk.support := by
    intro z hz
    have hzDrop :
        z ∈ ((T.path j).drop s).walk.support := by
      simpa [A, outsideCrossTail,
        SimplePath.reverse] using hz
    exact (T.path j).mem_support_of_mem_drop s hzDrop
  have hA_drop :
      ∀ z ∈ A.walk.support,
        z ∈ ((T.path j).drop s).walk.support := by
    intro z hz
    simpa [A, outsideCrossTail,
      SimplePath.reverse] using hz
  have hB_support :
      ∀ z ∈ B.walk.support,
        z ∈ (T.path k).walk.support ∨
          z ∈ ((T.path j).take s).walk.support := by
    intro z hz
    simp only [B, outsideCrossViaThird,
      SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzK | hzJ
    · exact Or.inl (by
        simpa [SimplePath.reverse] using hzK)
    · exact Or.inr (List.mem_of_mem_tail hzJ)
  have hC_support :
      ∀ z ∈ C.walk.support,
        z ∈ ((T.path i).drop r).walk.support ∨
          z = v ∨ z = b := by
    intro z hz
    simp only [C, outsideCrossViaOutside,
      SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzI | hzOutside
    · exact Or.inl (by
        simpa [SimplePath.reverse] using hzI)
    · have hzCases :
          z = v ∨
            z = (T.path j).walk.getVert s := by
        simpa [viaOutside] using hzOutside
      exact Or.inr (by simpa [b] using hzCases)
  have hxA : T.x ∉ A.walk.support := by
    intro hx
    exact (T.path j).start_not_mem_drop
      hspos hs.le (hA_drop T.x hx)
  have hxB : T.x ∈ B.walk.support := by
    simp only [B, outsideCrossViaThird,
      SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append]
    apply List.mem_append_left
    simp [SimplePath.reverse]
  have hvA : v ∉ A.walk.support := by
    intro hvA
    exact hv (T.path_support_subset_verts_basic j v
      (hA_support v hvA))
  have hvB : v ∉ B.walk.support := by
    intro hvB
    rcases hB_support v hvB with hvK | hvJ
    · exact hv (T.path_support_subset_verts_basic k v hvK)
    · exact hv (T.path_support_subset_verts_basic j v
        ((T.path j).mem_support_of_mem_take s hvJ))
  have hvC : v ∈ C.walk.support := by
    simp [C, outsideCrossViaOutside, viaOutside,
      SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append]
  have hABne : A.walk ≠ B.walk := by
    intro h
    exact hxA (h ▸ hxB)
  have hACne : A.walk ≠ C.walk := by
    intro h
    exact hvA (h ▸ hvC)
  have hBCne : B.walk ≠ C.walk := by
    intro h
    exact hvB (h ▸ hvC)
  have hABdisjoint :
      A.internalSupport.Disjoint B.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzA hzB
    have hzAData := internal_support_data A hyb hzA
    have hzBData := internal_support_data B hyb hzB
    have hzADrop := hA_drop z hzAData.1
    have hzAJ := hA_support z hzAData.1
    rcases hB_support z hzBData.1 with hzK | hzJTake
    · rcases T.eq_root_of_mem_two_paths
          (fun h => hjk h.symm) hzK hzAJ with hzx | hzy
      · exact hxA (hzx ▸ hzAData.1)
      · exact hzAData.2.1 hzy
    · obtain ⟨n, hsN, hnLength, hnEq⟩ :=
        mem_drop_support_position (T.path j) s hs.le hzADrop
      obtain ⟨m, hmS, hmLength, hmEq⟩ :=
        mem_take_support_position (T.path j) s hs.le hzJTake
      have hnm :
          n = m :=
        (getVert_eq_iff (T.path j) hnLength hmLength).1
          (hnEq.trans hmEq.symm)
      have hzEq : z = b := by
        rw [← hnEq]
        congr 1
        omega
      exact hzAData.2.2 hzEq
  have hACdisjoint :
      A.internalSupport.Disjoint C.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzA hzC
    have hzAData := internal_support_data A hyb hzA
    have hzCData := internal_support_data C hyb hzC
    have hzAJ := hA_support z hzAData.1
    rcases hC_support z hzCData.1 with hzIDrop | hzv | hzb
    · have hzI :
          z ∈ (T.path i).walk.support :=
        (T.path i).mem_support_of_mem_drop r hzIDrop
      rcases T.eq_root_of_mem_two_paths hij.symm
          hzAJ hzI with hzx | hzy
      · exact (T.path i).start_not_mem_drop
          hrpos hr.le (hzx ▸ hzIDrop)
      · exact hzAData.2.1 hzy
    · apply hv
      rw [← hzv]
      exact T.path_support_subset_verts_basic j z hzAJ
    · exact hzAData.2.2 hzb
  have hBCdisjoint :
      B.internalSupport.Disjoint C.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzB hzC
    have hzBData := internal_support_data B hyb hzB
    have hzCData := internal_support_data C hyb hzC
    rcases hC_support z hzCData.1 with hzIDrop | hzv | hzb
    · have hzI :
          z ∈ (T.path i).walk.support :=
        (T.path i).mem_support_of_mem_drop r hzIDrop
      rcases hB_support z hzBData.1 with hzK | hzJTake
      · rcases T.eq_root_of_mem_two_paths
            (fun h => hik h.symm) hzK hzI with hzx | hzy
        · exact (T.path i).start_not_mem_drop
            hrpos hr.le (hzx ▸ hzIDrop)
        · exact hzBData.2.1 hzy
      · have hzJ :
            z ∈ (T.path j).walk.support :=
          (T.path j).mem_support_of_mem_take s hzJTake
        rcases T.eq_root_of_mem_two_paths hij.symm
            hzJ hzI with hzx | hzy
        · exact (T.path i).start_not_mem_drop
            hrpos hr.le (hzx ▸ hzIDrop)
        · exact (T.path j).end_not_mem_take
            hs (hzy ▸ hzJTake)
    · apply hv
      rw [← hzv]
      rcases hB_support z hzBData.1 with hzK | hzJ
      · exact T.path_support_subset_verts_basic k z hzK
      · exact T.path_support_subset_verts_basic j z
          ((T.path j).mem_support_of_mem_take s hzJ)
    · exact hzBData.2.2 hzb
  let U : Theta G := {
    x := T.y
    y := b
    roots_ne := hyb
    path := ![A, B, C]
    paths_ne := by
      intro p q hpq
      have hBAne : B.walk ≠ A.walk := Ne.symm hABne
      have hCAne : C.walk ≠ A.walk := Ne.symm hACne
      have hCBne : C.walk ≠ B.walk := Ne.symm hBCne
      fin_cases p <;> fin_cases q <;> simp_all
    internal_disjoint := by
      intro p q hpq
      fin_cases p <;> fin_cases q <;>
        simp_all [List.Disjoint.symm]
  }
  have hsubset :
      U.verts ⊆ insert v T.verts := by
    intro z hzU
    simp only [Theta.verts, Finset.mem_biUnion] at hzU
    obtain ⟨p, -, hp⟩ := hzU
    fin_cases p
    · exact Finset.mem_insert_of_mem
        (T.path_support_subset_verts_basic j z
          (hA_support z (by simpa [U] using hp)))
    · rcases hB_support z (by simpa [U] using hp) with
        hzK | hzJ
      · exact Finset.mem_insert_of_mem
          (T.path_support_subset_verts_basic k z hzK)
      · exact Finset.mem_insert_of_mem
          (T.path_support_subset_verts_basic j z
            ((T.path j).mem_support_of_mem_take s hzJ))
    · rcases hC_support z (by simpa [U] using hp) with
        hzI | rfl | hzb
      · exact Finset.mem_insert_of_mem
          (T.path_support_subset_verts_basic i z
            ((T.path i).mem_support_of_mem_drop r hzI))
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (T.path_support_subset_verts_basic j z
            (hzb ▸ (T.path j).walk.getVert_mem_support s))
  have omitted_data :
      ∀ n : ℕ, 0 < n → n < r →
        let q := (T.path i).walk.getVert n
        q ∈ T.verts ∧ q ∉ U.verts := by
    intro n hnpos hnlt
    let q := (T.path i).walk.getVert n
    have hnLength : n < (T.path i).length :=
      hnlt.trans hr
    have hqSupport :
        q ∈ (T.path i).walk.support :=
      (T.path i).walk.getVert_mem_support n
    have hqInternal :
        q ∈ (T.path i).internalSupport :=
      (T.path i).mem_internalSupport_of_mem_support
        hqSupport
        (by
          intro h
          have : n = 0 :=
            ((T.path i).isPath.getVert_eq_start_iff
              (by
                simpa [SimplePath.length] using hnLength.le)).1 h
          omega)
        (by
          intro h
          have :
              n = (T.path i).walk.length :=
            ((T.path i).isPath.getVert_eq_end_iff
              (by
                simpa [SimplePath.length] using hnLength.le)).1 h
          simpa [SimplePath.length] using hnLength.ne this)
    have hqData :=
      internal_support_data (T.path i) T.roots_ne hqInternal
    have hqT :
        q ∈ T.verts :=
      T.path_support_subset_verts_basic i q hqSupport
    refine ⟨hqT, ?_⟩
    intro hqU
    simp only [Theta.verts, Finset.mem_biUnion] at hqU
    obtain ⟨p, -, hp⟩ := hqU
    fin_cases p
    · have hqJ :=
        hA_support q (by simpa [U] using hp)
      rcases T.eq_root_of_mem_two_paths hij
          hqSupport hqJ with hqx | hqy
      · exact hqData.2.1 hqx
      · exact hqData.2.2 hqy
    · rcases hB_support q (by simpa [U] using hp) with
        hqK | hqJTake
      · rcases T.eq_root_of_mem_two_paths hik
            hqSupport hqK with hqx | hqy
        · exact hqData.2.1 hqx
        · exact hqData.2.2 hqy
      · have hqJ :
            q ∈ (T.path j).walk.support :=
          (T.path j).mem_support_of_mem_take s hqJTake
        rcases T.eq_root_of_mem_two_paths hij
            hqSupport hqJ with hqx | hqy
        · exact hqData.2.1 hqx
        · exact hqData.2.2 hqy
    · rcases hC_support q (by simpa [U] using hp) with
        hqIDrop | hqv | hqb
      · obtain ⟨m, hrM, hmLength, hmEq⟩ :=
          mem_drop_support_position (T.path i) r hr.le hqIDrop
        have hnm :
            n = m :=
          (getVert_eq_iff (T.path i)
            hnLength.le hmLength).1 hmEq.symm
        omega
      · exact hv (hqv ▸ hqT)
      · have hqJ :
            q ∈ (T.path j).walk.support := by
          rw [hqb]
          exact (T.path j).walk.getVert_mem_support s
        rcases T.eq_root_of_mem_two_paths hij
            hqSupport hqJ with hqx | hqy
        · exact hqData.2.1 hqx
        · exact hqData.2.2 hqy
  let q₁ := (T.path i).walk.getVert 1
  let q₂ := (T.path i).walk.getVert 2
  have hq₁Data :=
    omitted_data 1 (by omega) (by omega)
  have hq₂Data :=
    omitted_data 2 (by omega) (by omega)
  have hqne : q₁ ≠ q₂ := by
    intro h
    have :
        (1 : ℕ) = 2 :=
      (getVert_eq_iff (T.path i)
        (by omega) (by omega)).1 h
    omega
  exact minimumOrder_no_two_omitted
    T hminimum v hv U hsubset hqne
    hq₁Data.1 hq₂Data.1 hq₁Data.2 hq₂Data.2

/--
If an outside vertex joins internal points of two distinct legs of a
minimum-order theta, then the unused third leg has length at most two.
-/
theorem minimumOrder_thirdLeg_length_le_two_of_outside_chord
    [DecidableEq V]
    (T : Theta G)
    (hminimum : T.IsMinimumOrder)
    (v : V) (hv : v ∉ T.verts)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s < (T.path j).length)
    (hvr : G.Adj v ((T.path i).walk.getVert r))
    (hvs : G.Adj v ((T.path j).walk.getVert s)) :
    (T.path k).length ≤ 2 := by
  let a := (T.path i).walk.getVert r
  let b := (T.path j).walk.getVert s
  let A := T.viaFirstRoot hij r s hr
  let B := T.viaEnd hij r s hrpos hr.le
  let C :=
    viaOutside T hij r s hrpos hr hspos hs
      v hv hvr hvs
  have hab : a ≠ b := by
    intro hab
    have haJ : a ∈ (T.path j).walk.support := by
      have hab' :
          (T.path i).walk.getVert r =
            (T.path j).walk.getVert s := by
        simpa [a, b] using hab
      dsimp [a]
      rw [hab']
      exact (T.path j).walk.getVert_mem_support s
    rcases T.eq_root_of_mem_two_paths hij
        ((T.path i).walk.getVert_mem_support r) haJ with
      hax | hay
    · have : r = 0 :=
        ((T.path i).isPath.getVert_eq_start_iff
          (by
            simpa [SimplePath.length] using hr.le)).1 hax
      omega
    · have :
          r = (T.path i).walk.length :=
        ((T.path i).isPath.getVert_eq_end_iff
          (by
            simpa [SimplePath.length] using hr.le)).1 hay
      simpa [SimplePath.length] using hr.ne this
  have hA_parts :
      ∀ z ∈ A.walk.support,
        z ∈ ((T.path i).take r).walk.support ∨
          z ∈ ((T.path j).take s).walk.support := by
    intro z hz
    simp only [A, viaFirstRoot,
      SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzI | hzJ
    · exact Or.inl (by
        simpa [SimplePath.reverse] using hzI)
    · exact Or.inr (List.mem_of_mem_tail hzJ)
  have hB_parts :
      ∀ z ∈ B.walk.support,
        z ∈ ((T.path i).drop r).walk.support ∨
          z ∈ ((T.path j).drop s).walk.support := by
    intro z hz
    simp only [B, viaEnd,
      SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzI | hzJ
    · exact Or.inl hzI
    · exact Or.inr (by
        simpa [SimplePath.reverse] using
          List.mem_of_mem_tail hzJ)
  have hA_sources :
      ∀ z ∈ A.walk.support,
        z ∈ (T.path i).walk.support ∨
          z ∈ (T.path j).walk.support := by
    intro z hz
    rcases hA_parts z hz with hzI | hzJ
    · exact Or.inl
        ((T.path i).mem_support_of_mem_take r hzI)
    · exact Or.inr
        ((T.path j).mem_support_of_mem_take s hzJ)
  have hB_sources :
      ∀ z ∈ B.walk.support,
        z ∈ (T.path i).walk.support ∨
          z ∈ (T.path j).walk.support := by
    intro z hz
    rcases hB_parts z hz with hzI | hzJ
    · exact Or.inl
        ((T.path i).mem_support_of_mem_drop r hzI)
    · exact Or.inr
        ((T.path j).mem_support_of_mem_drop s hzJ)
  have hA_T :
      ∀ z ∈ A.walk.support, z ∈ T.verts := by
    intro z hz
    rcases hA_sources z hz with hzI | hzJ
    · exact T.path_support_subset_verts_basic i z hzI
    · exact T.path_support_subset_verts_basic j z hzJ
  have hB_T :
      ∀ z ∈ B.walk.support, z ∈ T.verts := by
    intro z hz
    rcases hB_sources z hz with hzI | hzJ
    · exact T.path_support_subset_verts_basic i z hzI
    · exact T.path_support_subset_verts_basic j z hzJ
  have hxA : T.x ∈ A.walk.support := by
    simp only [A, viaFirstRoot,
      SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append]
    apply List.mem_append_left
    simp [SimplePath.reverse]
  have hxB : T.x ∉ B.walk.support := by
    intro hx
    rcases hB_parts T.x hx with hxI | hxJ
    · exact (T.path i).start_not_mem_drop
        hrpos hr.le hxI
    · exact (T.path j).start_not_mem_drop
        hspos hs.le hxJ
  have hvC : v ∈ C.walk.support := by
    simp [C, viaOutside]
  have hvA : v ∉ A.walk.support :=
    fun hvA => hv (hA_T v hvA)
  have hvB : v ∉ B.walk.support :=
    fun hvB => hv (hB_T v hvB)
  have hABne : A.walk ≠ B.walk := by
    intro h
    exact hxB (h ▸ hxA)
  have hACne : A.walk ≠ C.walk := by
    intro h
    exact hvA (h ▸ hvC)
  have hBCne : B.walk ≠ C.walk := by
    intro h
    exact hvB (h ▸ hvC)
  have hABdisjoint :
      A.internalSupport.Disjoint B.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzA hzB
    have hzAData := internal_support_data A hab hzA
    have hzBData := internal_support_data B hab hzB
    rcases hA_parts z hzAData.1 with hzAITake | hzAJTake <;>
      rcases hB_parts z hzBData.1 with hzBIDrop | hzBJDrop
    ·
      obtain ⟨m, hmR, hmLength, hmEq⟩ :=
        mem_take_support_position (T.path i) r hr.le hzAITake
      obtain ⟨n, hrN, hnLength, hnEq⟩ :=
        mem_drop_support_position (T.path i) r hr.le hzBIDrop
      have hmn :
          m = n :=
        (getVert_eq_iff (T.path i) hmLength hnLength).1
          (hmEq.trans hnEq.symm)
      have hzEq : z = a := by
        rw [← hmEq]
        congr 1
        omega
      exact hzAData.2.1 hzEq
    ·
      have hzAI :=
        (T.path i).mem_support_of_mem_take r hzAITake
      have hzBJ :=
        (T.path j).mem_support_of_mem_drop s hzBJDrop
      rcases T.eq_root_of_mem_two_paths hij hzAI hzBJ with
        hzx | hzy
      · exact (T.path j).start_not_mem_drop
          hspos hs.le (hzx ▸ hzBJDrop)
      · exact (T.path i).end_not_mem_take hr
          (hzy ▸ hzAITake)
    ·
      have hzAJ :=
        (T.path j).mem_support_of_mem_take s hzAJTake
      have hzBI :=
        (T.path i).mem_support_of_mem_drop r hzBIDrop
      rcases T.eq_root_of_mem_two_paths hij.symm hzAJ hzBI with
        hzx | hzy
      · exact (T.path i).start_not_mem_drop
          hrpos hr.le (hzx ▸ hzBIDrop)
      · exact (T.path j).end_not_mem_take hs
          (hzy ▸ hzAJTake)
    ·
      obtain ⟨m, hmS, hmLength, hmEq⟩ :=
        mem_take_support_position (T.path j) s hs.le hzAJTake
      obtain ⟨n, hsN, hnLength, hnEq⟩ :=
        mem_drop_support_position (T.path j) s hs.le hzBJDrop
      have hmn :
          m = n :=
        (getVert_eq_iff (T.path j) hmLength hnLength).1
          (hmEq.trans hnEq.symm)
      have hzEq : z = b := by
        rw [← hmEq]
        congr 1
        omega
      exact hzAData.2.2 hzEq
  have hACdisjoint :
      A.internalSupport.Disjoint C.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzA hzC
    have hzASupport :=
      (internal_support_data A hab hzA).1
    have hzCeq : z = v := by
      simpa [C, viaOutside, SimplePath.internalSupport] using hzC
    subst z
    exact hv (hA_T v hzASupport)
  have hBCdisjoint :
      B.internalSupport.Disjoint C.internalSupport := by
    apply List.disjoint_left.mpr
    intro z hzB hzC
    have hzBSupport :=
      (internal_support_data B hab hzB).1
    have hzCeq : z = v := by
      simpa [C, viaOutside, SimplePath.internalSupport] using hzC
    subst z
    exact hv (hB_T v hzBSupport)
  let U : Theta G := {
    x := a
    y := b
    roots_ne := hab
    path := ![A, B, C]
    paths_ne := by
      intro p q hpq
      have hBAne : B.walk ≠ A.walk := Ne.symm hABne
      have hCAne : C.walk ≠ A.walk := Ne.symm hACne
      have hCBne : C.walk ≠ B.walk := Ne.symm hBCne
      fin_cases p <;> fin_cases q <;>
        simp_all
    internal_disjoint := by
      intro p q hpq
      fin_cases p <;> fin_cases q <;>
        simp_all [List.Disjoint.symm]
  }
  have hC_support :
      ∀ z ∈ C.walk.support,
        z = a ∨ z = v ∨ z = b := by
    intro z hz
    simpa [C, viaOutside, a, b] using hz
  have hsubset :
      U.verts ⊆ insert v T.verts := by
    intro z hzU
    simp only [Theta.verts, Finset.mem_biUnion] at hzU
    obtain ⟨p, -, hp⟩ := hzU
    fin_cases p
    · exact Finset.mem_insert_of_mem
        (hA_T z (by simpa [U] using hp))
    · exact Finset.mem_insert_of_mem
        (hB_T z (by simpa [U] using hp))
    · rcases hC_support z (by simpa [U] using hp) with
        rfl | rfl | rfl
      · exact Finset.mem_insert_of_mem
          (T.path_support_subset_verts_basic i a
            (by simp [a]))
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (T.path_support_subset_verts_basic j b
            (by simp [b]))
  by_contra hkLength
  have hklarge : 3 ≤ (T.path k).length := by omega
  let q₁ := (T.path k).walk.getVert 1
  let q₂ := (T.path k).walk.getVert 2
  have hq₁Support :
      q₁ ∈ (T.path k).walk.support :=
    (T.path k).walk.getVert_mem_support 1
  have hq₂Support :
      q₂ ∈ (T.path k).walk.support :=
    (T.path k).walk.getVert_mem_support 2
  have hq₁Internal :
      q₁ ∈ (T.path k).internalSupport :=
    (T.path k).mem_internalSupport_of_mem_support
      hq₁Support
      (by
        intro h
        have :
            (1 : ℕ) = 0 :=
          ((T.path k).isPath.getVert_eq_start_iff
            (by
              change 3 ≤ (T.path k).walk.length at hklarge
              omega)).1 h
        omega)
      (by
        intro h
        have :
            (1 : ℕ) = (T.path k).walk.length :=
          ((T.path k).isPath.getVert_eq_end_iff
            (by
              change 3 ≤ (T.path k).walk.length at hklarge
              omega)).1 h
        change 3 ≤ (T.path k).walk.length at hklarge
        omega)
  have hq₂Internal :
      q₂ ∈ (T.path k).internalSupport :=
    (T.path k).mem_internalSupport_of_mem_support
      hq₂Support
      (by
        intro h
        have :
            (2 : ℕ) = 0 :=
          ((T.path k).isPath.getVert_eq_start_iff
            (by
              change 3 ≤ (T.path k).walk.length at hklarge
              omega)).1 h
        omega)
      (by
        intro h
        have :
            (2 : ℕ) = (T.path k).walk.length :=
          ((T.path k).isPath.getVert_eq_end_iff
            (by
              change 3 ≤ (T.path k).walk.length at hklarge
              omega)).1 h
        change 3 ≤ (T.path k).walk.length at hklarge
        omega)
  have hq₁T : q₁ ∈ T.verts :=
    T.path_support_subset_verts_basic k q₁ hq₁Support
  have hq₂T : q₂ ∈ T.verts :=
    T.path_support_subset_verts_basic k q₂ hq₂Support
  have q_not_old_paths :
      ∀ {q : V},
        q ∈ (T.path k).internalSupport →
        q ∉ A.walk.support ∧ q ∉ B.walk.support := by
    intro q hq
    have hqData := internal_support_data
      (T.path k) T.roots_ne hq
    constructor
    · intro hqA
      rcases hA_sources q hqA with hqi | hqj
      · rcases T.eq_root_of_mem_two_paths
            (fun h => hik h.symm) hqData.1 hqi with
          hqx | hqy
        · exact hqData.2.1 hqx
        · exact hqData.2.2 hqy
      · rcases T.eq_root_of_mem_two_paths
            (fun h => hjk h.symm) hqData.1 hqj with
          hqx | hqy
        · exact hqData.2.1 hqx
        · exact hqData.2.2 hqy
    · intro hqB
      rcases hB_sources q hqB with hqi | hqj
      · rcases T.eq_root_of_mem_two_paths
            (fun h => hik h.symm) hqData.1 hqi with
          hqx | hqy
        · exact hqData.2.1 hqx
        · exact hqData.2.2 hqy
      · rcases T.eq_root_of_mem_two_paths
            (fun h => hjk h.symm) hqData.1 hqj with
          hqx | hqy
        · exact hqData.2.1 hqx
        · exact hqData.2.2 hqy
  have q_not_C :
      ∀ {q : V},
        q ∈ (T.path k).internalSupport →
        q ∉ C.walk.support := by
    intro q hq hqC
    have hqData := internal_support_data
      (T.path k) T.roots_ne hq
    rcases hC_support q hqC with hqa | hqv | hqb
    · have haI :
          a ∈ (T.path i).walk.support :=
        (T.path i).walk.getVert_mem_support r
      rcases T.eq_root_of_mem_two_paths
          (fun h => hik h.symm) hqData.1 (hqa ▸ haI) with
        hqx | hqy
      · exact hqData.2.1 hqx
      · exact hqData.2.2 hqy
    · subst q
      exact hv (T.path_support_subset_verts_basic k v hqData.1)
    · have hbJ :
          b ∈ (T.path j).walk.support :=
        (T.path j).walk.getVert_mem_support s
      rcases T.eq_root_of_mem_two_paths
          (fun h => hjk h.symm) hqData.1 (hqb ▸ hbJ) with
        hqx | hqy
      · exact hqData.2.1 hqx
      · exact hqData.2.2 hqy
  have hq₁NotU : q₁ ∉ U.verts := by
    intro hqU
    simp only [Theta.verts, Finset.mem_biUnion] at hqU
    obtain ⟨p, -, hp⟩ := hqU
    fin_cases p
    · exact (q_not_old_paths hq₁Internal).1
        (by simpa [U] using hp)
    · exact (q_not_old_paths hq₁Internal).2
        (by simpa [U] using hp)
    · exact q_not_C hq₁Internal
        (by simpa [U] using hp)
  have hq₂NotU : q₂ ∉ U.verts := by
    intro hqU
    simp only [Theta.verts, Finset.mem_biUnion] at hqU
    obtain ⟨p, -, hp⟩ := hqU
    fin_cases p
    · exact (q_not_old_paths hq₂Internal).1
        (by simpa [U] using hp)
    · exact (q_not_old_paths hq₂Internal).2
        (by simpa [U] using hp)
    · exact q_not_C hq₂Internal
        (by simpa [U] using hp)
  have hq₁q₂ : q₁ ≠ q₂ := by
    intro h
    have :
        (1 : ℕ) = 2 :=
      (getVert_eq_iff (T.path k)
        (by omega) (by omega)).1 h
    omega
  have hq₁NotInsert :
      q₁ ∉ insert q₂ U.verts := by
    simp [hq₁q₂, hq₁NotU]
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

/--
All four theta segments cut out by two cross-leg outside attachments have
length at most two.  The first two bounds use comparison thetas directly;
the terminal bounds are the same argument after reversing all three legs.
-/
theorem minimumOrder_outside_chord_segment_bounds
    [DecidableEq V]
    (T : Theta G)
    (hminimum : T.IsMinimumOrder)
    (v : V) (hv : v ∉ T.verts)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s < (T.path j).length)
    (hvr : G.Adj v ((T.path i).walk.getVert r))
    (hvs : G.Adj v ((T.path j).walk.getVert s)) :
    r ≤ 2 ∧
      s ≤ 2 ∧
      (T.path i).length - r ≤ 2 ∧
      (T.path j).length - s ≤ 2 := by
  have hrBound :=
    minimumOrder_prefix_length_le_two_of_outside_chord
      T hminimum v hv hij hik hjk
      r s hrpos hr hspos hs hvr hvs
  have hsBound :=
    minimumOrder_prefix_length_le_two_of_outside_chord
      T hminimum v hv hij.symm hjk hik
      s r hspos hs hrpos hr hvs hvr
  let R := reverseRoots T
  let r' := (T.path i).length - r
  let s' := (T.path j).length - s
  have hRminimum : R.IsMinimumOrder := by
    simpa [R] using reverseRoots_minimumOrder T hminimum
  have hvR : v ∉ R.verts := by
    simpa [R] using hv
  have hr'pos : 0 < r' := by
    simp only [r']
    exact Nat.sub_pos_of_lt hr
  have hs'pos : 0 < s' := by
    simp only [s']
    exact Nat.sub_pos_of_lt hs
  have hr'lt : r' < (R.path i).length := by
    simp only [r', R, reverseRoots_path_length]
    omega
  have hs'lt : s' < (R.path j).length := by
    simp only [s', R, reverseRoots_path_length]
    omega
  have hvrR :
      G.Adj v ((R.path i).walk.getVert r') := by
    rw [show
      (R.path i).walk.getVert r' =
        (T.path i).walk.getVert r by
      simpa [R, r'] using
        reverseRoots_getVert_sub T i r hr.le]
    exact hvr
  have hvsR :
      G.Adj v ((R.path j).walk.getVert s') := by
    rw [show
      (R.path j).walk.getVert s' =
        (T.path j).walk.getVert s by
      simpa [R, s'] using
        reverseRoots_getVert_sub T j s hs.le]
    exact hvs
  have hr'Tail :=
    minimumOrder_prefix_length_le_two_of_outside_chord
      R hRminimum v hvR hij hik hjk
      r' s' hr'pos hr'lt hs'pos hs'lt hvrR hvsR
  have hs'Tail :=
    minimumOrder_prefix_length_le_two_of_outside_chord
      R hRminimum v hvR hij.symm hjk hik
      s' r' hs'pos hs'lt hr'pos hr'lt hvsR hvrR
  exact ⟨hrBound, hsBound, hr'Tail, hs'Tail⟩

end Theta

end DeanK5
