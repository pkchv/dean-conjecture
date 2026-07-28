import DeanK5.Graph.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.EquivFin

/-!
# Paths in complete bipartite cores

This module proves internally the elementary alternating-path input used in
the four-cycle argument.
-/

open Function

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace BipartitePaths

private theorem range_tail_subset
    {n : ℕ} {α : Type*} (e : Fin (n + 1) ↪ α) :
    Set.range (Fin.Embedding.tail e) ⊆ Set.range e := by
  rintro x ⟨i, rfl⟩
  exact ⟨i.succ, rfl⟩

private theorem exists_embedding_first
    [Fintype V] [DecidableEq V]
    {S : Finset V} {u : V} (hu : u ∈ S)
    {n : ℕ} (hcard : n + 1 ≤ S.card) :
    ∃ e : Fin (n + 1) ↪ V,
      e 0 = u ∧ Set.range e ⊆ (↑S : Set V) := by
  have herase : n ≤ (S.erase u).card := by
    rw [Finset.card_erase_of_mem hu]
    omega
  obtain ⟨e : Fin n ↪ V, he⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin n) (s := S.erase u) (by simpa using herase)
  have huRange : u ∉ Set.range e := by
    rintro ⟨i, hi⟩
    have := he (Set.mem_range_self i)
    simp [hi] at this
  let e' : Fin (n + 1) ↪ V :=
    Fin.Embedding.cons e huRange
  refine ⟨e', ?_, ?_⟩
  · simp [e', Fin.Embedding.cons]
  · rintro z ⟨i, rfl⟩
    refine Fin.cases hu (fun j => ?_) i
    exact Finset.mem_of_mem_erase
      (he (Set.mem_range_self j))

private theorem exists_embedding_last
    [Fintype V] [DecidableEq V]
    {S : Finset V} {v : V} (hv : v ∈ S)
    {n : ℕ} (hcard : n + 1 ≤ S.card) :
    ∃ e : Fin (n + 1) ↪ V,
      e (Fin.last n) = v ∧
      Set.range e ⊆ (↑S : Set V) := by
  have herase : n ≤ (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv]
    omega
  obtain ⟨e : Fin n ↪ V, he⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin n) (s := S.erase v) (by simpa using herase)
  have hvRange : v ∉ Set.range e := by
    rintro ⟨i, hi⟩
    have := he (Set.mem_range_self i)
    simp [hi] at this
  let e' : Fin (n + 1) ↪ V :=
    Fin.Embedding.snoc e hvRange
  refine ⟨e', ?_, ?_⟩
  · exact Fin.Embedding.snoc_last
  · rintro z ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [e', Fin.Embedding.snoc] using hv
    · simpa [e', Fin.Embedding.snoc] using
        (Finset.mem_of_mem_erase
          (he (Set.mem_range_self j)))

private theorem exists_embedding_first_last
    [Fintype V] [DecidableEq V]
    {S : Finset V} {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    {n : ℕ} (hcard : n + 2 ≤ S.card) :
    ∃ e : Fin (n + 2) ↪ V,
      e 0 = u ∧ e (Fin.last (n + 1)) = v ∧
      Set.range e ⊆ (↑S : Set V) := by
  have hvErase : v ∈ S.erase u := by
    simp [hv, huv.symm]
  have hsmall :
      n ≤ ((S.erase u).erase v).card := by
    rw [Finset.card_erase_of_mem hvErase,
      Finset.card_erase_of_mem hu]
    omega
  obtain ⟨e : Fin n ↪ V, he⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin n) (s := (S.erase u).erase v)
      (by simpa using hsmall)
  have huRange : u ∉ Set.range e := by
    rintro ⟨i, hi⟩
    have := he (Set.mem_range_self i)
    simp [hi] at this
  let eu : Fin (n + 1) ↪ V :=
    Fin.Embedding.cons e huRange
  have hvRange : v ∉ Set.range eu := by
    rintro ⟨i, hi⟩
    exact Fin.cases
      (motive := fun i => eu i = v → False)
      (fun hi => by
        apply huv
        change u = v at hi
        exact hi)
      (fun j hi => by
        have hmem := he (Set.mem_range_self j)
        apply (Finset.mem_erase.mp hmem).1
        change e j = v at hi
        exact hi)
      i hi
  let e' : Fin (n + 2) ↪ V :=
    Fin.Embedding.snoc eu hvRange
  refine ⟨e', ?_, ?_, ?_⟩
  · simp [e', eu, Fin.Embedding.snoc,
      Fin.Embedding.cons]
  · exact Fin.Embedding.snoc_last
  · rintro z ⟨i, rfl⟩
    exact Fin.lastCases
      (motive := fun i => e' i ∈ (↑S : Set V))
      (by
        rw [show e' (Fin.last (n + 1)) = v from
          Fin.Embedding.snoc_last]
        exact hv)
      (fun j => by
        rw [show e' j.castSucc = eu j from
          Fin.Embedding.snoc_castSucc]
        exact Fin.cases
          (motive := fun j => eu j ∈ (↑S : Set V))
          (by
            change u ∈ S
            exact hu)
          (fun k => by
            change e k ∈ S
            exact Finset.mem_of_mem_erase
              (Finset.mem_of_mem_erase
                (he (Set.mem_range_self k))))
          j)
      i

private theorem disjoint_ranges_of_subsets
    [DecidableEq V]
    {S T : Finset V} (hST : Disjoint S T)
    {m n : ℕ} (s : Fin m ↪ V) (t : Fin n ↪ V)
    (hs : Set.range s ⊆ (↑S : Set V))
    (ht : Set.range t ⊆ (↑T : Set V)) :
    Disjoint (Set.range s) (Set.range t) := by
  refine Set.disjoint_left.2 ?_
  intro z hzS hzT
  exact Finset.disjoint_left.mp hST (hs hzS) (ht hzT)

private theorem mem_range_of_full_embedding
    [Fintype V] [DecidableEq V]
    {S : Finset V} {n : ℕ} (e : Fin n ↪ V)
    (hsubset : Set.range e ⊆ (↑S : Set V))
    (hcard : n = S.card)
    {x : V} (hx : x ∈ S) :
    x ∈ Set.range e := by
  let R : Finset V := Finset.univ.map e
  have hRS : R ⊆ S := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hz
    exact hsubset (Set.mem_range_self i)
  have hcardR : R.card = S.card := by
    simp [R, hcard]
  have hEq : R = S :=
    Finset.eq_of_subset_of_card_le hRS (by omega)
  have hxR : x ∈ R := by simpa [hEq] using hx
  obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hxR
  exact ⟨i, hi⟩

private def swapDomain
    {n : ℕ} {α : Type*} (e : Fin n ↪ α) (i j : Fin n) :
    Fin n ↪ α :=
  (Equiv.swap i j).toEmbedding.trans e

@[simp] private theorem swapDomain_right
    {n : ℕ} {α : Type*} (e : Fin n ↪ α) (i j : Fin n) :
    swapDomain e i j j = e i := by
  simp [swapDomain, Equiv.swap_apply_right]

private theorem swapDomain_apply_of_ne
    {n : ℕ} {α : Type*} (e : Fin n ↪ α)
    {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    swapDomain e i j k = e k := by
  simp [swapDomain, Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem swapDomain_range_subset
    {n : ℕ} {α : Type*} (e : Fin n ↪ α)
    {i j : Fin n} {S : Set α}
    (hsubset : Set.range e ⊆ S) :
    Set.range (swapDomain e i j) ⊆ S := by
  rintro z ⟨k, rfl⟩
  exact hsubset ⟨Equiv.swap i j k, rfl⟩

/--
Alternating selected vertices from the same side to the same side give a
simple path.  Only the consecutive cross-edges used by the path are
required.
-/
private theorem exists_same_alternating_path
    {G : SimpleGraph V} {n : ℕ}
    (s : Fin (n + 1) ↪ V) (t : Fin n ↪ V)
    (hdisjoint : Disjoint (Set.range s) (Set.range t))
    (hdown :
      ∀ i : Fin n, G.Adj (s i.castSucc) (t i))
    (hup :
      ∀ i : Fin n, G.Adj (t i) (s i.succ)) :
    ∃ P : SimplePath G (s 0) (s (Fin.last n)),
      P.length = 2 * n ∧
      ∀ z ∈ P.walk.support,
        z ∈ Set.range s ∨ z ∈ Set.range t := by
  induction n with
  | zero =>
      let P : SimplePath G (s 0) (s (Fin.last 0)) := {
        walk := .nil
        isPath := .nil
      }
      refine ⟨P, by simp [P, SimplePath.length], ?_⟩
      intro z hz
      left
      have hz' : z = s 0 := by
        simpa [P] using hz
      exact ⟨0, hz'.symm⟩
  | succ n ih =>
      let sTail : Fin (n + 1) ↪ V := Fin.Embedding.tail s
      let tTail : Fin n ↪ V := Fin.Embedding.tail t
      have hdisjointTail :
          Disjoint (Set.range sTail) (Set.range tTail) :=
        hdisjoint.mono (range_tail_subset s) (range_tail_subset t)
      have hdownTail :
          ∀ i : Fin n,
            G.Adj (sTail i.castSucc) (tTail i) := by
        intro i
        change G.Adj (s i.castSucc.succ) (t i.succ)
        exact hdown i.succ
      have hupTail :
          ∀ i : Fin n,
            G.Adj (tTail i) (sTail i.succ) := by
        intro i
        change G.Adj (t i.succ) (s i.succ.succ)
        exact hup i.succ
      obtain ⟨P, hPlength, hPsupport⟩ :=
        ih sTail tTail hdisjointTail hdownTail hupTail
      have hPstart : sTail 0 = s ⟨1, by omega⟩ := by
        rfl
      have hPend :
          sTail (Fin.last n) = s (Fin.last (n + 1)) := by
        apply congrArg s
        apply Fin.ext
        simp
      let P' : SimplePath G
          (s ⟨1, by omega⟩)
          (s (Fin.last (n + 1))) :=
        (P.castStart hPstart).castEnd hPend
      have htNot : t 0 ∉ P'.walk.support := by
        intro ht
        have htP : t 0 ∈ P.walk.support := by
          simpa [P'] using ht
        rcases hPsupport (t 0) htP with htS | htT
        · exact Set.disjoint_left.mp hdisjoint
            (range_tail_subset s htS) (Set.mem_range_self 0)
        · obtain ⟨i, hi⟩ := htT
          change t i.succ = t 0 at hi
          exact (Fin.succ_ne_zero i) (t.injective hi)
      have hsNot :
          s 0 ∉
            (SimpleGraph.Walk.cons (hup 0) P'.walk).support := by
        intro hs
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
        rcases hs with hs | hs
        · exact Set.disjoint_left.mp hdisjoint
            (Set.mem_range_self 0) (hs ▸ Set.mem_range_self 0)
        · have hsP : s 0 ∈ P.walk.support := by
            simpa [P'] using hs
          rcases hPsupport (s 0) hsP with hsS | hsT
          · obtain ⟨i, hi⟩ := hsS
            change s i.succ = s 0 at hi
            exact (Fin.succ_ne_zero i) (s.injective hi)
          · exact Set.disjoint_left.mp hdisjoint
              (Set.mem_range_self 0) (range_tail_subset t hsT)
      let Q : SimplePath G (s 0) (s (Fin.last (n + 1))) := {
        walk := .cons (hdown 0) (.cons (hup 0) P'.walk)
        isPath := (P'.isPath.cons htNot).cons hsNot
      }
      refine ⟨Q, ?_, ?_⟩
      · have hP'length : P'.length = 2 * n := by
          simpa [P'] using hPlength
        change P'.length + 1 + 1 = 2 * (n + 1)
        omega
      · intro z hz
        simp only [Q, SimpleGraph.Walk.support_cons,
          List.mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · exact Or.inl (Set.mem_range_self 0)
        · exact Or.inr (Set.mem_range_self 0)
        · have hzP : z ∈ P.walk.support := by
            simpa [P'] using hz
          rcases hPsupport z hzP with hzS | hzT
          · exact Or.inl (range_tail_subset s hzS)
          · exact Or.inr (range_tail_subset t hzT)

/--
Alternating selected vertices from opposite sides give a simple path.  Only
the consecutive cross-edges used by the path are required.
-/
private theorem exists_opposite_alternating_path
    {G : SimpleGraph V} {n : ℕ}
    (s : Fin (n + 1) ↪ V) (t : Fin (n + 1) ↪ V)
    (hdisjoint : Disjoint (Set.range s) (Set.range t))
    (hdown :
      ∀ i : Fin (n + 1), G.Adj (s i) (t i))
    (hup :
      ∀ i : Fin n, G.Adj (t i.castSucc) (s i.succ)) :
    ∃ P : SimplePath G (s 0) (t (Fin.last n)),
      P.length = 2 * n + 1 ∧
      ∀ z ∈ P.walk.support,
        z ∈ Set.range s ∨ z ∈ Set.range t := by
  induction n with
  | zero =>
      refine ⟨SimplePath.ofAdj (hdown 0), by simp, ?_⟩
      intro z hz
      rw [SimplePath.ofAdj_support] at hz
      have hz' : z = s 0 ∨ z = t 0 := by
        simpa using hz
      rcases hz' with rfl | rfl
      · exact Or.inl (Set.mem_range_self 0)
      · exact Or.inr (Set.mem_range_self 0)
  | succ n ih =>
      let sTail : Fin (n + 1) ↪ V := Fin.Embedding.tail s
      let tTail : Fin (n + 1) ↪ V := Fin.Embedding.tail t
      have hdisjointTail :
          Disjoint (Set.range sTail) (Set.range tTail) :=
        hdisjoint.mono (range_tail_subset s) (range_tail_subset t)
      have hdownTail :
          ∀ i : Fin (n + 1),
            G.Adj (sTail i) (tTail i) := by
        intro i
        change G.Adj (s i.succ) (t i.succ)
        exact hdown i.succ
      have hupTail :
          ∀ i : Fin n,
            G.Adj (tTail i.castSucc) (sTail i.succ) := by
        intro i
        change G.Adj (t i.castSucc.succ) (s i.succ.succ)
        exact hup i.succ
      obtain ⟨P, hPlength, hPsupport⟩ :=
        ih sTail tTail hdisjointTail hdownTail hupTail
      have hPstart : sTail 0 = s ⟨1, by omega⟩ := by
        rfl
      have hPend :
          tTail (Fin.last n) = t (Fin.last (n + 1)) := by
        apply congrArg t
        apply Fin.ext
        simp
      let P' : SimplePath G
          (s ⟨1, by omega⟩)
          (t (Fin.last (n + 1))) :=
        (P.castStart hPstart).castEnd hPend
      have htNot : t 0 ∉ P'.walk.support := by
        intro ht
        have htP : t 0 ∈ P.walk.support := by
          simpa [P'] using ht
        rcases hPsupport (t 0) htP with htS | htT
        · exact Set.disjoint_left.mp hdisjoint
            (range_tail_subset s htS) (Set.mem_range_self 0)
        · obtain ⟨i, hi⟩ := htT
          change t i.succ = t 0 at hi
          exact (Fin.succ_ne_zero i) (t.injective hi)
      have hsNot :
          s 0 ∉
            (SimpleGraph.Walk.cons (hup 0) P'.walk).support := by
        intro hs
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
        rcases hs with hs | hs
        · exact Set.disjoint_left.mp hdisjoint
            (Set.mem_range_self 0) (hs ▸ Set.mem_range_self 0)
        · have hsP : s 0 ∈ P.walk.support := by
            simpa [P'] using hs
          rcases hPsupport (s 0) hsP with hsS | hsT
          · obtain ⟨i, hi⟩ := hsS
            change s i.succ = s 0 at hi
            exact (Fin.succ_ne_zero i) (s.injective hi)
          · exact Set.disjoint_left.mp hdisjoint
              (Set.mem_range_self 0) (range_tail_subset t hsT)
      let Q : SimplePath G (s 0) (t (Fin.last (n + 1))) := {
        walk := .cons (hdown 0) (.cons (hup 0) P'.walk)
        isPath := (P'.isPath.cons htNot).cons hsNot
      }
      refine ⟨Q, ?_, ?_⟩
      · have hP'length : P'.length = 2 * n + 1 := by
          simpa [P'] using hPlength
        change P'.length + 1 + 1 = 2 * (n + 1) + 1
        omega
      · intro z hz
        simp only [Q, SimpleGraph.Walk.support_cons,
          List.mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · exact Or.inl (Set.mem_range_self 0)
        · exact Or.inr (Set.mem_range_self 0)
        · have hzP : z ∈ P.walk.support := by
            simpa [P'] using hz
          rcases hPsupport z hzP with hzS | hzT
          · exact Or.inl (range_tail_subset s hzS)
          · exact Or.inr (range_tail_subset t hzT)

private theorem same_path_of_cross_complete
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B)
    (hcomplete : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y)
    (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (n : ℕ) (hn : 1 ≤ n)
    (hAcard : n + 1 ≤ A.card)
    (hBcard : n ≤ B.card) :
    ∃ P : SimplePath G u v, P.length = 2 * n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨a, ha0, haLast, haRange⟩ :=
    exists_embedding_first_last hu hv huv hAcard
  obtain ⟨b : Fin (k + 1) ↪ V, hbRange⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin (k + 1)) (s := B) (by simpa using hBcard)
  have hdisjoint :=
    disjoint_ranges_of_subsets hAB a b haRange hbRange
  have hdown :
      ∀ i : Fin (k + 1),
        G.Adj (a i.castSucc) (b i) := by
    intro i
    exact hcomplete _ (haRange (Set.mem_range_self _))
      _ (hbRange (Set.mem_range_self _))
  have hup :
      ∀ i : Fin (k + 1),
        G.Adj (b i) (a i.succ) := by
    intro i
    exact (hcomplete _ (haRange (Set.mem_range_self _))
      _ (hbRange (Set.mem_range_self _))).symm
  obtain ⟨P, hPlength, -⟩ :=
    exists_same_alternating_path a b hdisjoint hdown hup
  let P' : SimplePath G u v :=
    (P.castStart ha0).castEnd haLast
  refine ⟨P', ?_⟩
  simpa [P'] using hPlength

private theorem opposite_path_of_cross_complete
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B)
    (hcomplete : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y)
    (u v : V) (hu : u ∈ A) (hv : v ∈ B)
    (n : ℕ)
    (hAcard : n + 1 ≤ A.card)
    (hBcard : n + 1 ≤ B.card) :
    ∃ P : SimplePath G u v, P.length = 2 * n + 1 := by
  obtain ⟨a, ha0, haRange⟩ :=
    exists_embedding_first hu hAcard
  obtain ⟨b, hbLast, hbRange⟩ :=
    exists_embedding_last hv hBcard
  have hdisjoint :=
    disjoint_ranges_of_subsets hAB a b haRange hbRange
  have hdown :
      ∀ i : Fin (n + 1), G.Adj (a i) (b i) := by
    intro i
    exact hcomplete _ (haRange (Set.mem_range_self _))
      _ (hbRange (Set.mem_range_self _))
  have hup :
      ∀ i : Fin n,
        G.Adj (b i.castSucc) (a i.succ) := by
    intro i
    exact (hcomplete _ (haRange (Set.mem_range_self _))
      _ (hbRange (Set.mem_range_self _))).symm
  obtain ⟨P, hPlength, -⟩ :=
    exists_opposite_alternating_path a b hdisjoint hdown hup
  let P' : SimplePath G u v :=
    (P.castStart ha0).castEnd hbLast
  exact ⟨P', by simpa [P'] using hPlength⟩

private theorem terminal_same_path_missing
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B)
    (a b : V) (ha : a ∈ A) (hb : b ∈ B)
    (hadj :
      ∀ x ∈ A, ∀ y ∈ B,
        (x ≠ a ∨ y ≠ b) → G.Adj x y)
    (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (r : ℕ) (hr : 3 ≤ r)
    (hAcard : r + 1 ≤ A.card)
    (hBcard : B.card = r) :
    ∃ P : SimplePath G u v, P.length = 2 * r := by
  obtain ⟨k, hk⟩ : ∃ k, r = k + 3 :=
    ⟨r - 3, by omega⟩
  subst r
  rw [hk] at hr hAcard ⊢
  have build
      (s : Fin (k + 4) ↪ V) (t : Fin (k + 3) ↪ V)
      (hs0 : s 0 = u)
      (hsLast : s (Fin.last (k + 3)) = v)
      (hsRange : Set.range s ⊆ (↑A : Set V))
      (htRange : Set.range t ⊆ (↑B : Set V))
      (ia : Fin (k + 4)) (ib : Fin (k + 3))
      (haPos : s ia = a) (hbPos : t ib = b)
      (hdownSafe :
        ∀ i : Fin (k + 3), ¬(i.castSucc = ia ∧ i = ib))
      (hupSafe :
        ∀ i : Fin (k + 3), ¬(i.succ = ia ∧ i = ib)) :
      ∃ P : SimplePath G u v,
        P.length = 2 * (k + 3) := by
    have hdisjoint :=
      disjoint_ranges_of_subsets hAB s t hsRange htRange
    have hdown :
        ∀ i : Fin (k + 3),
          G.Adj (s i.castSucc) (t i) := by
      intro i
      apply hadj _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))
      by_cases hsa : s i.castSucc = a
      · right
        intro htb
        have hiA : i.castSucc = ia :=
          s.injective (hsa.trans haPos.symm)
        have hiB : i = ib :=
          t.injective (htb.trans hbPos.symm)
        exact hdownSafe i ⟨hiA, hiB⟩
      · exact Or.inl hsa
    have hup :
        ∀ i : Fin (k + 3),
          G.Adj (t i) (s i.succ) := by
      intro i
      apply (hadj _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _)) ?_).symm
      by_cases hsa : s i.succ = a
      · right
        intro htb
        have hiA : i.succ = ia :=
          s.injective (hsa.trans haPos.symm)
        have hiB : i = ib :=
          t.injective (htb.trans hbPos.symm)
        exact hupSafe i ⟨hiA, hiB⟩
      · exact Or.inl hsa
    obtain ⟨P, hPlength, -⟩ :=
      exists_same_alternating_path s t hdisjoint hdown hup
    let P' : SimplePath G u v :=
      (P.castStart hs0).castEnd hsLast
    exact ⟨P', by simpa [P'] using hPlength⟩
  obtain ⟨s, hs0, hsLast, hsRange⟩ :=
    exists_embedding_first_last
      (n := k + 2) hu hv huv (by omega)
  by_cases hau : a = u
  · subst a
    obtain ⟨t, htLast, htRange⟩ :=
      exists_embedding_last
        (n := k + 2) hb (by omega)
    apply build s t hs0 hsLast hsRange htRange
      0 (Fin.last (k + 2))
    · exact hs0
    · exact htLast
    · intro i hi
      rcases hi with ⟨hi0, rfl⟩
      have hval := congrArg Fin.val hi0
      change k + 2 = 0 at hval
      omega
    · intro i hi
      have hi0 : i.succ = (0 : Fin (k + 4)) := hi.1
      exact Fin.succ_ne_zero i hi0
  · by_cases hav : a = v
    · subst a
      obtain ⟨t, ht0, htRange⟩ :=
        exists_embedding_first
          (n := k + 2) hb (by omega)
      apply build s t hs0 hsLast hsRange htRange
        (Fin.last (k + 3)) 0
      · exact hsLast
      · exact ht0
      · intro i hi
        exact Fin.castSucc_ne_last i hi.1
      · intro i hi
        rcases hi with ⟨hiLast, rfl⟩
        have hval := congrArg Fin.val hiLast
        change 1 = k + 3 at hval
        omega
    · by_cases hspare : k + 5 ≤ A.card
      · have huErase : u ∈ A.erase a := by
          simp only [Finset.mem_erase, hu, and_true]
          exact fun h => hau h.symm
        have hvErase : v ∈ A.erase a := by
          simp only [Finset.mem_erase, hv, and_true]
          exact fun h => hav h.symm
        have hcompleteErase :
            ∀ x ∈ A.erase a, ∀ y ∈ B, G.Adj x y := by
          intro x hx y hy
          exact hadj x (Finset.mem_of_mem_erase hx)
            y hy (Or.inl (Finset.ne_of_mem_erase hx))
        exact same_path_of_cross_complete
          G (A.erase a) B
          (hAB.mono_left (Finset.erase_subset _ _))
          hcompleteErase u v huErase hvErase huv
          (k + 3) (by omega) (by
            rw [Finset.card_erase_of_mem ha]
            omega)
          (by omega)
      · have hAeq : A.card = k + 4 := by omega
        obtain ⟨ia, hia⟩ :=
          mem_range_of_full_embedding s hsRange
            (by omega) ha
        let one : Fin (k + 4) := ⟨1, by omega⟩
        let s' : Fin (k + 4) ↪ V :=
          swapDomain s ia one
        have hia0 : ia ≠ (0 : Fin (k + 4)) := by
          intro h
          apply hau
          calc
            a = s ia := hia.symm
            _ = s 0 := congrArg s h
            _ = u := hs0
        have hiaLast : ia ≠ Fin.last (k + 3) := by
          intro h
          apply hav
          calc
            a = s ia := hia.symm
            _ = s (Fin.last (k + 3)) := congrArg s h
            _ = v := hsLast
        have hone0 : (0 : Fin (k + 4)) ≠ one := by
          intro h
          have hval := congrArg Fin.val h
          simp [one] at hval
        have honeLast : Fin.last (k + 3) ≠ one := by
          intro h
          have hval := congrArg Fin.val h
          simp [one] at hval
        have hs'0 : s' 0 = u := by
          rw [swapDomain_apply_of_ne s hia0.symm hone0]
          exact hs0
        have hs'Last :
            s' (Fin.last (k + 3)) = v := by
          rw [swapDomain_apply_of_ne s hiaLast.symm honeLast]
          exact hsLast
        have hs'Range :
            Set.range s' ⊆ (↑A : Set V) :=
          swapDomain_range_subset s hsRange
        have hs'One : s' one = a := by
          rw [swapDomain_right, hia]
        obtain ⟨t, htLast, htRange⟩ :=
          exists_embedding_last
            (n := k + 2) hb (by omega)
        apply build s' t hs'0 hs'Last hs'Range htRange
          one (Fin.last (k + 2)) hs'One htLast
        · intro i hi
          have hi1 := congrArg Fin.val hi.1
          have hi2 := congrArg Fin.val hi.2
          change i.val = 1 at hi1
          change i.val = k + 2 at hi2
          omega
        · intro i hi
          have hi1 := congrArg Fin.val hi.1
          have hi2 := congrArg Fin.val hi.2
          change i.val + 1 = 1 at hi1
          change i.val = k + 2 at hi2
          omega

private theorem complete_same_part_paths
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V)
    (hST : Disjoint S T)
    (hcomplete : ∀ x ∈ S, ∀ y ∈ T, G.Adj x y)
    (u v : V) (huv : u ≠ v)
    (hsame : (u ∈ S ∧ v ∈ S) ∨ (u ∈ T ∧ v ∈ T))
    (ℓ : ℕ)
    (hℓeven : Even ℓ)
    (hℓlo : 2 ≤ ℓ)
    (hallowed :
      ℓ ≤ 2 * min S.card T.card - 2 ∨
      (ℓ = 2 * min S.card T.card ∧
        ((u ∈ S ∧ v ∈ S ∧ min S.card T.card < S.card) ∨
         (u ∈ T ∧ v ∈ T ∧ min S.card T.card < T.card)))) :
    ∃ P : SimplePath G u v, P.length = ℓ := by
  obtain ⟨n, hnℓ⟩ := hℓeven
  have hℓeq : ℓ = 2 * n := by omega
  have hnpos : n ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos
  subst ℓ
  rcases hsame with hsameS | hsameT
  · have hScard : k + 2 ≤ S.card := by
      rcases hallowed with hshort | hterminal
      · have hminS := min_le_left S.card T.card
        omega
      · rcases hterminal.2 with hlargeS | hlargeT
        · omega
        · exact False.elim (Finset.disjoint_left.mp hST
            hsameS.1 hlargeT.1)
    have hTcard : k + 1 ≤ T.card := by
      rcases hallowed with hshort | hterminal
      · have hminT := min_le_right S.card T.card
        omega
      · have hminT := min_le_right S.card T.card
        omega
    obtain ⟨s, hs0, hsLast, hsRange⟩ :=
      exists_embedding_first_last
        hsameS.1 hsameS.2 huv hScard
    obtain ⟨t : Fin (k + 1) ↪ V, htRange⟩ :=
      Function.Embedding.exists_of_card_le_finset
        (α := Fin (k + 1)) (s := T) (by simpa using hTcard)
    have hdisjoint :=
      disjoint_ranges_of_subsets hST s t hsRange htRange
    have hdown :
        ∀ i : Fin (k + 1),
          G.Adj (s i.castSucc) (t i) := by
      intro i
      exact hcomplete _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))
    have hup :
        ∀ i : Fin (k + 1),
          G.Adj (t i) (s i.succ) := by
      intro i
      exact (hcomplete _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))).symm
    obtain ⟨P, hPlength, -⟩ :=
      exists_same_alternating_path s t hdisjoint hdown hup
    let P' : SimplePath G u v :=
      (P.castStart hs0).castEnd hsLast
    refine ⟨P', ?_⟩
    have hP'length : P'.length = 2 * (k + 1) := by
      simpa [P'] using hPlength
    omega
  · have hTcard : k + 2 ≤ T.card := by
      rcases hallowed with hshort | hterminal
      · have hminT := min_le_right S.card T.card
        omega
      · rcases hterminal.2 with hlargeS | hlargeT
        · exact False.elim (Finset.disjoint_left.mp hST
            hlargeS.1 hsameT.1)
        · omega
    have hScard : k + 1 ≤ S.card := by
      rcases hallowed with hshort | hterminal
      · have hminS := min_le_left S.card T.card
        omega
      · have hminS := min_le_left S.card T.card
        omega
    obtain ⟨t, ht0, htLast, htRange⟩ :=
      exists_embedding_first_last
        hsameT.1 hsameT.2 huv hTcard
    obtain ⟨s : Fin (k + 1) ↪ V, hsRange⟩ :=
      Function.Embedding.exists_of_card_le_finset
        (α := Fin (k + 1)) (s := S) (by simpa using hScard)
    have hdisjoint :=
      (disjoint_ranges_of_subsets hST s t hsRange htRange).symm
    have hdown :
        ∀ i : Fin (k + 1),
          G.Adj (t i.castSucc) (s i) := by
      intro i
      exact (hcomplete _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))).symm
    have hup :
        ∀ i : Fin (k + 1),
          G.Adj (s i) (t i.succ) := by
      intro i
      exact hcomplete _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))
    obtain ⟨P, hPlength, -⟩ :=
      exists_same_alternating_path t s hdisjoint hdown hup
    let P' : SimplePath G u v :=
      (P.castStart ht0).castEnd htLast
    refine ⟨P', ?_⟩
    have hP'length : P'.length = 2 * (k + 1) := by
      simpa [P'] using hPlength
    omega

private theorem complete_opposite_part_paths
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V)
    (hST : Disjoint S T)
    (hcomplete : ∀ x ∈ S, ∀ y ∈ T, G.Adj x y)
    (u v : V) (_huv : u ≠ v)
    (hopposite : (u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S))
    (ℓ : ℕ)
    (hℓodd : Odd ℓ)
    (hℓhi : ℓ ≤ 2 * min S.card T.card - 1) :
    ∃ P : SimplePath G u v, P.length = ℓ := by
  obtain ⟨n, rfl⟩ := hℓodd
  have hScard : n + 1 ≤ S.card := by
    have hminS := min_le_left S.card T.card
    omega
  have hTcard : n + 1 ≤ T.card := by
    have hminT := min_le_right S.card T.card
    omega
  rcases hopposite with hoppositeST | hoppositeTS
  · obtain ⟨s, hs0, hsRange⟩ :=
      exists_embedding_first hoppositeST.1 hScard
    obtain ⟨t, htLast, htRange⟩ :=
      exists_embedding_last hoppositeST.2 hTcard
    have hdisjoint :=
      disjoint_ranges_of_subsets hST s t hsRange htRange
    have hdown :
        ∀ i : Fin (n + 1), G.Adj (s i) (t i) := by
      intro i
      exact hcomplete _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))
    have hup :
        ∀ i : Fin n,
          G.Adj (t i.castSucc) (s i.succ) := by
      intro i
      exact (hcomplete _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))).symm
    obtain ⟨P, hPlength, -⟩ :=
      exists_opposite_alternating_path s t hdisjoint hdown hup
    let P' : SimplePath G u v :=
      (P.castStart hs0).castEnd htLast
    exact ⟨P', by simpa [P'] using hPlength⟩
  · obtain ⟨t, ht0, htRange⟩ :=
      exists_embedding_first hoppositeTS.1 hTcard
    obtain ⟨s, hsLast, hsRange⟩ :=
      exists_embedding_last hoppositeTS.2 hScard
    have hdisjoint :=
      (disjoint_ranges_of_subsets hST s t hsRange htRange).symm
    have hdown :
        ∀ i : Fin (n + 1), G.Adj (t i) (s i) := by
      intro i
      exact (hcomplete _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))).symm
    have hup :
        ∀ i : Fin n,
          G.Adj (s i.castSucc) (t i.succ) := by
      intro i
      exact hcomplete _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))
    obtain ⟨P, hPlength, -⟩ :=
      exists_opposite_alternating_path t s hdisjoint hdown hup
    let P' : SimplePath G u v :=
      (P.castStart ht0).castEnd hsLast
    exact ⟨P', by simpa [P'] using hPlength⟩

theorem core_same_part_paths
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V)
    (hcore : IsCompleteBipartiteMinusAtMostOne G S T)
    (u v : V) (huv : u ≠ v)
    (hsame : (u ∈ S ∧ v ∈ S) ∨ (u ∈ T ∧ v ∈ T))
    (ℓ : ℕ)
    (hℓeven : Even ℓ)
    (hℓlo : 2 ≤ ℓ)
    (hallowed :
      ℓ ≤ 2 * min S.card T.card - 2 ∨
      (ℓ = 2 * min S.card T.card ∧
        ((u ∈ S ∧ v ∈ S ∧ min S.card T.card < S.card) ∨
         (u ∈ T ∧ v ∈ T ∧ min S.card T.card < T.card))))
    (hsafe :
      ℓ ≤ 2 * min S.card T.card - 2 ∨
      3 ≤ min S.card T.card ∨
      ∀ x ∈ S, ∀ y ∈ T, G.Adj x y) :
    ∃ P : SimplePath G u v, P.length = ℓ := by
  rcases hcore with
    ⟨hST, -, -, missing, hmissingPart, -, hAdj⟩
  rcases missing with _ | p
  · have hcomplete :
        ∀ x ∈ S, ∀ y ∈ T, G.Adj x y := by
      intro x hx y hy
      apply (hAdj x y).2
      exact ⟨Or.inl ⟨hx, hy⟩, trivial⟩
    exact complete_same_part_paths
      G S T hST hcomplete u v huv hsame ℓ hℓeven hℓlo hallowed
  · obtain ⟨hpS, hpT⟩ := hmissingPart p rfl
    have hcrossAdj :
        ∀ x ∈ S, ∀ y ∈ T,
          (x ≠ p.1 ∨ y ≠ p.2) → G.Adj x y := by
      intro x hx y hy hneq
      apply (hAdj x y).2
      refine ⟨Or.inl ⟨hx, hy⟩, ?_⟩
      simp only
      rintro (hbad | hbad)
      · exact hneq.elim
          (fun hxp => hxp hbad.1)
          (fun hyp => hyp hbad.2)
      · exact Finset.disjoint_left.mp hST
          (hbad.1 ▸ hx) hpT
    have hnotMissing : ¬G.Adj p.1 p.2 := by
      rw [hAdj]
      simp [hpS, hpT]
    have hsafe' :
        ℓ ≤ 2 * min S.card T.card - 2 ∨
        3 ≤ min S.card T.card := by
      rcases hsafe with hshort | hrank | hcomplete
      · exact Or.inl hshort
      · exact Or.inr hrank
      · exact False.elim
          (hnotMissing (hcomplete p.1 hpS p.2 hpT))
    obtain ⟨n, hnℓ⟩ := hℓeven
    have hℓeq : ℓ = 2 * n := by omega
    rcases hallowed with hshort | hterminal
    · have hnpos : 1 ≤ n := by omega
      rcases hsame with hsameS | hsameT
      · have huErase : u ∈ S := hsameS.1
        have hvErase : v ∈ S := hsameS.2
        have hcompleteErase :
            ∀ x ∈ S, ∀ y ∈ T.erase p.2, G.Adj x y := by
          intro x hx y hy
          exact hcrossAdj x hx y (Finset.mem_of_mem_erase hy)
            (Or.inr (Finset.ne_of_mem_erase hy))
        have hScard : n + 1 ≤ S.card := by
          have hminS := min_le_left S.card T.card
          omega
        have hTcard : n ≤ (T.erase p.2).card := by
          rw [Finset.card_erase_of_mem hpT]
          have hminT := min_le_right S.card T.card
          omega
        obtain ⟨P, hP⟩ :=
          same_path_of_cross_complete
            G S (T.erase p.2)
            (hST.mono_right (Finset.erase_subset _ _))
            hcompleteErase u v huErase hvErase huv
            n hnpos hScard hTcard
        exact ⟨P, hP.trans hℓeq.symm⟩
      · have hcompleteErase :
            ∀ x ∈ T, ∀ y ∈ S.erase p.1, G.Adj x y := by
          intro x hx y hy
          exact (hcrossAdj y (Finset.mem_of_mem_erase hy)
            x hx (Or.inl (Finset.ne_of_mem_erase hy))).symm
        have hTcard : n + 1 ≤ T.card := by
          have hminT := min_le_right S.card T.card
          omega
        have hScard : n ≤ (S.erase p.1).card := by
          rw [Finset.card_erase_of_mem hpS]
          have hminS := min_le_left S.card T.card
          omega
        obtain ⟨P, hP⟩ :=
          same_path_of_cross_complete
            G T (S.erase p.1)
            (hST.symm.mono_right (Finset.erase_subset _ _))
            hcompleteErase u v hsameT.1 hsameT.2 huv
            n hnpos hTcard hScard
        exact ⟨P, hP.trans hℓeq.symm⟩
    · have hrank : 3 ≤ min S.card T.card := by
        rcases hsafe' with hshort | hrank
        · omega
        · exact hrank
      rcases hterminal with ⟨hterminal, hlargeS | hlargeT⟩
      · have hTcard :
            T.card = min S.card T.card := by omega
        have hScard :
            min S.card T.card + 1 ≤ S.card := by omega
        obtain ⟨P, hP⟩ :=
          terminal_same_path_missing
            G S T hST p.1 p.2 hpS hpT hcrossAdj
            u v hlargeS.1 hlargeS.2.1 huv
            (min S.card T.card) hrank hScard hTcard
        exact ⟨P, hP.trans hterminal.symm⟩
      · have hScard :
            S.card = min S.card T.card := by omega
        have hTcard :
            min S.card T.card + 1 ≤ T.card := by omega
        have hcrossAdj' :
            ∀ x ∈ T, ∀ y ∈ S,
              (x ≠ p.2 ∨ y ≠ p.1) → G.Adj x y := by
          intro x hx y hy hneq
          apply (hcrossAdj y hy x hx ?_).symm
          rcases hneq with hxp | hyp
          · exact Or.inr hxp
          · exact Or.inl hyp
        obtain ⟨P, hP⟩ :=
          terminal_same_path_missing
            G T S hST.symm p.2 p.1 hpT hpS hcrossAdj'
            u v hlargeT.1 hlargeT.2.1 huv
            (min S.card T.card) hrank hTcard hScard
        exact ⟨P, hP.trans hterminal.symm⟩

private theorem opposite_path_missing_adjacent
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B)
    (a b : V) (ha : a ∈ A) (hb : b ∈ B)
    (hadj :
      ∀ x ∈ A, ∀ y ∈ B,
        (x ≠ a ∨ y ≠ b) → G.Adj x y)
    (hnotMissing : ¬G.Adj a b)
    (u v : V) (hu : u ∈ A) (hv : v ∈ B)
    (huvAdj : G.Adj u v)
    (n : ℕ)
    (hAcard : n + 1 ≤ A.card)
    (hBcard : n + 1 ≤ B.card)
    (hrank : 3 ≤ min A.card B.card) :
    ∃ P : SimplePath G u v, P.length = 2 * n + 1 := by
  by_cases hn0 : n = 0
  · subst n
    exact ⟨SimplePath.ofAdj huvAdj, by simp⟩
  have build
      (s t : Fin (n + 1) ↪ V)
      (hs0 : s 0 = u) (htLast : t (Fin.last n) = v)
      (hsRange : Set.range s ⊆ (↑A : Set V))
      (htRange : Set.range t ⊆ (↑B : Set V))
      (ia ib : Fin (n + 1))
      (haPos : s ia = a) (hbPos : t ib = b)
      (hdownSafe :
        ∀ i : Fin (n + 1), ¬(i = ia ∧ i = ib))
      (hupSafe :
        ∀ i : Fin n, ¬(i.succ = ia ∧ i.castSucc = ib)) :
      ∃ P : SimplePath G u v, P.length = 2 * n + 1 := by
    have hdisjoint :=
      disjoint_ranges_of_subsets hAB s t hsRange htRange
    have hdown :
        ∀ i : Fin (n + 1), G.Adj (s i) (t i) := by
      intro i
      apply hadj _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _))
      by_cases hsa : s i = a
      · right
        intro htb
        have hiA : i = ia :=
          s.injective (hsa.trans haPos.symm)
        have hiB : i = ib :=
          t.injective (htb.trans hbPos.symm)
        exact hdownSafe i ⟨hiA, hiB⟩
      · exact Or.inl hsa
    have hup :
        ∀ i : Fin n, G.Adj (t i.castSucc) (s i.succ) := by
      intro i
      apply (hadj _ (hsRange (Set.mem_range_self _))
        _ (htRange (Set.mem_range_self _)) ?_).symm
      by_cases hsa : s i.succ = a
      · right
        intro htb
        have hiA : i.succ = ia :=
          s.injective (hsa.trans haPos.symm)
        have hiB : i.castSucc = ib :=
          t.injective (htb.trans hbPos.symm)
        exact hupSafe i ⟨hiA, hiB⟩
      · exact Or.inl hsa
    obtain ⟨P, hPlength, -⟩ :=
      exists_opposite_alternating_path s t hdisjoint hdown hup
    let P' : SimplePath G u v :=
      (P.castStart hs0).castEnd htLast
    exact ⟨P', by simpa [P'] using hPlength⟩
  by_cases hau : a = u
  · subst a
    have hbv : b ≠ v := by
      intro hbv
      subst b
      exact hnotMissing huvAdj
    by_cases hBspare : n + 2 ≤ B.card
    · have hvErase : v ∈ B.erase b := by
        simp only [Finset.mem_erase, hv, and_true]
        exact fun h => hbv h.symm
      have hcompleteErase :
          ∀ x ∈ A, ∀ y ∈ B.erase b, G.Adj x y := by
        intro x hx y hy
        exact hadj x hx y (Finset.mem_of_mem_erase hy)
          (Or.inr (Finset.ne_of_mem_erase hy))
      exact opposite_path_of_cross_complete
        G A (B.erase b)
        (hAB.mono_right (Finset.erase_subset _ _))
        hcompleteErase u v hu hvErase n hAcard
        (by
          rw [Finset.card_erase_of_mem hb]
          omega)
    · have hBeq : B.card = n + 1 := by omega
      have hn2 : 2 ≤ n := by
        have hminB := min_le_right A.card B.card
        omega
      obtain ⟨s, hs0, hsRange⟩ :=
        exists_embedding_first hu hAcard
      obtain ⟨t, htLast, htRange⟩ :=
        exists_embedding_last hv hBcard
      obtain ⟨ib, hib⟩ :=
        mem_range_of_full_embedding t htRange
          (by omega) hb
      let one : Fin (n + 1) := ⟨1, by omega⟩
      let t' : Fin (n + 1) ↪ V :=
        swapDomain t ib one
      have hibLast : ib ≠ Fin.last n := by
        intro h
        apply hbv
        calc
          b = t ib := hib.symm
          _ = t (Fin.last n) := congrArg t h
          _ = v := htLast
      have honeLast : Fin.last n ≠ one := by
        intro h
        have hval := congrArg Fin.val h
        change n = 1 at hval
        omega
      have ht'Last : t' (Fin.last n) = v := by
        rw [swapDomain_apply_of_ne t hibLast.symm honeLast]
        exact htLast
      have ht'Range :
          Set.range t' ⊆ (↑B : Set V) :=
        swapDomain_range_subset t htRange
      have ht'One : t' one = b := by
        rw [swapDomain_right, hib]
      apply build s t' hs0 ht'Last hsRange ht'Range
        0 one hs0 ht'One
      · intro i hi
        have hi0 := congrArg Fin.val hi.1
        have hi1 := congrArg Fin.val hi.2
        change i.val = 0 at hi0
        change i.val = 1 at hi1
        omega
      · intro i hi
        exact Fin.succ_ne_zero i hi.1
  · by_cases hbv : b = v
    · subst b
      by_cases hAspare : n + 2 ≤ A.card
      · have huErase : u ∈ A.erase a := by
          simp only [Finset.mem_erase, hu, and_true]
          exact fun h => hau h.symm
        have hcompleteErase :
            ∀ x ∈ A.erase a, ∀ y ∈ B, G.Adj x y := by
          intro x hx y hy
          exact hadj x (Finset.mem_of_mem_erase hx) y hy
            (Or.inl (Finset.ne_of_mem_erase hx))
        exact opposite_path_of_cross_complete
          G (A.erase a) B
          (hAB.mono_left (Finset.erase_subset _ _))
          hcompleteErase u v huErase hv n
          (by
            rw [Finset.card_erase_of_mem ha]
            omega)
          hBcard
      · have hAeq : A.card = n + 1 := by omega
        have hn2 : 2 ≤ n := by
          have hminA := min_le_left A.card B.card
          omega
        obtain ⟨s, hs0, hsRange⟩ :=
          exists_embedding_first hu hAcard
        obtain ⟨t, htLast, htRange⟩ :=
          exists_embedding_last hv hBcard
        obtain ⟨ia, hia⟩ :=
          mem_range_of_full_embedding s hsRange
            (by omega) ha
        let one : Fin (n + 1) := ⟨1, by omega⟩
        let s' : Fin (n + 1) ↪ V :=
          swapDomain s ia one
        have hia0 : ia ≠ (0 : Fin (n + 1)) := by
          intro h
          apply hau
          calc
            a = s ia := hia.symm
            _ = s 0 := congrArg s h
            _ = u := hs0
        have hone0 : (0 : Fin (n + 1)) ≠ one := by
          intro h
          have hval := congrArg Fin.val h
          simp [one] at hval
        have hs'0 : s' 0 = u := by
          rw [swapDomain_apply_of_ne s hia0.symm hone0]
          exact hs0
        have hs'Range :
            Set.range s' ⊆ (↑A : Set V) :=
          swapDomain_range_subset s hsRange
        have hs'One : s' one = a := by
          rw [swapDomain_right, hia]
        apply build s' t hs'0 htLast hs'Range htRange
          one (Fin.last n) hs'One htLast
        · intro i hi
          have hi1 := congrArg Fin.val hi.1
          have hiLast := congrArg Fin.val hi.2
          change i.val = 1 at hi1
          change i.val = n at hiLast
          omega
        · intro i hi
          exact Fin.castSucc_ne_last i hi.2
    · by_cases hAspare : n + 2 ≤ A.card
      · have huErase : u ∈ A.erase a := by
          simp only [Finset.mem_erase, hu, and_true]
          exact fun h => hau h.symm
        have hcompleteErase :
            ∀ x ∈ A.erase a, ∀ y ∈ B, G.Adj x y := by
          intro x hx y hy
          exact hadj x (Finset.mem_of_mem_erase hx) y hy
            (Or.inl (Finset.ne_of_mem_erase hx))
        exact opposite_path_of_cross_complete
          G (A.erase a) B
          (hAB.mono_left (Finset.erase_subset _ _))
          hcompleteErase u v huErase hv n
          (by
            rw [Finset.card_erase_of_mem ha]
            omega)
          hBcard
      · by_cases hBspare : n + 2 ≤ B.card
        · have hvErase : v ∈ B.erase b := by
            simp only [Finset.mem_erase, hv, and_true]
            exact fun h => hbv h.symm
          have hcompleteErase :
              ∀ x ∈ A, ∀ y ∈ B.erase b, G.Adj x y := by
            intro x hx y hy
            exact hadj x hx y (Finset.mem_of_mem_erase hy)
              (Or.inr (Finset.ne_of_mem_erase hy))
          exact opposite_path_of_cross_complete
            G A (B.erase b)
            (hAB.mono_right (Finset.erase_subset _ _))
            hcompleteErase u v hu hvErase n hAcard
            (by
              rw [Finset.card_erase_of_mem hb]
              omega)
        · have hAeq : A.card = n + 1 := by omega
          have hBeq : B.card = n + 1 := by omega
          have hn2 : 2 ≤ n := by
            have hminA := min_le_left A.card B.card
            omega
          obtain ⟨s, hs0, hsRange⟩ :=
            exists_embedding_first hu hAcard
          obtain ⟨t, htLast, htRange⟩ :=
            exists_embedding_last hv hBcard
          obtain ⟨ia, hia⟩ :=
            mem_range_of_full_embedding s hsRange
              (by omega) ha
          obtain ⟨ib, hib⟩ :=
            mem_range_of_full_embedding t htRange
              (by omega) hb
          let last : Fin (n + 1) := Fin.last n
          let s' : Fin (n + 1) ↪ V :=
            swapDomain s ia last
          let t' : Fin (n + 1) ↪ V :=
            swapDomain t ib 0
          have hia0 : ia ≠ (0 : Fin (n + 1)) := by
            intro h
            apply hau
            calc
              a = s ia := hia.symm
              _ = s 0 := congrArg s h
              _ = u := hs0
          have hlast0 : last ≠ (0 : Fin (n + 1)) := by
            intro h
            have hval := congrArg Fin.val h
            change n = 0 at hval
            omega
          have hibLast : ib ≠ Fin.last n := by
            intro h
            apply hbv
            calc
              b = t ib := hib.symm
              _ = t (Fin.last n) := congrArg t h
              _ = v := htLast
          have hs'0 : s' 0 = u := by
            rw [swapDomain_apply_of_ne s hia0.symm hlast0.symm]
            exact hs0
          have ht'Last : t' (Fin.last n) = v := by
            rw [swapDomain_apply_of_ne t hibLast.symm]
            · exact htLast
            · exact fun h => hlast0 (by simpa [last] using h)
          have hs'Range :
              Set.range s' ⊆ (↑A : Set V) :=
            swapDomain_range_subset s hsRange
          have ht'Range :
              Set.range t' ⊆ (↑B : Set V) :=
            swapDomain_range_subset t htRange
          have hs'Last : s' last = a := by
            rw [swapDomain_right, hia]
          have ht'0 : t' 0 = b := by
            rw [swapDomain_right, hib]
          apply build s' t' hs'0 ht'Last hs'Range ht'Range
            last 0 hs'Last ht'0
          · intro i hi
            have hiLast := congrArg Fin.val hi.1
            have hi0 := congrArg Fin.val hi.2
            change i.val = n at hiLast
            change i.val = 0 at hi0
            omega
          · intro i hi
            have hiSucc := congrArg Fin.val hi.1
            have hi0 := congrArg Fin.val hi.2
            change i.val + 1 = n at hiSucc
            change i.val = 0 at hi0
            omega

theorem core_opposite_part_paths
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V)
    (hcore : IsCompleteBipartiteMinusAtMostOne G S T)
    (u v : V) (huv : u ≠ v)
    (hopposite : (u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S))
    (hsafe :
      3 ≤ min S.card T.card ∨
      ∀ x ∈ S, ∀ y ∈ T, G.Adj x y)
    (ℓ : ℕ)
    (hℓodd : Odd ℓ)
    (hadj : G.Adj u v)
    (hℓhi : ℓ ≤ 2 * min S.card T.card - 1) :
    ∃ P : SimplePath G u v, P.length = ℓ := by
  rcases hcore with
    ⟨hST, -, -, missing, hmissingPart, -, hAdj⟩
  obtain ⟨n, hnℓ⟩ := hℓodd
  have hℓeq : ℓ = 2 * n + 1 := by omega
  have hScard : n + 1 ≤ S.card := by
    have hminS := min_le_left S.card T.card
    omega
  have hTcard : n + 1 ≤ T.card := by
    have hminT := min_le_right S.card T.card
    omega
  rcases missing with _ | p
  · have hcomplete :
        ∀ x ∈ S, ∀ y ∈ T, G.Adj x y := by
      intro x hx y hy
      apply (hAdj x y).2
      exact ⟨Or.inl ⟨hx, hy⟩, trivial⟩
    obtain ⟨P, hP⟩ :=
      complete_opposite_part_paths
        G S T hST hcomplete u v huv hopposite
        ℓ ⟨n, hnℓ⟩ hℓhi
    exact ⟨P, hP⟩
  · obtain ⟨hpS, hpT⟩ := hmissingPart p rfl
    have hcrossAdj :
        ∀ x ∈ S, ∀ y ∈ T,
          (x ≠ p.1 ∨ y ≠ p.2) → G.Adj x y := by
      intro x hx y hy hneq
      apply (hAdj x y).2
      refine ⟨Or.inl ⟨hx, hy⟩, ?_⟩
      simp only
      rintro (hbad | hbad)
      · exact hneq.elim
          (fun hxp => hxp hbad.1)
          (fun hyp => hyp hbad.2)
      · exact Finset.disjoint_left.mp hST
          (hbad.1 ▸ hx) hpT
    have hnotMissing : ¬G.Adj p.1 p.2 := by
      rw [hAdj]
      simp [hpS, hpT]
    have hrank : 3 ≤ min S.card T.card := by
      rcases hsafe with hrank | hcomplete
      · exact hrank
      · exact False.elim
          (hnotMissing (hcomplete p.1 hpS p.2 hpT))
    rcases hopposite with hoppositeST | hoppositeTS
    · obtain ⟨P, hP⟩ :=
        opposite_path_missing_adjacent
          G S T hST p.1 p.2 hpS hpT hcrossAdj hnotMissing
          u v hoppositeST.1 hoppositeST.2 hadj
          n hScard hTcard hrank
      exact ⟨P, hP.trans hℓeq.symm⟩
    · have hcrossAdj' :
          ∀ x ∈ T, ∀ y ∈ S,
            (x ≠ p.2 ∨ y ≠ p.1) → G.Adj x y := by
        intro x hx y hy hneq
        apply (hcrossAdj y hy x hx ?_).symm
        rcases hneq with hxp | hyp
        · exact Or.inr hxp
        · exact Or.inl hyp
      obtain ⟨P, hP⟩ :=
        opposite_path_missing_adjacent
          G T S hST.symm p.2 p.1 hpT hpS hcrossAdj'
          (fun h => hnotMissing h.symm)
          u v hoppositeTS.1 hoppositeTS.2 hadj
          n hTcard hScard (by simpa [min_comm] using hrank)
      exact ⟨P, hP.trans hℓeq.symm⟩

end BipartitePaths

namespace BGLP

/--
The same-part path range needed from BGLP Lemma 3.1, proved directly.

The unrestricted short range is valid.  At terminal length `2r`, the
rank-two one-missing-edge exception is excluded by `hsafe`.
-/
theorem complete_bipartite_core_same_part_paths
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V)
    (hcore : IsCompleteBipartiteMinusAtMostOne G S T)
    (u v : V) (huv : u ≠ v)
    (hsame : (u ∈ S ∧ v ∈ S) ∨ (u ∈ T ∧ v ∈ T))
    (ℓ : ℕ)
    (hℓeven : Even ℓ)
    (hℓlo : 2 ≤ ℓ)
    (hallowed :
      ℓ ≤ 2 * min S.card T.card - 2 ∨
      (ℓ = 2 * min S.card T.card ∧
        ((u ∈ S ∧ v ∈ S ∧ min S.card T.card < S.card) ∨
         (u ∈ T ∧ v ∈ T ∧ min S.card T.card < T.card))))
    (hsafe :
      ℓ ≤ 2 * min S.card T.card - 2 ∨
      3 ≤ min S.card T.card ∨
      ∀ x ∈ S, ∀ y ∈ T, G.Adj x y) :
    ∃ P : SimplePath G u v, P.length = ℓ :=
  BipartitePaths.core_same_part_paths
    G S T hcore u v huv hsame ℓ hℓeven hℓlo hallowed hsafe

/--
The adjacent, opposite-part path range used from BGLP Lemma 3.1, proved
directly.  The rank-two one-missing-edge exception is excluded by `hsafe`.
-/
theorem complete_bipartite_core_opposite_part_paths
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V)
    (hcore : IsCompleteBipartiteMinusAtMostOne G S T)
    (u v : V) (huv : u ≠ v)
    (hopposite : (u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S))
    (hsafe :
      3 ≤ min S.card T.card ∨
      ∀ x ∈ S, ∀ y ∈ T, G.Adj x y)
    (ℓ : ℕ)
    (hℓodd : Odd ℓ)
    (hadj : G.Adj u v)
    (hℓhi : ℓ ≤ 2 * min S.card T.card - 1) :
    ∃ P : SimplePath G u v, P.length = ℓ :=
  BipartitePaths.core_opposite_part_paths
    G S T hcore u v huv hopposite hsafe ℓ hℓodd hadj hℓhi

end BGLP

end DeanK5
