import DeanK5.Graph.FeasibleBlockAnchor

/-!
# Block anchors avoiding a prescribed non-cut vertex

If deleting a vertex leaves a connected graph and that vertex lies outside
a block, the block can be re-anchored toward a target by a connector that
avoids the deleted vertex.  The connector is chosen by minimizing distance
to the block in the deletion graph.  This is the precise graph-theoretic
step used when COY enlarges its temporary core by one exterior vertex.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace GraphBlock

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/--
Choose a connector from a block to `target` that avoids a prescribed
non-cut vertex outside the block.
-/
theorem exists_anchor_path_to_avoiding
    (hconnected : G.Connected)
    (B : GraphBlock G) (target avoid : V)
    (havoidCarrier : avoid ∉ B.carrier)
    (havoidTarget : avoid ≠ target)
    (havoidNotCut : ¬IsCutVertex G avoid) :
    ∃ (b : V) (R : SimplePath G b target),
      b ∈ B.carrier ∧
        (b = target ∨ IsCutVertex G b) ∧
          (∀ ⦃v : V⦄, v ∈ R.walk.support →
            v ∈ B.carrier → v = b) ∧
          avoid ∉ R.walk.support := by
  classical
  let surviving : Set V :=
    {v | v ∉ ({avoid} : Finset V)}
  let D : SimpleGraph surviving :=
    deleteVertices G {avoid}
  let target' : surviving :=
    ⟨target, by simpa [surviving] using havoidTarget.symm⟩
  have hsurvives : Nonempty {w : V // w ≠ avoid} :=
    ⟨⟨target, havoidTarget.symm⟩⟩
  have hdelete : D.Connected := by
    exact
      (not_isCutVertex_iff_delete_connected
        G avoid hconnected hsurvives).1 havoidNotCut
  let survivor (v : V) : surviving :=
    if hv : v ∈ surviving then
      ⟨v, hv⟩
    else
      target'
  let distanceToTarget (v : V) : ℕ :=
    D.dist target' (survivor v)
  have hcarrierNonempty : B.carrier.Nonempty :=
    Finset.card_pos.mp (by
      have := B.card_ge_two
      omega)
  obtain ⟨b, hbCarrier, hbMinimal⟩ :=
    Finset.exists_min_image B.carrier
      distanceToTarget hcarrierNonempty
  have hbAvoid : b ∈ surviving := by
    change b ∉ ({avoid} : Finset V)
    simpa using fun hba : b = avoid =>
      havoidCarrier (hba ▸ hbCarrier)
  let b' : surviving := ⟨b, hbAvoid⟩
  have hsurvivorB : survivor b = b' := by
    apply Subtype.ext
    simp [survivor, hbAvoid, b']
  obtain ⟨p, hpPath, hpLength⟩ :=
    hdelete.exists_path_of_dist target' b'
  let inclusion : D →g G :=
    (Embedding.induce surviving).toHom
  let mapped : G.Walk target b :=
    p.map inclusion
  let R : SimplePath G b target := {
    walk := mapped.reverse
    isPath := hpPath.map Subtype.val_injective |>.reverse
  }
  have havoidR : avoid ∉ R.walk.support := by
    intro havoid
    have hmapped :
        avoid ∈ mapped.support := by
      simpa [R, SimpleGraph.Walk.support_reverse] using
        havoid
    change avoid ∈ (p.map inclusion).support at hmapped
    rw [SimpleGraph.Walk.support_map] at hmapped
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hmapped
    change w.1 = avoid at hw
    exact w.2 (by simp [surviving, hw])
  have hmeet :
      ∀ ⦃v : V⦄, v ∈ R.walk.support →
        v ∈ B.carrier → v = b := by
    intro v hvSupport hvCarrier
    by_contra hvb
    have hvMapped :
        v ∈ mapped.support := by
      simpa [R, SimpleGraph.Walk.support_reverse] using
        hvSupport
    change v ∈ (p.map inclusion).support at hvMapped
    rw [SimpleGraph.Walk.support_map] at hvMapped
    obtain ⟨w, hwSupport, hwv⟩ :=
      List.mem_map.mp hvMapped
    change w.1 = v at hwv
    have hwCarrier : w.1 ∈ B.carrier := by
      simpa [hwv] using hvCarrier
    have hsurvivorW : survivor w.1 = w := by
      apply Subtype.ext
      simp only [survivor, dif_pos w.2]
    have hminimal :
        D.dist target' b' ≤ D.dist target' w := by
      have h :=
        hbMinimal w.1 hwCarrier
      dsimp [distanceToTarget] at h
      rw [hsurvivorB, hsurvivorW] at h
      exact h
    have hwb : w ≠ b' := by
      intro h
      apply hvb
      exact hwv.symm.trans (congrArg Subtype.val h)
    have htakeLength :
        (p.takeUntil w hwSupport).length =
          D.dist target' w :=
      length_eq_dist_of_subwalk hpLength
        (p.isSubwalk_takeUntil hwSupport)
    have hstrict :
        (p.takeUntil w hwSupport).length < p.length :=
      p.length_takeUntil_lt_length hwSupport hwb
    omega
  have hbTargetOrCut :
      b = target ∨ IsCutVertex G b := by
    by_cases hbTarget : b = target
    · exact Or.inl hbTarget
    · right
      obtain ⟨a, hba, tail, hreverse⟩ :=
        R.walk.exists_eq_cons_of_ne hbTarget
      have haSupport : a ∈ R.walk.support := by
        rw [hreverse]
        simp
      have haOutside : a ∉ B.carrier := by
        intro haCarrier
        have hab : a = b :=
          hmeet haSupport haCarrier
        exact hba.ne hab.symm
      exact B.isCutVertex_of_adj_outside
        hconnected hbCarrier hba haOutside
  exact ⟨b, R, hbCarrier, hbTargetOrCut, hmeet, havoidR⟩

/--
Complete a prescribed block connector to the standard feasible-anchor
package.
-/
theorem exists_feasibleBlockAnchor_of_path
    (marked : Finset V)
    (B : GraphBlock G) (target : V)
    (htarget : target ∈ marked)
    (hfeasible : IsFeasibleBlock G marked B)
    (b : V) (pathToTarget : SimplePath G b target)
    (hbCarrier : b ∈ B.carrier)
    (hbTargetOrCut : b = target ∨ IsCutVertex G b)
    (hpathMeet :
      ∀ ⦃v : V⦄, v ∈ pathToTarget.walk.support →
        v ∈ B.carrier → v = b) :
    ∃ A : FeasibleBlockAnchor G marked B target,
      A.pathToTarget.walk.support =
        pathToTarget.walk.support := by
  classical
  let special :=
    B.carrier ∩ (cutVertices G ∪ marked)
  have hbSpecial : b ∈ cutVertices G ∪ marked := by
    rcases hbTargetOrCut with hbTarget | hbCut
    · exact Finset.mem_union_right _ (hbTarget ▸ htarget)
    · exact Finset.mem_union_left _ (by simpa using hbCut)
  have hbSpecialCarrier : b ∈ special :=
    Finset.mem_inter.mpr ⟨hbCarrier, hbSpecial⟩
  let remaining := special.erase b
  have hremainingCard : remaining.card ≤ 1 := by
    have hspecialCard : special.card ≤ 2 := by
      exact hfeasible.1
    rw [show remaining = special.erase b by rfl,
      Finset.card_erase_of_mem hbSpecialCarrier]
    omega
  obtain ⟨ordinary, hordinary⟩ := hfeasible.2
  have hordinaryCarrier : ordinary ∈ B.carrier :=
    (Finset.mem_sdiff.mp hordinary).1
  have hordinaryNotSpecial :
      ordinary ∉ cutVertices G ∪ marked :=
    (Finset.mem_sdiff.mp hordinary).2
  by_cases hremaining : remaining.Nonempty
  · let zPrime := hremaining.choose
    have hzRemaining : zPrime ∈ remaining :=
      hremaining.choose_spec
    have hzSpecialCarrier : zPrime ∈ special :=
      Finset.mem_of_mem_erase hzRemaining
    have hzSpecial : zPrime ∈ cutVertices G ∪ marked :=
      (Finset.mem_inter.mp hzSpecialCarrier).2
    exact ⟨{
      b := b
      zPrime := zPrime
      ordinary := ordinary
      b_mem := hbCarrier
      zPrime_mem := (Finset.mem_inter.mp hzSpecialCarrier).1
      b_eq_target_or_cut := hbTargetOrCut
      b_special := hbSpecial
      zPrime_special := hzSpecial
      special_subset := by
        intro v hvSpecial
        by_cases hvb : v = b
        · simp [hvb]
        · have hvRemaining : v ∈ remaining := by
            exact Finset.mem_erase.mpr ⟨hvb, hvSpecial⟩
          have hvz : v = zPrime :=
            Finset.card_le_one.mp hremainingCard
              v hvRemaining zPrime hzRemaining
          simp [hvz]
      ordinary_mem := hordinaryCarrier
      ordinary_not_special := hordinaryNotSpecial
      pathToTarget := pathToTarget
      path_meets_carrier_only_at_b := hpathMeet
    }, rfl⟩
  · have hremainingEmpty : remaining = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hremaining
    exact ⟨{
      b := b
      zPrime := b
      ordinary := ordinary
      b_mem := hbCarrier
      zPrime_mem := hbCarrier
      b_eq_target_or_cut := hbTargetOrCut
      b_special := hbSpecial
      zPrime_special := hbSpecial
      special_subset := by
        intro v hvSpecial
        have hvb : v = b := by
          by_contra hvb
          have hvRemaining : v ∈ remaining :=
            Finset.mem_erase.mpr ⟨hvb, hvSpecial⟩
          rw [hremainingEmpty] at hvRemaining
          simp at hvRemaining
        simp [hvb]
      ordinary_mem := hordinaryCarrier
      ordinary_not_special := hordinaryNotSpecial
      pathToTarget := pathToTarget
      path_meets_carrier_only_at_b := hpathMeet
    }, rfl⟩

/--
A feasible block admits a full anchor package whose connector avoids a
prescribed non-cut vertex outside the block.
-/
theorem exists_feasibleBlockAnchor_avoiding
    (hconnected : G.Connected)
    (marked : Finset V)
    (B : GraphBlock G) (target avoid : V)
    (htarget : target ∈ marked)
    (hfeasible : IsFeasibleBlock G marked B)
    (havoidCarrier : avoid ∉ B.carrier)
    (havoidTarget : avoid ≠ target)
    (havoidNotCut : ¬IsCutVertex G avoid) :
    ∃ A : FeasibleBlockAnchor G marked B target,
      avoid ∉ A.pathToTarget.walk.support := by
  obtain
      ⟨b, pathToTarget, hbCarrier,
        hbTargetOrCut, hpathMeet, havoidPath⟩ :=
    B.exists_anchor_path_to_avoiding
      hconnected target avoid havoidCarrier
        havoidTarget havoidNotCut
  obtain ⟨A, hpath⟩ :=
    B.exists_feasibleBlockAnchor_of_path
      marked target htarget hfeasible
      b pathToTarget hbCarrier hbTargetOrCut hpathMeet
  refine ⟨A, ?_⟩
  rw [hpath]
  exact havoidPath

end GraphBlock

end DeanK5
