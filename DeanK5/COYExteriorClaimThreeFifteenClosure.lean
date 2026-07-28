import DeanK5.COYExteriorClaimThreeFifteenSetup
import DeanK5.COYExteriorClaimThreeFourteen
import DeanK5.COYPathOperations

/-!
# Closing the local recursion in COY Claim 3.15

This file isolates the two short conclusions that do not depend on how the
source recursive graph `B'` is encoded.

First, any strictly smaller rooted instance that maps injectively to an
`x`--`b` subgraph and whose paths avoid the tail of the fixed `b`--`y`
connector immediately contradicts minimality.  This is the common final
step in both cardinality cases of Claim 3.15(1).

Second, once Claim 3.15(1) is known, the selected exterior cannot itself be
the chosen block.  This is Claim 3.15(2), using Claim 3.14(2) and the
terminal-attachment exclusion from Claim 3.12(1).
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/--
The source conclusion in Claim 3.15(1), expressed using the anchored block
interface: `B-b` contains `y` or the second selected exception.
-/
def MeetsProtectedInterior
    (C : P.ExteriorFeasibleBlockChoice) : Prop :=
  y ∈ C.compressionInterior ∨
    C.zPrime ∈ C.compressionInterior

/-- The chosen block spans the entire selected exterior component. -/
def SpansExterior
    (C : P.ExteriorFeasibleBlockChoice) : Prop :=
  C.ambientCarrier =
    P.working.rooted.otherRegion

/--
The common induction-and-connector closure for the two recursive graphs
`B'` in Claim 3.15(1).

The hypotheses name exactly what the concrete construction must prove:
a valid smaller rooted instance, an injective homomorphism back to the
ambient graph taking its roots to `x,b`, and support separation from the
fixed connector.
-/
theorem false_of_claimThreeFifteen_recursiveInstance
    (M : MinimalCounterexample q G x y z)
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {a b e : W}
    (I : RootedInstance q H a b e)
    (hsmaller :
      rootedComplexity H < rootedComplexity G)
    (f : H →g G)
    (hinjective : Function.Injective f)
    (hleft : f a = x)
    (connector : SimplePath G (f b) y)
    (hdisjoint :
      ∀ Q : SimplePath H a b,
        (Q.mapInjectiveHom f hinjective).walk.support.Disjoint
          connector.walk.support.tail) :
    False := by
  obtain ⟨F⟩ :=
    M.smaller_solvable I hsmaller
  let mapped :
      AdmissiblePathFamily G (f a) (f b) q :=
    F.mapInjectiveHom f hinjective
  let appendedRaw :
      AdmissiblePathFamily G (f a) y q :=
    mapped.appendFixed connector (by
      intro i
      exact hdisjoint (F.path i))
  let appended :
      AdmissiblePathFamily G x y q := by
    simpa [hleft] using appendedRaw
  exact M.no_paths ⟨appended⟩

/-- If the chosen block spans the exterior, its anchor is `y`. -/
theorem b_eq_y_of_spansExterior
    (C : P.ExteriorFeasibleBlockChoice)
    (hspan : C.SpansExterior) :
    C.b = y := by
  have hyCarrier : y ∈ C.ambientCarrier := by
    rw [hspan]
    exact P.working.rooted.other_root_mem_otherRegion
  have hySupport :
      y ∈ C.pathToY.walk.support := by
    simp
  have hyEq :
      y = C.b :=
    C.pathToY_meets_block_only_at_b
      hySupport
      (by
        rw [C.mem_ambientCarrier] at hyCarrier
        obtain ⟨w, hw, hwVal⟩ := hyCarrier
        exact ⟨w, hw, hwVal⟩)
  exact hyEq.symm

/--
Claim 3.15(2), conditional only on the already established conclusion of
part (1): the selected exterior cannot itself be the chosen block.
-/
theorem not_spansExterior_of_meetsProtectedInterior
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (C : P.ExteriorFeasibleBlockChoice)
    (hpartOne : C.MeetsProtectedInterior) :
    ¬C.SpansExterior := by
  intro hspan
  have hby : C.b = y :=
    C.b_eq_y_of_spansExterior hspan
  have hyNotInterior :
      y ∉ C.compressionInterior := by
    simpa [hby] using C.b_not_mem_compressionInterior
  have hzPrimeInterior :
      C.zPrime ∈ C.compressionInterior :=
    hpartOne.resolve_left hyNotInterior
  have hzPrimeNeY :
      C.zPrime ≠ y := by
    intro h
    apply hyNotInterior
    simpa [h] using hzPrimeInterior
  have hzPrimeProtected :
      C.anchor.zPrime ∈ P.exteriorProtected := by
    rcases Finset.mem_union.mp
        C.anchor.zPrime_special with
      hcut | hprotected
    · have hwhole :
          C.block.carrier = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro w
        have hwAmbient :
            w.1 ∈ C.ambientCarrier := by
          rw [hspan]
          exact w.2
        rw [C.mem_ambientCarrier] at hwAmbient
        obtain ⟨w', hw', hwValue⟩ := hwAmbient
        have hww' : w' = w := by
          apply Subtype.ext
          exact hwValue
        simpa [hww'] using hw'
      have hordinaryNe :
          C.anchor.ordinary ≠ C.anchor.zPrime := by
        intro h
        apply C.anchor.ordinary_not_special
        exact h ▸ C.anchor.zPrime_special
      have hsurvives :
          Nonempty
            {w : P.ExteriorVertex //
              w ≠ C.anchor.zPrime} :=
        ⟨⟨C.anchor.ordinary, hordinaryNe⟩⟩
      have hdelete :=
        C.block.delete_connected C.anchor.zPrime_mem
      rw [hwhole] at hdelete
      have hset :
          (↑((Finset.univ :
              Finset P.ExteriorVertex).erase
                C.anchor.zPrime) :
            Set P.ExteriorVertex) =
              {w | w ≠ C.anchor.zPrime} := by
        ext w
        simp
      rw [hset] at hdelete
      have hnotCut :
          ¬IsCutVertex P.exteriorGraph
            C.anchor.zPrime := by
        apply
          (not_isCutVertex_iff_delete_connected
            P.exteriorGraph C.anchor.zPrime
            P.exteriorGraph_connected
            hsurvives).2
        change
          (P.exteriorGraph.induce
            {w |
              w ∉ ({C.anchor.zPrime} :
                Finset P.ExteriorVertex)}).Connected
        have hset' :
            {w : P.ExteriorVertex |
              w ∉ ({C.anchor.zPrime} :
                Finset P.ExteriorVertex)} =
                {w | w ≠ C.anchor.zPrime} := by
          ext w
          simp
        rw [hset']
        exact hdelete
      exact False.elim
        (hnotCut
          ((mem_cutVertices_iff
            P.exteriorGraph C.anchor.zPrime).1 hcut))
    · exact hprotected
  have hzPrimeEqZ :
      C.zPrime = z := by
    have hprotected :=
      P.mem_exteriorProtected.mp hzPrimeProtected
    rcases hprotected with hEqY | hEqZ
    · exact False.elim (hzPrimeNeY hEqY)
    · exact hEqZ
  have hzRegion :
      z ∈ P.working.rooted.otherRegion := by
    have hzPrimeRegion :
        C.zPrime ∈ P.working.rooted.otherRegion :=
      C.ambientCarrier_subset_otherRegion
      (Finset.mem_of_mem_erase hzPrimeInterior)
    exact
      Eq.mp
        (congrArg
          (fun v =>
            v ∈ P.working.rooted.otherRegion)
          hzPrimeEqZ)
        hzPrimeRegion
  obtain ⟨s, hS, -⟩ :=
    C.exists_claimThreeFifteen_boundary_data M D
  obtain ⟨a, haErase, t, htT, hta⟩ :=
    P.exists_T_attachment_in_otherRegion_erase_y
      M D.core D.core_eq hS
      (P.otherRegion_ne_singleton M) hzRegion
  have haRegion :
      a ∈ P.working.rooted.otherRegion :=
    Finset.mem_of_mem_erase haErase
  have haNeY : a ≠ y :=
    (Finset.mem_erase.mp haErase).1
  have haCarrier : a ∈ C.ambientCarrier := by
    rw [hspan]
    exact haRegion
  have haInterior : a ∈ C.compressionInterior := by
    exact Finset.mem_erase.mpr
      ⟨by simpa [hby] using haNeY, haCarrier⟩
  have htWorking :
      t ∈ P.working.rooted.core.T := by
    simpa [D.core_eq, Core.T] using htT
  have htAttachment :
      t ∈ C.terminalAttachments := by
    classical
    change
      t ∈ P.working.rooted.core.T.filter
        (fun t =>
          ∃ d ∈ C.compressionInterior, G.Adj t d)
    exact Finset.mem_filter.mpr
      ⟨htWorking, ⟨a, haInterior, hta⟩⟩
  rw [C.terminalAttachments_eq_empty M] at htAttachment
  simp at htAttachment

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
