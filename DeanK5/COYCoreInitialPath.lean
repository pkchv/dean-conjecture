import DeanK5.COYCores
import DeanK5.COYCoreStructure

/-!
# A fixed path to the initial side of a COY core

The singleton-boundary branch of COY Claim 3.12 joins the recursive
block paths to a fixed path in the core.  A boundary vertex belongs to
`{x} ∪ S`: it is either the root itself, is adjacent directly to the root
in a type-2 core, or is reached through one `T`-vertex in a type-3 core.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace Core

variable [DecidableEq V]
  {G : SimpleGraph V} {x : V} {ℓ : ℕ}

/--
A fixed root-to-`{x} ∪ S` path, together with its exact locality
certificate.
-/
structure InitialPathData
    (C : Core G x ℓ) (target : V) where
  /-- The selected path from the core root to `target`. -/
  path : SimplePath G x target
  /-- Every vertex of the selected path lies in the core carrier. -/
  support_subset :
    ∀ ⦃v : V⦄, v ∈ path.walk.support → v ∈ C.carrier

/--
Every vertex of `{x} ∪ S` is joined to the root by a path contained in
the core carrier.
-/
noncomputable def initialPathData
    (C : Core G x ℓ) (target : V)
    (htarget : target ∈ insert x C.S) :
    C.InitialPathData target := by
  classical
  by_cases htargetRoot : target = x
  · subst target
    exact {
      path := {
        walk := .nil
        isPath := .nil
      }
      support_subset := by
        intro v hv
        have hvx : v = x := by
          simpa using hv
        subst v
        exact C.root_mem_carrier
    }
  cases C with
  | typeOne C =>
      simp [Core.S, htargetRoot] at htarget
  | typeTwo C =>
      have htargetS : target ∈ C.S := by
        simpa [Core.S, htargetRoot] using htarget
      exact {
        path := SimplePath.ofAdj
          (C.root_adj_S target htargetS)
        support_subset := by
          intro v hv
          have hvClass : v = x ∨ v = target := by
            simpa using hv
          rcases hvClass with rfl | rfl
          · exact Core.root_mem_carrier (.typeTwo C)
          · exact Core.S_subset_carrier (.typeTwo C) htargetS
      }
  | typeThree C =>
      have htargetS : target ∈ C.S := by
        simpa [Core.S, htargetRoot] using htarget
      have hTNonempty : C.T.Nonempty := by
        rw [← Finset.card_pos]
        have htwo : 2 ≤ C.T.card :=
          (Nat.le_max_right (ℓ + 1) 2).trans
            C.card_T_lower
        omega
      let t : V := hTNonempty.choose
      have ht : t ∈ C.T := hTNonempty.choose_spec
      have hxt : x ≠ t :=
        (C.root_adj_T t ht).ne
      have htv : t ≠ target :=
        (C.cross_adj t ht target htargetS).ne
      have hxTarget : x ≠ target :=
        Ne.symm htargetRoot
      let P : SimplePath G x target :=
        SimplePath.ofVertexList [t]
          (by
            simp [C.root_adj_T t ht,
              C.cross_adj t ht target htargetS])
          (by simp [hxTarget, hxt, htv])
      exact {
        path := P
        support_subset := by
          intro v hv
          have hvClass :
              v = x ∨ v = t ∨ v = target := by
            simpa [P] using hv
          rcases hvClass with rfl | rfl | rfl
          · exact Core.root_mem_carrier (.typeThree C)
          · exact Core.T_subset_carrier (.typeThree C) ht
          · exact Core.S_subset_carrier
              (.typeThree C) htargetS
      }

/--
A fixed path from the root to an arbitrary vertex of the core carrier,
together with its locality certificate.
-/
structure CarrierPathData
    (C : Core G x ℓ) (target : V) where
  /-- The selected path from the core root to `target`. -/
  path : SimplePath G x target
  /-- Every vertex of the selected path lies in the core carrier. -/
  support_subset :
    ∀ ⦃v : V⦄, v ∈ path.walk.support → v ∈ C.carrier

/-- Every vertex of a COY core is reachable from its root inside the core. -/
noncomputable def carrierPathData
    (C : Core G x ℓ) (target : V)
    (htarget : target ∈ C.carrier) :
    C.CarrierPathData target := by
  classical
  by_cases htargetRoot : target = x
  · subst target
    exact {
      path := {
        walk := .nil
        isPath := .nil
      }
      support_subset := by
        intro v hv
        have hvx : v = x := by
          simpa using hv
        subst v
        exact C.root_mem_carrier
    }
  cases C with
  | typeOne C =>
      have htargetT : target ∈ C.T := by
        simpa [Core.carrier, Core.S, Core.T,
          htargetRoot] using htarget
      exact {
        path := SimplePath.ofAdj
          (C.root_adj target htargetT)
        support_subset := by
          intro v hv
          have hvClass : v = x ∨ v = target := by
            simpa using hv
          rcases hvClass with rfl | rfl
          · exact Core.root_mem_carrier (.typeOne C)
          · exact Core.T_subset_carrier
              (.typeOne C) htargetT
      }
  | typeTwo C =>
      have htargetClass :
          target ∈ C.S ∨ target ∈ C.T := by
        simpa [Core.carrier, Core.S, Core.T,
          htargetRoot] using htarget
      by_cases htargetS : target ∈ C.S
      · exact {
          path := SimplePath.ofAdj
            (C.root_adj_S target htargetS)
          support_subset := by
            intro v hv
            have hvClass : v = x ∨ v = target := by
              simpa using hv
            rcases hvClass with rfl | rfl
            · exact Core.root_mem_carrier (.typeTwo C)
            · exact Core.S_subset_carrier
                (.typeTwo C) htargetS
        }
      · have htargetT : target ∈ C.T :=
          htargetClass.resolve_left htargetS
        have hSNonempty : C.S.Nonempty := by
          rw [← Finset.card_pos, C.card_S]
          omega
        let s : V := hSNonempty.choose
        have hs : s ∈ C.S := hSNonempty.choose_spec
        have hxs : x ≠ s :=
          (C.root_adj_S s hs).ne
        have hst : s ≠ target :=
          (C.cross_adj s hs target htargetT).ne
        have hxTarget : x ≠ target :=
          Ne.symm htargetRoot
        let P : SimplePath G x target :=
          SimplePath.ofVertexList [s]
            (by
              simp [C.root_adj_S s hs,
                C.cross_adj s hs target htargetT])
            (by simp [hxTarget, hxs, hst])
        exact {
          path := P
          support_subset := by
            intro v hv
            have hvClass :
                v = x ∨ v = s ∨ v = target := by
              simpa [P] using hv
            rcases hvClass with rfl | rfl | rfl
            · exact Core.root_mem_carrier (.typeTwo C)
            · exact Core.S_subset_carrier
                (.typeTwo C) hs
            · exact Core.T_subset_carrier
                (.typeTwo C) htargetT
        }
  | typeThree C =>
      have htargetClass :
          target ∈ C.S ∨ target ∈ C.T := by
        simpa [Core.carrier, Core.S, Core.T,
          htargetRoot] using htarget
      by_cases htargetS : target ∈ C.S
      · have hTNonempty : C.T.Nonempty := by
          rw [← Finset.card_pos]
          have htwo : 2 ≤ C.T.card :=
            (Nat.le_max_right (ℓ + 1) 2).trans
              C.card_T_lower
          omega
        let t : V := hTNonempty.choose
        have ht : t ∈ C.T := hTNonempty.choose_spec
        have hxt : x ≠ t :=
          (C.root_adj_T t ht).ne
        have htv : t ≠ target :=
          (C.cross_adj t ht target htargetS).ne
        have hxTarget : x ≠ target :=
          Ne.symm htargetRoot
        let P : SimplePath G x target :=
          SimplePath.ofVertexList [t]
            (by
              simp [C.root_adj_T t ht,
                C.cross_adj t ht target htargetS])
            (by simp [hxTarget, hxt, htv])
        exact {
          path := P
          support_subset := by
            intro v hv
            have hvClass :
                v = x ∨ v = t ∨ v = target := by
              simpa [P] using hv
            rcases hvClass with rfl | rfl | rfl
            · exact Core.root_mem_carrier (.typeThree C)
            · exact Core.T_subset_carrier
                (.typeThree C) ht
            · exact Core.S_subset_carrier
                (.typeThree C) htargetS
        }
      · have htargetT : target ∈ C.T :=
          htargetClass.resolve_left htargetS
        exact {
          path := SimplePath.ofAdj
            (C.root_adj_T target htargetT)
          support_subset := by
            intro v hv
            have hvClass : v = x ∨ v = target := by
              simpa using hv
            rcases hvClass with rfl | rfl
            · exact Core.root_mem_carrier (.typeThree C)
            · exact Core.T_subset_carrier
                (.typeThree C) htargetT
        }

end Core

end COY

end DeanK5
