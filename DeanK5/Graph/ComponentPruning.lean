import DeanK5.Graph.Connectivity

/-!
# Pruning a component behind a rooted boundary

Suppose `Q` is a component region of `G - S`.  This file proves that a
2-connected rooted graph on the boundary `S` remains 2-connected after
all vertices outside `Q` are restored.  The proof treats connectivity and
every one-vertex deletion explicitly.  Paths in the ambient graph are
followed only until they first meet `S`; component closure guarantees that
these initial segments avoid `Q`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace ComponentPruning

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {S Q : Finset V} {a b : V}

/-- The carrier left after pruning the component region `Q`. -/
abbrev Outside (Q : Finset V) :=
  {v : V // v ∉ Q}

/-- A boundary vertex survives pruning because component and separator are disjoint. -/
def boundaryVertex
    (hQ : ComponentRegion G S Q)
    (v : V) (hvS : v ∈ S) :
    Outside Q :=
  ⟨v, fun hvQ => hQ.not_mem_separator hvQ hvS⟩

omit [Fintype V] in
@[simp] theorem boundaryVertex_val
    (hQ : ComponentRegion G S Q)
    (v : V) (hvS : v ∈ S) :
    (boundaryVertex hQ v hvS : V) = v :=
  rfl

/--
The inclusion of the separator carrier into the carrier left after pruning.
-/
def boundaryEmbedding
    (hQ : ComponentRegion G S Q) :
    (↑S : Set V) ↪ Outside Q where
  toFun v := boundaryVertex hQ v.1 v.2
  inj' := by
    intro x y h
    exact Subtype.ext
      (congrArg (fun z : Outside Q => z.1) h)

/--
The rooted boundary graph embeds into the rooted graph left after pruning.
-/
def rootedBoundaryHom
    (hQ : ComponentRegion G S Q)
    (haS : a ∈ S) (hbS : b ∈ S) :
    (G.induce (↑S : Set V) ⊔
      edge (⟨a, haS⟩ : (↑S : Set V)) ⟨b, hbS⟩) →g
      (G.induce {v | v ∉ Q} ⊔
        edge (boundaryVertex hQ a haS)
          (boundaryVertex hQ b hbS)) where
  toFun := boundaryEmbedding hQ
  map_rel' := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact Or.inl hxy
    · right
      rw [SimpleGraph.edge_adj] at hxy ⊢
      refine ⟨?_, ?_⟩
      · rcases hxy.1 with hxy | hxy
        · left
          exact ⟨congrArg (boundaryEmbedding hQ) hxy.1,
            congrArg (boundaryEmbedding hQ) hxy.2⟩
        · right
          exact ⟨congrArg (boundaryEmbedding hQ) hxy.1,
            congrArg (boundaryEmbedding hQ) hxy.2⟩
      · exact fun heq =>
          hxy.2 ((boundaryEmbedding hQ).injective heq)

omit [Fintype V] in
/-- The boundary embedding is injective. -/
theorem rootedBoundaryHom_injective
    (hQ : ComponentRegion G S Q)
    (haS : a ∈ S) (hbS : b ∈ S) :
    Function.Injective (rootedBoundaryHom hQ haS hbS) :=
  (boundaryEmbedding hQ).injective

/--
Pruning one component region preserves rooted 2-connectivity when the
separator itself is rooted 2-connected.

The endpoint proofs in the conclusion are canonical consequences of
`hQ.disjoint`; callers do not need to provide them separately.
-/
theorem rooted_two_connected
    (hG : IsTwoConnected G)
    (hQ : ComponentRegion G S Q)
    (haS : a ∈ S) (hbS : b ∈ S)
    (hboundary :
      IsTwoConnected
        (G.induce (↑S : Set V) ⊔
          edge (⟨a, haS⟩ : (↑S : Set V)) ⟨b, hbS⟩)) :
    IsTwoConnected
      (G.induce {v | v ∉ Q} ⊔
        edge (boundaryVertex hQ a haS)
          (boundaryVertex hQ b hbS)) := by
  classical
  let BS : SimpleGraph (↑S : Set V) :=
    G.induce (↑S : Set V) ⊔
      edge (⟨a, haS⟩ : (↑S : Set V)) ⟨b, hbS⟩
  let U : Set V := {v | v ∉ Q}
  let H : SimpleGraph U :=
    G.induce U ⊔
      edge (boundaryVertex hQ a haS)
        (boundaryVertex hQ b hbS)
  let ι := rootedBoundaryHom hQ haS hbS
  have hι_injective : Function.Injective ι :=
    rootedBoundaryHom_injective hQ haS hbS
  have horder : 3 ≤ Fintype.card U := by
    exact hboundary.1.trans
      (Fintype.card_le_of_injective ι hι_injective)
  have hGconnected : G.Connected := by
    have h :=
      hG.2 (∅ : Finset V) (by simp)
    have hset :
        {v : V | v ∉ (∅ : Finset V)} =
          (Set.univ : Set V) := by
      ext v
      simp
    rw [hset] at h
    exact (G.induceUnivIso.connected_iff).1 h
  have hBSconnected : BS.Connected := by
    have h :=
      hboundary.2 (∅ : Finset (↑S : Set V)) (by simp)
    have hset :
        {v : (↑S : Set V) |
            v ∉ (∅ : Finset (↑S : Set V))} =
          (Set.univ : Set (↑S : Set V)) := by
      ext v
      simp
    rw [hset] at h
    exact (BS.induceUnivIso.connected_iff).1 h
  have hconnected : H.Connected := by
    let aS : (↑S : Set V) := ⟨a, haS⟩
    let aU : U := ι aS
    let rec reachBoundary
        {v : V} (hvQ : v ∉ Q)
        (p : G.Walk v a) :
        ∃ s : (↑S : Set V),
          H.Reachable (⟨v, hvQ⟩ : U) (ι s) := by
      by_cases hvS : v ∈ S
      · let vS : (↑S : Set V) := ⟨v, hvS⟩
        exact ⟨vS, by
          have heq : (⟨v, hvQ⟩ : U) = ι vS := by
            apply Subtype.ext
            rfl
          rw [heq]⟩
      · cases p with
        | nil =>
            exact False.elim (hvS haS)
        | @cons _ w _ hvw p =>
            have hwQ : w ∉ Q := by
              intro hwQ
              exact hvQ (hQ.closed hwQ hvw.symm hvS)
            obtain ⟨s, hs⟩ := reachBoundary hwQ p
            have hvwH :
                H.Adj (⟨v, hvQ⟩ : U) (⟨w, hwQ⟩ : U) :=
              Or.inl hvw
            exact ⟨s, hvwH.reachable.trans hs⟩
    rw [connected_iff_exists_forall_reachable]
    refine ⟨aU, ?_⟩
    intro v
    obtain ⟨p⟩ := hGconnected.preconnected v.1 a
    obtain ⟨s, hvs⟩ := reachBoundary v.2 p
    have hsa : BS.Reachable s aS :=
      hBSconnected.preconnected s aS
    have hsaH : H.Reachable (ι s) aU := by
      exact hsa.map ι
    exact (hvs.trans hsaH).symm
  apply isTwoConnected_of_connected_delete_one H horder hconnected
  intro r
  let W : Set U := {v | v ≠ r}
  let HD : SimpleGraph W := H.induce W
  have coreReach :
      ∀ (s t : (↑S : Set V))
        (hsr : ι s ≠ r) (htr : ι t ≠ r),
        HD.Reachable
          (⟨ι s, hsr⟩ : W)
          (⟨ι t, htr⟩ : W) := by
    intro s t hsr htr
    by_cases hrS : r.1 ∈ S
    · let rS : (↑S : Set V) := ⟨r.1, hrS⟩
      have hιrS : ι rS = r := by
        apply Subtype.ext
        rfl
      have hsne : s ≠ rS := by
        intro h
        exact hsr (h ▸ hιrS)
      have htne : t ≠ rS := by
        intro h
        exact htr (h ▸ hιrS)
      have hdeleted :=
        hboundary.2 ({rS} : Finset (↑S : Set V)) (by simp)
      let f :
          BS.induce {v | v ∉ ({rS} : Finset (↑S : Set V))} →g
            HD := {
        toFun v := ⟨ι v.1, by
          intro h
          have hir : ι v.1 = r := h
          exact v.2 (by
            simp only [Finset.mem_singleton]
            apply hι_injective
            rw [hir, hιrS])⟩
        map_rel' := by
          intro u v huv
          exact ι.map_rel' huv
      }
      have hreach :=
        hdeleted.preconnected
          (⟨s, by simpa using hsne⟩ :
            {v : (↑S : Set V) // v ∉ ({rS} : Finset _)})
          (⟨t, by simpa using htne⟩ :
            {v : (↑S : Set V) // v ∉ ({rS} : Finset _)})
      simpa [f] using hreach.map f
    · let f : BS →g HD := {
        toFun v := ⟨ι v, by
          intro h
          apply hrS
          have hval :=
            congrArg (fun z : Outside Q => z.1) h
          have hιval : (ι v).1 = v.1 := rfl
          exact (hιval.symm.trans hval) ▸ v.2⟩
        map_rel' := by
          intro u v huv
          exact ι.map_rel' huv
      }
      have hreach :=
        hBSconnected.preconnected s t
      simpa [f] using hreach.map f
  have hsurvivingBoundary :
      ∃ t : (↑S : Set V), ι t ≠ r := by
    by_cases hrS : r.1 ∈ S
    · let rS : (↑S : Set V) := ⟨r.1, hrS⟩
      have hproper :
          ({rS} : Finset (↑S : Set V)) ⊂ Finset.univ := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.subset_univ _, ?_⟩
        intro h
        have hcard :
            Fintype.card (↑S : Set V) = 1 := by
          rw [← Finset.card_univ, ← h]
          simp
        have := hboundary.1
        omega
      obtain ⟨t, -, ht⟩ :=
        Finset.exists_of_ssubset hproper
      refine ⟨t, ?_⟩
      intro hit
      have htrS : t = rS := by
        apply hι_injective
        exact hit.trans (by
          apply Subtype.ext
          rfl)
      exact ht (by simp [htrS])
    · refine ⟨(⟨a, haS⟩ : (↑S : Set V)), ?_⟩
      intro h
      apply hrS
      have hval :=
        congrArg (fun z : Outside Q => z.1) h
      exact hval ▸ haS
  obtain ⟨t, htr⟩ := hsurvivingBoundary
  let tD : {v : V // v ≠ r.1} :=
    ⟨t.1, by
      intro h
      apply htr
      apply Subtype.ext
      exact h⟩
  let tH : W := ⟨ι t, htr⟩
  have hGdeleted :
      (G.induce {v | v ≠ r.1}).Connected := by
    have h :=
      hG.2 ({r.1} : Finset V) (by simp)
    have hset :
        {v : V | v ∉ ({r.1} : Finset V)} =
          {v : V | v ≠ r.1} := by
      ext v
      simp
    rw [hset] at h
    exact h
  let rec reachBoundaryDeleted
      {v : V} (hvQ : v ∉ Q) (hvr : v ≠ r.1)
      (p : G.Walk v t.1)
      (havoid : ∀ w ∈ p.support, w ≠ r.1) :
      ∃ s : (↑S : Set V), ∃ hsr : ι s ≠ r,
        HD.Reachable
          (⟨⟨v, hvQ⟩, by
            intro h
            exact hvr (congrArg
              (fun z : U => z.1) h)⟩ : W)
          ⟨ι s, hsr⟩ := by
    by_cases hvS : v ∈ S
    · let vS : (↑S : Set V) := ⟨v, hvS⟩
      have hvr' : ι vS ≠ r := by
        intro h
        exact hvr (congrArg Subtype.val h)
      refine ⟨vS, hvr', ?_⟩
      have heq :
          (⟨⟨v, hvQ⟩, by
            intro h
            exact hvr (congrArg
              (fun z : U => z.1) h)⟩ : W) =
            ⟨ι vS, hvr'⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      rw [heq]
    · cases p with
      | nil =>
          exact False.elim (hvS t.2)
      | @cons _ w _ hvw p =>
          have hwQ : w ∉ Q := by
            intro hwQ
            exact hvQ (hQ.closed hwQ hvw.symm hvS)
          have hwr : w ≠ r.1 :=
            havoid w (by simp)
          have htail :
              ∀ z ∈ p.support, z ≠ r.1 := by
            intro z hz
            exact havoid z (by simp [hz])
          obtain ⟨s, hsr, hs⟩ :=
            reachBoundaryDeleted hwQ hwr p htail
          have hvwHD :
              HD.Adj
                (⟨⟨v, hvQ⟩, by
                  intro h
                  exact hvr (congrArg
                    (fun z : U => z.1) h)⟩ : W)
                (⟨⟨w, hwQ⟩, by
                  intro h
                  exact hwr (congrArg
                    (fun z : U => z.1) h)⟩ : W) :=
            Or.inl hvw
          exact ⟨s, hsr, hvwHD.reachable.trans hs⟩
  change HD.Connected
  rw [connected_iff_exists_forall_reachable]
  refine ⟨tH, ?_⟩
  intro v
  let vD : {w : V // w ≠ r.1} :=
    ⟨v.1.1, by
      intro h
      apply v.2
      apply Subtype.ext
      exact h⟩
  obtain ⟨p⟩ :=
    hGdeleted.preconnected vD tD
  let pG : G.Walk v.1.1 t.1 :=
    p.map (Embedding.induce {w : V | w ≠ r.1}).toHom
  have havoid :
      ∀ w ∈ pG.support, w ≠ r.1 := by
    intro w hw
    change w ∈
      (p.map (Embedding.induce
        {w : V | w ≠ r.1}).toHom).support at hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hw
    change z.1 = w at hzw
    exact hzw ▸ z.2
  obtain ⟨s, hsr, hvs⟩ :=
    reachBoundaryDeleted v.1.2 vD.2 pG havoid
  have hst := coreReach s t hsr htr
  exact hst.symm.trans hvs.symm

end ComponentPruning

end DeanK5
