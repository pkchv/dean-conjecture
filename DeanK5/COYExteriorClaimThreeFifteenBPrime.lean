import DeanK5.COYExteriorClaimThreeFifteenSetup
import DeanK5.Graph.NonseparableRootAdjunction
import DeanK5.Graph.RootAdjunction

/-!
# The two recursive graphs in COY Claim 3.15(1)

This file gives a typed version of the first source graph `B'`.
`singleBPrime` is `G[B ∪ {x}]`, used when the unique `S`-vertex has
exactly one block neighbour.

The graph is expressed by adjoining the core root to the induced block
graph.  Its canonical homomorphism into `G` is injective, and the artificial
edge from `x` to `b` makes it 2-connected.  The remaining Claim 3.15
obligation is the degree ledger for its nonexceptional block vertices.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s : V}
  {P : PreferredWorkingCoreData G x y z}

/-- Vertices of the selected block, typed in the ambient graph. -/
abbrev BPrimeBlockVertex
    (C : P.ExteriorFeasibleBlockChoice) :=
  (↑C.ambientCarrier : Set V)

/-- The graph induced by the selected block in the ambient graph. -/
abbrev bPrimeBlockGraph
    (C : P.ExteriorFeasibleBlockChoice) :
    SimpleGraph C.BPrimeBlockVertex :=
  G.induce (↑C.ambientCarrier : Set V)

/-- A named ambient vertex, viewed as the anchor inside the block graph. -/
def bPrimeAnchor
    (C : P.ExteriorFeasibleBlockChoice) :
    C.BPrimeBlockVertex :=
  ⟨C.b, C.b_mem_ambientCarrier⟩

/-- Actual neighbours of `v` in the selected block, on the block subtype. -/
noncomputable def bPrimeAttachments
    (C : P.ExteriorFeasibleBlockChoice) (v : V) :
    Finset C.BPrimeBlockVertex := by
  classical
  exact Finset.univ.filter fun d => G.Adj v d.1

@[simp] theorem mem_bPrimeAttachments
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} {d : C.BPrimeBlockVertex} :
    d ∈ C.bPrimeAttachments v ↔ G.Adj v d.1 := by
  classical
  simp [bPrimeAttachments]

/-- The block-subtype attachment count equals the ambient finite-set count. -/
theorem card_bPrimeAttachments
    (C : P.ExteriorFeasibleBlockChoice) (v : V) :
    (C.bPrimeAttachments v).card =
      (C.blockNeighbors v).card := by
  classical
  apply Finset.card_bij
      (fun d _ => d.1)
  · intro d hd
    exact C.mem_blockNeighbors.mpr
      ⟨d.2, C.mem_bPrimeAttachments.mp hd⟩
  · intro d₁ hd₁ d₂ hd₂ h
    exact Subtype.ext h
  · intro d hd
    exact
      ⟨⟨d, (C.mem_blockNeighbors.mp hd).1⟩,
        C.mem_bPrimeAttachments.mpr
          (C.mem_blockNeighbors.mp hd).2,
        rfl⟩

/-- The canonical inclusion of the induced block graph into `G`. -/
def bPrimeBlockEmbedding
    (C : P.ExteriorFeasibleBlockChoice) :
    C.bPrimeBlockGraph ↪g G :=
  Embedding.induce (↑C.ambientCarrier : Set V)

/-- The source graph `G[B ∪ {x}]`. -/
noncomputable def singleBPrime
    (C : P.ExteriorFeasibleBlockChoice) :
    SimpleGraph (Option C.BPrimeBlockVertex) :=
  adjoinRoot C.bPrimeBlockGraph
    (C.bPrimeAttachments x)

/-- Its left root, representing `x`. -/
abbrev singleBPrimeRoot
    (C : P.ExteriorFeasibleBlockChoice) :
    Option C.BPrimeBlockVertex :=
  none

/-- Its right root, representing `b`. -/
def singleBPrimeAnchor
    (C : P.ExteriorFeasibleBlockChoice) :
    Option C.BPrimeBlockVertex :=
  some C.bPrimeAnchor

/-- The canonical homomorphism `G[B ∪ {x}] → G`. -/
noncomputable def singleBPrimeHom
    (C : P.ExteriorFeasibleBlockChoice) :
    C.singleBPrime →g G :=
  adjoinRootHom C.bPrimeBlockGraph
    (C.bPrimeAttachments x)
    C.bPrimeBlockEmbedding.toHom x
    (by
      intro d hd
      exact C.mem_bPrimeAttachments.mp hd)

@[simp] theorem singleBPrimeHom_root
    (C : P.ExteriorFeasibleBlockChoice) :
    C.singleBPrimeHom C.singleBPrimeRoot = x :=
  rfl

@[simp] theorem singleBPrimeHom_anchor
    (C : P.ExteriorFeasibleBlockChoice) :
    C.singleBPrimeHom C.singleBPrimeAnchor = C.b :=
  rfl

/-- The canonical homomorphism for the one-adjoined-vertex graph is injective. -/
theorem singleBPrimeHom_injective
    (C : P.ExteriorFeasibleBlockChoice) :
    Function.Injective C.singleBPrimeHom := by
  apply adjoinRootHom_injective
  · exact C.bPrimeBlockEmbedding.injective
  · rintro ⟨d, hd⟩
    change d.1 = x at hd
    have hxCore :
        x ∈ P.working.rooted.core.carrier :=
      P.working.rooted.core.root_mem_carrier
    exact Finset.disjoint_left.mp
      C.ambientCarrier_disjoint_core
      d.2
      (Eq.mp
        (congrArg
          (fun v =>
            v ∈ P.working.rooted.core.carrier)
          hd.symm)
        hxCore)

/--
After adjoining the artificial root edge `xb`, the one-vertex recursive
graph is the root adjunction at the enlarged attachment set.
-/
theorem singleBPrime_sup_rootEdge
    (C : P.ExteriorFeasibleBlockChoice) :
    C.singleBPrime ⊔
        edge C.singleBPrimeRoot C.singleBPrimeAnchor =
      adjoinRoot C.bPrimeBlockGraph
        (insert C.bPrimeAnchor
          (C.bPrimeAttachments x)) := by
  ext a b
  cases a <;> cases b <;>
    simp [singleBPrime, singleBPrimeAnchor,
      bPrimeAnchor, adjoinRoot, edge, or_comm]

/-- Equation (3.2) supplies two distinct rooted attachments, `b` and one
actual `x`-neighbour in `B-b`. -/
theorem two_le_insert_anchor_rootAttachments
    (C : P.ExteriorFeasibleBlockChoice)
    (hboundary : C.coreAttachments = {x, s}) :
    2 ≤
      (insert C.bPrimeAnchor
        (C.bPrimeAttachments x)).card := by
  obtain ⟨d, hd, hxd⟩ :=
    C.exists_root_attachment_in_compressionInterior
      hboundary
  let dB : C.BPrimeBlockVertex :=
    ⟨d, Finset.mem_of_mem_erase hd⟩
  have hdAttach :
      dB ∈ C.bPrimeAttachments x :=
    C.mem_bPrimeAttachments.mpr hxd
  have hne : C.bPrimeAnchor ≠ dB := by
    intro h
    exact (Finset.mem_erase.mp hd).1
      (congrArg Subtype.val h).symm
  have hpair :
      ({C.bPrimeAnchor, dB} :
        Finset C.BPrimeBlockVertex) ⊆
        insert C.bPrimeAnchor
          (C.bPrimeAttachments x) := by
    intro w hw
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hdAttach
  have hpairCard :
      ({C.bPrimeAnchor, dB} :
        Finset C.BPrimeBlockVertex).card = 2 := by
    simp [hne]
  rw [← hpairCard]
  exact Finset.card_le_card hpair

/-- The one-vertex recursive graph is rooted 2-connected. -/
theorem singleBPrime_rooted_twoConnected
    (C : P.ExteriorFeasibleBlockChoice)
    (hboundary : C.coreAttachments = {x, s}) :
    IsTwoConnected
      (C.singleBPrime ⊔
        edge C.singleBPrimeRoot
          C.singleBPrimeAnchor) := by
  rw [C.singleBPrime_sup_rootEdge]
  exact
    C.ambientCarrier_nonseparable.isTwoConnected_adjoinRoot
      _ (C.two_le_insert_anchor_rootAttachments hboundary)

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
