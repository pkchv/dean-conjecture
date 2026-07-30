# Dean's conjecture at five

[![Lean verification](https://github.com/pkchv/dean-conjecture/actions/workflows/lean.yml/badge.svg)](https://github.com/pkchv/dean-conjecture/actions/workflows/lean.yml)

**AI disclosure.** The mathematical proof, manuscript, and Lean formalization
were generated entirely by GPT-5.6 Sol and GPT-5.6 Sol Pro.

This repository contains a proposed proof of the remaining `k = 5` case of
Dean's conjecture:

> **Theorem.** Every nonempty finite simple graph of minimum degree at least
> five contains a simple cycle whose length is divisible by five.

The theorem is verified in Lean 4. Independent expert review is welcome.

## Paper

- [Read the PDF](paper/Dean_conjecture_k5.pdf)
- [View the Markdown source](paper/Dean_conjecture_k5.md)
- [Download the TeX source](paper/Dean_conjecture_k5.tex)

## Independent specification and verification

The theorem was specified independently of its Lean implementation. Using
[Oracle](https://github.com/steipete/oracle), GPT-5.6 Sol Pro received the
paper, but not the Lean sources or an existing theorem signature, and was
asked to:

1. isolate the principal fixed-modulus-five theorem;
2. make every hypothesis and conclusion explicit;
3. translate that contract using only Mathlib primitives, then check the empty
   carrier, finiteness, degree, cycle, length, and divisibility semantics.

The resulting mathematical specification is:

> **Theorem.** Every finite nonempty simple graph of minimum degree at least
> five contains a simple cycle whose length is divisible by five.

$$
\forall\,G\text{ finite, nonempty, and simple},\qquad
\delta(G)\ge 5
\Longrightarrow
\exists\,C\subseteq G\;
\bigl(C\text{ is a simple cycle}\land 5\mid |E(C)|\bigr).
$$

The corresponding trusted input to
[Comparator](https://github.com/leanprover/comparator) is
[`DeanK5Challenge.lean`](DeanK5Challenge.lean):

```lean
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card

namespace DeanK5.Comparator

theorem dean_conjecture_k5
    {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V)
    (hmin : ∀ v : V, 5 ≤ (G.neighborSet v).ncard) :
    ∃ (v : V) (C : G.Walk v v),
      C.IsCycle ∧ 5 ∣ C.length := by
  sorry

end DeanK5.Comparator
```

This statement imports no project definitions. The correspondence is literal:
`SimpleGraph V` encodes an undirected simple graph; `Finite` and `Nonempty`
encode the carrier assumptions; `neighborSet.ncard` encodes degree;
`Walk.IsCycle` encodes a simple cycle; `Walk.length` counts edges; and
`5 ∣ C.length` is divisibility by five.

[`DeanK5Solution.lean`](DeanK5Solution.lean) repeats the same declaration and
derives it from the project's top-level theorem. Comparator builds the
challenge and solution separately, compares their exported statements, checks
the permitted axiom set, and replays the exported proof with both Lean and
Nanoda. The `sorry` above is the specification placeholder expected by
Comparator; the solution and the project proof contain no `sorry`.

## Formalization map

The project proves the exact portions of the published results needed here.

Lean formalizes the `2 ≤ q ≤ 4` fragment of COY Theorem 3 and derives the
needed fragment of GHLM Theorem 3.1 from it. The required `k = 5`, `r = 1`
case of BGLP Lemma 2.3 is also proved internally, as is GHLM Lemma 5.10.

The entries below are the main review points. The
[Paper-to-Lean map](#paper-to-lean-map) gives the section-by-section detail.

### Core interfaces

- [`Graph/`](DeanK5/Graph/): Graph vocabulary, connectivity, blocks, paths,
  and cycles.
- [`COYRootedInternal.lean`](DeanK5/COYRootedInternal.lean): The bounded COY
  rooted-path theorem.
- [`GHLMRootedInternal.lean`](DeanK5/GHLMRootedInternal.lean): The required
  GHLM rooted-path theorem, derived from COY.
- [`BGLPConnectivityInternal.lean`](DeanK5/BGLPConnectivityInternal.lean):
  The `k = 5`, `r = 1` connectivity step.
- [`GHLMMinimumTheta.lean`](DeanK5/GHLMMinimumTheta.lean): The minimum-theta
  structure lemma.

### Proof spine

- [`StandingSetup.lean`](DeanK5/StandingSetup.lean): The shared hypotheses
  for Sections 3–7.
- [`GirthSixCase.lean`](DeanK5/GirthSixCase.lean): The common Sections 4–7
  contradiction.
- [`TwoConnectedCase.lean`](DeanK5/TwoConnectedCase.lean): The
  two-connected branch.
- [`Reduction.lean`](DeanK5/Reduction.lean): The rooted end-block branch.
- [`FinalDeduction.lean`](DeanK5/FinalDeduction.lean): The top-level theorem.

### Audits and sources

- [`FinalDeductionAudit.lean`](DeanK5/FinalDeductionAudit.lean): Focused
  axiom and proof-reachability checks.
- [`AxiomAudit.lean`](DeanK5/AxiomAudit.lean): The exhaustive project audit.
- [`DeanK5Challenge.lean`](DeanK5Challenge.lean): The final theorem stated
  directly with Mathlib primitives for independent comparison.
- [`DeanK5Solution.lean`](DeanK5Solution.lean): The proof-side bridge to that
  statement.
- [`references/`](references/): Published sources, checksums, and statement
  provenance.

## Paper-to-Lean map

| Paper | Principal Lean modules |
|---|---|
| Section 1: introduction, proof architecture, and published results | [`Graph.Basic`](DeanK5/Graph/Basic.lean), [`COYRootedInternal`](DeanK5/COYRootedInternal.lean) |
| Section 2: length arithmetic and simple-cycle assembly | [`Arithmetic`](DeanK5/Arithmetic.lean), [`Concatenation`](DeanK5/Concatenation.lean), [`ThetaResidue`](DeanK5/ThetaResidue.lean) |
| Section 3: rooted end-block reduction | [`Reduction`](DeanK5/Reduction.lean), [`Structural`](DeanK5/Structural.lean), [`RootLifting`](DeanK5/RootLifting.lean), [`StandingSetup`](DeanK5/StandingSetup.lean), [`EndLobeExistence`](DeanK5/EndLobeExistence.lean), [`EndLobeAttachments`](DeanK5/EndLobeAttachments.lean) |
| Section 4: from 3-connectivity to 4-connectivity | [`ThreeSeparator`](DeanK5/ThreeSeparator.lean), [`StandingSetup`](DeanK5/StandingSetup.lean) |
| Section 5: first local exclusions: `K₄⁻` and triangles | [`Contraction`](DeanK5/Contraction.lean), [`SmallSubgraphs`](DeanK5/SmallSubgraphs.lean) |
| Section 6: boundary lifting and the four-cycle exclusion | [`BoundaryLifting`](DeanK5/BoundaryLifting.lean), [`BipartitePaths`](DeanK5/BipartitePaths.lean), [`FourCycleExclusion`](DeanK5/FourCycleExclusion.lean) |
| Section 7: the minimum-theta argument | [`GirthSixCase`](DeanK5/GirthSixCase.lean), [`ThetaExistence`](DeanK5/ThetaExistence.lean), [`ThetaCore`](DeanK5/ThetaCore.lean), [`ThetaMinimumInduced`](DeanK5/ThetaMinimumInduced.lean), [`ThetaOutsideChord`](DeanK5/ThetaOutsideChord.lean), [`ThetaMinimumAttachment`](DeanK5/ThetaMinimumAttachment.lean), [`GHLMMinimumTheta`](DeanK5/GHLMMinimumTheta.lean), [`SubdivisionK4`](DeanK5/SubdivisionK4.lean), [`MengerTwo`](DeanK5/MengerTwo.lean), [`EndLobeComponents`](DeanK5/EndLobeComponents.lean), [`RootLifting`](DeanK5/RootLifting.lean), [`ThetaResidue`](DeanK5/ThetaResidue.lean), [`FinalResidue`](DeanK5/FinalResidue.lean) |
| Section 8: completion of the modulus-five case | [`FinalDeduction`](DeanK5/FinalDeduction.lean) |

## Verify the Lean proof

Type-check the complete formalization with:

```sh
lake build
```
