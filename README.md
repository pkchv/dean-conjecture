# Dean's conjecture at five

[![Lean verification](https://github.com/pkchv/dean-conjecture/actions/workflows/lean.yml/badge.svg)](https://github.com/pkchv/dean-conjecture/actions/workflows/lean.yml)

This repository contains a paper proposing a proof of Dean's conjecture for
modulus five, together with a Lean 4 formalization of the paper's internal
argument.

> **Verification status.** Lean checks the deduction from the explicit
> external inputs to the modulus-five theorem. Exactly five quoted published
> statements remain as explicit named axioms.

| Artifact | Status |
|---|---|
| Paper | Maintained in Markdown with scripted PDF and TeX builds |
| Internal proof | Lean-checked end to end, with no `sorry`, `admit`, or `native_decide` |
| Published inputs | Stated as named axioms and audited against archived source PDFs |

## Result

Every nonempty finite simple graph of minimum degree at least five contains a
simple cycle whose length is divisible by five. Together with the previously
known cases, this completes Dean's conjecture for every integer `k ≥ 3`. The
assembled Lean theorem formalizes the new modulus-five case:

```lean
theorem DeanK5.dean_conjecture_k5
    {X : Type*} [Fintype X]
    [Nonempty X]
    (G : SimpleGraph X)
    (hdegree : MinDegreeAtLeast G 5) :
    HasCycleDivisibleBy G 5
```

The carrier is explicitly nonempty because the project's pointwise
`MinDegreeAtLeast` predicate is vacuously true on an empty type.

## Paper

- [Read the PDF](paper/Dean_conjecture_k5.pdf)
- [View the Markdown source](paper/Dean_conjecture_k5.md)
- [Download the TeX source](paper/Dean_conjecture_k5.tex)

The Markdown file is the source of truth. To regenerate the PDF and the
standalone XeLaTeX source:

```sh
./scripts/build-paper.sh
```

The build requires Pandoc, XeLaTeX, and the LaTeX `needspace` package. The
generated `.tex` file is self-contained and compiles with XeLaTeX.

## Verify the formalization

The repository pins Lean and Mathlib through
[`lean-toolchain`](lean-toolchain) and
[`lake-manifest.json`](lake-manifest.json). With Elan and Lake installed, run:

```sh
./scripts/verify-lean.sh
```

GitHub Actions runs the same verifier on every pull request targeting `main`
and every push to `main`; it can also be started manually from the
[Lean verification workflow](.github/workflows/lean.yml).

This builds every project module and runs
[`DeanK5/AxiomAudit.lean`](DeanK5/AxiomAudit.lean). The audit rejects
`sorry` and unlisted dependencies, enforces the final theorem's exact
allowlist, and checks that the library root imports every proof module.

## Formalization map

Lean checks the modulus-five deduction from five external mathematical assumptions:
GHLM Theorem 3.1 and Lemma 5.10; COY Theorem 3 in the form quoted as BGLP
Theorem 2.2; and BGLP Theorem 1.3 and Lemma 2.3. No other graph-theoretic
statement is axiomatized. The audit separately reports Lean's ordinary
logical foundations: `propext`, `Classical.choice`, and `Quot.sound`.

| File or directory | What it does |
|---|---|
| [`Published.lean`](DeanK5/Published.lean), [`references/`](references/) | Declare the five external mathematical assumptions and record their source PDFs, checksums, and theorem locations |
| [`Graph/`](DeanK5/Graph/), [`Arithmetic.lean`](DeanK5/Arithmetic.lean), [`Concatenation.lean`](DeanK5/Concatenation.lean) | Define the formal vocabulary, prove the length arithmetic, and certify simple paths and cycles using Mathlib's `Walk.IsPath` and `Walk.IsCycle` |
| [`ClassicalGraphTheory.lean`](DeanK5/ClassicalGraphTheory.lean), [`EndLobeExistence.lean`](DeanK5/EndLobeExistence.lean), [`EndLobeAttachments.lean`](DeanK5/EndLobeAttachments.lean), [`EndLobeComponents.lean`](DeanK5/EndLobeComponents.lean), [`MengerTwo.lean`](DeanK5/MengerTwo.lean) | Prove the finite-graph, end-lobe, and two-link Menger results used by the reductions |
| [`Structural.lean`](DeanK5/Structural.lean), [`RootLifting.lean`](DeanK5/RootLifting.lean), [`ThreeSeparator.lean`](DeanK5/ThreeSeparator.lean), [`StandingSetup.lean`](DeanK5/StandingSetup.lean) | Formalize the rooted end-block and connectivity reductions in Sections 3–4 |
| [`Contraction.lean`](DeanK5/Contraction.lean), [`SmallSubgraphs.lean`](DeanK5/SmallSubgraphs.lean), [`BoundaryLifting.lean`](DeanK5/BoundaryLifting.lean), [`BipartitePaths.lean`](DeanK5/BipartitePaths.lean), [`FourCycleExclusion.lean`](DeanK5/FourCycleExclusion.lean) | Formalize Sections 5–6, including the complete-bipartite path ranges used in Section 6 |
| [`ThetaResidue.lean`](DeanK5/ThetaResidue.lean), [`ThetaExistence.lean`](DeanK5/ThetaExistence.lean), [`ThetaCore.lean`](DeanK5/ThetaCore.lean), [`SubdivisionK4.lean`](DeanK5/SubdivisionK4.lean), [`GirthSixCase.lean`](DeanK5/GirthSixCase.lean), [`FinalResidue.lean`](DeanK5/FinalResidue.lean) | Formalize Section 7, including the subdivision-attachment and theta-residue lemmas proved in the paper |
| [`Reduction.lean`](DeanK5/Reduction.lean) | Assemble the end-block reduction and prove `DeanK5.dean_conjecture_k5` |
| [`AxiomAudit.lean`](DeanK5/AxiomAudit.lean), [`DeanK5.lean`](DeanK5.lean), [`verify-lean.sh`](scripts/verify-lean.sh) | Enforce the dependency boundary across every proof module and run the complete build |

## Paper-to-Lean map

| Paper | Principal Lean modules |
|---|---|
| Section 1: introduction, proof architecture, and published results | [`Graph.Basic`](DeanK5/Graph/Basic.lean), [`Published`](DeanK5/Published.lean), [`AxiomAudit`](DeanK5/AxiomAudit.lean) |
| Section 2: length arithmetic and simple-cycle assembly | [`Arithmetic`](DeanK5/Arithmetic.lean), [`Concatenation`](DeanK5/Concatenation.lean), [`ThetaResidue`](DeanK5/ThetaResidue.lean) |
| Section 3: rooted end-block reduction | [`Reduction`](DeanK5/Reduction.lean), [`Structural`](DeanK5/Structural.lean), [`RootLifting`](DeanK5/RootLifting.lean), [`StandingSetup`](DeanK5/StandingSetup.lean), [`EndLobeExistence`](DeanK5/EndLobeExistence.lean), [`EndLobeAttachments`](DeanK5/EndLobeAttachments.lean) |
| Section 4: from 3-connectivity to 4-connectivity | [`ThreeSeparator`](DeanK5/ThreeSeparator.lean), [`StandingSetup`](DeanK5/StandingSetup.lean) |
| Section 5: first local exclusions—`K₄⁻` and triangles | [`Contraction`](DeanK5/Contraction.lean), [`SmallSubgraphs`](DeanK5/SmallSubgraphs.lean) |
| Section 6: boundary lifting and the four-cycle exclusion | [`BoundaryLifting`](DeanK5/BoundaryLifting.lean), [`BipartitePaths`](DeanK5/BipartitePaths.lean), [`FourCycleExclusion`](DeanK5/FourCycleExclusion.lean) |
| Section 7: the minimum-theta argument | [`GirthSixCase`](DeanK5/GirthSixCase.lean), [`ThetaExistence`](DeanK5/ThetaExistence.lean), [`ThetaCore`](DeanK5/ThetaCore.lean), [`SubdivisionK4`](DeanK5/SubdivisionK4.lean), [`MengerTwo`](DeanK5/MengerTwo.lean), [`EndLobeComponents`](DeanK5/EndLobeComponents.lean), [`RootLifting`](DeanK5/RootLifting.lean), [`ThetaResidue`](DeanK5/ThetaResidue.lean), [`FinalResidue`](DeanK5/FinalResidue.lean) |
| Section 8: completion of the modulus-five case | [`Reduction`](DeanK5/Reduction.lean) |

The Lean development proves the new modulus-five theorem. The full-conjecture
corollary at the end of Section 8 additionally invokes the previously
known cases for `k = 3, 4` and `k ≥ 6` and is not separately formalized.
