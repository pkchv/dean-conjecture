# Mathematical provenance sources

This directory contains the exact source snapshots used to compare the paper
and its internal Lean proofs with the published literature. They record
mathematical provenance, theorem locations, and stable checksums; none is
imported as an axiom by the Lean development.

## Source index

### BGLP

Y. Bai, A. Grzesik, B. Li, and M. Prorok, "Cycle lengths in graphs of given
minimum degree," *Journal of Combinatorial Theory, Series B* **180** (2026),
111--150.
[doi:10.1016/j.jctb.2026.06.003](https://doi.org/10.1016/j.jctb.2026.06.003);
[arXiv:2511.03085v2](https://arxiv.org/abs/2511.03085v2).

- Snapshot: [`BGLP_2511.03085v2.pdf`](BGLP_2511.03085v2.pdf)
- SHA-256: `9126320d86bf6579916af192c61fcd04630654b87ad9d6bad4147201541ba8d7`
- Statement comparison: Theorem 2.2 (PDF page 6) records the finite-order
  form of the bounded COY theorem proved in
  [`COYRootedInternal.lean`](../DeanK5/COYRootedInternal.lean).
- Internally formalized comparison results: the needed `k = 5`
  divisible-cycle consequence of Theorem 1.3 (PDF page 2), the needed
  `k = 5`, `r = 1` consequence of Lemma 2.3 (PDF page 6), and the
  complete-bipartite path ranges used from Lemma 3.1 (PDF page 8). The first
  is obtained by reusing the paper's Sections 4 through 7 in the
  deficiency-free case rather than by formalizing BGLP Lemma 3.11 verbatim.

### COY

S. Chiba, K. Ota, and T. Yamashita, "Minimum degree conditions for the
existence of a sequence of cycles whose lengths differ by one or two,"
*Journal of Graph Theory* **103** (2023), no. 2, 340--358.
[doi:10.1002/jgt.22921](https://doi.org/10.1002/jgt.22921);
[arXiv:2008.09783v1](https://arxiv.org/abs/2008.09783v1).

- Snapshot: [`COY_2008.09783v1.pdf`](COY_2008.09783v1.pdf)
- SHA-256: `f2f810840c43bee2a2835cace2dafe430b3daae6fa4b53a6f658d26715832957`
- Internal comparison result: the `2 ≤ q ≤ 4` fragment of Theorem 3
  (PDF page 3), in the order-at-least-four form quoted as BGLP Theorem 2.2
  (BGLP PDF page 6). The public Lean theorem has the exceptional vertex
  distinct from both roots.

### GHLM

J. Gao, Q. Huo, C.-H. Liu, and J. Ma, "A unified proof of conjectures on
cycle lengths in graphs," *International Mathematics Research Notices*
**2022** (2022), no. 10, 7615--7653.
[doi:10.1093/imrn/rnaa324](https://doi.org/10.1093/imrn/rnaa324);
[arXiv:1904.08126v3](https://arxiv.org/abs/1904.08126v3).

- Snapshot: [`GHLM_1904.08126v3.pdf`](GHLM_1904.08126v3.pdf)
- SHA-256: `8ad18b1cb762642487d4fcaff58ba9786356e427c41fefb78b8209ae2de2795a`
- Internally formalized comparison results: the needed `2 ≤ q ≤ 4` fragment
  of Theorem 3.1 (PDF page 5), and Lemmas 5.9 and 5.10 (PDF page 22). The
  rooted-path fragment is derived from the internally proved COY theorem;
  the `q = 1` base case needed by the bounded COY induction is proved
  directly.
