# Formal trust-audit sources

This directory contains only the exact source snapshots used in the Lean trust
audit: the named published assumptions in `DeanK5/Published.lean` and the
published statements compared with internal Lean proofs.

## Source index

### BGLP

Y. Bai, A. Grzesik, B. Li, and M. Prorok, "Cycle lengths in graphs of given
minimum degree," *Journal of Combinatorial Theory, Series B* **180** (2026),
111--150.
[doi:10.1016/j.jctb.2026.06.003](https://doi.org/10.1016/j.jctb.2026.06.003);
[arXiv:2511.03085v2](https://arxiv.org/abs/2511.03085v2).

- Snapshot: [`BGLP_2511.03085v2.pdf`](BGLP_2511.03085v2.pdf)
- SHA-256: `9126320d86bf6579916af192c61fcd04630654b87ad9d6bad4147201541ba8d7`
- External inputs: Theorem 1.3 (PDF page 2), and Theorem 2.2 and Lemma 2.3
  (PDF page 6).
- Internally formalized comparison result: Lemma 3.1 (PDF page 8).

### COY

S. Chiba, K. Ota, and T. Yamashita, "Minimum degree conditions for the
existence of a sequence of cycles whose lengths differ by one or two,"
*Journal of Graph Theory* **103** (2023), no. 2, 340--358.
[doi:10.1002/jgt.22921](https://doi.org/10.1002/jgt.22921);
[arXiv:2008.09783v1](https://arxiv.org/abs/2008.09783v1).

- Snapshot: [`COY_2008.09783v1.pdf`](COY_2008.09783v1.pdf)
- SHA-256: `f2f810840c43bee2a2835cace2dafe430b3daae6fa4b53a6f658d26715832957`
- Used result: Theorem 3 (PDF page 3), in the order-at-least-four form quoted
  as BGLP Theorem 2.2 (BGLP PDF page 6).

### GHLM

J. Gao, Q. Huo, C.-H. Liu, and J. Ma, "A unified proof of conjectures on
cycle lengths in graphs," *International Mathematics Research Notices*
**2022** (2022), no. 10, 7615--7653.
[doi:10.1093/imrn/rnaa324](https://doi.org/10.1093/imrn/rnaa324);
[arXiv:1904.08126v3](https://arxiv.org/abs/1904.08126v3).

- Snapshot: [`GHLM_1904.08126v3.pdf`](GHLM_1904.08126v3.pdf)
- SHA-256: `8ad18b1cb762642487d4fcaff58ba9786356e427c41fefb78b8209ae2de2795a`
- External inputs: Theorem 3.1 (PDF page 5) and Lemma 5.10 (PDF page 22).
- Internally formalized comparison result: the configuration used from
  Lemma 5.9 (PDF page 22).
