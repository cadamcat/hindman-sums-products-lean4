[English](README.md) | [简体中文](README_zh.md)

# Hindman sums and products in Lean 4

Every finite colouring of the positive integers contains, for each `m`, an `m`-element set whose nonempty subset sums and products all have one colour. This is problem JSP-000168 of the Justin Sun Prize catalog and the finite case of [Erdős Problem #172](https://www.erdosproblems.com/172). The formal statement is this conjecture; the main theorem of OpenAI's paper adds a separation clause and a corollary, which are not formalized ([details](docs/mathematics.md)).

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authors and attribution](AUTHORS.md).
- **Mathematical result:** OpenAI, [*Monochromatic finite sums and products in the positive integers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf).
- Developed with AI assistance (Claude Code and Codex); all proofs are verified by the Lean 4 kernel.

## Main results

| Theorem | Statement |
| --- | --- |
| `HindmanSumsProducts.hindman_finite_sums_products` | For every `r`, colouring `χ : ℕ → Fin r`, and `m`, there are `A : Finset ℕ` and `c : Fin r` with `A.card = m`, every element of `A` positive, and every nonempty subset sum and product of `A` coloured `c`. |

The proof is in [HindmanSumsProducts/Main.lean](HindmanSumsProducts/Main.lean). The corresponding challenge statement is in [Challenge.lean](Challenge.lean); [Challenge.json](Challenge.json) configures Comparator to compare them. See [the mathematical guide](docs/mathematics.md) for the statement's details and the proof's relation to the paper.

## Build and verify

Requirements: Git, Python 3, and [elan](https://github.com/leanprover/elan), with `lake` available on `PATH`. From the repository root, a fresh checkout is prepared with:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's `lake update` hook exits with an error beginning `iut: Lake resolved an unexpected checkout at …` after resolving dependencies and writing `lake-manifest.json`. Run the patch script next; it applies OpenAI's Lean 4.34.1 compatibility patches and can be run again after another `lake update`. The patches change the dependency sources that are then compiled (the PrimeNumberTheoremAnd patch is the largest), so a build checks the patched sources, not the revisions in `lake-manifest.json` alone.

To build the theorem and check both statements and the final theorem's axioms, run `LEAN_NUM_THREADS=4 ./scripts/verify.sh`. An open proof is reported as `sorryAx` and causes the script to exit with status 2. Verification details are in [docs/verification.md](docs/verification.md). A fresh clone of release `v1.0.0` on a new Linux machine also built with these steps, replayed in the kernel with `leanchecker --fresh`, and passed Comparator; the [independent check](docs/verification.md#independent-check-of-v100) lists the results.

## Fixed dependencies

- Lean `v4.34.1`, selected by [lean-toolchain](lean-toolchain).
- [Mathlib](https://github.com/leanprover-community/mathlib4), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- OpenAI's [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) commit `c39a751132c88b6e8080b74c74023fd95b3d8be0` and [StrongPNT](https://github.com/math-inc/strongpnt) commit `2f5835c322314f55f1026ec2f139d704b7c45c69`, pinned by OpenAI's library.
- The remaining dependency revisions are fixed in [lake-manifest.json](lake-manifest.json).

## Mathematical references

- OpenAI, [*Monochromatic finite sums and products in the positive integers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf), September 23, 2026.
- N. Kravitz, B. Kuca, and J. Leng, [*Quantitative concatenation for polynomial box norms*](https://arxiv.org/abs/2407.08636), §6.

See [THIRD_PARTY.md](THIRD_PARTY.md) for code attribution and [LICENSE](LICENSE) for the project license.
