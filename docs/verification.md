# Reproducing the verification

The project uses Lean `v4.34.1`, selected by [lean-toolchain](../lean-toolchain). Mathlib and the other package revisions are locked in [lake-manifest.json](../lake-manifest.json).

## Fresh checkout

From the repository root, prepare the dependencies and build the project:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's Lake hook exits with an error beginning `iut: Lake resolved an unexpected checkout at …`. It has still resolved the dependencies and written `lake-manifest.json`; run the patch script after that error. The script applies the `*-lean4341.patch` files from OpenAI's package and skips patches that are already applied. The hook leaves unused package clones under `.lake/packages/OAI/lean/.lake/packages/`; those clones can be removed.

## Statement and axiom checks

Run the repository verification script with a bounded build thread count:

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

It builds the solution and challenge modules, checks each declaration against the challenge's displayed Lean type, then prints and checks the axioms of `HindmanSumsProducts.hindman_finite_sums_products`. The statement checks use separate Lean runs because the challenge and solution modules declare the same fully qualified name. [Challenge.json](../Challenge.json) configures Comparator to compare those modules directly.

The accepted axiom set is `propext`, `Classical.choice`, and `Quot.sound`. If the theorem or a dependency still has an open proof, the script reports `sorryAx` explicitly and exits with status 2. Once the proof is complete, an unrecognized axiom or a missing axiom report is a verification failure.

The Lean checks run with `--trust=0`. They check the project modules and the statement correspondence; they do not rebuild all upstream dependencies from source. `lake exe cache get` obtains compiled dependency artifacts for the pinned sources.

## Independent check of v1.0.0

On 7–8 October 2026 (UTC), release `v1.0.0` (commit `5d18600a4518d42d5b1e916e908e50330eb38456`) was cloned from GitHub onto a new Google Cloud virtual machine (`c4d-standard-32`, 32 cores, Ubuntu 24.04 LTS, with only `elan` installed) and checked with the steps above, in order: Commit hashes were renumbered on 10 October 2026, when local file paths were removed from older commits of the history; the files of `v1.0.0` did not change (tree `1d77b96857b4c6d6566b8306e93793b3ce66c3ed`), so this check applies to the current tag.

| Step | Result |
|---|---|
| `lake update` | exit 1 with the `iut: Lake resolved an unexpected checkout at …` hook error described above; `lake-manifest.json` unchanged |
| `scripts/apply-oai-patches.sh` | exit 0; patches applied to 23 of OpenAI's pinned packages |
| `lake exe cache get`, then `lake build` | exit 0 (11472 jobs, 34 minutes); no errors and no `sorry` |
| `scripts/verify.sh` | exit 0; `hindman_finite_sums_products` depends on `propext`, `Classical.choice` and `Quot.sound` only |
| `lake env leanchecker --fresh HindmanSumsProducts.Main` | exit 0 (30 minutes): the kernel replayed the declarations of the main module and of everything it imports, including the cached dependency artifacts |
| Comparator with [Challenge.json](../Challenge.json) | exit 0; the solution's statement matches the challenge and the Lean kernel accepts the solution |

Comparator was [`leanprover/comparator`](https://github.com/leanprover/comparator) at `ca04cfc`, with `lean4export` at `076e8e5` (the `v4.34.0` source) built with the project toolchain `v4.34.1`. It ran with comparator's development stand-in for the `landrun` sandbox, so it checked the statement match and kernel acceptance without isolating the build from the code it checks.
