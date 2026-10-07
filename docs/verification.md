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
