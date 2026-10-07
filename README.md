# Hindman's finite sums and products in Lean 4

Lean 4 formalization of the finite sums and products theorem: for every finite colouring of the positive
integers and every `m`, there is an `m`-element set of positive integers whose nonempty subset sums and
products all have one colour. The statement is `HindmanSumsProducts.hindman_finite_sums_products` in
[Challenge.lean](Challenge.lean); the proof is in `HindmanSumsProducts.Main`.

## Build

Lean 4.34.1 (pinned in `lean-toolchain`). The project depends on OpenAI's library `openai/math`, which pins
patched third-party packages. OpenAI's `lake update` hook applies those patches only when OpenAI's package
is the root, so this project applies them with a script:

```bash
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

`lake update` exits with status 1, ending with an error from OpenAI's patch hook
(`iut: Lake resolved an unexpected checkout at …`). The dependencies are resolved and `lake-manifest.json`
is written all the same; run the script next. The script applies each `lean/patches/*-lean4341.patch` of
OpenAI's package to the package of the same name under `.lake/packages/`, and skips patches that are
already applied, so it can be run again after any `lake update`. OpenAI's hook also leaves unused clones
under `.lake/packages/OAI/lean/.lake/packages/`; they can be deleted.
