# Hindman's finite sums and products in Lean 4

A Lean 4 formalization of Hindman's finite sums and products conjecture: every finite colouring of the
positive integers contains, for every `m`, an `m`-element set of positive integers whose nonempty subset
sums and nonempty subset products all have one colour.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)).
- **Mathematical result:** OpenAI, [*Monochromatic finite sums and products in the positive
  integers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf)
  (September 23, 2026). The formal proof follows this paper.
- **OpenAI's Lean library:** the proof builds on [`openai/math`](https://github.com/openai/math) (Apache-2.0)
  at commit `adc7f124`; what it takes from that library is listed [below](#what-comes-from-openais-library).
- Developed with AI assistance (Claude Code, Codex); every proof is checked by the Lean 4 kernel.

## Main result

```lean
theorem HindmanSumsProducts.hindman_finite_sums_products (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) :
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c
```

The statement uses Mathlib definitions only. [Challenge.lean](Challenge.lean) states it with `sorry`;
the proof is the theorem of the same name in [HindmanSumsProducts/Main.lean](HindmanSumsProducts/Main.lean),
and `#print axioms` shows `propext`, `Classical.choice` and `Quot.sound` only. [Challenge.json](Challenge.json)
configures Comparator to check that the two statements agree.

A colouring is a map `χ : ℕ → Fin r`; its value at `0` never matters, because every nonempty subset sum
or product of positive integers is positive. The paper's main theorem also has a separation clause; the
conjecture does not ask for it, and it is not formalized. [audit/](audit/) holds statement probes
(`ChallengeProbes.lean`, `OpusFidelityProbes.lean`): small colourings that satisfy or violate the conclusion,
and the equivalence with colourings of `ℕ+` by an arbitrary finite type.

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

## How the proof is organized

The paper proves the theorem from two principles about finite colourings and nilsequence menus, a
Prediction Principle (§3–§5) and an Alignment Principle (§6–§8). The formalization follows it:

| Part | Lean | Paper |
|---|---|---|
| Deduction of the theorem from the two principles, chain selection, finite sums theorem | `Framework.lean` (`main_of_principles`), `ChainSelection.lean` | §2 |
| Alignment Principle for charted menus | OpenAI's library (`OAI.SourceMenuLiteral.charted_finite_menu_alignment`), used through `OAIAlignment.lean` | §6–§8 |
| Arithmetic: master scales, rough coprimality, sampling, product law, linear forms | `Arithmetic/` | §3 |
| Correlation: mask removal, additive elimination, the correlation test | `Correlation.lean`, `Correlation/` | §4 |
| Prediction Principle: test laws, dense models, recipes, projections, subgroup inverse step, completion | `Prediction/` | §5 |
| Missing-corner lemma for the recipes | `CubeCorner.lean`, `CubeCornerCharted.lean` | §7 |

The formal proof departs from the paper in two places, both in §5:

- **Concatenation.** The paper uses the Tao–Ziegler concatenation theorem. The formalization uses instead
  the subgroup box-norm concatenation of Kravitz, Kuca and Leng ([arXiv:2407.08636](https://arxiv.org/abs/2407.08636),
  §6), proved in `Concatenation.lean`, which serves both uses in §5 with inverse degree `2^(2^d) − 1`.
- **Inverse theorem.** The paper needs the Green–Tao–Ziegler inverse theorem with linear orbits on a fixed
  finite family of nilmanifolds. OpenAI's library proves an inverse theorem on cyclic groups with
  polynomial orbits (`OAI.Erdos3.exists_cyclicNativeInverse_positive`). `InverseBridge/` transfers it to
  the form §5 uses (`InverseBridge.cyclic_inverse_menu`): each model is covered by a canonical model with
  a coordinate sublattice, polynomial orbits are linearized by a Baker–Campbell–Hausdorff argument, and
  observables descend to one finite charted menu.

Outside results come from Mathlib, from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) as
pinned by OpenAI's library (the prime number theorem in arithmetic progressions, through `Wiener`), and from
OpenAI's library (Brun–Titchmarsh, through `PrimeFibreBrunBound`).

## What comes from OpenAI's library

Code adapted from `openai/math` (Apache-2.0) is marked in the source by `-- Adapted from OpenAI openai/math
(Apache-2.0), <path>` and `-- End of code adapted from OpenAI`:

| File | Lines | Adapted from (openai/math, `lean/`) |
|---|---|---|
| `HindmanSumsProducts/Arithmetic/Sampling.lean` | from 153 (end not marked) | `OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean` |
| `HindmanSumsProducts/Arithmetic/Sampling.lean` | from 814 (end not marked) | `OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean` |
| `HindmanSumsProducts/Arithmetic/Sampling.lean` | from 843 (end not marked) | `OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean` |
| `HindmanSumsProducts/ChainSelection/FiniteRamsey.lean` | whole file | `OAI/Analysis/MarkovType/FiniteRamsey.lean` |
| `HindmanSumsProducts/Concatenation.lean` | from 493 (end not marked) | `OAI/Combinatorics/Progressions/Estimates/BooleanCubeProduct.lean` |
| `HindmanSumsProducts/Prediction/PkgB.lean` | from 3037 (end not marked) | `OAI/MeasureTheory/Falconer/Estimates/FiniteHolder.lean` |

Modules of `openai/math` (and of the packages it pins) that the project imports:

| Imported module | Imported by |
|---|---|
| `OAI.Combinatorics.Progressions.Estimates.AxisCompression` | `HindmanSumsProducts/InverseBridge.lean`, `HindmanSumsProducts/InverseBridge/Adjoint.lean`, `HindmanSumsProducts/InverseBridge/AdjointExp.lean` and 3 more |
| `OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative` | `HindmanSumsProducts/Prediction/Outside.lean` |
| `OAI.Combinatorics.Progressions.Estimates.NativeModelOrbit` | `HindmanSumsProducts/InverseBridge/Canonical.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.Admissible01` | `HindmanSumsProducts/Arithmetic/Defs.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.Blocks01` | `HindmanSumsProducts/Arithmetic/Defs.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.ConstantCoefficient01` | `HindmanSumsProducts/Arithmetic/Defs.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.HarmonicTranslation01` | `HindmanSumsProducts/Arithmetic/Sampling.lean`, `HindmanSumsProducts/Prediction/PkgF.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.IntegerArrays14` | `HindmanSumsProducts/Arithmetic/Defs.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.MenuLiteral01` | `HindmanSumsProducts/InverseBridge.lean`, `HindmanSumsProducts/InverseBridge/Adjoint.lean`, `HindmanSumsProducts/InverseBridge/Menu.lean` and 1 more |
| `OAI.Combinatorics.SumProduct.Alignment.MicrocellScale01` | `HindmanSumsProducts/Arithmetic/Defs.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.ProductExposure03` | `HindmanSumsProducts/Arithmetic/ProductLaw.lean`, `HindmanSumsProducts/Prediction/PkgH.lean`, `HindmanSumsProducts/Prediction/PkgH2.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.RawHarmonic01` | `HindmanSumsProducts/Arithmetic/Defs.lean`, `HindmanSumsProducts/Prediction/PkgD.lean` |
| `OAI.Combinatorics.SumProduct.Alignment.RawMenu` | `HindmanSumsProducts/Arithmetic/Defs.lean`, `HindmanSumsProducts/CubeCorner.lean`, `HindmanSumsProducts/Framework.lean` and 1 more |
| `OAI.Combinatorics.SumProduct.Alignment.WordPlan01` | `HindmanSumsProducts/Arithmetic/Defs.lean` |
| `OAI.NumberTheory.Jacobsthal.Sieve.PrimeFibreBrunBound` | `HindmanSumsProducts/Arithmetic/Outside.lean` |
| `PrimeNumberTheoremAnd.Erdos970.Wiener` | `HindmanSumsProducts/Arithmetic/Outside.lean`, `HindmanSumsProducts/Arithmetic/Outside/AP.lean` |
| `PrimeNumberTheoremAnd.Wiener` | `HindmanSumsProducts/Arithmetic/Outside.lean` |

## AI use

AI coding agents wrote the Lean code, under acceptance criteria set by the author. The target statement
was written first and reviewed clause by clause against the conjecture and the paper's main theorem. Each
intermediate statement was frozen, with a hash of its elaborated type, before any proof of it was
attempted; a proof was accepted only if the statement still had the frozen type and its axioms were within
`propext`, `Classical.choice` and `Quot.sound`, up to other frozen statements still open. Statements were
also attacked for counterexamples, and the few found false were repaired and frozen again before proofs
resumed.

Claude Code (Claude Opus 5.5) coordinated the work and integrated it; Codex (GPT-6 Luna) wrote most of the
proofs; GPT-6.1 Sol checked statements for counterexamples and wrote detailed proof designs for the
hardest steps; Claude Opus 5.5 reviewed the target statement and repaired defective intermediate
statements. Model agreement was not treated as verification: correctness rests on the Lean kernel and the
axiom check of the final theorem. The author is responsible for the content.

## License

Apache-2.0; see [LICENSE](LICENSE). Code adapted from `openai/math` is under its Apache-2.0 license; see
[NOTICE](NOTICE).
