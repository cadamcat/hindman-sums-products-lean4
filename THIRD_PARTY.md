# Third-party code and mathematical sources

## OpenAI's Lean library

This project uses [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, under the Apache-2.0 license. The blocks adapted into this repository are marked in their source files with comments naming the upstream paths. The following tables are generated from those markers and imports:

<!-- attribution:start -->
| File | Lines | Adapted from (openai/math, `lean/`) |
|---|---|---|
| `HindmanSumsProducts/Arithmetic/Sampling.lean` | 153–154 | `OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean` |
| `HindmanSumsProducts/Arithmetic/Sampling.lean` | 815–840 | `OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean` |
| `HindmanSumsProducts/Arithmetic/Sampling.lean` | 845–884 | `OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean` |
| `HindmanSumsProducts/ChainSelection/FiniteRamsey.lean` | whole file | `OAI/Analysis/MarkovType/FiniteRamsey.lean` |
| `HindmanSumsProducts/Concatenation.lean` | 363–371 | `OAI/Combinatorics/Progressions/Estimates/ComplexFiniteMeans.lean` |
| `HindmanSumsProducts/Concatenation.lean` | 484–494 | `OAI/Combinatorics/Progressions/Estimates/ComplexFiniteMeans.lean` |
| `HindmanSumsProducts/Concatenation.lean` | 499–569 | `OAI/Combinatorics/Progressions/Estimates/BooleanCubeProduct.lean` |
| `HindmanSumsProducts/Concatenation.lean` | 658–688 | `OAI/Combinatorics/Progressions/Estimates/ComplexFiniteMeans.lean` |
| `HindmanSumsProducts/Prediction/PkgB.lean` | 3683–3822 | `OAI/MeasureTheory/Falconer/Estimates/FiniteHolder.lean` |
| `HindmanSumsProducts/Prediction/PkgB.lean` | 3869–3946 | `OAI/Probability/InvariantIsing/Arrays/PerturbationFeatures.lean` |

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
<!-- attribution:end -->

## Other Lean dependencies

The formalization also imports Mathlib, PrimeNumberTheoremAnd, and StrongPNT. OpenAI's library pins PrimeNumberTheoremAnd at `c39a751132c88b6e8080b74c74023fd95b3d8be0` and StrongPNT at `2f5835c322314f55f1026ec2f139d704b7c45c69`; Mathlib is fixed at `d13f23b723b8a846827a245b89c10fc7d3f11612`. The [Lake manifest](lake-manifest.json) records the remaining transitive packages and their exact revisions. Their source licenses and notices remain with those dependency packages.

## Mathematical sources

The formalized result is from OpenAI, [*Monochromatic finite sums and products in the positive integers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf). The proof uses OpenAI's charted Alignment theorem `OAI.SourceMenuLiteral.charted_finite_menu_alignment`, cyclic inverse theorem `OAI.Erdos3.exists_cyclicNativeInverse_positive`, and the Brun–Titchmarsh bound `OAI.NumberTheory.Jacobsthal.Sieve.PrimeFibreBrunBound`.

The replacement for the Tao–Ziegler concatenation step is N. Kravitz, B. Kuca, and J. Leng, [*Quantitative concatenation for polynomial box norms*](https://arxiv.org/abs/2407.08636), §6.
