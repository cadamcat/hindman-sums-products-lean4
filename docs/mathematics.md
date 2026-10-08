# The statement and proof

## The formal statement

The public result is `HindmanSumsProducts.hindman_finite_sums_products`, in [Main.lean](../HindmanSumsProducts/Main.lean):

```lean
(r : ℕ) (χ : ℕ → Fin r) (m : ℕ) :
  ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
    ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c
```

Thus every finite colouring `χ : ℕ → Fin r` and every `m` yield a set `A` with exactly `m` distinct positive elements and a colour `c` such that each nonempty subset `B ⊆ A` has both its sum and product coloured `c`. Singletons are included among the subsets.

[Challenge.lean](../Challenge.lean) states the same theorem in Mathlib vocabulary with a placeholder proof for Comparator; the formal proof is in `Main.lean`. [Challenge.json](../Challenge.json) names the challenge and solution modules and the permitted axioms. The theorem's value at `0` is immaterial: a nonempty sum or product of positive elements is positive.

The main theorem in OpenAI's paper also asserts a separation clause. The conjecture does not require that clause, and this formalization omits it.

## Proof organization

Some source comments cite planning notes under `research/`; those notes are development records and are not part of this repository.

The proof follows the paper's deduction from the Prediction and Alignment principles:

| Part | Lean development | Paper |
| --- | --- | --- |
| Deduce the theorem from the two principles, select a chain, and obtain finite sums | [`Framework.lean`](../HindmanSumsProducts/Framework.lean) (`main_of_principles`), [`ChainSelection/`](../HindmanSumsProducts/ChainSelection/) | §2 |
| Alignment Principle for charted menus | OpenAI's `OAI.SourceMenuLiteral.charted_finite_menu_alignment`, used through [`OAIAlignment.lean`](../HindmanSumsProducts/OAIAlignment.lean) | §6–§8 |
| Arithmetic: master scales, rough coprimality, sampling, product law, and linear forms | [`Arithmetic/`](../HindmanSumsProducts/Arithmetic/) | §3 |
| Correlation: mask removal, additive elimination, and the correlation test | [`Correlation.lean`](../HindmanSumsProducts/Correlation.lean), [`Correlation/`](../HindmanSumsProducts/Correlation/) | §4 |
| Prediction Principle: test laws, dense models, recipes, projections, subgroup inverse step, and completion | [`Prediction/`](../HindmanSumsProducts/Prediction/) | §5 |
| Missing-corner lemma for the recipes | [`CubeCorner.lean`](../HindmanSumsProducts/CubeCorner.lean), [`CubeCornerCharted.lean`](../HindmanSumsProducts/CubeCornerCharted.lean) | §7 |

## Differences from the paper

Two steps in §5 use different theorems.

- **Concatenation.** The paper uses the Tao–Ziegler concatenation theorem. The formalization uses subgroup box-norm concatenation from N. Kravitz, B. Kuca, and J. Leng, [*Quantitative concatenation for polynomial box norms*](https://arxiv.org/abs/2407.08636), §6. It is proved in [`Concatenation.lean`](../HindmanSumsProducts/Concatenation.lean) and serves both concatenation uses in §5, with inverse degree `2^(2^d) − 1`.
- **Inverse theorem.** The paper uses the Green–Tao–Ziegler inverse theorem for linear orbits on a fixed finite family of nilmanifolds. OpenAI's library supplies the cyclic inverse theorem `OAI.Erdos3.exists_cyclicNativeInverse_positive` for polynomial orbits. [`InverseBridge/`](../HindmanSumsProducts/InverseBridge/) transfers it to the form used in §5: each model is covered by a canonical model with a coordinate sublattice, polynomial orbits are linearized by a Baker–Campbell–Hausdorff argument, and observables descend to one finite charted menu.

The outside results are identified in [THIRD_PARTY.md](../THIRD_PARTY.md): Mathlib, the prime number theorem in arithmetic progressions through PrimeNumberTheoremAnd's Wiener results, and OpenAI's Brun–Titchmarsh bound.
