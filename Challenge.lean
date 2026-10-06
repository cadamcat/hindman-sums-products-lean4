import Mathlib

/-!
# Hindman's finite sums and products conjecture

Every finite colouring of the positive integers contains, for every `m`, an `m`-element set of
positive integers whose nonempty subset sums and nonempty subset products all have one colour.

A colouring with `r` colours is a map `χ : ℕ → Fin r`. Its value at `0` never matters: the
elements of `A` are positive, so every nonempty subset sum and product is positive.

This file states the target in Mathlib vocabulary only. The proof is in
`HindmanSumsProducts.Main`, which proves a theorem of the same name and statement.
-/

namespace HindmanSumsProducts

theorem hindman_finite_sums_products (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) :
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  sorry

end HindmanSumsProducts
