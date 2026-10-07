import HindmanSumsProducts.Main

/-!
Checks the solution declaration against the challenge statement.
-/

namespace HindmanSumsProducts.Verification

abbrev targetStatement : Prop :=
  ∀ (r : ℕ) (χ : ℕ → Fin r) (m : ℕ),
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c

example : type_of% @HindmanSumsProducts.hindman_finite_sums_products = targetStatement := rfl

end HindmanSumsProducts.Verification
