import HindmanSumsProducts.Framework
import HindmanSumsProducts.Prediction

/-!
# Hindman's finite sums and products theorem

The final theorem, with the same name and statement as `Challenge.lean`: the deduction of §2
(`main_of_principles`, from OpenAI's Alignment theorem and the chain selection) applied to the
Prediction Principle proved in §3–§5.
-/

namespace HindmanSumsProducts

theorem hindman_finite_sums_products (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) :
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c :=
  main_of_principles Prediction.prediction_principle r χ m

end HindmanSumsProducts
