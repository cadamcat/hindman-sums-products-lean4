import HindmanSumsProducts.InverseBridge.Menu

/-!
Final assembly of the cyclic inverse theorem into the fixed charted menu (IB.d1).
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3 OAI.SourceChartedMenu OAI.SourceMenuLiteral
open scoped NNReal BigOperators

/-- IB.d1: assemble the cyclic polynomial inverse theorem, finite canonical list,
linearization, and real observable rotation into the frozen consumer statement. -/
theorem inverse_bridge_assembly (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔐 : Menu (2 * (t - 1))) (K : ℝ≥0) (c : ℝ), 0 < 𝔐.size ∧ 0 < c ∧
      ∀ (N : ℕ) [NeZero N] (v : ZMod N → ℝ), (∀ x, |v x| ≤ 1) →
        δ ≤ gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece 𝔐 K,
          c ≤ 𝔼 x, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1) := by
  sorry

end HindmanSumsProducts.InverseBridge
