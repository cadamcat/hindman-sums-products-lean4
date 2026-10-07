import HindmanSumsProducts.Prediction.Imported
import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative

/-!
# The outside inverse theorem used by §5

The two external statements of 05:450–489 are replaced as decided by the coordinator:

* Tao–Ziegler's Bessel inequality (eq:prediction-bessel) is replaced by the subgroup box-norm
  concatenation `HindmanSumsProducts.SubgroupBox.combine_subgroups` (`Concatenation.lean`), used
  directly; there is no copy here.  The concatenation degree is `t = 2^k − 1` with `k = 2^d`.
* The Green–Tao–Ziegler interval inverse theorem and the cyclic-to-interval periodization
  (05:472–489, 597–642) are replaced by the cyclic inverse theorem `cyclic_inverse_menu` below,
  stated exactly as `research/blueprint/INVERSE-BRIDGE.md` §0 writes it.  Its menu has step
  `2(t − 1)`.  When the inverse-bridge lane delivers this declaration, delete it here and import
  that file instead.
-/

namespace HindmanSumsProducts.InverseBridge
open OAI OAI.Erdos3 OAI.SourceChartedMenu OAI.SourceMenuLiteral
open scoped NNReal BigOperators

/-- Gowers inverse theorem in the form paper Section 5 consumes (05:631–674): cyclic, real input,
one finite charted menu fixed by (t, δ), linear orbits, `[0,1]`-valued observables with a
common Lipschitz bound, positive correlation with the affine image `2·obs − 1`. -/
theorem cyclic_inverse_menu (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔐 : Menu (2 * (t - 1))) (K : ℝ≥0) (c : ℝ), 0 < 𝔐.size ∧ 0 < c ∧
      ∀ (N : ℕ) [NeZero N] (v : ZMod N → ℝ), (∀ x, |v x| ≤ 1) →
        δ ≤ gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece 𝔐 K, c ≤ 𝔼 x, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1) := by
  sorry

end HindmanSumsProducts.InverseBridge
