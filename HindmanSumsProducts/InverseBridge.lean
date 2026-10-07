import OAI.Combinatorics.Progressions.Estimates.AxisCompression
import OAI.Combinatorics.SumProduct.Alignment.MenuLiteral01

/-!
# The Gowers inverse theorem in the form §5 consumes

OpenAI's library proves an inverse theorem on cyclic groups with polynomial nilsequences
(`OAI.Erdos3.exists_cyclicNativeInverse_positive`). The paper's §5 (`05_prediction.tex` 472–489,
631–674) needs it with linear orbits on one finite charted menu, the menu type that OpenAI's
charted Alignment theorem consumes. Design: `research/blueprint/INVERSE-BRIDGE.md` (consumer §0,
ledger §1, sketches §2, construction §4). The menu step is `2 * (t - 1)`: linearizing a polynomial
orbit doubles the step.
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3 OAI.SourceChartedMenu OAI.SourceMenuLiteral
open scoped NNReal BigOperators

/-- Gowers inverse theorem in the form paper §5 consumes (05:631–674): cyclic, real input, one
finite charted menu fixed by `(t, δ)`, linear orbits, `[0,1]`-valued observables with a common
Lipschitz bound, positive correlation with the affine image `2 · obs − 1`. -/
theorem cyclic_inverse_menu (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔐 : Menu (2 * (t - 1))) (K : ℝ≥0) (c : ℝ), 0 < 𝔐.size ∧ 0 < c ∧
      ∀ (N : ℕ) [NeZero N] (v : ZMod N → ℝ), (∀ x, |v x| ≤ 1) →
        δ ≤ gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece 𝔐 K, c ≤ 𝔼 x, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1) := by
  sorry

/-- IB.a6: the adjoint formula `Ad (exp a) = exp (ad a)` in BCH form, for a nilpotent rational
Lie algebra of step `S`. -/
theorem lieBCH_conj_eq_exp_ad {M : Type*} [LieRing M] [LieAlgebra ℚ M] {S : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ M M S = ⊥) (a b : M) :
    lieBCH S (lieBCH S a b) (-a) =
      ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) • ((LieAlgebra.ad ℚ M a) ^ j) b := by
  sorry

end HindmanSumsProducts.InverseBridge
