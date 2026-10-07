import HindmanSumsProducts.Prediction.Imported
import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
import HindmanSumsProducts.InverseBridge

/-!
# The outside inverse theorem used by §5

The two external statements of 05:450–489 are replaced as follows:

* Tao–Ziegler's Bessel inequality (eq:prediction-bessel) is replaced by the subgroup box-norm
  concatenation `HindmanSumsProducts.SubgroupBox.combine_subgroups` (`Concatenation.lean`), used
  directly; there is no copy here.  The concatenation degree is `t = 2^k − 1` with `k = 2^d`.
* The Green–Tao–Ziegler interval inverse theorem and the cyclic-to-interval periodization
  (05:472–489, 597–642) are replaced by the cyclic inverse theorem
  `HindmanSumsProducts.InverseBridge.cyclic_inverse_menu` (`InverseBridge.lean`, stated as
  `research/blueprint/INVERSE-BRIDGE.md` §0 writes it).  Its menu has step `2(t − 1)`.
-/
