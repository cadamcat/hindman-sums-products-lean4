import OAI.Combinatorics.Progressions.Estimates.AxisCompression
import OAI.Combinatorics.SumProduct.Alignment.MenuLiteral01
import HindmanSumsProducts.InverseBridge.AdjointExp
import HindmanSumsProducts.InverseBridge.Canonical
import HindmanSumsProducts.InverseBridge.Linear
import HindmanSumsProducts.InverseBridge.Observable
import HindmanSumsProducts.InverseBridge.Menu
import HindmanSumsProducts.InverseBridge.Assembly

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
  exact inverse_bridge_assembly t ht δ hδ

/-- IB.a6: the adjoint formula `Ad (exp a) = exp (ad a)` in BCH form, for a nilpotent rational
Lie algebra of step `S`. -/
theorem lieBCH_conj_eq_exp_ad {M : Type*} [LieRing M] [LieAlgebra ℚ M] {S : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ M M S = ⊥) (a b : M) :
    lieBCH S (lieBCH S a b) (-a) =
      ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) • ((LieAlgebra.ad ℚ M a) ^ j) b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let A := TruncatedSeries (FreeAlgebra ℚ (Fin 2)) S
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) S
  let X := scaledFreeGenerator S (0 : Fin 2)
  let Y := scaledFreeGenerator S (1 : Fin 2)
  let ev := scaledFreeLieEval (X := Fin 2) S
  letI : LieRing A := LieRing.ofAssociativeRing
  have hgen (i : Fin 2) : scaledFreeGenerator S i ∈ F.layer 1 :=
    scaledFreeGenerator_mem_layer S i
  have hX : X ∈ F.layer 1 := hgen 0
  have hY : Y ∈ F.layer 1 := hgen 1
  have had : LieAlgebra.ad ℚ A X = commutatorMap X := by
    ext z
    simpa [commutatorMap, LieAlgebra.ad_apply, LinearMap.sub_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using
      (LieRing.of_associative_ring_bracket X z)
  have hpow (j : ℕ) :
      ev (((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)) =
        ((LieAlgebra.ad ℚ A X) ^ j) Y := by
    induction j with
    | zero => simp [ev, x, X, Y]
    | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      calc
        ev ⁅x 0, ((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)⁆ =
            ⁅ev (x 0), ev (((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1))⁆ :=
              ev.map_lie _ _
        _ = ⁅X, ((LieAlgebra.ad ℚ A X) ^ j) Y⁆ := by simp [ev, x, X, Y, ih]
  let p : FreeLieAlgebra ℚ (Fin 2) :=
    ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) •
      ((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)
  have hp : ev p = ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) •
      (((LieAlgebra.ad ℚ A X) ^ j) Y) := by
    simp only [p, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun z => ((j.factorial : ℚ)⁻¹) • z) (hpow j)
  have hleft : ev (lieBCH S (lieBCH S (x 0) (x 1)) (-(x 0))) =
      lieBCH S (lieBCH S X Y) (-X) := by
    simp only [map_lieBCH, ev, x, X, Y, scaledFreeLieEval_of, map_neg]
  have hEval :
      ev (lieBCH S (lieBCH S (x 0) (x 1)) (-(x 0))) = ev p := by
    calc
      ev (lieBCH S (lieBCH S (x 0) (x 1)) (-(x 0))) =
          lieBCH S (lieBCH S X Y) (-X) := hleft
      _ = ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) •
            ((LieAlgebra.ad ℚ A X) ^ j) Y :=
          lieBCH_conj_eq_commutator_exp F hX hY had
      _ = ev p := hp.symm
  let φ := FreeLieAlgebra.lift ℚ ![a, b]
  have h := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil hEval
  have hliftpow (j : ℕ) :
      φ (((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)) =
        ((LieAlgebra.ad ℚ M a) ^ j) b := by
    induction j with
    | zero => simp [φ, x, Matrix.cons_val_zero, Matrix.cons_val_one]
    | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      calc
        φ ⁅x 0, ((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)⁆ =
            ⁅φ (x 0), φ (((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1))⁆ :=
              φ.map_lie _ _
        _ = ⁅a, ((LieAlgebra.ad ℚ M a) ^ j) b⁆ := by
              simp [φ, x, Matrix.cons_val_zero, Matrix.cons_val_one, ih]
  have hlhs : φ (lieBCH S (lieBCH S (x 0) (x 1)) (-(x 0))) =
      lieBCH S (lieBCH S a b) (-a) := by
    simp only [φ, map_lieBCH, x, map_neg, FreeLieAlgebra.lift_of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have hrhs : φ p = ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) •
      ((LieAlgebra.ad ℚ M a) ^ j) b := by
    simp only [p, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun z => ((j.factorial : ℚ)⁻¹) • z) (hliftpow j)
  exact hlhs.symm.trans (h.trans hrhs)

end HindmanSumsProducts.InverseBridge
