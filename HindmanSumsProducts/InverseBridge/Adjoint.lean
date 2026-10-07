import OAI.Combinatorics.Progressions.Estimates.AxisCompression
import OAI.Combinatorics.SumProduct.Alignment.MenuLiteral01
import HindmanSumsProducts.InverseBridge.AdjointExp

/-!
# IB.a6: the BCH adjoint formula

Split out of `InverseBridge.lean` so that the inverse-bridge nodes (`Linear.lean`, `Assembly.lean`)
can use it without an import cycle.
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3 OAI.SourceChartedMenu OAI.SourceMenuLiteral
open scoped NNReal BigOperators

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
