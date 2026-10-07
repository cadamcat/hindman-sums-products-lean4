import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.PkgElim2

/-! Weighted variance replacement for additive elimination. -/

namespace HindmanSumsProducts
open Filter
open scoped BigOperators Topology

noncomputable section

theorem sol_var_linear_mono {α : Type*} (E : (α → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ E f)
    {f g : α → ℝ} (hfg : ∀ x, f x ≤ g x) : E f ≤ E g := by
  have h := hpos (g - f) (fun x => sub_nonneg.mpr (hfg x))
  simpa only [map_sub, sub_nonneg] using h

/-- Weighted Cauchy–Schwarz for a positive linear expectation. -/
theorem sol_var_weighted_cauchy {α : Type*} (E : (α → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ E f)
    (B G D : α → ℝ) (hB : ∀ x, 0 ≤ B x) (hG : ∀ x, |G x| ≤ B x) :
    |E (fun x => G x * D x)| ^ 2 ≤
      E B * E (fun x => B x * D x ^ 2) := by
  let A := E (fun x => B x * |D x|)
  have hA : 0 ≤ A := hpos _ (fun x => mul_nonneg (hB x) (abs_nonneg _))
  have hmajor : |E (fun x => G x * D x)| ≤ A := by
    apply abs_le.mpr
    constructor
    · have h := sol_var_linear_mono E hpos
        (f := fun x => -(B x * |D x|)) (g := fun x => G x * D x) (fun x => by
          have hm := mul_le_mul_of_nonneg_right (hG x) (abs_nonneg (D x))
          have ha := neg_abs_le (G x * D x)
          rw [abs_mul] at ha
          linarith)
      change E (-(fun x => B x * |D x|)) ≤ E (fun x => G x * D x) at h
      rw [map_neg] at h
      exact h
    · exact sol_var_linear_mono E hpos (fun x => by
        calc
          G x * D x ≤ |G x * D x| := le_abs_self _
          _ = |G x| * |D x| := abs_mul _ _
          _ ≤ B x * |D x| := mul_le_mul_of_nonneg_right (hG x) (abs_nonneg _))
  have hquadratic (t : ℝ) :
      0 ≤ E B * (t * t) + (-2 * A) * t + E (fun x => B x * D x ^ 2) := by
    have heq : (fun x => B x * (|D x| - t) ^ 2) =
        ((fun x => B x * D x ^ 2) - (2 * t) • (fun x => B x * |D x|)) +
          t ^ 2 • B := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← sq_abs (D x)]
      ring
    have h := hpos (fun x => B x * (|D x| - t) ^ 2)
      (fun x => mul_nonneg (hB x) (sq_nonneg _))
    rw [heq, map_add, map_sub, map_smul, map_smul] at h
    dsimp only [smul_eq_mul] at h
    change 0 ≤ E (fun x => B x * D x ^ 2) - (2 * t) * A + t ^ 2 * E B at h
    nlinarith only [h]
  have hcs : A ^ 2 ≤ E B * E (fun x => B x * D x ^ 2) := by
    have h := discrim_le_zero hquadratic
    unfold discrim at h
    nlinarith only [h]
  exact ((sq_le_sq₀ (abs_nonneg _) hA).2 hmajor).trans hcs

variable {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- The finite good-support formula makes the elimination expectation linear. -/
def sol_var_eliminationLinear (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 : ℕ) :
    (((Fin q → ℕ) × (Fin m → ℚ) × (NonTarget Sh → Fin 2 → ℕ)) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := eliminationAverage S C N dirs tests J0 (fun p z u => F (p, z, u))
  map_add' F G := by
    simp only [c_elim2_eliminationAverage_eq_finiteGoodSupport, Pi.add_apply]
    simp only [shiftAverage, Finset.sum_add_distrib, mul_add]
  map_smul' c F := by
    simp only [c_elim2_eliminationAverage_eq_finiteGoodSupport,
      Pi.smul_apply, smul_eq_mul, shiftAverage]
    simp only [← Finset.mul_sum, RingHom.id_apply, mul_assoc, mul_left_comm]

theorem sol_var_eliminationLinear_nonneg (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 : ℕ)
    (F : ((Fin q → ℕ) × (Fin m → ℚ) × (NonTarget Sh → Fin 2 → ℕ)) → ℝ)
    (hF : ∀ x, 0 ≤ F x) : 0 ≤ sol_var_eliminationLinear S C N dirs tests J0 F := by
  classical
  have hprime (lo hi p : ℕ) : 0 ≤ primePoolLaw lo hi p := by
    unfold primePoolLaw primePoolMass
    split_ifs <;> positivity
  have hgap (p : Fin q → ℕ) : 0 ≤ gapSlotMass S C.gap N p := by
    unfold gapSlotMass independentPrimePoolMass
    exact Finset.prod_nonneg (fun i _ => hprime _ _ _)
  have hprob : 0 ≤ gapSlotProbability S C.gap N
      (GoodTuple S C.gap N tests dirs.poly) := by
    apply tsum_nonneg
    intro p
    exact mul_nonneg (hgap p) (by split_ifs <;> norm_num)
  have hpivot (z : Fin m → ℤ) : 0 ≤ pivotMass S.core.parameters C N z := by
    apply Finset.prod_nonneg
    intro k hk
    unfold harmonicLaw harmonicNormalizer
    split_ifs <;> positivity
  change 0 ≤ eliminationAverage S C N dirs tests J0 (fun p z u => F (p, z, u))
  rw [c_elim2_eliminationAverage_eq_finiteGoodSupport]
  apply mul_nonneg (inv_nonneg.mpr hprob)
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro z hz
  apply mul_nonneg (mul_nonneg (hgap p.1) (hpivot z.1))
  unfold shiftAverage
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun u _ => hF _)

/-- Expand the centered second moment through the linear expectation. -/
theorem sol_var_centered_moment {α : Type*} (E : (α → ℝ) →ₗ[ℝ] ℝ)
    (B H : α → ℝ) (c : ℝ) :
    E (fun x => B x * (H x - c) ^ 2) =
      E (fun x => B x * H x ^ 2) - (2 * c) * E (fun x => B x * H x) +
        c ^ 2 * E B := by
  have heq : (fun x => B x * (H x - c) ^ 2) =
      ((fun x => B x * H x ^ 2) - (2 * c) • (fun x => B x * H x)) + c ^ 2 • B := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, map_add, map_sub, map_smul, map_smul]
  rfl

end
end HindmanSumsProducts
