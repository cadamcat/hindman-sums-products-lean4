import HindmanSumsProducts.Prediction.PkgOpusDpo

/-! Helpers for the zero-dimensional case of `dual_products_orthogonal`. -/

namespace HindmanSumsProducts
namespace Prediction

open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

noncomputable section

private def l_dflat_poolTupleSupport {q : ℕ} (lo hi : Fin q → ℕ) :
    Finset (Fin q → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

private lemma l_dflat_poolMass_zero_of_not_support {q : ℕ} (lo hi : Fin q → ℕ)
    (p : Fin q → ℕ) (hp : p ∉ l_dflat_poolTupleSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnotall : ¬ ∀ i : Fin q, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hp
    simpa [l_dflat_poolTupleSupport] using hall
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private lemma l_dflat_poolProbability_summable {q : ℕ} (lo hi : Fin q → ℕ)
    (E : (Fin q → ℕ) → Prop) :
    Summable (fun p => independentPrimePoolMass lo hi p * if E p then 1 else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := l_dflat_poolTupleSupport lo hi)
  intro p hp
  rw [l_dflat_poolMass_zero_of_not_support lo hi p hp]
  simp

/-- A bounded function remains bounded under the conditioned good-slot average.  This local copy
is needed because the general theorem lives downstream of `Results`, which imports this file. -/
private theorem l_dflat_goodSlotAverage_abs_le {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (S : FromArithmetic.MasterScales K As sl Dm)
    (l : Fin K) (N : ℕ) {q : ℕ} (good : (Fin q → ℕ) → Prop)
    (F : (Fin q → ℕ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ p, good p → |F p| ≤ C) :
    |goodSlotAverage S l N good F| ≤ C := by
  classical
  let lo : Fin q → ℕ := fun _ => (S.primeStage.pool N l).lower
  let hi : Fin q → ℕ := fun _ => (S.primeStage.pool N l).upper
  let mass : (Fin q → ℕ) → ℝ := independentPrimePoolMass lo hi
  let gp : ℝ := gapSlotProbability S l N good
  let num : ℝ := ∑' p : Fin q → ℕ, mass p * if good p then F p else 0
  have hnumSumm : Summable (fun p : Fin q → ℕ => mass p * if good p then F p else 0) := by
    apply summable_of_ne_finset_zero (s := l_dflat_poolTupleSupport lo hi)
    intro p hp
    change independentPrimePoolMass lo hi p * (if good p then F p else 0) = 0
    rw [l_dflat_poolMass_zero_of_not_support lo hi p hp]
    simp
  have hposSumm : Summable (fun p : Fin q → ℕ => mass p * if good p then 1 else 0) :=
    l_dflat_poolProbability_summable lo hi good
  have hconstantSumm : Summable (fun p : Fin q → ℕ => mass p * if good p then C else 0) := by
    apply summable_of_ne_finset_zero (s := l_dflat_poolTupleSupport lo hi)
    intro p hp
    change independentPrimePoolMass lo hi p * (if good p then C else 0) = 0
    rw [l_dflat_poolMass_zero_of_not_support lo hi p hp]
    simp
  have hgp : gp = ∑' p : Fin q → ℕ, mass p * if good p then 1 else 0 := by
    change independentPrimePoolProbability lo hi good = _
    rfl
  have hmassNonneg (p : Fin q → ℕ) : 0 ≤ mass p := by
    dsimp [mass, independentPrimePoolMass]
    apply Finset.prod_nonneg
    intro i hii
    have hpm : 0 ≤ primePoolMass (lo i) (hi i) := by
      unfold primePoolMass
      positivity
    unfold primePoolLaw
    split_ifs <;> positivity
  have hupper : num ≤ C * gp := by
    calc
      num ≤ ∑' p : Fin q → ℕ, mass p * if good p then C else 0 := by
        apply Summable.tsum_le_tsum
          (f := fun p : Fin q → ℕ => mass p * if good p then F p else 0)
          (g := fun p => mass p * if good p then C else 0)
        · intro p
          by_cases hp : good p
          · simpa [hp] using mul_le_mul_of_nonneg_left (abs_le.mp (hF p hp)).2
              (hmassNonneg p)
          · simp [hp]
        · exact hnumSumm
        · exact hconstantSumm
      _ = C * gp := by
        rw [hgp, ← tsum_mul_left]
        apply tsum_congr
        intro p
        by_cases hp : good p <;> simp [hp] <;> ring
  have hnegSumm : Summable (fun p : Fin q → ℕ => mass p * if good p then -C else 0) := by
    apply summable_of_ne_finset_zero (s := l_dflat_poolTupleSupport lo hi)
    intro p hp
    change independentPrimePoolMass lo hi p * (if good p then -C else 0) = 0
    rw [l_dflat_poolMass_zero_of_not_support lo hi p hp]
    simp
  have hnegEq : -C * gp =
      ∑' p : Fin q → ℕ, mass p * if good p then -C else 0 := by
    rw [hgp, ← tsum_mul_left]
    apply tsum_congr
    intro p
    by_cases hp : good p <;> simp [hp] <;> ring
  have hlower : -C * gp ≤ num := by
    calc
      -C * gp = ∑' p : Fin q → ℕ, mass p * if good p then -C else 0 := hnegEq
      _ ≤ num := Summable.tsum_le_tsum
        (fun p => by
          by_cases hp : good p
          · simpa [hp] using mul_le_mul_of_nonneg_left (abs_le.mp (hF p hp)).1
              (hmassNonneg p)
          · simp [hp])
        hnegSumm hnumSumm
  have hlower' : -(C * gp) ≤ num := by simpa [neg_mul] using hlower
  have habsNum : |num| ≤ C * gp := abs_le.mpr ⟨hlower', hupper⟩
  by_cases hgp0 : gp = 0
  · unfold goodSlotAverage
    rw [show gapSlotProbability S l N good = gp by rfl, hgp0]
    simp
    exact hC
  · have hgpPos : 0 < gp := by
      have hgpNonneg : 0 ≤ gp := by
        rw [hgp]
        exact tsum_nonneg fun p => mul_nonneg (hmassNonneg p) (by split_ifs <;> norm_num)
      exact lt_of_le_of_ne hgpNonneg (Ne.symm hgp0)
    change |gp⁻¹ * num| ≤ C
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hgpPos.le)]
    calc
      gp⁻¹ * |num| ≤ gp⁻¹ * (C * gp) :=
        mul_le_mul_of_nonneg_left habsNum (inv_nonneg.mpr hgpPos.le)
      _ = C := by field_simp [ne_of_gt hgpPos]

/-- A zero-dimensional dual test is its prime-slot average of the bounded coefficient. -/
theorem l_dflat_dualTest_eq_goodSlotAverage
    {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (T : CubeTemplate)
    (l : Fin K) (J0 N : ℕ) (I : DualInput MS B T N) (hd : T.d = 0) (y : ℤ) :
    dualTest MS B T l J0 N I y =
      goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N) I.e := by
  classical
  have hEmptySet (ω : Finset (Fin 0)) : ω = ∅ := by
    ext j
    exact Fin.elim0 j
  have hErase : (Finset.univ : Finset (Finset (Fin T.d))).erase ∅ = ∅ := by
    rw [hd]
    ext ω
    simp [hEmptySet ω]
  have hShift (L : ℕ) :
      shiftAverage (Fin T.d) L (fun _ : (Fin T.d → Fin 2 → ℕ) => (1 : ℝ)) = 1 := by
    rw [hd]
    simp [shiftAverage]
  have hProd (p : Fin T.q → ℕ) (u : Fin T.d → Fin 2 → ℕ) (z : ℤ) :
      (∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅,
        I.g ω p (z + (T.modulus (corrScales MS) N p : ℤ) *
          ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))) = 1 := by
    rw [hErase]
    simp
  unfold dualTest
  congr 1
  funext p
  simp_rw [hProd]
  rw [hShift]
  ring

/-- Every zero-dimensional dual test has absolute value at most one. -/
theorem l_dflat_dualTest_abs_le_one
    {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (T : CubeTemplate)
    (l : Fin K) (J0 N : ℕ) (I : DualInput MS B T N) (hd : T.d = 0) (y : ℤ) :
    |dualTest MS B T l J0 N I y| ≤ 1 := by
  rw [l_dflat_dualTest_eq_goodSlotAverage MS B T l J0 N I hd y]
  apply l_dflat_goodSlotAverage_abs_le (corrScales MS) l N
    (T.Good (corrScales MS) l N) I.e 1 (by norm_num)
  intro p hp
  exact I.e_bound p

end

end Prediction
end HindmanSumsProducts
