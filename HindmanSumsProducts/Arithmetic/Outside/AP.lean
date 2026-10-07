import HindmanSumsProducts.Arithmetic.Defs
import PrimeNumberTheoremAnd.Erdos970.Wiener

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts.Arithmetic.Outside
noncomputable section

private def apPartialSum (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, b i

private def reciprocalBand (Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico Y (2 * Y), 1 / (n : ℝ)

private def weightedBand (b : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico Y (2 * Y), b n / (n : ℝ)

private theorem reciprocalBand_lower {Y : ℕ} (hY : 2 ≤ Y) :
    (1 / 2 : ℝ) ≤ reciprocalBand Y := by
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hterm : ∀ n ∈ Finset.Ico Y (2 * Y),
      (1 / (2 * (Y : ℝ)) : ℝ) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hnI := Finset.mem_Ico.mp hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnle : (n : ℝ) ≤ 2 * (Y : ℝ) := by exact_mod_cast hnI.2.le
    exact (div_le_div_iff₀ (by positivity) hnpos).2 (by nlinarith)
  have hcard : (Finset.Ico Y (2 * Y)).card = Y := by
    rw [Nat.card_Ico]
    omega
  calc
    (1 / 2 : ℝ) = (Finset.Ico Y (2 * Y)).card *
        (1 / (2 * (Y : ℝ))) := by rw [hcard]; field_simp
    _ = ∑ _n ∈ Finset.Ico Y (2 * Y), 1 / (2 * (Y : ℝ)) := by simp
    _ ≤ reciprocalBand Y := Finset.sum_le_sum hterm

private theorem reciprocalBand_upper {Y : ℕ} (hY : 0 < Y) :
    reciprocalBand Y ≤ 1 := by
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hterm : ∀ n ∈ Finset.Ico Y (2 * Y),
      1 / (n : ℝ) ≤ 1 / (Y : ℝ) := by
    intro n hn
    have hnI := Finset.mem_Ico.mp hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hYle : (Y : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnI.1
    exact (div_le_div_iff₀ hnpos hYpos).2 (by nlinarith)
  have hcard : (Finset.Ico Y (2 * Y)).card = Y := by
    rw [Nat.card_Ico]
    omega
  calc
    reciprocalBand Y ≤ ∑ _n ∈ Finset.Ico Y (2 * Y), 1 / (Y : ℝ) :=
      Finset.sum_le_sum hterm
    _ = (Y : ℝ) * (1 / (Y : ℝ)) := by rw [Finset.sum_const, hcard]; simp
    _ = 1 := by field_simp

private theorem reciprocal_weighted_band_tendsto
    (b : ℕ → ℝ) (c : ℝ)
    (hlim : Tendsto (fun n : ℕ => apPartialSum b n / (n : ℝ))
      atTop (𝓝 c)) :
    Tendsto (fun Y : ℕ => weightedBand b Y / reciprocalBand Y)
      atTop (𝓝 c) := by
  let A := apPartialSum b
  let E : ℕ → ℝ := fun n => A n - (n : ℝ) * c
  have herr : Tendsto (fun n : ℕ => E n / (n : ℝ)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n : ℕ => A n / (n : ℝ) - c) atTop (𝓝 0) := by
      simpa using hlim.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
    have heq : (fun n : ℕ => E n / (n : ℝ)) =ᶠ[atTop]
        (fun n => A n / (n : ℝ) - c) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      dsimp [E]
      field_simp
      <;> ring
    exact hsub.congr' heq.symm
  have habel (Y : ℕ) (hY : 0 < Y) :
      weightedBand b Y =
        (1 / ((2 * Y - 1 : ℕ) : ℝ)) * A (2 * Y) -
          (1 / (Y : ℝ)) * A Y -
            ∑ i ∈ Finset.Ico Y (2 * Y - 1),
              (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * A (i + 1) := by
    simpa [weightedBand, A, apPartialSum, one_div, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using
      (Finset.sum_Ico_by_parts (fun n : ℕ => (n : ℝ)⁻¹) b (by omega : Y < 2 * Y))
  have hconst (Y : ℕ) (hY : 0 < Y) :
      c * reciprocalBand Y =
        (1 / ((2 * Y - 1 : ℕ) : ℝ)) * ((2 * Y : ℝ) * c) -
          (1 / (Y : ℝ)) * ((Y : ℝ) * c) -
            ∑ i ∈ Finset.Ico Y (2 * Y - 1),
              (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * ((i + 1 : ℝ) * c) := by
    have h := Finset.sum_Ico_by_parts (fun n : ℕ => (n : ℝ)⁻¹) (fun _ => c)
      (by omega : Y < 2 * Y)
    have hconstSum (n : ℕ) : (∑ i ∈ Finset.range n, c) = (n : ℝ) * c := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hconstSum] at h
    calc
      c * reciprocalBand Y =
          ∑ i ∈ Finset.Ico Y (2 * Y), c * (1 / (i : ℝ)) := by
            rw [reciprocalBand, Finset.mul_sum]
      _ = _ := by simpa [one_div, smul_eq_mul, mul_comm] using h
  have hdecomp (n : ℕ) : A n = (n : ℝ) * c + E n := by
    dsimp [E]
    ring
  have hbandError (Y : ℕ) (hY : 2 ≤ Y) :
      weightedBand b Y - c * reciprocalBand Y =
        (1 / ((2 * Y - 1 : ℕ) : ℝ)) * E (2 * Y) -
          (1 / (Y : ℝ)) * E Y -
            ∑ i ∈ Finset.Ico Y (2 * Y - 1),
              (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * E (i + 1) := by
    rw [habel Y (by omega), hconst Y (by omega)]
    have hsumA :
        (∑ i ∈ Finset.Ico Y (2 * Y - 1),
          (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * A (i + 1)) =
          (∑ i ∈ Finset.Ico Y (2 * Y - 1),
            (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * ((i + 1 : ℝ) * c)) +
            ∑ i ∈ Finset.Ico Y (2 * Y - 1),
              (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * E (i + 1) := by
      calc
        _ = ∑ i ∈ Finset.Ico Y (2 * Y - 1),
              (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) *
                (((i + 1 : ℝ) * c) + E (i + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa only [Nat.cast_add, Nat.cast_one] using
            congrArg (fun z : ℝ =>
              (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * z) (hdecomp (i + 1))
        _ = _ := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
    rw [hsumA, hdecomp (2 * Y), hdecomp Y]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε' : 0 < ε / 16 := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop, |E n / (n : ℝ)| < ε / 16 :=
    herr.abs.eventually (Iio_mem_nhds (by simpa using hε'))
  obtain ⟨N0, hN0⟩ := (eventually_atTop.1 hsmall)
  let N : ℕ := max N0 1
  have hN (n : ℕ) (hn : N ≤ n) : |E n / (n : ℝ)| < ε / 16 :=
    hN0 n (le_trans (le_max_left _ _) hn)
  refine ⟨max N 2, ?_⟩
  intro Y hYmax
  have hY : 2 ≤ Y := le_trans (le_max_right _ _) hYmax
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hKpos : 0 < reciprocalBand Y := lt_of_lt_of_le (by norm_num) (reciprocalBand_lower hY)
  have heSmall (n : ℕ) (hn : N ≤ n) : |E n| ≤ (ε / 16) * (n : ℝ) := by
    have h := hN n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h' : |E n| / (n : ℝ) < ε / 16 := by
      simpa [abs_div, abs_of_pos hnpos] using h
    exact le_of_lt ((div_lt_iff₀ hnpos).1 h')
  have htwoY : N ≤ 2 * Y := by omega
  have hYsmall := heSmall Y (le_trans (le_max_left _ _) hYmax)
  have h2Ysmall := heSmall (2 * Y) htwoY
  have hsumSmall :
      |∑ i ∈ Finset.Ico Y (2 * Y - 1),
          (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * E (i + 1)| ≤ ε / 16 := by
    calc
      _ ≤ ∑ i ∈ Finset.Ico Y (2 * Y - 1),
          |(1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * E (i + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico Y (2 * Y - 1), (ε / 16) / (i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiI := Finset.mem_Ico.mp hi
        have hiNat : 0 < i := lt_of_lt_of_le (by omega : 0 < Y) hiI.1
        have hiPos : 0 < (i : ℝ) := by exact_mod_cast hiNat
        have hi1Pos : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
        have hi1N : N ≤ i + 1 := by omega
        have he := heSmall (i + 1) hi1N
        have hdiff : (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) ≤ 0 := by
          apply sub_nonpos.mpr
          apply (div_le_div_iff₀ hi1Pos hiPos).2
          have hiLt : (i : ℝ) < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self i
          nlinarith
        have hcoef : |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| =
            1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ) := by
          rw [abs_of_nonpos hdiff]
          field_simp [hiPos.ne', hi1Pos.ne']
          norm_num [Nat.cast_add]
        have hmul :
            (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ)) *
                ((ε / 16) * ((i + 1 : ℕ) : ℝ)) = (ε / 16) / (i : ℝ) := by
          field_simp [hiPos.ne', hi1Pos.ne']
          rw [Nat.cast_add, Nat.cast_one]
          ring
        calc
          _ = |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| * |E (i + 1)| := by rw [abs_mul]
          _ ≤ |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| *
              ((ε / 16) * ((i + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left he (abs_nonneg _)
          _ = (ε / 16) / (i : ℝ) := by rw [hcoef, hmul]
      _ ≤ ε / 16 := by
        have hsub : Finset.Ico Y (2 * Y - 1) ⊆ Finset.Ico Y (2 * Y) := by
          intro i hi
          have hiI := Finset.mem_Ico.mp hi
          have hupper : 2 * Y - 1 < 2 * Y := Nat.sub_lt (by omega) (by omega)
          exact Finset.mem_Ico.mpr ⟨hiI.1, hiI.2.trans hupper⟩
        have hrecip :
            (∑ i ∈ Finset.Ico Y (2 * Y - 1), 1 / (i : ℝ)) ≤ 1 := by
          calc
            _ ≤ reciprocalBand Y :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i hi _; positivity)
            _ ≤ 1 := reciprocalBand_upper (by omega)
        calc
          _ = (ε / 16) *
              (∑ i ∈ Finset.Ico Y (2 * Y - 1), 1 / (i : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ ≤ ε / 16 := by nlinarith [hrecip]
  have hfirst : |(1 / ((2 * Y - 1 : ℕ) : ℝ)) * E (2 * Y)| ≤ ε / 8 := by
    have hden : 0 < ((2 * Y - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * Y - 1)
    have hdenY : (Y : ℝ) ≤ ((2 * Y - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : Y ≤ 2 * Y - 1)
    have h2Ysmall' : |E (2 * Y)| ≤ (ε / 16) * (2 * (Y : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h2Ysmall
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ((2 * Y - 1 : ℕ) : ℝ))]
    calc
      _ ≤ (1 / ((2 * Y - 1 : ℕ) : ℝ)) * ((ε / 16) * (2 * (Y : ℝ))) :=
        mul_le_mul_of_nonneg_left h2Ysmall' (by positivity)
      _ ≤ ε / 8 := by
        have hfinal : ((ε / 16) * (2 * (Y : ℝ))) /
            ((2 * Y - 1 : ℕ) : ℝ) ≤ ε / 8 := by
          apply (div_le_iff₀ hden).2
          have hmul := mul_le_mul_of_nonneg_left hdenY
            (by positivity : 0 ≤ ε / 8)
          nlinarith [hmul]
        simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hfinal
  have hsecond : |(1 / (Y : ℝ)) * E Y| ≤ ε / 16 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (Y : ℝ))]
    calc
      _ ≤ (1 / (Y : ℝ)) * ((ε / 16) * (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left hYsmall (by positivity)
      _ = ε / 16 := by field_simp [hYpos.ne']
  have herrBound :
      |weightedBand b Y - c * reciprocalBand Y| ≤ ε / 4 := by
    rw [hbandError Y hY]
    have hfirstsecond :
        |(1 / ((2 * Y - 1 : ℕ) : ℝ)) * E (2 * Y) -
          (1 / (Y : ℝ)) * E Y| ≤ ε / 8 + ε / 16 := by
      calc
        _ = |(1 / ((2 * Y - 1 : ℕ) : ℝ)) * E (2 * Y) +
              -((1 / (Y : ℝ)) * E Y)| := by congr 1 <;> ring
        _ ≤ _ := (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add hfirst hsecond)
    calc
      _ = |((1 / ((2 * Y - 1 : ℕ) : ℝ)) * E (2 * Y) -
            (1 / (Y : ℝ)) * E Y) -
            ∑ i ∈ Finset.Ico Y (2 * Y - 1),
              (1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)) * E (i + 1)| := rfl
      _ ≤ _ := (abs_add_le _ _).trans (by
        simpa [abs_neg] using add_le_add hfirstsecond hsumSmall)
      _ ≤ ε / 4 := by linarith
  have hratioBound :
      |(weightedBand b Y - c * reciprocalBand Y) / reciprocalBand Y| ≤ ε / 2 := by
    rw [abs_div, abs_of_pos hKpos]
    apply (div_le_iff₀ hKpos).2
    have hlower := reciprocalBand_lower hY
    have hmul := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ ε / 2)
    nlinarith [herrBound]
  have hdist :
      dist (weightedBand b Y / reciprocalBand Y) c < ε := by
    rw [Real.dist_eq]
    have heq : weightedBand b Y / reciprocalBand Y - c =
        (weightedBand b Y - c * reciprocalBand Y) / reciprocalBand Y := by
      field_simp [hKpos.ne']
      <;> ring
    rw [heq]
    exact lt_of_le_of_lt hratioBound (by linarith)
  exact hdist

private def residueLambdaTerm (Q : ℕ) (a : Fin Q) (n : ℕ) : ℝ :=
  if n % Q = a.val then ArithmeticFunction.vonMangoldt n else 0

private def residuePrimeLogTerm (Q : ℕ) (a : Fin Q) (n : ℕ) : ℝ :=
  if n.Prime ∧ n % Q = a.val then Real.log n else 0

private def residuePrimeHarmonicTerm (Q : ℕ) (a : Fin Q) (n : ℕ) : ℝ :=
  if n.Prime ∧ n % Q = a.val then 1 else 0

private def residuePrimeLogBand (Y Q : ℕ) (a : Fin Q) : ℝ :=
  weightedBand (residuePrimeLogTerm Q a) Y

private def residuePrimeHarmonicBand (Y Q : ℕ) (a : Fin Q) : ℝ :=
  weightedBand (residuePrimeHarmonicTerm Q a) Y

private theorem residueLambda_partial_limit {Q : ℕ} (hQ : 0 < Q) (a : Fin Q)
    (ha : Nat.Coprime a.val Q) :
    Tendsto (fun n : ℕ => apPartialSum (residueLambdaTerm Q a) n / (n : ℝ))
      atTop (𝓝 (1 / (Q.totient : ℝ))) := by
  have h := Erdos970.WeakPNT_AP (q := Q) (a := a.val) (by omega) ha a.isLt
  simpa [apPartialSum, residueLambdaTerm, Erdos970.cumsum] using h

private theorem log_dyadic_ratio_tendsto :
    Tendsto (fun Y : ℕ => Real.log (Y : ℝ) /
      Real.log ((2 * Y : ℕ) : ℝ)) atTop (𝓝 1) := by
  have hlogY : Tendsto (fun Y : ℕ => Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2Y : Tendsto (fun Y : ℕ => Real.log ((2 * Y : ℕ) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono (f := fun Y : ℕ => Real.log (Y : ℝ))
      (g := fun Y => Real.log ((2 * Y : ℕ) : ℝ)) (by
        intro Y
        by_cases hY : Y = 0
        · simp [hY]
        · apply Real.log_le_log
          · exact_mod_cast Nat.pos_of_ne_zero hY
          · exact_mod_cast (by omega : Y ≤ 2 * Y)) hlogY
  have hinv : Tendsto (fun Y : ℕ => (Real.log ((2 * Y : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlog2Y
  have hconstLog : Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
    tendsto_const_nhds
  have hterm : Tendsto (fun Y : ℕ => Real.log 2 *
      (Real.log ((2 * Y : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hconstLog.mul hinv
  have heq : (fun Y : ℕ => Real.log (Y : ℝ) /
      Real.log ((2 * Y : ℕ) : ℝ)) =ᶠ[atTop]
      (fun Y => 1 - Real.log 2 * (Real.log ((2 * Y : ℕ) : ℝ))⁻¹) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with Y hY
    have hYposNat : 0 < Y := by omega
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hYposNat
    have h2Ypos : ((2 * Y : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show (2 * Y : ℕ) = 2 * Y by rfl, Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num) hYpos.ne']
    field_simp [h2Ypos]
    <;> ring
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using (hone.sub hterm).congr' heq.symm

private def nonprimeLambdaSum (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 0 N).filter (fun n => ¬ n.Prime),
    ArithmeticFunction.vonMangoldt n

private theorem nonprimeLambdaSum_eq_psi_sub_theta (N : ℕ) :
    nonprimeLambdaSum N =
      Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) := by
  have htheta : Chebyshev.theta (N : ℝ) =
      ∑ n ∈ (Finset.Icc 0 N).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.theta_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    apply Finset.sum_congr rfl
    intro p hp
    exact (ArithmeticFunction.vonMangoldt_apply_prime
      ((Finset.mem_filter.mp hp).2)).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 0 N) Nat.Prime (fun n => ArithmeticFunction.vonMangoldt n)
  unfold nonprimeLambdaSum
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, htheta]
  linarith [hsplit]

private def residueNonprimeLambdaBand (Y Q : ℕ) (a : Fin Q) : ℝ :=
  ∑ n ∈ (Finset.Ico Y (2 * Y)).filter (fun n => ¬ n.Prime),
    if n % Q = a.val then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0

private theorem residueLambdaBand_eq_primeLog_add_error (Y Q : ℕ) (a : Fin Q) :
    weightedBand (residueLambdaTerm Q a) Y =
      residuePrimeLogBand Y Q a + residueNonprimeLambdaBand Y Q a := by
  let S := Finset.Ico Y (2 * Y)
  have hsplit := Finset.sum_filter_add_sum_filter_not S Nat.Prime
    (fun n => residueLambdaTerm Q a n / (n : ℝ))
  have hprime :
      (∑ n ∈ S.filter Nat.Prime, residueLambdaTerm Q a n / (n : ℝ)) =
        residuePrimeLogBand Y Q a := by
    unfold residuePrimeLogBand weightedBand residueLambdaTerm residuePrimeLogTerm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> by_cases hr : n % Q = a.val <;>
      simp [hp, hr, ArithmeticFunction.vonMangoldt_apply_prime]
  unfold weightedBand residueLambdaTerm residueNonprimeLambdaBand
  dsimp only [S] at hsplit hprime
  simp only [residueLambdaTerm] at hsplit hprime
  rw [← hsplit, hprime]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hr : n % Q = a.val <;> simp [hr]

private theorem residueNonprimeLambdaBand_nonneg (Y Q : ℕ) (a : Fin Q) :
    0 ≤ residueNonprimeLambdaBand Y Q a := by
  unfold residueNonprimeLambdaBand
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  · simp

private theorem residueNonprimeLambdaBand_le (Q : ℕ) (a : Fin Q)
    {Y : ℕ} (hY : 2 ≤ Y) :
    residueNonprimeLambdaBand Y Q a ≤
      (1 / (Y : ℝ)) *
        (Chebyshev.psi ((2 * Y - 1 : ℕ) : ℝ) -
          Chebyshev.theta ((2 * Y - 1 : ℕ) : ℝ)) := by
  let S := Finset.Ico Y (2 * Y)
  let T := Finset.Icc 0 (2 * Y - 1)
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hsub : S.filter (fun n => ¬ n.Prime) ⊆
      T.filter (fun n => ¬ n.Prime) := by
    intro n hn
    have hnS := Finset.mem_filter.mp hn
    have hnI := Finset.mem_Ico.mp hnS.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hnS.2⟩
    omega
  have hmassSub :
      (∑ n ∈ S.filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n) ≤ nonprimeLambdaSum (2 * Y - 1) := by
    calc
      _ ≤ ∑ n ∈ T.filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (by intro n hn _; exact ArithmeticFunction.vonMangoldt_nonneg)
      _ = nonprimeLambdaSum (2 * Y - 1) := by rfl
  calc
    residueNonprimeLambdaBand Y Q a ≤
        ∑ n ∈ S.filter (fun n => ¬ n.Prime),
          (1 / (Y : ℝ)) * ArithmeticFunction.vonMangoldt n := by
      unfold residueNonprimeLambdaBand S
      apply Finset.sum_le_sum
      intro n hn
      have hnS := Finset.mem_filter.mp hn
      have hnI := Finset.mem_Ico.mp hnS.1
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hYle : (Y : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnI.1
      have hrecip : (1 / (n : ℝ)) ≤ 1 / (Y : ℝ) :=
        (div_le_div_iff₀ hnpos hYpos).2 (by norm_num; linarith)
      by_cases hr : n % Q = a.val
      · have hLambda := ArithmeticFunction.vonMangoldt_nonneg (n := n)
        calc
          (if n % Q = a.val then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) =
              ArithmeticFunction.vonMangoldt n / (n : ℝ) := by simp [hr]
          _ = ArithmeticFunction.vonMangoldt n * (1 / (n : ℝ)) := by ring
          _ ≤ ArithmeticFunction.vonMangoldt n * (1 / (Y : ℝ)) :=
            mul_le_mul_of_nonneg_left hrecip hLambda
          _ = (1 / (Y : ℝ)) * ArithmeticFunction.vonMangoldt n := by ring
      · simp [hr]
        exact mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg
    _ = (1 / (Y : ℝ)) *
        (∑ n ∈ S.filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (Y : ℝ)) * nonprimeLambdaSum (2 * Y - 1) :=
      mul_le_mul_of_nonneg_left hmassSub (by positivity)
    _ = _ := by rw [nonprimeLambdaSum_eq_psi_sub_theta]

private theorem sqrt_dyadic_div_tendsto :
    Tendsto (fun Y : ℕ => Real.sqrt (2 * (Y : ℝ)) / (Y : ℝ)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun Y : ℕ => Real.sqrt (Y : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun Y : ℕ => (Real.sqrt (Y : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hupper : Tendsto (fun Y : ℕ => 2 / Real.sqrt (Y : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (Filter.Tendsto.const_mul 2 hinv)
  apply squeeze_zero
    (f := fun Y : ℕ => Real.sqrt (2 * (Y : ℝ)) / (Y : ℝ))
    (g := fun Y : ℕ => 2 / Real.sqrt (Y : ℝ))
    (fun Y => div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
    (fun Y => ?_) hupper
  by_cases hY : Y = 0
  · simp [hY]
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hY)
  have hsqrtPos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYpos
  have hsqrtUpper : Real.sqrt (2 * (Y : ℝ)) ≤ 2 * Real.sqrt (Y : ℝ) := by
    calc
      Real.sqrt (2 * (Y : ℝ)) ≤ Real.sqrt (4 * (Y : ℝ)) :=
        Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * Real.sqrt (Y : ℝ) := by
        rw [Real.sqrt_mul (by norm_num) (Y : ℝ)]
        norm_num
  have hcross : Real.sqrt (2 * (Y : ℝ)) * Real.sqrt (Y : ℝ) ≤
      2 * (Y : ℝ) := by
    calc
      _ ≤ 2 * Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrtUpper (Real.sqrt_nonneg _)
      _ = 2 * (Y : ℝ) := by
        calc
          _ = 2 * (Real.sqrt (Y : ℝ)) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hYpos.le]
  apply (div_le_div_iff₀ hYpos hsqrtPos).2
  exact hcross

private theorem residueNonprimeLambdaBand_div_tendsto (Q : ℕ) (a : Fin Q) :
    Tendsto (fun Y : ℕ => residueNonprimeLambdaBand Y Q a / reciprocalBand Y)
      atTop (𝓝 0) := by
  obtain ⟨Cψ, hCψ⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hupperLimit : Tendsto (fun Y : ℕ =>
      2 * |Cψ| * (Real.sqrt (2 * (Y : ℝ)) / (Y : ℝ))) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (Filter.Tendsto.const_mul (2 * |Cψ|) sqrt_dyadic_div_tendsto)
  have hnonneg : ∀ Y : ℕ, 0 ≤
      residueNonprimeLambdaBand Y Q a / reciprocalBand Y := by
    intro Y
    by_cases hY : 2 ≤ Y
    · exact div_nonneg (residueNonprimeLambdaBand_nonneg Y Q a)
        (le_of_lt (lt_of_lt_of_le (by norm_num) (reciprocalBand_lower hY)))
    · interval_cases Y
      · simp [residueNonprimeLambdaBand, reciprocalBand]
      · have hK : 0 < reciprocalBand 1 := by simp [reciprocalBand]
        exact div_nonneg (residueNonprimeLambdaBand_nonneg 1 Q a) hK.le
  have hupper : ∀ᶠ Y : ℕ in atTop,
      residueNonprimeLambdaBand Y Q a / reciprocalBand Y ≤
        2 * |Cψ| * (Real.sqrt (2 * (Y : ℝ)) / (Y : ℝ)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with Y hY
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
    have hK : 1 / 2 ≤ reciprocalBand Y := reciprocalBand_lower hY
    have hKpos : 0 < reciprocalBand Y := lt_of_lt_of_le (by norm_num) hK
    let x : ℝ := ((2 * Y - 1 : ℕ) : ℝ)
    have hx : 0 ≤ x := by positivity
    have hxle : x ≤ 2 * (Y : ℝ) := by
      dsimp [x]
      exact_mod_cast (by omega : 2 * Y - 1 ≤ 2 * Y)
    have hglobal : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
      exact sub_nonneg.mpr (Chebyshev.theta_le_psi x)
    have hglobal' : Chebyshev.psi x - Chebyshev.theta x ≤
        |Cψ| * Real.sqrt x := by
      calc
        _ ≤ Cψ * Real.sqrt x := hCψ x
        _ ≤ |Cψ| * Real.sqrt x :=
          mul_le_mul_of_nonneg_right (le_abs_self Cψ) (Real.sqrt_nonneg _)
    have hsqrtUpper : Real.sqrt x ≤ Real.sqrt (2 * (Y : ℝ)) := Real.sqrt_le_sqrt hxle
    have herror : 0 ≤ residueNonprimeLambdaBand Y Q a ∧
        residueNonprimeLambdaBand Y Q a ≤
          (|Cψ| * Real.sqrt (2 * (Y : ℝ))) / (Y : ℝ) := by
      constructor
      · exact residueNonprimeLambdaBand_nonneg Y Q a
      · calc
          residueNonprimeLambdaBand Y Q a ≤
              (1 / (Y : ℝ)) * (Chebyshev.psi x - Chebyshev.theta x) := by
                simpa [x] using residueNonprimeLambdaBand_le Q a hY
          _ ≤ (1 / (Y : ℝ)) * (|Cψ| * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hglobal' (by positivity)
          _ ≤ (1 / (Y : ℝ)) * (|Cψ| * Real.sqrt (2 * (Y : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsqrtUpper (abs_nonneg Cψ)) (by positivity)
          _ = _ := by ring
    apply (div_le_iff₀ hKpos).2
    have hmul := mul_le_mul_of_nonneg_left hK (by positivity :
      0 ≤ 2 * (|Cψ| * Real.sqrt (2 * (Y : ℝ)) / (Y : ℝ)))
    have hprod : residueNonprimeLambdaBand Y Q a ≤
        (2 * (|Cψ| * Real.sqrt (2 * (Y : ℝ)) / (Y : ℝ))) *
          reciprocalBand Y := by
      calc
        _ ≤ (|Cψ| * Real.sqrt (2 * (Y : ℝ))) / (Y : ℝ) := herror.2
        _ ≤ _ := by nlinarith [hmul]
    simpa [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using hprod
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun Y : ℕ => residueNonprimeLambdaBand Y Q a / reciprocalBand Y)
    (g := fun _ : ℕ => (0 : ℝ))
    (h := fun Y : ℕ => 2 * |Cψ| *
      (Real.sqrt (2 * (Y : ℝ)) / (Y : ℝ)))
    tendsto_const_nhds hupperLimit (Filter.Eventually.of_forall hnonneg) hupper

private theorem residuePrimeLogBand_div_tendsto {Q : ℕ} (hQ : 0 < Q)
    (a : Fin Q) (ha : Nat.Coprime a.val Q) :
    Tendsto (fun Y : ℕ => residuePrimeLogBand Y Q a / reciprocalBand Y)
      atTop (𝓝 (1 / (Q.totient : ℝ))) := by
  have hPart : Tendsto (fun n : ℕ =>
      apPartialSum (residueLambdaTerm Q a) n / (n : ℝ)) atTop
      (𝓝 (1 / (Q.totient : ℝ))) :=
    residueLambda_partial_limit (Q := Q) hQ a ha
  have hLambdaBand : Tendsto
      (fun Y : ℕ => weightedBand (residueLambdaTerm Q a) Y / reciprocalBand Y)
      atTop (𝓝 (1 / (Q.totient : ℝ))) :=
    reciprocal_weighted_band_tendsto (residueLambdaTerm Q a)
      (1 / (Q.totient : ℝ)) hPart
  have herr := residueNonprimeLambdaBand_div_tendsto Q a
  have heq : (fun Y : ℕ =>
      weightedBand (residueLambdaTerm Q a) Y / reciprocalBand Y -
        residueNonprimeLambdaBand Y Q a / reciprocalBand Y) =ᶠ[atTop]
      (fun Y => residuePrimeLogBand Y Q a / reciprocalBand Y) := by
    filter_upwards with Y
    rw [residueLambdaBand_eq_primeLog_add_error]
    ring
  simpa using (hLambdaBand.sub herr).congr' heq

private theorem residuePrimeHarmonicBand_scaled_tendsto {Q : ℕ} (hQ : 0 < Q)
    (a : Fin Q) (ha : Nat.Coprime a.val Q) :
    Tendsto (fun Y : ℕ => residuePrimeHarmonicBand Y Q a *
      Real.log (Y : ℝ) / reciprocalBand Y) atTop
      (𝓝 (1 / (Q.totient : ℝ))) := by
  let H : ℕ → ℝ := fun Y => residuePrimeHarmonicBand Y Q a
  let T : ℕ → ℝ := fun Y => residuePrimeLogBand Y Q a
  have hT := residuePrimeLogBand_div_tendsto hQ a ha
  have hratio := log_dyadic_ratio_tendsto
  have hlower (Y : ℕ) (hY : 2 ≤ Y) :
      Real.log (Y : ℝ) * H Y ≤ T Y := by
    unfold H T residuePrimeHarmonicBand residuePrimeLogBand weightedBand
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnI := Finset.mem_Ico.mp hn
    by_cases hp : n.Prime
    · by_cases hr : n % Q = a.val
      · have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast hp.pos
        have hlog : Real.log (Y : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log hYpos (by exact_mod_cast hnI.1)
        simp [residuePrimeHarmonicTerm, residuePrimeLogTerm, hp, hr]
        simpa only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hlog (by positivity)
      · simp [residuePrimeHarmonicTerm, residuePrimeLogTerm, hp, hr]
    · simp [residuePrimeHarmonicTerm, residuePrimeLogTerm, hp]
  have hupper (Y : ℕ) (hY : 2 ≤ Y) :
      T Y ≤ Real.log ((2 * Y : ℕ) : ℝ) * H Y := by
    unfold H T residuePrimeHarmonicBand residuePrimeLogBand weightedBand
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnI := Finset.mem_Ico.mp hn
    by_cases hp : n.Prime
    · by_cases hr : n % Q = a.val
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hp.pos
        have htop : (n : ℝ) ≤ ((2 * Y : ℕ) : ℝ) := by exact_mod_cast hnI.2.le
        have hlog : Real.log (n : ℝ) ≤ Real.log ((2 * Y : ℕ) : ℝ) :=
          Real.log_le_log hnpos htop
        simp [residuePrimeHarmonicTerm, residuePrimeLogTerm, hp, hr]
        simpa only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hlog (by positivity)
      · simp [residuePrimeHarmonicTerm, residuePrimeLogTerm, hp, hr]
    · simp [residuePrimeHarmonicTerm, residuePrimeLogTerm, hp]
  have hleftLimit : Tendsto (fun Y : ℕ =>
      (T Y / reciprocalBand Y) *
        (Real.log (Y : ℝ) / Real.log ((2 * Y : ℕ) : ℝ))) atTop
      (𝓝 (1 / (Q.totient : ℝ))) := by
    simpa using hT.mul hratio
  have hrightLimit : Tendsto (fun Y : ℕ => T Y / reciprocalBand Y) atTop
      (𝓝 (1 / (Q.totient : ℝ))) := hT
  have hevent : ∀ᶠ Y : ℕ in atTop,
      (T Y / reciprocalBand Y) *
          (Real.log (Y : ℝ) / Real.log ((2 * Y : ℕ) : ℝ)) ≤
        H Y * Real.log (Y : ℝ) / reciprocalBand Y ∧
      H Y * Real.log (Y : ℝ) / reciprocalBand Y ≤ T Y / reciprocalBand Y := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with Y hY
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
    have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
    have hlog2Y : 0 < Real.log ((2 * Y : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * Y))
    have hKpos : 0 < reciprocalBand Y :=
      lt_of_lt_of_le (by norm_num) (reciprocalBand_lower hY)
    constructor
    · have hm := mul_le_mul_of_nonneg_right (hupper Y hY) hlogY.le
      have hd := div_le_div_of_nonneg_right hm (le_of_lt (mul_pos hKpos hlog2Y))
      calc
        _ = (T Y * Real.log (Y : ℝ)) /
            (reciprocalBand Y * Real.log ((2 * Y : ℕ) : ℝ)) := by ring
        _ ≤ _ := hd
        _ = _ := by field_simp [hKpos.ne', hlog2Y.ne']
    · have hl : H Y * Real.log (Y : ℝ) ≤ T Y := by
        simpa [mul_comm] using hlower Y hY
      have hd := div_le_div_of_nonneg_right hl hKpos.le
      calc
        _ = (H Y * Real.log (Y : ℝ)) / reciprocalBand Y := by ring
        _ ≤ _ := hd
  have hleft : ∀ᶠ Y : ℕ in atTop,
      (T Y / reciprocalBand Y) *
          (Real.log (Y : ℝ) / Real.log ((2 * Y : ℕ) : ℝ)) ≤
        H Y * Real.log (Y : ℝ) / reciprocalBand Y :=
    hevent.mono (fun Y h => h.1)
  have hright : ∀ᶠ Y : ℕ in atTop,
      H Y * Real.log (Y : ℝ) / reciprocalBand Y ≤ T Y / reciprocalBand Y :=
    hevent.mono (fun Y h => h.2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun Y : ℕ => H Y * Real.log (Y : ℝ) / reciprocalBand Y)
    (g := fun Y : ℕ =>
      (T Y / reciprocalBand Y) *
        (Real.log (Y : ℝ) / Real.log ((2 * Y : ℕ) : ℝ)))
    (h := fun Y : ℕ => T Y / reciprocalBand Y)
    hleftLimit hrightLimit hleft hright

private theorem residuePrimeHarmonicBand_eventually_zero (Q : ℕ) (a : Fin Q)
    (ha : ¬ Nat.Coprime a.val Q) :
    ∀ᶠ Y : ℕ in atTop, residuePrimeHarmonicBand Y Q a = 0 := by
  filter_upwards [eventually_ge_atTop (Q + 1)] with Y hY
  have hYQ : Q < Y := by omega
  unfold residuePrimeHarmonicBand weightedBand
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hp : n.Prime
  · by_cases hr : n % Q = a.val
    · have hnQ : Q < n := lt_of_lt_of_le hYQ (Finset.mem_Ico.mp hn).1
      have hcop : Nat.Coprime n Q := by
        by_contra hnot
        obtain ⟨r, hrp, hrn, hrQ⟩ :=
          (Nat.Prime.not_coprime_iff_dvd).mp hnot
        have hrEq : r = n := by
          rcases (Nat.dvd_prime hp).mp hrn with hr1 | hrn'
          · have hrgt1 := hrp.two_le
            omega
          · exact hrn'
        subst r
        have hnleQ : n ≤ Q := Nat.le_of_dvd (by omega) hrQ
        omega
      have ha' : Nat.Coprime a.val Q := by
        simpa [hr] using (ZMod.coprime_mod_iff_coprime n Q).2 hcop
      exact (ha ha').elim
    · simp [residuePrimeHarmonicTerm, hp, hr]
  · simp [residuePrimeHarmonicTerm, hp]

private theorem residuePrimeHarmonicBand_scaled_tendsto_all (Q : ℕ) (hQ : 0 < Q)
    (a : Fin Q) :
    Tendsto (fun Y : ℕ => residuePrimeHarmonicBand Y Q a *
      Real.log (Y : ℝ) / reciprocalBand Y) atTop
      (𝓝 (uniformUnitResidueLaw Q a)) := by
  by_cases ha : Nat.Coprime a.val Q
  · rw [uniformUnitResidueLaw, if_pos ha]
    exact residuePrimeHarmonicBand_scaled_tendsto hQ a ha
  · have hzero := residuePrimeHarmonicBand_eventually_zero Q a ha
    have heq : (fun Y : ℕ => residuePrimeHarmonicBand Y Q a *
        Real.log (Y : ℝ) / reciprocalBand Y) =ᶠ[atTop]
        (fun _ : ℕ => (0 : ℝ)) := by
      filter_upwards [hzero] with Y hY
      simp [hY]
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (uniformUnitResidueLaw Q a)) := by
      rw [uniformUnitResidueLaw, if_neg ha]
      exact tendsto_const_nhds
    exact hconst.congr' heq.symm

private theorem residuePrimeHarmonicBand_eq_numerator (Y Q : ℕ) (a : Fin Q) :
    residuePrimeHarmonicBand Y Q a =
      (∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
        if p % Q = a.val then 1 / (p : ℝ) else 0) := by
  unfold residuePrimeHarmonicBand weightedBand residuePrimeHarmonicTerm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> by_cases hres : p % Q = a.val <;>
    simp [hprime, hres]

private theorem residuePrimeHarmonicBand_sum_eq (Y Q : ℕ) (hQ : 0 < Q) :
    (∑ a : Fin Q, residuePrimeHarmonicBand Y Q a) = primePoolMass Y (2 * Y) := by
  classical
  rw [Finset.sum_congr rfl (fun a _ => residuePrimeHarmonicBand_eq_numerator Y Q a)]
  unfold primePoolMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2
  let a₀ : Fin Q := ⟨p % Q, Nat.mod_lt _ hQ⟩
  have hclass : ∑ a : Fin Q,
      (if p % Q = a.val then 1 / (p : ℝ) else 0) = 1 / (p : ℝ) := by
    rw [Finset.sum_eq_single a₀]
    · simp [a₀]
    · intro a ha hne
      by_cases hr : p % Q = a.val
      · exact False.elim (hne (Fin.ext hr.symm))
      · simp [hr]
    · simp
  exact hclass

private theorem uniformUnitResidueLaw_sum (Q : ℕ) (hQ : 0 < Q) :
    (∑ a : Fin Q, uniformUnitResidueLaw Q a) = 1 := by
  classical
  let U := Finset.univ.filter (fun a : Fin Q => Nat.Coprime a.val Q)
  have hcard : U.card = Q.totient := by
    have hcard' : U.card = ((Finset.range Q).filter
        (fun n => Nat.Coprime Q n)).card := by
      apply Finset.card_bij (fun (a : Fin Q) _ => a.val)
      · intro a ha
        have ha' := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt, ha'.symm⟩
      · intro a ha b hb hab
        exact Fin.ext hab
      · intro n hn
        have hn' := Finset.mem_filter.mp hn
        refine ⟨⟨n, Finset.mem_range.mp hn'.1⟩, ?_, rfl⟩
        simpa [U] using hn'.2.symm
    calc
      U.card = ((Finset.range Q).filter (fun n => Nat.Coprime Q n)).card := hcard'
      _ = Q.totient := (Nat.totient_eq_card_coprime Q).symm
  have hphi : 0 < (Q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hQ
  unfold uniformUnitResidueLaw
  calc
    _ = (U.card : ℝ) * (1 / (Q.totient : ℝ)) := by
      rw [← Finset.sum_filter]
      simp [U, Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by rw [hcard]; field_simp [hphi.ne']

private theorem primePoolMass_scaled_tendsto (Q : ℕ) (hQ : 0 < Q) :
    Tendsto (fun Y : ℕ => primePoolMass Y (2 * Y) *
      Real.log (Y : ℝ) / reciprocalBand Y) atTop (𝓝 1) := by
  have hsum : Tendsto (fun Y : ℕ =>
      ∑ a : Fin Q, residuePrimeHarmonicBand Y Q a *
        Real.log (Y : ℝ) / reciprocalBand Y) atTop
      (𝓝 (∑ a : Fin Q, uniformUnitResidueLaw Q a)) := by
    apply tendsto_finsetSum Finset.univ
    intro a ha
    exact residuePrimeHarmonicBand_scaled_tendsto_all Q hQ a
  have hEq : (fun Y : ℕ => primePoolMass Y (2 * Y) *
      Real.log (Y : ℝ) / reciprocalBand Y) =
      (fun Y => ∑ a : Fin Q, residuePrimeHarmonicBand Y Q a *
        Real.log (Y : ℝ) / reciprocalBand Y) := by
    funext Y
    rw [← residuePrimeHarmonicBand_sum_eq Y Q hQ]
    conv_rhs => rw [← Finset.sum_div]
    conv_rhs => rw [← Finset.sum_mul]
  have hEqEvent : (fun Y : ℕ => primePoolMass Y (2 * Y) *
      Real.log (Y : ℝ) / reciprocalBand Y) =ᶠ[atTop]
      (fun Y => ∑ a : Fin Q, residuePrimeHarmonicBand Y Q a *
        Real.log (Y : ℝ) / reciprocalBand Y) :=
    Filter.Eventually.of_forall (fun Y => congrFun hEq Y)
  have hmass := hsum.congr' hEqEvent.symm
  rw [uniformUnitResidueLaw_sum Q hQ] at hmass
  exact hmass

private theorem primePoolResidueLaw_eq_scaled_ratio (Y Q : ℕ) (a : Fin Q) :
    primePoolResidueLaw Y (2 * Y) Q a =
      residuePrimeHarmonicBand Y Q a / primePoolMass Y (2 * Y) := by
  unfold primePoolResidueLaw
  rw [← residuePrimeHarmonicBand_eq_numerator Y Q a]

theorem primePoolResidueLaw_tendsto (Q : ℕ) (hQ : 0 < Q) (a : Fin Q) :
    Tendsto (fun Y : ℕ => primePoolResidueLaw Y (2 * Y) Q a) atTop
      (𝓝 (uniformUnitResidueLaw Q a)) := by
  have hNum := residuePrimeHarmonicBand_scaled_tendsto_all Q hQ a
  have hDen := primePoolMass_scaled_tendsto Q hQ
  let f : ℕ → ℝ := fun Y =>
    residuePrimeHarmonicBand Y Q a * Real.log (Y : ℝ) / reciprocalBand Y
  let g : ℕ → ℝ := fun Y =>
    primePoolMass Y (2 * Y) * Real.log (Y : ℝ) / reciprocalBand Y
  have hNum' : Tendsto f atTop (𝓝 (uniformUnitResidueLaw Q a)) := by
    simpa [f] using hNum
  have hDen' : Tendsto g atTop (𝓝 1) := by simpa [g] using hDen
  have hratio : Tendsto (f / g) atTop
      (𝓝 (uniformUnitResidueLaw Q a)) := by
    simpa only [div_one] using hNum'.div hDen' one_ne_zero
  have hDenPos : ∀ᶠ Y : ℕ in atTop,
      0 < primePoolMass Y (2 * Y) * Real.log (Y : ℝ) / reciprocalBand Y :=
    hDen.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq : (fun Y : ℕ => primePoolResidueLaw Y (2 * Y) Q a) =ᶠ[atTop]
      (f / g) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hDenPos] with Y hY hMscaled
    change primePoolResidueLaw Y (2 * Y) Q a = f Y / g Y
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
    have hKpos : 0 < reciprocalBand Y :=
      lt_of_lt_of_le (by norm_num) (reciprocalBand_lower hY)
    have hlogpos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
    have hscale : 0 < Real.log (Y : ℝ) / reciprocalBand Y := div_pos hlogpos hKpos
    have hMpos : 0 < primePoolMass Y (2 * Y) := by
      have hprod : 0 < primePoolMass Y (2 * Y) *
          (Real.log (Y : ℝ) / reciprocalBand Y) := by
        simpa [div_eq_mul_inv, mul_assoc] using hMscaled
      by_contra hM
      have hMle : primePoolMass Y (2 * Y) ≤ 0 := le_of_not_gt hM
      have hle := mul_nonpos_of_nonpos_of_nonneg hMle hscale.le
      linarith
    rw [primePoolResidueLaw_eq_scaled_ratio]
    dsimp [f, g]
    field_simp [hMpos.ne', hKpos.ne', hlogpos.ne']
    <;> ring
  simpa [f, g, Pi.div_apply] using hratio.congr' heq.symm

end
end HindmanSumsProducts.Arithmetic.Outside
