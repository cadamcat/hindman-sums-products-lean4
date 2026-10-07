import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for §4 (part Prime). -/

namespace HindmanSumsProducts

open scoped BigOperators Topology
open Filter
open FromArithmetic

private def harmonicSupport (X : ℕ) : Finset ℤ :=
  (Finset.Ico X (X ^ 2) : Finset ℕ).image (fun n : ℕ => (n : ℤ))

private theorem harmonicLaw_eq_zero_of_not_mem (X W : ℕ) (z : ℤ)
    (hz : z ∉ harmonicSupport X) : harmonicLaw X W z = 0 := by
  by_cases hc : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W
  · have hzmem : z ∈ harmonicSupport X := by
      refine Finset.mem_image.mpr ⟨z.toNat, ?_, Int.toNat_of_nonneg hc.1⟩
      exact Finset.mem_Ico.mpr ⟨hc.2.1, hc.2.2.1⟩
    exact (hz hzmem).elim
  · simp [harmonicLaw, hc]

private theorem harmonicLaw_mul_summable (X W : ℕ) (F : ℤ → ℝ) :
    Summable (fun z => harmonicLaw X W z * F z) := by
  apply summable_of_ne_finset_zero (s := harmonicSupport X)
  intro z hz
  simp [harmonicLaw_eq_zero_of_not_mem X W z hz]

private theorem harmonicNormalizer_pos (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log (X : ℝ) > (W : ℝ) / X) : 0 < harmonicNormalizer X W := by
  have hphi : 0 < (Nat.totient W : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hW)
  have hWreal : 0 < (W : ℝ) := by exact_mod_cast hW
  have hXreal : 0 < (X : ℝ) := by positivity
  have hcoeff : 0 < (Nat.totient W : ℝ) / W := div_pos hphi hWreal
  have hdiff : 0 < Real.log (X : ℝ) - (W : ℝ) / X := sub_pos.mpr hlog
  have hmain : 0 < (Nat.totient W : ℝ) / W * Real.log X -
      (Nat.totient W : ℝ) / X := by
    have heq : (Nat.totient W : ℝ) / W * Real.log X -
        (Nat.totient W : ℝ) / X =
        ((Nat.totient W : ℝ) / W) * (Real.log X - (W : ℝ) / X) := by
      field_simp [ne_of_gt hWreal, ne_of_gt hXreal]
    rw [heq]
    exact mul_pos hcoeff hdiff
  have hnorm := (FromArithmetic.sampling_pointwise_claim X W hW hX hlog).normalizer hX hlog
  have hlower : (Nat.totient W : ℝ) / W * Real.log X -
      (Nat.totient W : ℝ) / X ≤ harmonicNormalizer X W := by
    have h := (abs_le.mp hnorm).1
    linarith
  exact lt_of_lt_of_le hmain hlower

private theorem harmonicLaw_tsum_eq_one (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log (X : ℝ) > (W : ℝ) / X) :
    ∑' z : ℤ, harmonicLaw X W z = 1 := by
  classical
  have hZ : 0 < harmonicNormalizer X W := harmonicNormalizer_pos X W hW hX hlog
  have hzero (z : ℤ) (hz : z ∉ harmonicSupport X) : harmonicLaw X W z = 0 :=
    harmonicLaw_eq_zero_of_not_mem X W z hz
  rw [tsum_eq_sum (s := harmonicSupport X) hzero]
  unfold harmonicSupport
  rw [Finset.sum_image (s := Finset.Ico X (X ^ 2))
    (f := fun z : ℤ => harmonicLaw X W z)
    (g := fun n : ℕ => (n : ℤ)) Nat.cast_injective.injOn]
  have hterm (n : ℕ) (hn : n ∈ Finset.Ico X (X ^ 2)) :
      harmonicLaw X W (n : ℤ) =
        if Nat.Coprime n W then
          1 / ((n : ℝ) * harmonicNormalizer X W) else 0 := by
    have hn' := Finset.mem_Ico.mp hn
    simp [harmonicLaw, hn', Int.toNat_natCast]
  calc
    (∑ n ∈ Finset.Ico X (X ^ 2), harmonicLaw X W (n : ℤ)) =
        ∑ n ∈ Finset.Ico X (X ^ 2),
          if Nat.Coprime n W then 1 / ((n : ℝ) * harmonicNormalizer X W) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm n hn
    _ = ∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W),
          1 / ((n : ℝ) * harmonicNormalizer X W) := by
      rw [← Finset.sum_filter]
    _ = (∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W),
          1 / (n : ℝ)) / harmonicNormalizer X W := by
      calc
        _ = ∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W),
              (1 / (n : ℝ)) / harmonicNormalizer X W := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnI : n ∈ Finset.Ico X (X ^ 2) := (Finset.mem_filter.mp hn).1
          have hnX : 0 < n := lt_of_lt_of_le (by omega) (Finset.mem_Ico.mp hnI).1
          have hnXreal : 0 < (n : ℝ) := by exact_mod_cast hnX
          field_simp [ne_of_gt hnXreal, ne_of_gt hZ]
        _ = (∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W),
              1 / (n : ℝ)) / harmonicNormalizer X W := by rw [Finset.sum_div]
    _ = 1 := by
      change harmonicNormalizer X W / harmonicNormalizer X W = 1
      exact div_self (ne_of_gt hZ)

private theorem harmonicDivisibility_eq_residue (X W k : ℕ) (hk : 0 < k) :
    (∑' z : ℤ, harmonicLaw X W z * (if (k : ℤ) ∣ z then 1 else 0)) =
      harmonicResidueLaw (harmonicLaw X W) k ⟨0, hk⟩ := by
  apply tsum_congr
  intro z
  by_cases hz : 0 ≤ z
  · have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
    have hdiv' : (k : ℤ) ∣ z ↔ k ∣ z.toNat := by
      calc
        (k : ℤ) ∣ z ↔ (k : ℤ) ∣ (z.toNat : ℤ) := by rw [hcast]
        _ ↔ k ∣ z.toNat := Int.natCast_dvd_natCast
    have hdiv : (k : ℤ) ∣ z ↔ z.toNat % k = 0 := by
      rw [hdiv', Nat.dvd_iff_mod_eq_zero]
    simp [harmonicResidueLaw, hz, hdiv]
  · simp [harmonicResidueLaw, hz, harmonicLaw, hz]

private def primeSupport (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ico lo hi).filter Nat.Prime

private noncomputable def primeDivisibilityWeight (P : Finset ℕ) (S : ℝ) (y : ℤ) : ℝ :=
  S⁻¹ * ∑ p ∈ P, (if (p : ℤ) ∣ y then 1 else 0)

private theorem primePoolLaw_zero_of_not_mem (lo hi p : ℕ)
    (hp : p ∉ primeSupport lo hi) : primePoolLaw lo hi p = 0 := by
  have hcond : ¬ (lo ≤ p ∧ p < hi ∧ p.Prime) := by
    simpa [primeSupport, Finset.mem_filter, Finset.mem_Ico] using hp
  simp [primePoolLaw, hcond]

private theorem primePoolLaw_eq_reciprocal_div_mass (lo hi p : ℕ)
    (hp : p ∈ primeSupport lo hi) :
    primePoolLaw lo hi p = (1 / (p : ℝ)) / primePoolMass lo hi := by
  have hcond : lo ≤ p ∧ p < hi ∧ p.Prime := by
    simpa [primeSupport, Finset.mem_filter, Finset.mem_Ico, and_assoc] using hp
  simp [primePoolLaw, hcond]

private theorem primePoolLaw_tsum_eq_one (lo hi : ℕ)
    (hS : 0 < primePoolMass lo hi) :
    ∑' p : ℕ, primePoolLaw lo hi p = 1 := by
  classical
  rw [tsum_eq_sum (s := primeSupport lo hi)
    (fun p hp => primePoolLaw_zero_of_not_mem lo hi p hp)]
  calc
    (∑ p ∈ primeSupport lo hi, primePoolLaw lo hi p) =
        (∑ p ∈ primeSupport lo hi, 1 / (p : ℝ)) / primePoolMass lo hi := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      exact primePoolLaw_eq_reciprocal_div_mass lo hi p hp
    _ = 1 := by
      have heq : (∑ p ∈ primeSupport lo hi, 1 / (p : ℝ)) = primePoolMass lo hi := by
        rfl
      rw [heq]
      exact div_self (ne_of_gt hS)

private theorem primePoolLaw_divisibility_weight (lo hi p : ℕ) (y : ℤ)
    (hp : p ∈ primeSupport lo hi) (hS : 0 < primePoolMass lo hi) :
    primePoolLaw lo hi p * (if (p : ℤ) ∣ y then (p : ℝ) else 0) =
      (primePoolMass lo hi)⁻¹ * (if (p : ℤ) ∣ y then 1 else 0) := by
  by_cases hdiv : (p : ℤ) ∣ y
  · have hp' : p ∈ (Finset.Ico lo hi).filter Nat.Prime := by simpa [primeSupport] using hp
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp').2
    have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    rw [if_pos hdiv, if_pos hdiv, primePoolLaw_eq_reciprocal_div_mass lo hi p hp]
    field_simp [ne_of_gt hpRpos, ne_of_gt hS]
  · simp [hdiv]

private theorem primePoolAverage_reference_eq_weighted (X W lo hi : ℕ)
    (F : ℤ → ℝ) (hS : 0 < primePoolMass lo hi) :
    (∑' p : ℕ, primePoolLaw lo hi p *
      (∑' y : ℤ, harmonicLaw X W y *
        ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y))) =
      ∑' y : ℤ, harmonicLaw X W y *
        (primeDivisibilityWeight (primeSupport lo hi) (primePoolMass lo hi) y * F y) := by
  classical
  let P : Finset ℕ := primeSupport lo hi
  let μ : ℤ → ℝ := harmonicLaw X W
  let f : ℕ → ℝ := fun p => primePoolLaw lo hi p *
    (∑' y : ℤ, μ y * ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y))
  let g : ℤ → ℝ := fun y => μ y *
    (primeDivisibilityWeight P (primePoolMass lo hi) y * F y)
  have hfzero (p : ℕ) (hp : p ∉ P) : f p = 0 := by
    simp [f, P, primePoolLaw_zero_of_not_mem lo hi p hp]
  have hinner (p : ℕ) :
      (∑' y : ℤ, μ y * ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y)) =
        ∑ y ∈ harmonicSupport X,
          μ y * ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y) := by
    apply tsum_eq_sum (s := harmonicSupport X)
    intro y hy
    simp [μ, harmonicLaw_eq_zero_of_not_mem X W y hy]
  have hgzero (y : ℤ) (hy : y ∉ harmonicSupport X) : g y = 0 := by
    simp [g, μ, harmonicLaw_eq_zero_of_not_mem X W y hy]
  change (∑' p : ℕ, f p) = ∑' y : ℤ, g y
  rw [tsum_eq_sum (s := P) hfzero]
  have hL :
      (∑ p ∈ P, f p) =
        ∑ p ∈ P, primePoolLaw lo hi p *
          (∑ y ∈ harmonicSupport X,
            μ y * ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y)) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [f]
    rw [hinner p]
  rw [hL, tsum_eq_sum (s := harmonicSupport X) hgzero]
  calc
    (∑ p ∈ P, primePoolLaw lo hi p *
      (∑ y ∈ harmonicSupport X,
        μ y * ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y))) =
      ∑ p ∈ P, ∑ y ∈ harmonicSupport X,
        primePoolLaw lo hi p * (μ y *
          ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = ∑ y ∈ harmonicSupport X, ∑ p ∈ P,
        primePoolLaw lo hi p * (μ y *
          ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y)) := by
      rw [Finset.sum_comm]
    _ = ∑ y ∈ harmonicSupport X, μ y *
        (primeDivisibilityWeight P (primePoolMass lo hi) y * F y) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [primeDivisibilityWeight]
      calc
        (∑ p ∈ P, primePoolLaw lo hi p *
          (μ y * ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y))) =
            ∑ p ∈ P, μ y *
              (((primePoolMass lo hi)⁻¹ * (if (p : ℤ) ∣ y then 1 else 0)) * F y) := by
          apply Finset.sum_congr rfl
          intro p hp
          calc
            primePoolLaw lo hi p *
                (μ y * ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y)) =
              μ y *
                ((primePoolLaw lo hi p * (if (p : ℤ) ∣ y then (p : ℝ) else 0)) * F y) := by ring
            _ = μ y *
                (((primePoolMass lo hi)⁻¹ * (if (p : ℤ) ∣ y then 1 else 0)) * F y) := by
              rw [primePoolLaw_divisibility_weight lo hi p y hp hS]
        _ = μ y *
            ((primePoolMass lo hi)⁻¹ *
              (∑ p ∈ P, if (p : ℤ) ∣ y then 1 else 0) * F y) := by
          rw [← Finset.mul_sum]
          congr 1
          calc
            (∑ p ∈ P,
              ((primePoolMass lo hi)⁻¹ * (if (p : ℤ) ∣ y then 1 else 0)) * F y) =
                (∑ p ∈ P,
                  (primePoolMass lo hi)⁻¹ * (if (p : ℤ) ∣ y then 1 else 0)) * F y := by
              rw [Finset.sum_mul]
            _ = ((primePoolMass lo hi)⁻¹ *
                ∑ p ∈ P, if (p : ℤ) ∣ y then 1 else 0) * F y := by
              rw [← Finset.mul_sum]

private theorem prime_pool_eventual_data {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) :
    ∀ᶠ N in atTop,
      1 ≤ primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper ∧
      ∀ p ∈ primeSupport (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper,
        Nat.Coprime p (primorial (N + 1)) := by
  let A := S.core.parameters
  have hVgeW : ∀ N, primorial (N + 1) ≤ FromArithmetic.masterScaleV A N l := by
    intro N
    have hWM := A.Wle N
    unfold FromArithmetic.masterScaleV
    omega
  have hVpos : ∀ N, 0 < (FromArithmetic.masterScaleV A N l : ℝ) := by
    intro N
    have hV : 2 ≤ FromArithmetic.masterScaleV A N l := by unfold FromArithmetic.masterScaleV; omega
    exact_mod_cast lt_of_lt_of_le (by norm_num) hV
  have hmassDom := S.primeStage.pool_harmonic_mass_dominates l
  have hlowerDom := S.primeStage.pool_lower_dominates l
  have hmassLarge : ∀ᶠ N in atTop,
      1 ≤ primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper := by
    have h := (hmassDom 1 (by norm_num)).eventually_ge_atTop 1
    filter_upwards [h] with N hN
    have hVposN := hVpos N
    have hratio : 1 ≤ primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper / (FromArithmetic.masterScaleV A N l : ℝ) := by
      simpa [Real.rpow_one] using hN
    have hVleS : (FromArithmetic.masterScaleV A N l : ℝ) ≤
        primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper :=
      (one_le_div hVposN).mp hratio
    have hVone : 1 ≤ (FromArithmetic.masterScaleV A N l : ℝ) := by
      have hV : 2 ≤ FromArithmetic.masterScaleV A N l := by unfold FromArithmetic.masterScaleV; omega
      exact_mod_cast (Nat.le_trans (by norm_num) hV)
    exact le_trans hVone hVleS
  have hlowerLarge : ∀ᶠ N in atTop,
      2 * (FromArithmetic.masterScaleV A N l : ℝ) ≤ (S.primeStage.pool N l).lower := by
    have h := (hlowerDom 1 (by norm_num)).eventually_ge_atTop 2
    filter_upwards [h] with N hN
    have hVposN := hVpos N
    have hratio : 2 ≤ (S.primeStage.pool N l).lower /
        (FromArithmetic.masterScaleV A N l : ℝ) := by simpa [Real.rpow_one] using hN
    exact (le_div_iff₀ hVposN).mp hratio
  filter_upwards [hmassLarge, hlowerLarge] with N hmass hlower
  constructor
  · exact hmass
  · intro p hp
    have hmem : (S.primeStage.pool N l).lower ≤ p ∧ p <
        (S.primeStage.pool N l).upper ∧ Nat.Prime p := by
      simpa [primeSupport, Finset.mem_filter, Finset.mem_Ico, and_assoc] using hp
    have hWpos : 0 < primorial (N + 1) := primorial_pos _
    have hWpV : primorial (N + 1) ≤ FromArithmetic.masterScaleV A N l := hVgeW N
    have hlt : primorial (N + 1) < p := by
      have hlowN : 2 * FromArithmetic.masterScaleV A N l ≤ (S.primeStage.pool N l).lower := by
        exact_mod_cast hlower
      omega
    exact hmem.2.2.coprime_iff_not_dvd.mpr (by
      intro hd
      have hpLe : p ≤ primorial (N + 1) := Nat.le_of_dvd hWpos hd
      omega)

private theorem tsum_mul_sub_bound_of_support {α : Type*} [DecidableEq α]
    (μ ν F : α → ℝ) (s : Finset α) (M : ℝ)
    (hμ : ∀ x, x ∉ s → μ x = 0) (hν : ∀ x, x ∉ s → ν x = 0)
    (hF : ∀ x, |F x| ≤ M) :
    |∑' x, (μ x - ν x) * F x| ≤ M * arithmeticL1 μ ν := by
  have hterm (x : α) (hx : x ∉ s) : (μ x - ν x) * F x = 0 := by
    simp [hμ x hx, hν x hx]
  have hnorm (x : α) (hx : x ∉ s) : |μ x - ν x| = 0 := by
    simp [hμ x hx, hν x hx]
  rw [tsum_eq_sum (s := s) hterm, arithmeticL1, tsum_eq_sum (s := s) hnorm]
  calc
    |∑ x ∈ s, (μ x - ν x) * F x| ≤ ∑ x ∈ s, |(μ x - ν x) * F x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ s, (M * |μ x - ν x|) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      calc
        |μ x - ν x| * |F x| ≤ |μ x - ν x| * M :=
          mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
        _ = M * |μ x - ν x| := mul_comm _ _
    _ = M * ∑ x ∈ s, |μ x - ν x| := by rw [← Finset.mul_sum]

private theorem harmonicLaw_zero_of_not_mem (X W : ℕ) (z : ℤ)
    (hz : z ∉ harmonicSupport X) : harmonicLaw X W z = 0 :=
  harmonicLaw_eq_zero_of_not_mem X W z hz

private theorem tendsto_atTop_of_eventually_le {f g : ℕ → ℝ}
    (hfg : ∀ᶠ n in atTop, f n ≤ g n)
    (hf : Tendsto f atTop atTop) : Tendsto g atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [hf.eventually_ge_atTop b, hfg] with n hfb hfg
  exact le_trans hfb hfg

private theorem dominates_of_eventually_below_scale {A S T : ℕ → ℝ}
    (hA : ∀ᶠ n in atTop, 0 ≤ A n)
    (hT : ∀ᶠ n in atTop, 0 < T n)
    (hTS : ∀ᶠ n in atTop, T n ≤ S n)
    (hdom : OAI.MicrocellScale.Dominates A S) :
    OAI.MicrocellScale.Dominates A T := by
  intro C hC
  have hpow : ∀ᶠ n in atTop, T n ^ C ≤ S n ^ C := by
    filter_upwards [hT, hTS] with n hn hns
    exact Real.rpow_le_rpow hn.le hns hC.le
  have hratio : ∀ᶠ n in atTop, A n / S n ^ C ≤ A n / T n ^ C := by
    filter_upwards [hA, hT, hTS, hpow] with n hA hn hns hp
    exact div_le_div_of_nonneg_left hA (Real.rpow_pos_of_pos hn C) hp
  exact tendsto_atTop_of_eventually_le hratio (hdom C hC)

private theorem prime_sampling_scale_dominance {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K) (hli : l < i) (B : ℕ) :
    OAI.MicrocellScale.Dominates
      (fun N => (S.core.parameters.X N i : ℝ))
      (fun N => (2 + primorial (N + 1) +
        ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B + 1 +
        (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) ∧
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (S.core.parameters.X N i : ℝ))
      (fun N => (2 + primorial (N + 1) +
        ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B +
        (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) := by
  let A := S.core.parameters
  let size : ℕ → ℕ := fun N => (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV A N l
  let commonX : ℕ → ℕ := fun N => 2 + primorial (N + 1) + size N ^ B + 1 + size N
  let commonLog : ℕ → ℕ := fun N => 2 + primorial (N + 1) + size N ^ B + size N
  have hsize2 : ∀ N, 2 ≤ size N := by
    intro N
    dsimp [size]
    unfold FromArithmetic.masterScaleV
    omega
  have hWsize : ∀ N, primorial (N + 1) ≤ size N := by
    intro N
    have hWM : primorial (N + 1) ≤ A.M N := A.Wle N
    dsimp [size]
    unfold FromArithmetic.masterScaleV
    omega
  have hHle : ∀ N, A.H N l ≤ A.H N i := by
    intro N
    exact Nat.le_of_dvd (A.Hpos N i) (S.gapStage.earlier_gaps_divide N l i hli)
  have hGap := S.gapStage.gap_dominates_pool_and_bound l
  have hGapLarge : ∀ᶠ N in atTop,
      6 ≤ (A.H N l : ℝ) / (size N : ℝ) ^ ((B : ℝ) + 2) := by
    have h := hGap ((B : ℝ) + 2) (by positivity)
    filter_upwards [h.eventually_ge_atTop 6] with N hN
    simpa [size] using hN
  have hpowBounds : ∀ N,
      (3 + 2 * (size N : ℝ) + (size N : ℝ) ^ B) ≤
        6 * (size N : ℝ) ^ (B + 2) := by
    intro N
    have hs : 2 ≤ (size N : ℝ) := by exact_mod_cast hsize2 N
    have hs1 : 1 ≤ (size N : ℝ) := by linarith
    have hs2 : (size N : ℝ) ≤ (size N : ℝ) ^ 2 := by nlinarith
    have hpowB : (size N : ℝ) ^ B ≤ (size N : ℝ) ^ (B + 2) := by
      rw [pow_add]
      have hn : 0 ≤ (size N : ℝ) ^ B := pow_nonneg (by positivity) B
      have hsq : 1 ≤ (size N : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hsq)]
    have hpowSize : (size N : ℝ) ≤ (size N : ℝ) ^ (B + 2) := by
      rw [pow_add]
      have hpowB1 : 1 ≤ (size N : ℝ) ^ B := one_le_pow₀ hs1
      have hmul := mul_le_mul hpowB1 hs2 (by positivity) (by positivity)
      simpa using hmul
    have hpowOne : 1 ≤ (size N : ℝ) ^ (B + 2) := by
      have hbase : 1 ≤ (size N : ℝ) := hs1
      exact one_le_pow₀ hbase
    nlinarith
  have hcommonX_le : ∀ᶠ N in atTop, (commonX N : ℝ) ≤ (A.H N l : ℝ) := by
    filter_upwards [hGapLarge] with N hN
    have hspos : 0 < (size N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (hsize2 N))
    have hpowpos : 0 < (size N : ℝ) ^ (B + 2) := by positivity
    have hN' : 6 ≤ (A.H N l : ℝ) / (size N : ℝ) ^ (B + 2) := by
      have hexp : (B : ℝ) + 2 = ((B + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_natCast] at hN
      exact hN
    have hHbound : 6 * (size N : ℝ) ^ (B + 2) ≤ (A.H N l : ℝ) :=
      (le_div_iff₀ hpowpos).mp hN'
    have hW : (primorial (N + 1) : ℝ) ≤ (size N : ℝ) := by exact_mod_cast hWsize N
    have hsum : (commonX N : ℝ) ≤ 3 + 2 * (size N : ℝ) + (size N : ℝ) ^ B := by
      dsimp [commonX, commonLog]
      push_cast
      nlinarith
    exact le_trans (le_trans hsum (hpowBounds N)) hHbound
  have hcommonX_le_i : ∀ᶠ N in atTop, (commonX N : ℝ) ≤ (A.H N i : ℝ) := by
    filter_upwards [hcommonX_le] with N hN
    have hle : (A.H N l : ℝ) ≤ (A.H N i : ℝ) := by exact_mod_cast hHle N
    exact le_trans hN hle
  have hcommonLog_le : ∀ᶠ N in atTop, (commonLog N : ℝ) ≤ (A.H N i : ℝ) := by
    filter_upwards [hcommonX_le_i] with N hN
    have hnat : commonLog N ≤ commonX N := by
      dsimp [commonLog, commonX]
      omega
    exact le_trans (by exact_mod_cast hnat) hN
  have hraw := S.gapStage.raw_cutoff_log_dominates_gap i
  have hlogpos : ∀ᶠ N in atTop, 0 ≤ Real.log (A.X N i : ℝ) := by
    have hlarge := (hraw 1 (by norm_num)).eventually_ge_atTop 1
    filter_upwards [hlarge] with N hN
    have hHpos : 0 < (A.H N i : ℝ) := by exact_mod_cast A.Hpos N i
    have hratio : 1 ≤ Real.log (A.X N i : ℝ) / (A.H N i : ℝ) := by
      simpa [Real.rpow_one] using hN
    have hHlog : (A.H N i : ℝ) ≤ Real.log (A.X N i : ℝ) :=
      (one_le_div hHpos).mp hratio
    exact le_trans (by positivity) hHlog
  have hcommonXpos : ∀ N, 0 < (commonX N : ℝ) := by
    intro N
    dsimp [commonX]
    positivity
  have hcommonLogpos : ∀ N, 0 < (commonLog N : ℝ) := by
    intro N
    dsimp [commonLog]
    positivity
  have hlogCommonX := dominates_of_eventually_below_scale hlogpos
    (Filter.Eventually.of_forall hcommonXpos) hcommonX_le_i hraw
  have hlogCommon := dominates_of_eventually_below_scale hlogpos
    (Filter.Eventually.of_forall hcommonLogpos) hcommonLog_le hraw
  have hlogleX : ∀ᶠ N in atTop, Real.log (A.X N i : ℝ) ≤ (A.X N i : ℝ) := by
    filter_upwards [] with N
    exact Real.log_le_self (by positivity)
  have hXCommon : OAI.MicrocellScale.Dominates
      (fun N => (A.X N i : ℝ)) (fun N => (commonX N : ℝ)) := by
    intro C hC
    have hratio : ∀ᶠ N in atTop,
        Real.log (A.X N i : ℝ) / (commonX N : ℝ) ^ C ≤
          (A.X N i : ℝ) / (commonX N : ℝ) ^ C := by
      filter_upwards [hlogleX] with N hN
      exact div_le_div_of_nonneg_right hN (Real.rpow_nonneg (le_of_lt (hcommonXpos N)) C)
    exact tendsto_atTop_of_eventually_le hratio (hlogCommonX C hC)
  have hlogScale : ∀ᶠ N in atTop,
      (2 + primorial (N + 1) + size N ^ B + size N : ℝ) ≤ (commonLog N : ℝ) := by
    filter_upwards [] with N
    have heq : (2 + primorial (N + 1) + size N ^ B + size N : ℝ) =
        (commonLog N : ℝ) := by simp [commonLog]
    exact heq.le
  have hscaleX : ∀ᶠ N in atTop,
      (2 + primorial (N + 1) + size N ^ B + 1 + size N : ℝ) ≤ (commonX N : ℝ) := by
    filter_upwards [] with N
    have heq : (2 + primorial (N + 1) + size N ^ B + 1 + size N : ℝ) =
        (commonX N : ℝ) := by simp [commonX]
    exact heq.le
  have hscaleXpos : ∀ N,
      0 < (2 + primorial (N + 1) + size N ^ B + 1 + size N : ℝ) := by
    intro N
    positivity
  have hDomX := dominates_of_eventually_below_scale
    (Filter.Eventually.of_forall (fun N => by positivity))
    (Filter.Eventually.of_forall hscaleXpos) hscaleX hXCommon
  have hDomLog := dominates_of_eventually_below_scale hlogpos
    (Filter.Eventually.of_forall (fun N => by positivity)) hlogScale hlogCommon
  have hfinalX :
      (fun N => (2 + primorial (N + 1) +
        ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B + 1 +
        (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) =
        (fun N => (commonX N : ℝ)) := by
    funext N
    dsimp [commonX, size, A]
    push_cast
    ring
  have hfinalLog :
      (fun N => (2 + primorial (N + 1) +
        ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B +
        (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) =
        (fun N => (commonLog N : ℝ)) := by
    funext N
    dsimp [commonLog, size, A]
    push_cast
    ring
  rw [hfinalX, hfinalLog]
  exact ⟨by simpa [A, commonX, Nat.cast_add, Nat.cast_pow] using hDomX,
    by simpa [A, commonLog, Nat.cast_add, Nat.cast_pow] using hDomLog⟩

private theorem prime_residue_error_superpolynomial {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K) (hli : l < i) :
    SuperPolynomialSmall
      (fun N => FromArithmetic.harmonicResidueUniformError (S.core.parameters.X N i) (primorial (N + 1))
        (((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ 2))
      (fun N => (((S.primeStage.pool N l).upper +
        FromArithmetic.masterScaleV S.core.parameters N l : ℕ) : ℝ)) := by
  let size : ℕ → ℕ := fun N =>
    (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l
  let Kseq : ℕ → ℕ := fun N => size N ^ 2
  let Vseq : ℕ → ℕ := size
  let Hseq : ℕ → ℕ := fun _ => 1
  let Wseq : ℕ → ℕ := fun N => primorial (N + 1)
  let Xseq : ℕ → ℕ := fun N => S.core.parameters.X N i
  have hdom := prime_sampling_scale_dominance S l i hli 2
  have hDomX : OAI.MicrocellScale.Dominates
      (fun N => (Xseq N : ℝ))
      (fun N => (2 + Wseq N + Kseq N + Hseq N + Vseq N : ℝ)) := by
    have heq :
        (fun N => (2 + Wseq N + Kseq N + Hseq N + Vseq N : ℝ)) =
        (fun N => (2 + primorial (N + 1) +
          ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ 2 + 1 +
          (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) := by
      funext N
      dsimp [Wseq, Kseq, Hseq, Vseq, size]
      push_cast
      ring
    rw [heq]
    exact hdom.1
  have hDomLog : OAI.MicrocellScale.Dominates
      (fun N => Real.log (Xseq N : ℝ))
      (fun N => (2 + Wseq N + Kseq N + Vseq N : ℝ)) := by
    have heq :
        (fun N => (2 + Wseq N + Kseq N + Vseq N : ℝ)) =
        (fun N => (2 + primorial (N + 1) +
          ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ 2 +
          (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) := by
      funext N
      dsimp [Wseq, Kseq, Vseq, size]
      push_cast
      ring
    rw [heq]
    exact hdom.2
  have hXevent : ∀ᶠ N in atTop, 2 ≤ Xseq N := by
    apply Filter.Eventually.of_forall
    intro N
    dsimp [Xseq]
    have hcut := S.gapStage.valid_raw_cutoffs N i
    have hWpos : 1 ≤ primorial (N + 1) := by
      have hp : 0 < primorial (N + 1) := primorial_pos _
      omega
    omega
  have hloglarge : ∀ᶠ N in atTop, 1 ≤ Real.log (Xseq N : ℝ) := by
    have h := (hDomLog 1 (by norm_num)).eventually_ge_atTop 1
    filter_upwards [h] with N hN
    have hscale : 1 ≤ (2 + Wseq N + Kseq N + Vseq N : ℝ) := by
      have hWnonneg : 0 ≤ (Wseq N : ℝ) := by positivity
      have hKnonneg : 0 ≤ (Kseq N : ℝ) := by positivity
      have hVnonneg : 0 ≤ (Vseq N : ℝ) := by positivity
      linarith
    have hratio : 1 ≤ Real.log (Xseq N : ℝ) /
        (2 + Wseq N + Kseq N + Vseq N : ℝ) := by
      simpa [Real.rpow_one] using hN
    have hscaleLog : (2 + Wseq N + Kseq N + Vseq N : ℝ) ≤
        Real.log (Xseq N : ℝ) := (one_le_div (by positivity)).mp hratio
    exact le_trans hscale hscaleLog
  have hden : ∀ᶠ N in atTop,
      Real.log (Xseq N : ℝ) > (Wseq N : ℝ) / Xseq N := by
    filter_upwards [hloglarge] with N hlog
    have hcut : 4 * (Wseq N : ℝ) ≤ (Xseq N : ℝ) := by
      exact_mod_cast S.gapStage.valid_raw_cutoffs N i
    have hXpos : 0 < (Xseq N : ℝ) := by
      have hWpos : 0 < (Wseq N : ℝ) := by exact_mod_cast primorial_pos (N + 1)
      nlinarith
    have hfrac : (Wseq N : ℝ) / Xseq N ≤ 1 / 4 := by
      apply (div_le_iff₀ hXpos).2
      nlinarith
    linarith
  have hsam := FromArithmetic.sampling_asymptotics Wseq Kseq Hseq Vseq Xseq
    (by intro N; dsimp [Kseq]; exact one_le_pow₀ (by dsimp [size]; unfold FromArithmetic.masterScaleV; omega))
    (by intro N; rfl)
    (by
      intro N
      dsimp [Vseq, size]
      have hv : 2 ≤ FromArithmetic.masterScaleV S.core.parameters N l := by unfold FromArithmetic.masterScaleV; omega
      omega)
    (by intro N; rfl)
    hXevent hden hDomX hDomLog
  have hsmall := hsam.1
  simpa [FromArithmetic.harmonicResidueUniformError, Wseq, Kseq, Xseq, Vseq, size] using hsmall

private noncomputable def harmonicDivProbability (X W k : ℕ) : ℝ :=
  ∑ y ∈ harmonicSupport X,
    harmonicLaw X W y * (if (k : ℤ) ∣ y then 1 else 0)

private noncomputable def harmonicDivPairProbability (X W p q : ℕ) : ℝ :=
  ∑ y ∈ harmonicSupport X,
    harmonicLaw X W y * (if (p : ℤ) ∣ y then 1 else 0) *
      (if (q : ℤ) ∣ y then 1 else 0)

private theorem natPrimePair_dvd_iff (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) (y : ℤ) :
    ((p : ℤ) ∣ y ∧ (q : ℤ) ∣ y) ↔ ((p * q : ℕ) : ℤ) ∣ y := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  constructor
  · rintro ⟨hpD, hqD⟩
    exact Int.natCast_dvd.mpr
      (hcop.mul_dvd_of_dvd_of_dvd (Int.natCast_dvd.mp hpD) (Int.natCast_dvd.mp hqD))
  · intro hpqD
    have hnat : p * q ∣ y.natAbs := Int.natCast_dvd.mp hpqD
    constructor
    · exact Int.natCast_dvd.mpr (dvd_trans (dvd_mul_right p q) hnat)
    · have hqmul : q ∣ p * q := by
        simpa [Nat.mul_comm] using (dvd_mul_right q p)
      exact Int.natCast_dvd.mpr (dvd_trans hqmul hnat)

private theorem harmonicDivPair_eq_product_probability (X W p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    harmonicDivPairProbability X W p q = harmonicDivProbability X W (p * q) := by
  classical
  unfold harmonicDivPairProbability harmonicDivProbability
  apply Finset.sum_congr rfl
  intro y hy
  have hpair := natPrimePair_dvd_iff p q hp hq hne y
  by_cases hprod : ((p * q : ℕ) : ℤ) ∣ y
  · have hdivs := hpair.2 hprod
    have hprodInt : (p : ℤ) * (q : ℤ) ∣ y := by simpa using hprod
    simp [hprodInt, hdivs.1, hdivs.2]
  · have hnotPair : ¬ ((p : ℤ) ∣ y ∧ (q : ℤ) ∣ y) := by
      intro h
      exact hprod (hpair.1 h)
    have hprodInt : ¬ (p : ℤ) * (q : ℤ) ∣ y := by
      intro h
      exact hprod (by simpa using h)
    by_cases hpdiv : (p : ℤ) ∣ y
    · have hqnot : ¬ (q : ℤ) ∣ y := by
        intro hqdiv
        exact hnotPair ⟨hpdiv, hqdiv⟩
      simp [hprodInt, hpdiv, hqnot]
    · simp [hprodInt, hpdiv]

private theorem harmonicDivPair_diagonal (X W p : ℕ) :
    harmonicDivPairProbability X W p p = harmonicDivProbability X W p := by
  classical
  unfold harmonicDivPairProbability harmonicDivProbability
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : (p : ℤ) ∣ y <;> simp [h]

private theorem harmonicDivProbability_eq_residue (X W k : ℕ) (hk : 0 < k) :
    harmonicDivProbability X W k =
      harmonicResidueLaw (harmonicLaw X W) k ⟨0, hk⟩ := by
  classical
  unfold harmonicDivProbability
  have hzero (y : ℤ) (hy : y ∉ harmonicSupport X) :
      harmonicLaw X W y * (if (k : ℤ) ∣ y then 1 else 0) = 0 := by
    simp [harmonicLaw_eq_zero_of_not_mem X W y hy]
  have hsum :
      (∑' y : ℤ, harmonicLaw X W y * (if (k : ℤ) ∣ y then 1 else 0)) =
        ∑ y ∈ harmonicSupport X, harmonicLaw X W y * (if (k : ℤ) ∣ y then 1 else 0) :=
    tsum_eq_sum (s := harmonicSupport X) hzero
  calc
    _ = ∑' y : ℤ, harmonicLaw X W y * (if (k : ℤ) ∣ y then 1 else 0) := hsum.symm
    _ = harmonicResidueLaw (harmonicLaw X W) k ⟨0, hk⟩ :=
      harmonicDivisibility_eq_residue X W k hk

private theorem harmonicDivProbability_residue_error (X W k : ℕ)
    (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log (X : ℝ) > (W : ℝ) / X)
    (hk : 0 < k) (hcop : Nat.Coprime k W) :
    |(k : ℝ) * harmonicDivProbability X W k - 1| ≤ FromArithmetic.harmonicResidueError X W k := by
  rw [harmonicDivProbability_eq_residue X W k hk]
  exact (FromArithmetic.sampling_pointwise_claim X W hW hX hlog).residue_pointwise
    hX hlog k 0 hcop hk hk

private theorem harmonicResidueError_mono {X W k K : ℕ}
    (hkK : k ≤ K) (hX : 2 ≤ X)
    (hlog : Real.log (X : ℝ) > (W : ℝ) / X) :
    FromArithmetic.harmonicResidueError X W k ≤ FromArithmetic.harmonicResidueError X W K := by
  have hden : 0 < (X : ℝ) * (Real.log (X : ℝ) - (W : ℝ) / X) := by
    apply mul_pos
    · exact_mod_cast (by omega : 0 < X)
    · exact sub_pos.mpr hlog
  have hnum : (W : ℝ) * (k + 1 : ℕ) ≤ (W : ℝ) * (K + 1 : ℕ) := by
    have hcast : (k + 1 : ℕ) ≤ (K + 1 : ℕ) := Nat.add_le_add_right hkK 1
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcast) (by positivity)
  unfold FromArithmetic.harmonicResidueError
  exact div_le_div_of_nonneg_right hnum hden.le

private theorem harmonicDivProbability_bounds (X W k : ℕ) (E : ℝ)
    (hk : 0 < k)
    (herr : |(k : ℝ) * harmonicDivProbability X W k - 1| ≤ E) :
    (1 - E) / (k : ℝ) ≤ harmonicDivProbability X W k ∧
      harmonicDivProbability X W k ≤ (1 + E) / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbounds := abs_le.mp herr
  constructor
  · apply (div_le_iff₀ hkR).2
    nlinarith [hbounds.1]
  · apply (le_div_iff₀ hkR).2
    nlinarith [hbounds.2]

private theorem abs_le_delta_add_square (x δ : ℝ) (hδ : 0 < δ) :
    |x| ≤ δ + x ^ 2 / δ := by
  have heq : δ + x ^ 2 / δ = (δ ^ 2 + x ^ 2) / δ := by
    field_simp [ne_of_gt hδ]
  rw [heq]
  apply (le_div_iff₀ hδ).2
  have hsquare := sq_nonneg (|x| - δ)
  nlinarith [sq_abs x, hsquare]

private theorem finite_deviation_l1_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (μ f : α → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hμ : ∀ x ∈ s, 0 ≤ μ x) (hMass : ∑ x ∈ s, μ x = 1) :
    (∑ x ∈ s, μ x * |f x - 1|) ≤
      δ + (∑ x ∈ s, μ x * (f x - 1) ^ 2) / δ := by
  have hterm (x : α) (hx : x ∈ s) :
      μ x * |f x - 1| ≤ μ x * (δ + (f x - 1) ^ 2 / δ) :=
    mul_le_mul_of_nonneg_left (abs_le_delta_add_square (f x - 1) δ hδ) (hμ x hx)
  calc
    (∑ x ∈ s, μ x * |f x - 1|) ≤
        ∑ x ∈ s, μ x * (δ + (f x - 1) ^ 2 / δ) :=
      Finset.sum_le_sum fun x hx => hterm x hx
    _ = δ + (∑ x ∈ s, μ x * (f x - 1) ^ 2) / δ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hleft : (∑ x ∈ s, μ x * δ) = δ := by
        calc
          (∑ x ∈ s, μ x * δ) = (∑ x ∈ s, μ x) * δ := by rw [Finset.sum_mul]
          _ = δ := by rw [hMass]; ring
      have hright :
          (∑ x ∈ s, μ x * ((f x - 1) ^ 2 / δ)) =
            (∑ x ∈ s, μ x * (f x - 1) ^ 2) / δ := by
        calc
          (∑ x ∈ s, μ x * ((f x - 1) ^ 2 / δ)) =
              ∑ x ∈ s, (μ x * (f x - 1) ^ 2) / δ := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = (∑ x ∈ s, μ x * (f x - 1) ^ 2) / δ := by rw [Finset.sum_div]
      rw [hleft, hright]

private theorem harmonic_primeWeight_mean_formula (X W : ℕ) (P : Finset ℕ)
    (S : ℝ) :
    (∑ y ∈ harmonicSupport X,
      harmonicLaw X W y * primeDivisibilityWeight P S y) =
      ∑ p ∈ P, S⁻¹ * harmonicDivProbability X W p := by
  classical
  calc
    (∑ y ∈ harmonicSupport X,
      harmonicLaw X W y * primeDivisibilityWeight P S y) =
        ∑ y ∈ harmonicSupport X, ∑ p ∈ P,
          S⁻¹ * (harmonicLaw X W y * (if (p : ℤ) ∣ y then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [primeDivisibilityWeight]
      calc
        harmonicLaw X W y * (S⁻¹ * ∑ p ∈ P, (if (p : ℤ) ∣ y then 1 else 0)) =
            (harmonicLaw X W y * S⁻¹) *
              ∑ p ∈ P, (if (p : ℤ) ∣ y then 1 else 0) := by ring
        _ = ∑ p ∈ P,
              (harmonicLaw X W y * S⁻¹) * (if (p : ℤ) ∣ y then 1 else 0) := by
              rw [Finset.mul_sum]
        _ = ∑ p ∈ P,
              S⁻¹ * (harmonicLaw X W y * (if (p : ℤ) ∣ y then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro p hp
              ring
    _ = ∑ p ∈ P, ∑ y ∈ harmonicSupport X,
          S⁻¹ * (harmonicLaw X W y * (if (p : ℤ) ∣ y then 1 else 0)) := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P, S⁻¹ * harmonicDivProbability X W p := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [harmonicDivProbability]
      rw [← Finset.mul_sum]

private theorem harmonic_primeWeight_second_formula (X W : ℕ) (P : Finset ℕ)
    (S : ℝ) :
    (∑ y ∈ harmonicSupport X,
      harmonicLaw X W y * (primeDivisibilityWeight P S y) ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P,
        (S⁻¹ * S⁻¹) * harmonicDivPairProbability X W p q := by
  classical
  have hsumSq (y : ℤ) :
      (∑ p ∈ P, if (p : ℤ) ∣ y then (1 : ℝ) else 0) ^ 2 =
        ∑ p ∈ P, ∑ q ∈ P,
          (if (p : ℤ) ∣ y then (1 : ℝ) else 0) *
            (if (q : ℤ) ∣ y then (1 : ℝ) else 0) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
  calc
    (∑ y ∈ harmonicSupport X,
      harmonicLaw X W y * (primeDivisibilityWeight P S y) ^ 2) =
        ∑ y ∈ harmonicSupport X, ∑ p ∈ P, ∑ q ∈ P,
          (S⁻¹ * S⁻¹) * (harmonicLaw X W y *
            ((if (p : ℤ) ∣ y then 1 else 0) * (if (q : ℤ) ∣ y then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [primeDivisibilityWeight]
      calc
        harmonicLaw X W y * (S⁻¹ * ∑ p ∈ P, (if (p : ℤ) ∣ y then 1 else 0)) ^ 2 =
            ((S⁻¹ * S⁻¹) * harmonicLaw X W y) *
              ((∑ p ∈ P, (if (p : ℤ) ∣ y then 1 else 0)) ^ 2) := by ring
        _ = ((S⁻¹ * S⁻¹) * harmonicLaw X W y) *
              (∑ p ∈ P, ∑ q ∈ P,
                (if (p : ℤ) ∣ y then 1 else 0) * (if (q : ℤ) ∣ y then 1 else 0)) := by
              exact congrArg (fun t : ℝ => ((S⁻¹ * S⁻¹) * harmonicLaw X W y) * t)
                (hsumSq y)
        _ = ∑ p ∈ P, ∑ q ∈ P,
              (S⁻¹ * S⁻¹) * (harmonicLaw X W y *
                ((if (p : ℤ) ∣ y then 1 else 0) * (if (q : ℤ) ∣ y then 1 else 0))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p hp
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro q hq
              ring
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ y ∈ harmonicSupport X,
          (S⁻¹ * S⁻¹) * (harmonicLaw X W y *
            ((if (p : ℤ) ∣ y then 1 else 0) * (if (q : ℤ) ∣ y then 1 else 0))) := by
      rw [Finset.sum_comm (s := harmonicSupport X) (t := P)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm (s := harmonicSupport X) (t := P)]
    _ = ∑ p ∈ P, ∑ q ∈ P,
          (S⁻¹ * S⁻¹) * harmonicDivPairProbability X W p q := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simp only [harmonicDivPairProbability]
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      ring

private theorem primeDivWeight_variance_bound (X W : ℕ) (P : Finset ℕ)
    (S E Kbound : ℝ)
    (hSpos : 0 < S) (hSone : 1 ≤ S)
    (hSsum : S = ∑ p ∈ P, 1 / (p : ℝ))
    (hMass : ∑ y ∈ harmonicSupport X, harmonicLaw X W y = 1)
    (hPrime : ∀ p ∈ P, Nat.Prime p)
    (hCoprime : ∀ p ∈ P, Nat.Coprime p W)
    (hKprod : ∀ p ∈ P, ∀ q ∈ P, (p * q : ℕ) ≤ Kbound)
    (hE : 0 ≤ E)
    (hResidue : ∀ k : ℕ, 0 < k → Nat.Coprime k W →
      (k : ℝ) ≤ Kbound →
      |(k : ℝ) * harmonicDivProbability X W k - 1| ≤ E) :
    (∑ y ∈ harmonicSupport X,
      harmonicLaw X W y * (primeDivisibilityWeight P S y - 1) ^ 2) ≤ 1 / S + 4 * E := by
  classical
  let mean : ℝ := ∑ y ∈ harmonicSupport X,
    harmonicLaw X W y * primeDivisibilityWeight P S y
  let second : ℝ := ∑ y ∈ harmonicSupport X,
    harmonicLaw X W y * (primeDivisibilityWeight P S y) ^ 2
  have hInvS : 0 ≤ S⁻¹ := by positivity
  have hMeanFormula := harmonic_primeWeight_mean_formula X W P S
  have hSecondFormula := harmonic_primeWeight_second_formula X W P S
  have hqBounds (k : ℕ) (hk : 0 < k) (hcop : Nat.Coprime k W)
      (hkK : (k : ℝ) ≤ Kbound) :
      (1 - E) / (k : ℝ) ≤ harmonicDivProbability X W k ∧
        harmonicDivProbability X W k ≤ (1 + E) / (k : ℝ) := by
    exact harmonicDivProbability_bounds X W k E hk (hResidue k hk hcop hkK)
  have hqLower (p : ℕ) (hp : p ∈ P) :
      (1 - E) / (p : ℝ) ≤ harmonicDivProbability X W p := by
    have hpPrime := hPrime p hp
    have hpPos : 0 < p := hpPrime.pos
    have hpKnat : p ≤ p * p := Nat.le_mul_of_pos_right p hpPos
    have hpK : (p : ℝ) ≤ Kbound := by
      have hpKreal : (p : ℝ) ≤ ((p * p : ℕ) : ℝ) := by exact_mod_cast hpKnat
      exact le_trans hpKreal (hKprod p hp p hp)
    exact (hqBounds p hpPos (hCoprime p hp) hpK).1
  have hqUpper (p : ℕ) (hp : p ∈ P) :
      harmonicDivProbability X W p ≤ (1 + E) / (p : ℝ) := by
    have hpPrime := hPrime p hp
    have hpPos : 0 < p := hpPrime.pos
    have hpKnat : p ≤ p * p := Nat.le_mul_of_pos_right p hpPos
    have hpK : (p : ℝ) ≤ Kbound := by
      have hpKreal : (p : ℝ) ≤ ((p * p : ℕ) : ℝ) := by exact_mod_cast hpKnat
      exact le_trans hpKreal (hKprod p hp p hp)
    exact (hqBounds p hpPos (hCoprime p hp) hpK).2
  have hmeanLower : 1 - E ≤ mean := by
    dsimp [mean]
    rw [hMeanFormula]
    have hterm :
        ∑ p ∈ P, S⁻¹ * ((1 - E) / (p : ℝ)) ≤
          ∑ p ∈ P, S⁻¹ * harmonicDivProbability X W p :=
      Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hqLower p hp) hInvS
    have hbase : ∑ p ∈ P, S⁻¹ * ((1 - E) / (p : ℝ)) = 1 - E := by
      calc
        _ = ∑ p ∈ P, ((1 - E) / S) * (1 / (p : ℝ)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpPos : 0 < p := (hPrime p hp).pos
          have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hpPos
          field_simp [ne_of_gt hSpos, ne_of_gt hpRpos]
        _ = ((1 - E) / S) * ∑ p ∈ P, 1 / (p : ℝ) := by
          rw [← Finset.mul_sum]
        _ = ((1 - E) / S) * S := by rw [hSsum]
        _ = 1 - E := by field_simp [ne_of_gt hSpos]
    exact le_trans (le_of_eq hbase.symm) hterm
  have hqPairUpper (p q : ℕ) (hp : p ∈ P) (hq : q ∈ P)
      (hne : p ≠ q) :
      harmonicDivPairProbability X W p q ≤ (1 + E) / ((p * q : ℕ) : ℝ) := by
    rw [harmonicDivPair_eq_product_probability X W p q (hPrime p hp) (hPrime q hq) hne]
    have hcop : Nat.Coprime (p * q) W := by
      rw [Nat.coprime_mul_iff_left]
      exact ⟨hCoprime p hp, hCoprime q hq⟩
    have hk : 0 < p * q := Nat.mul_pos (hPrime p hp).pos (hPrime q hq).pos
    have hkK : ((p * q : ℕ) : ℝ) ≤ Kbound := by exact_mod_cast hKprod p hp q hq
    simpa [Nat.cast_mul] using (hqBounds (p * q) hk hcop hkK).2
  have hInvS2 : 0 ≤ S⁻¹ * S⁻¹ := by positivity
  have hsecondUpper : second ≤ (1 + E) * (1 + 1 / S) := by
    let diag : ℕ → ℝ := fun p => (1 + E) / (p : ℝ)
    let offdiag : ℕ → ℕ → ℝ := fun p q => (1 + E) / ((p * q : ℕ) : ℝ)
    have hterm (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
        harmonicDivPairProbability X W p q ≤ if p = q then diag p else offdiag p q := by
      by_cases hpq : p = q
      · subst q
        simp [diag]
        rw [harmonicDivPair_diagonal]
        exact hqUpper p hp
      · simp [diag, offdiag, hpq]
        simpa [Nat.cast_mul, offdiag] using hqPairUpper p q hp hq hpq
    have hUpperSum :
        (∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) *
          (if p = q then diag p else offdiag p q)) ≤
          (S⁻¹ * S⁻¹) *
            ((∑ p ∈ P, diag p) + ∑ p ∈ P, ∑ q ∈ P, offdiag p q) := by
      calc
        _ ≤ ∑ p ∈ P, ∑ q ∈ P,
              ((S⁻¹ * S⁻¹) * (if p = q then diag p else 0) +
                (S⁻¹ * S⁻¹) * offdiag p q) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          by_cases hpq : p = q
          · simp [hpq]
            positivity
          · simp [hpq]
        _ = (∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) * (if p = q then diag p else 0)) +
              ∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) * offdiag p q := by
          simp_rw [Finset.sum_add_distrib]
        _ = (S⁻¹ * S⁻¹) * (∑ p ∈ P, diag p) +
              (S⁻¹ * S⁻¹) * (∑ p ∈ P, ∑ q ∈ P, offdiag p q) := by
          congr 1
          · calc
              (∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) * (if p = q then diag p else 0)) =
                  ∑ p ∈ P, (S⁻¹ * S⁻¹) * diag p := by
                apply Finset.sum_congr rfl
                intro p hp
                simp [Finset.sum_ite_eq, hp]
              _ = (S⁻¹ * S⁻¹) * ∑ p ∈ P, diag p := by rw [Finset.mul_sum]
          · calc
              (∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) * offdiag p q) =
                  ∑ p ∈ P, (S⁻¹ * S⁻¹) * ∑ q ∈ P, offdiag p q := by
                apply Finset.sum_congr rfl
                intro p hp
                rw [Finset.mul_sum]
              _ = (S⁻¹ * S⁻¹) * ∑ p ∈ P, ∑ q ∈ P, offdiag p q := by rw [Finset.mul_sum]
        _ = (S⁻¹ * S⁻¹) *
              ((∑ p ∈ P, diag p) + ∑ p ∈ P, ∑ q ∈ P, offdiag p q) := by ring
    have hdiagSum : ∑ p ∈ P, diag p = (1 + E) * S := by
      calc
        ∑ p ∈ P, diag p = ∑ p ∈ P, (1 + E) * (1 / (p : ℝ)) := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp [diag]
          have hpRpos : 0 < (p : ℝ) := by exact_mod_cast (hPrime p hp).pos
          field_simp [ne_of_gt hpRpos]
        _ = (1 + E) * ∑ p ∈ P, 1 / (p : ℝ) := by rw [← Finset.mul_sum]
        _ = (1 + E) * S := by rw [hSsum]
    have hoffdiagSum :
        ∑ p ∈ P, ∑ q ∈ P, offdiag p q = (1 + E) * S ^ 2 := by
      calc
        ∑ p ∈ P, ∑ q ∈ P, offdiag p q =
            ∑ p ∈ P, ∑ q ∈ P,
              (1 + E) * ((1 / (p : ℝ)) * (1 / (q : ℝ))) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          dsimp [offdiag]
          have hpPos : 0 < p := (hPrime p hp).pos
          have hqPos : 0 < q := (hPrime q hq).pos
          have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hpPos
          have hqRpos : 0 < (q : ℝ) := by exact_mod_cast hqPos
          rw [Nat.cast_mul]
          field_simp [ne_of_gt hpRpos, ne_of_gt hqRpos]
        _ = (1 + E) * ((∑ p ∈ P, 1 / (p : ℝ)) * (∑ q ∈ P, 1 / (q : ℝ))) := by
          calc
            _ = ∑ p ∈ P, (1 + E) *
                ((1 / (p : ℝ)) * ∑ q ∈ P, 1 / (q : ℝ)) := by
              apply Finset.sum_congr rfl
              intro p hp
              calc
                ∑ q ∈ P, (1 + E) * ((1 / (p : ℝ)) * (1 / (q : ℝ))) =
                    ∑ q ∈ P, ((1 + E) * (1 / (p : ℝ))) * (1 / (q : ℝ)) := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  ring
                _ = ((1 + E) * (1 / (p : ℝ))) * ∑ q ∈ P, 1 / (q : ℝ) := by
                  rw [← Finset.mul_sum]
                _ = (1 + E) * ((1 / (p : ℝ)) * ∑ q ∈ P, 1 / (q : ℝ)) := by ring
            _ = (1 + E) *
                (∑ p ∈ P, (1 / (p : ℝ)) * ∑ q ∈ P, 1 / (q : ℝ)) := by
              rw [← Finset.mul_sum]
            _ = (1 + E) *
                ((∑ p ∈ P, 1 / (p : ℝ)) * (∑ q ∈ P, 1 / (q : ℝ))) := by
              congr 1
              rw [← Finset.sum_mul]
        _ = (1 + E) * S ^ 2 := by rw [hSsum]; ring
    have hEval :
        (S⁻¹ * S⁻¹) *
          ((∑ p ∈ P, diag p) + ∑ p ∈ P, ∑ q ∈ P, offdiag p q) =
        (1 + E) * (1 + 1 / S) := by
      rw [hdiagSum, hoffdiagSum]
      field_simp [ne_of_gt hSpos]
      ring
    have hsecondLe :
        (∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) * harmonicDivPairProbability X W p q) ≤
        (∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) *
          (if p = q then diag p else offdiag p q)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hterm p hp q hq) hInvS2
    have hsecondEq : second =
        ∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) * harmonicDivPairProbability X W p q := by
      dsimp [second]
      exact hSecondFormula
    calc
      second = ∑ p ∈ P, ∑ q ∈ P,
          (S⁻¹ * S⁻¹) * harmonicDivPairProbability X W p q := hsecondEq
      _ ≤ ∑ p ∈ P, ∑ q ∈ P, (S⁻¹ * S⁻¹) *
          (if p = q then diag p else offdiag p q) := hsecondLe
      _ ≤ (1 + E) * (1 + 1 / S) := le_trans hUpperSum (le_of_eq hEval)
  have hvarianceEq :
      (∑ y ∈ harmonicSupport X,
        harmonicLaw X W y * (primeDivisibilityWeight P S y - 1) ^ 2) =
      second - 2 * mean + 1 := by
    dsimp [mean, second]
    have hm : ∑ y ∈ harmonicSupport X, harmonicLaw X W y = 1 := hMass
    calc
      ∑ y ∈ harmonicSupport X,
          harmonicLaw X W y * (primeDivisibilityWeight P S y - 1) ^ 2 =
        ∑ y ∈ harmonicSupport X,
          (harmonicLaw X W y * (primeDivisibilityWeight P S y ^ 2) -
            2 * (harmonicLaw X W y * primeDivisibilityWeight P S y) +
            harmonicLaw X W y) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = second - 2 * mean + 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
        rw [hm]
  have hvariance :
      (∑ y ∈ harmonicSupport X,
        harmonicLaw X W y * (primeDivisibilityWeight P S y - 1) ^ 2) ≤ 1 / S + 4 * E := by
    rw [hvarianceEq]
    have hEterm : E / S ≤ E := by
      have hSoneR : (1 : ℝ) ≤ S := hSone
      rw [div_le_iff₀ hSpos]
      nlinarith [hE]
    have hsecondExpanded : second ≤ 1 + E + 1 / S + E / S := by
      have heq : (1 + E) * (1 + 1 / S) = 1 + E + 1 / S + E / S := by ring
      rw [heq] at hsecondUpper
      exact hsecondUpper
    nlinarith [hsecondExpanded, hmeanLower, hE, hEterm]
  exact hvariance

private theorem primeDivWeight_deviation_small {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K) (hli : l < i) :
    ∀ A : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A *
        ∑ y ∈ harmonicSupport (S.core.parameters.X N i),
          harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            |primeDivisibilityWeight
                (primeSupport (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper)
                (primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper) y - 1| ≤ ε := by
  intro A ε hε
  let V : ℕ → ℕ := fun N => FromArithmetic.masterScaleV S.core.parameters N l
  let size : ℕ → ℕ := fun N => (S.primeStage.pool N l).upper + V N
  let W : ℕ → ℕ := fun N => primorial (N + 1)
  let X : ℕ → ℕ := fun N => S.core.parameters.X N i
  let P : ℕ → Finset ℕ := fun N =>
    primeSupport (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper
  let mass : ℕ → ℝ := fun N =>
    primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper
  let err : ℕ → ℝ := fun N =>
    FromArithmetic.harmonicResidueUniformError (X N) (W N) (size N ^ 2)
  let D : ℝ := max (2 * A) 1
  let T : ℝ := 128 / ε ^ 2
  have hDpos : 0 < D := by
    dsimp [D]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have h2AleD : 2 * A ≤ D := le_max_left _ _
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  have hV2 : ∀ N, 2 ≤ V N := by
    intro N
    dsimp [V]
    unfold FromArithmetic.masterScaleV
    omega
  have hsize2 : ∀ N, 2 ≤ size N := by
    intro N
    dsimp [size]
    have hV := hV2 N
    omega
  have hcutoff : (∀ N, 2 ≤ X N) ∧ ∀ᶠ N in atTop,
      Real.log (X N : ℝ) > (W N : ℝ) / X N := by
    let Aparam := S.core.parameters
    have hraw := S.gapStage.raw_cutoff_log_dominates_gap i
    have hloglarge : ∀ᶠ N in atTop, 1 ≤ Real.log (Aparam.X N i : ℝ) := by
      have h := (hraw 1 (by norm_num)).eventually_ge_atTop 1
      filter_upwards [h] with N hN
      have hHpos : 0 < (Aparam.H N i : ℝ) := by exact_mod_cast Aparam.Hpos N i
      have hHone : 1 ≤ Aparam.H N i := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Aparam.Hpos N i))
      have hHoneR : 1 ≤ (Aparam.H N i : ℝ) := by exact_mod_cast hHone
      have hratio : 1 ≤ Real.log (Aparam.X N i : ℝ) / (Aparam.H N i : ℝ) := by
        simpa [Real.rpow_one] using hN
      exact le_trans hHoneR ((one_le_div hHpos).mp hratio)
    have hden : ∀ᶠ N in atTop,
        Real.log (Aparam.X N i : ℝ) > (primorial (N + 1) : ℝ) / Aparam.X N i := by
      filter_upwards [hloglarge] with N hlog
      have hcut := S.gapStage.valid_raw_cutoffs N i
      have hWpos : 0 < primorial (N + 1) := primorial_pos _
      have hXpos : 0 < (Aparam.X N i : ℝ) := by
        have hWone : 1 ≤ primorial (N + 1) := Nat.succ_le_of_lt hWpos
        have h4W : 4 ≤ 4 * primorial (N + 1) := by
          simpa using Nat.mul_le_mul_left 4 hWone
        have h4X : 4 ≤ Aparam.X N i := le_trans h4W hcut
        have hXnat : 0 < Aparam.X N i := lt_of_lt_of_le (by norm_num) h4X
        exact_mod_cast hXnat
      have hcutR : 4 * (primorial (N + 1) : ℝ) ≤ Aparam.X N i := by exact_mod_cast hcut
      have hfrac : (primorial (N + 1) : ℝ) / Aparam.X N i ≤ 1 / 4 := by
        apply (div_le_iff₀ hXpos).2
        nlinarith
      linarith
    constructor
    · intro N
      dsimp [X]
      have hcut := S.gapStage.valid_raw_cutoffs N i
      have hWpos : 1 ≤ primorial (N + 1) := by
        have hp : 0 < primorial (N + 1) := primorial_pos _
        omega
      omega
    · simpa [X, W, Aparam] using hden
  have hresSmall := prime_residue_error_superpolynomial S l i hli
  have herr : ∀ᶠ N in atTop, err N * (size N : ℝ) ^ D < ε ^ 2 / 512 := by
    have h := (hresSmall D hDpos).eventually
      (Iio_mem_nhds (by positivity : 0 < ε ^ 2 / 512))
    filter_upwards [h] with N hN
    simpa [err, size, X, W, FromArithmetic.harmonicResidueUniformError] using hN
  have hmassDom := S.primeStage.pool_harmonic_mass_dominates l
  have hmassRate : ∀ᶠ N in atTop,
      T ≤ mass N / (V N : ℝ) ^ (D + 1) := by
    have h := (hmassDom (D + 1) (by linarith)).eventually_ge_atTop T
    simpa [mass, V, Real.rpow_one] using h
  have hPool := prime_pool_eventual_data S l
  filter_upwards [hcutoff.2, herr, hmassRate, hPool] with N hlog hErrN hMassRate hPoolN
  let pset : Finset ℕ := P N
  let SN : ℝ := mass N
  let VN : ℝ := (V N : ℝ)
  let sizeN : ℝ := (size N : ℝ)
  let EN : ℝ := err N
  have hX : 2 ≤ X N := hcutoff.1 N
  have hW : 0 < W N := by dsimp [W]; exact primorial_pos _
  have hSone : 1 ≤ SN := by simpa [SN, mass] using hPoolN.1
  have hSpos : 0 < SN := lt_of_lt_of_le (by norm_num) hSone
  have hVone : 1 ≤ VN := by
    have hNat : 1 ≤ V N := by have h' := hV2 N; omega
    have hReal : (1 : ℝ) ≤ (V N : ℝ) := by exact_mod_cast hNat
    simpa [VN] using hReal
  have hsizeV : VN ≤ sizeN := by
    dsimp [VN, sizeN, size, V]
    exact_mod_cast Nat.le_add_left _ _
  have hsizeone : 1 ≤ sizeN := le_trans hVone hsizeV
  have hVpos : 0 < VN := lt_of_lt_of_le (by norm_num) hVone
  have hVAp : 0 < VN ^ A := Real.rpow_pos_of_pos hVpos A
  have hVpowSize : VN ^ (2 * A) ≤ sizeN ^ D := by
    by_cases hA : 0 ≤ 2 * A
    · exact (Real.rpow_le_rpow hVpos.le hsizeV hA).trans
        (Real.rpow_le_rpow_of_exponent_le hsizeone (le_max_left _ _))
    · have hsmall : VN ^ (2 * A) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hVone (le_of_not_ge hA)
      exact hsmall.trans (Real.one_le_rpow hsizeone (le_trans (by norm_num) hDpos.le))
  have hVpowLarge : VN ^ (2 * A) ≤ VN ^ (D + 1) :=
    Real.rpow_le_rpow_of_exponent_le hVone (le_trans h2AleD (by linarith))
  have hVlargePos : 0 < VN ^ (D + 1) := Real.rpow_pos_of_pos hVpos (D + 1)
  have hMassBig : T * VN ^ (D + 1) ≤ SN := by
    simpa [SN, mass, VN, V] using (le_div_iff₀ hVlargePos).mp hMassRate
  have hInvMass : VN ^ (2 * A) / SN ≤ 1 / T := by
    have hpowSmall : T * VN ^ (2 * A) ≤ SN := by
      calc
        T * VN ^ (2 * A) ≤ T * VN ^ (D + 1) :=
          mul_le_mul_of_nonneg_left hVpowLarge hTpos.le
        _ ≤ SN := hMassBig
    apply (div_le_iff₀ hSpos).2
    have hdiv : VN ^ (2 * A) ≤ SN / T :=
      (le_div_iff₀ hTpos).2 (by simpa [mul_comm] using hpowSmall)
    calc
      VN ^ (2 * A) ≤ SN / T := hdiv
      _ = (1 / T) * SN := by ring
  have hSsum : SN = ∑ p ∈ pset, 1 / (p : ℝ) := by
    dsimp [SN, mass, pset, P]
    rfl
  have hENnonneg : 0 ≤ EN := by
    dsimp [EN, err, FromArithmetic.harmonicResidueUniformError, FromArithmetic.harmonicResidueError]
    positivity
  have hErrScaled : VN ^ (2 * A) * EN ≤ ε ^ 2 / 512 := by
    have hle : VN ^ (2 * A) * EN ≤ sizeN ^ D * EN :=
      mul_le_mul_of_nonneg_right hVpowSize hENnonneg
    have hsmall : EN * sizeN ^ D < ε ^ 2 / 512 := by simpa [EN, sizeN] using hErrN
    exact le_trans hle (le_of_lt (by simpa [mul_comm] using hsmall))
  have hWpos : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast hW
  have hlogden : 0 < Real.log (X N : ℝ) - (W N : ℝ) / X N := sub_pos.mpr hlog
  have hmassFinite :
      (∑ y ∈ harmonicSupport (X N), harmonicLaw (X N) (W N) y) = 1 := by
    have hMassTsum := harmonicLaw_tsum_eq_one (X N) (W N) hW hX hlog
    have hzero (y : ℤ) (hy : y ∉ harmonicSupport (X N)) :
        harmonicLaw (X N) (W N) y = 0 := harmonicLaw_eq_zero_of_not_mem _ _ _ hy
    rw [tsum_eq_sum (s := harmonicSupport (X N)) hzero] at hMassTsum
    exact hMassTsum
  have hprime : ∀ p ∈ pset, Nat.Prime p := by
    intro p hp
    have hp' : p ∈ primeSupport (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper := by simpa [pset, P] using hp
    have hpFilter : p ∈ (Finset.Ico (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper).filter Nat.Prime := by
      simpa [primeSupport] using hp'
    exact (Finset.mem_filter.mp hpFilter).2
  have hcop : ∀ p ∈ pset, Nat.Coprime p (W N) := by
    intro p hp
    exact hPoolN.2 p (by simpa [pset, P] using hp)
  have hKprod : ∀ p ∈ pset, ∀ q ∈ pset,
      ((p * q : ℕ) : ℝ) ≤ ((size N ^ 2 : ℕ) : ℝ) := by
    intro p hp q hq
    have hp' : p ∈ primeSupport (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper := by simpa [pset, P] using hp
    have hq' : q ∈ primeSupport (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper := by simpa [pset, P] using hq
    have hpFilter : p ∈ (Finset.Ico (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper).filter Nat.Prime := by
      simpa [primeSupport] using hp'
    have hqFilter : q ∈ (Finset.Ico (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper).filter Nat.Prime := by
      simpa [primeSupport] using hq'
    have hbound : (S.primeStage.pool N l).upper ≤ size N := by
      dsimp [size]
      exact Nat.le_add_right _ _
    have hpUpper : p ≤ size N :=
      le_trans (Nat.le_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp hpFilter).1).2) hbound
    have hqUpper : q ≤ size N :=
      le_trans (Nat.le_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp hqFilter).1).2) hbound
    have hnat : p * q ≤ size N ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hpUpper hqUpper
    have hnatR : ((p * q : ℕ) : ℝ) ≤ ((size N ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [sizeN, Nat.cast_pow] using hnatR
  have hresidue : ∀ k : ℕ, 0 < k → Nat.Coprime k (W N) →
      (k : ℝ) ≤ sizeN ^ 2 →
      |(k : ℝ) * harmonicDivProbability (X N) (W N) k - 1| ≤ EN := by
    intro k hk hkc hkSize
    have hkCast : (k : ℝ) ≤ ((size N ^ 2 : ℕ) : ℝ) := by
      simpa [sizeN, Nat.cast_pow] using hkSize
    have hkNat : k ≤ size N ^ 2 := by exact_mod_cast hkCast
    have hpoint := harmonicDivProbability_residue_error (X N) (W N) k hW hX hlog hk hkc
    have hmono := harmonicResidueError_mono hkNat hX hlog
    simpa [EN, err, FromArithmetic.harmonicResidueUniformError] using hpoint.trans hmono
  have hKprodReal : ∀ p ∈ pset, ∀ q ∈ pset,
      ((p * q : ℕ) : ℝ) ≤ sizeN ^ 2 := by
    intro p hp q hq
    simpa [sizeN, Nat.cast_pow] using hKprod p hp q hq
  have hVar :
      (∑ y ∈ harmonicSupport (X N),
        harmonicLaw (X N) (W N) y *
          (primeDivisibilityWeight pset SN y - 1) ^ 2) ≤ 1 / SN + 4 * EN :=
    primeDivWeight_variance_bound (X N) (W N) pset SN EN (sizeN ^ 2)
      hSpos hSone hSsum hmassFinite hprime hcop hKprodReal hENnonneg hresidue
  let δ : ℝ := ε / (8 * VN ^ A)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hμnonneg : ∀ y ∈ harmonicSupport (X N),
      0 ≤ harmonicLaw (X N) (W N) y := by
    intro y hy
    unfold harmonicLaw
    split_ifs with h
    · have hypos : 0 < y.toNat := lt_of_lt_of_le (by omega) h.2.1
      have hyR : 0 < (y.toNat : ℝ) := by exact_mod_cast hypos
      have hnormpos : 0 < harmonicNormalizer (X N) (W N) :=
        harmonicNormalizer_pos (X N) (W N) hW hX hlog
      positivity
    · positivity
  have hL1 := finite_deviation_l1_bound (harmonicSupport (X N))
    (harmonicLaw (X N) (W N)) (primeDivisibilityWeight pset SN) δ hδ
    hμnonneg (by
      have hMassTsum := harmonicLaw_tsum_eq_one (X N) (W N) hW hX hlog
      have hzero (y : ℤ) (hy : y ∉ harmonicSupport (X N)) :
          harmonicLaw (X N) (W N) y = 0 := harmonicLaw_eq_zero_of_not_mem _ _ _ hy
      rw [tsum_eq_sum (s := harmonicSupport (X N)) hzero] at hMassTsum
      exact hMassTsum)
  have hL1bound :
      (∑ y ∈ harmonicSupport (X N),
        harmonicLaw (X N) (W N) y *
          |primeDivisibilityWeight pset SN y - 1|) ≤
        δ + (1 / SN + 4 * EN) / δ := by
    calc
      _ ≤ δ +
          (∑ y ∈ harmonicSupport (X N), harmonicLaw (X N) (W N) y *
            (primeDivisibilityWeight pset SN y - 1) ^ 2) / δ := hL1
      _ ≤ δ + (1 / SN + 4 * EN) / δ :=
        add_le_add_right (div_le_div_of_nonneg_right hVar hδ.le) δ
  have h2AVar : VN ^ A *
      ∑ y ∈ harmonicSupport (X N),
        harmonicLaw (X N) (W N) y * |primeDivisibilityWeight pset SN y - 1| ≤
      ε / 8 + (8 / ε) * (VN ^ (2 * A) *
        ∑ y ∈ harmonicSupport (X N),
          harmonicLaw (X N) (W N) y *
            (primeDivisibilityWeight pset SN y - 1) ^ 2) := by
    calc
      _ ≤ VN ^ A * (δ + (∑ y ∈ harmonicSupport (X N),
          harmonicLaw (X N) (W N) y *
            (primeDivisibilityWeight pset SN y - 1) ^ 2) / δ) :=
        mul_le_mul_of_nonneg_left hL1 (Real.rpow_nonneg (le_of_lt hVpos) A)
      _ = ε / 8 + (8 / ε) * (VN ^ (2 * A) *
          ∑ y ∈ harmonicSupport (X N),
            harmonicLaw (X N) (W N) y *
              (primeDivisibilityWeight pset SN y - 1) ^ 2) := by
        dsimp [δ]
        have hpow : VN ^ A * VN ^ A = VN ^ (2 * A) := by
          rw [← Real.rpow_add hVpos]
          congr 1
          ring
        field_simp [ne_of_gt hε, ne_of_gt hVAp]
        simp_rw [pow_two]
        rw [hpow]
        ring
  have hVarScaled : VN ^ (2 * A) *
      ∑ y ∈ harmonicSupport (X N),
        harmonicLaw (X N) (W N) y *
          (primeDivisibilityWeight pset SN y - 1) ^ 2 ≤ ε ^ 2 / 64 := by
    calc
      _ ≤ VN ^ (2 * A) * (1 / SN + 4 * EN) :=
        mul_le_mul_of_nonneg_left hVar (Real.rpow_nonneg hVpos.le (2 * A))
      _ = VN ^ (2 * A) / SN + 4 * (VN ^ (2 * A) * EN) := by ring
      _ ≤ 1 / T + 4 * (ε ^ 2 / 512) := add_le_add hInvMass (mul_le_mul_of_nonneg_left hErrScaled (by norm_num))
      _ = ε ^ 2 / 64 := by dsimp [T]; field_simp [ne_of_gt hε]; ring
  have hfinal :
      VN ^ A *
        ∑ y ∈ harmonicSupport (X N),
          harmonicLaw (X N) (W N) y *
            |primeDivisibilityWeight pset SN y - 1| ≤ ε / 4 := by
    calc
      _ ≤ ε / 8 + (8 / ε) * (VN ^ (2 * A) *
          ∑ y ∈ harmonicSupport (X N),
            harmonicLaw (X N) (W N) y *
              (primeDivisibilityWeight pset SN y - 1) ^ 2) := h2AVar
      _ ≤ ε / 8 + (8 / ε) * (ε ^ 2 / 64) := by
        exact add_le_add (le_rfl) (mul_le_mul_of_nonneg_left hVarScaled (by positivity))
      _ = ε / 4 := by field_simp [ne_of_gt hε]; ring
  have hfinalLe : ε / 4 ≤ ε := by linarith
  exact le_trans (by simpa [VN, V, pset, P, SN, mass, W, X] using hfinal) hfinalLe

private theorem finite_weighted_average_error {α : Type*} [DecidableEq α]
    (s : Finset α) (w f g : α → ℝ) (δ : ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (hwsum : ∑ x ∈ s, w x = 1)
    (hfg : ∀ x ∈ s, |f x - g x| ≤ δ) :
    |(∑ x ∈ s, w x * f x) - ∑ x ∈ s, w x * g x| ≤ δ := by
  classical
  have hEq : (∑ x ∈ s, w x * f x) - ∑ x ∈ s, w x * g x =
      ∑ x ∈ s, w x * (f x - g x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hEq]
  calc
    |∑ x ∈ s, w x * (f x - g x)| ≤
        ∑ x ∈ s, |w x * (f x - g x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ s, w x * |f x - g x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg (hw x hx)]
    _ ≤ ∑ x ∈ s, w x * δ := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hfg x hx) (hw x hx)
    _ = δ := by rw [← Finset.sum_mul, hwsum, one_mul]

private theorem primePool_tsum_average_error (lo hi : ℕ) (hS : 0 < primePoolMass lo hi)
    (f g : ℕ → ℝ) (δ : ℝ)
    (hfg : ∀ p ∈ primeSupport lo hi, |f p - g p| ≤ δ) :
    |(∑' p : ℕ, primePoolLaw lo hi p * f p) -
      ∑' p : ℕ, primePoolLaw lo hi p * g p| ≤ δ := by
  classical
  let P := primeSupport lo hi
  have hzeroF (p : ℕ) (hp : p ∉ P) : primePoolLaw lo hi p * f p = 0 := by
    simp [primePoolLaw_zero_of_not_mem lo hi p hp]
  have hzeroG (p : ℕ) (hp : p ∉ P) : primePoolLaw lo hi p * g p = 0 := by
    simp [primePoolLaw_zero_of_not_mem lo hi p hp]
  have hwsum : ∑ p ∈ P, primePoolLaw lo hi p = 1 := by
    have h := primePoolLaw_tsum_eq_one lo hi hS
    rw [tsum_eq_sum (s := P)
      (fun p hp => primePoolLaw_zero_of_not_mem lo hi p hp)] at h
    exact h
  have hwpos (p : ℕ) (hp : p ∈ P) : 0 ≤ primePoolLaw lo hi p := by
    rw [primePoolLaw_eq_reciprocal_div_mass lo hi p hp]
    positivity
  rw [tsum_eq_sum (s := P) hzeroF, tsum_eq_sum (s := P) hzeroG]
  exact finite_weighted_average_error P (primePoolLaw lo hi) f g δ hwpos hwsum hfg

private theorem finite_weighted_function_deviation_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (μ g F : α → ℝ) (M : ℝ)
    (hμ : ∀ x ∈ s, 0 ≤ μ x) (hF : ∀ x, |F x| ≤ M) :
    |(∑ x ∈ s, μ x * F x) - ∑ x ∈ s, μ x * (g x * F x)| ≤
      M * ∑ x ∈ s, μ x * |g x - 1| := by
  classical
  have hEq : (∑ x ∈ s, μ x * F x) - ∑ x ∈ s, μ x * (g x * F x) =
      ∑ x ∈ s, μ x * ((1 - g x) * F x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hEq]
  calc
    |∑ x ∈ s, μ x * ((1 - g x) * F x)| ≤
        ∑ x ∈ s, |μ x * ((1 - g x) * F x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ s, (μ x * |g x - 1|) * |F x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_mul, abs_of_nonneg (hμ x hx), abs_sub_comm]
      ring
    _ ≤ ∑ x ∈ s, (M * (μ x * |g x - 1|)) := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        μ x * |g x - 1| * |F x| ≤ (μ x * |g x - 1|) * M :=
          mul_le_mul_of_nonneg_left (hF x)
            (mul_nonneg (hμ x hx) (abs_nonneg _))
        _ = M * (μ x * |g x - 1|) := by ring
    _ = M * ∑ x ∈ s, μ x * |g x - 1| := by rw [← Finset.mul_sum]

private theorem harmonic_function_deviation_bound (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log (X : ℝ) > (W : ℝ) / X) (g F : ℤ → ℝ)
    (M : ℝ) (hF : ∀ y, |F y| ≤ M) :
    |(∑' y : ℤ, harmonicLaw X W y * F y) -
      ∑' y : ℤ, harmonicLaw X W y * (g y * F y)| ≤
      M * ∑ y ∈ harmonicSupport X, harmonicLaw X W y * |g y - 1| := by
  classical
  have hzeroF (y : ℤ) (hy : y ∉ harmonicSupport X) :
      harmonicLaw X W y * F y = 0 := by
    simp [harmonicLaw_eq_zero_of_not_mem X W y hy]
  have hzeroG (y : ℤ) (hy : y ∉ harmonicSupport X) :
      harmonicLaw X W y * (g y * F y) = 0 := by
    simp [harmonicLaw_eq_zero_of_not_mem X W y hy]
  rw [tsum_eq_sum (s := harmonicSupport X) hzeroF,
    tsum_eq_sum (s := harmonicSupport X) hzeroG]
  apply finite_weighted_function_deviation_bound
  · intro y hy
    have hZ : 0 < harmonicNormalizer X W := harmonicNormalizer_pos X W hW hX hlog
    unfold harmonicLaw
    split_ifs with hc
    · have hypos : 0 < y.toNat := lt_of_lt_of_le (by omega) hc.2.1
      have hyR : 0 < (y.toNat : ℝ) := by exact_mod_cast hypos
      positivity
    · positivity
  · exact hF

private theorem dilatedHarmonic_zero_outside_image (X W k : ℕ) (hk : 0 < k) (z : ℤ)
    (hz : z ∉ (harmonicSupport X).image (fun y => (k : ℤ) * y)) :
    dilatedLaw (harmonicLaw X W) k z = 0 := by
  classical
  by_cases hzmod : z % (k : ℤ) = 0
  · have hdiv : (k : ℤ) ∣ z := Int.dvd_iff_emod_eq_zero.mpr hzmod
    have hy : z / (k : ℤ) ∉ harmonicSupport X := by
      intro hy
      apply hz
      refine Finset.mem_image.mpr ⟨z / (k : ℤ), hy, ?_⟩
      have hcancel := Int.ediv_mul_cancel hdiv
      calc
        (k : ℤ) * (z / (k : ℤ)) = (z / (k : ℤ)) * (k : ℤ) := by ring
        _ = z := hcancel
    simp [dilatedLaw, hzmod,
      harmonicLaw_eq_zero_of_not_mem X W (z / (k : ℤ)) hy]
  · simp [dilatedLaw, hzmod]

private theorem tsum_dilatedHarmonic_mul (X W k : ℕ) (hk : 0 < k) (F : ℤ → ℝ) :
    (∑' y : ℤ, harmonicLaw X W y * F ((k : ℤ) * y)) =
      ∑' z : ℤ, dilatedLaw (harmonicLaw X W) k z * F z := by
  classical
  have hzeroLeft (y : ℤ) (hy : y ∉ harmonicSupport X) :
      harmonicLaw X W y * F ((k : ℤ) * y) = 0 := by
    simp [harmonicLaw_eq_zero_of_not_mem X W y hy]
  have hzeroRight (z : ℤ)
      (hz : z ∉ (harmonicSupport X).image (fun y => (k : ℤ) * y)) :
      dilatedLaw (harmonicLaw X W) k z * F z = 0 := by
    simp [dilatedHarmonic_zero_outside_image X W k hk z hz]
  rw [tsum_eq_sum (s := harmonicSupport X) hzeroLeft,
    tsum_eq_sum (s := (harmonicSupport X).image (fun y => (k : ℤ) * y)) hzeroRight]
  have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hinj : Function.Injective (fun y : ℤ => (k : ℤ) * y) := by
    intro y y' h
    exact mul_left_cancel₀ hkz h
  rw [Finset.sum_image (s := harmonicSupport X)
    (f := fun z : ℤ => dilatedLaw (harmonicLaw X W) k z * F z)
    (g := fun y : ℤ => (k : ℤ) * y) hinj.injOn]
  apply Finset.sum_congr rfl
  intro y hy
  have hdiv : ((k : ℤ) * y) / (k : ℤ) = y := Int.mul_ediv_cancel_left y hkz
  simp [dilatedLaw, hkz, hdiv]

private theorem tsum_dilationReference_mul (X W k : ℕ) (F : ℤ → ℝ) :
    (∑' y : ℤ, harmonicLaw X W y *
      ((if (k : ℤ) ∣ y then (k : ℝ) else 0) * F y)) =
      ∑' y : ℤ, dilationReference (harmonicLaw X W) k y * F y := by
  apply tsum_congr
  intro y
  by_cases hy : (k : ℤ) ∣ y <;> simp [dilationReference, hy] <;> ring

private theorem dilatedHarmonic_mul_summable (X W k : ℕ) (hk : 0 < k) (F : ℤ → ℝ) :
    Summable (fun z : ℤ => dilatedLaw (harmonicLaw X W) k z * F z) := by
  apply summable_of_ne_finset_zero
    (s := (harmonicSupport X).image (fun y => (k : ℤ) * y))
  intro z hz
  simp [dilatedHarmonic_zero_outside_image X W k hk z hz]

private theorem dilationReference_mul_summable (X W k : ℕ) (F : ℤ → ℝ) :
    Summable (fun z : ℤ => dilationReference (harmonicLaw X W) k z * F z) := by
  apply summable_of_ne_finset_zero (s := harmonicSupport X)
  intro z hz
  simp [dilationReference, harmonicLaw_eq_zero_of_not_mem X W z hz]

private theorem dilation_expectation_bound (X W k : ℕ) (hk : 0 < k)
    (F : ℤ → ℝ) (M : ℝ) (hF : ∀ y, |F y| ≤ M) :
    |(∑' y : ℤ, harmonicLaw X W y * F ((k : ℤ) * y)) -
      ∑' y : ℤ, harmonicLaw X W y *
        ((if (k : ℤ) ∣ y then (k : ℝ) else 0) * F y)| ≤
      M * arithmeticL1 (dilatedLaw (harmonicLaw X W) k)
        (dilationReference (harmonicLaw X W) k) := by
  classical
  rw [tsum_dilatedHarmonic_mul X W k hk F,
    tsum_dilationReference_mul X W k F]
  let μ : ℤ → ℝ := fun z => dilatedLaw (harmonicLaw X W) k z
  let ν : ℤ → ℝ := fun z => dilationReference (harmonicLaw X W) k z
  let support : Finset ℤ := (harmonicSupport X).image (fun y => (k : ℤ) * y) ∪ harmonicSupport X
  have hμ (z : ℤ) (hz : z ∉ support) : μ z = 0 := by
    have hz' : z ∉ (harmonicSupport X).image (fun y => (k : ℤ) * y) := by
      intro hm
      exact hz (Finset.mem_union.mpr (Or.inl hm))
    exact dilatedHarmonic_zero_outside_image X W k hk z hz'
  have hν (z : ℤ) (hz : z ∉ support) : ν z = 0 := by
    have hz' : z ∉ harmonicSupport X := by
      intro hm
      exact hz (Finset.mem_union.mpr (Or.inr hm))
    simp [ν, dilationReference,
      harmonicLaw_eq_zero_of_not_mem X W z hz']
  have hμsum : Summable (fun z : ℤ => μ z * F z) := by
    simpa [μ] using dilatedHarmonic_mul_summable X W k hk F
  have hνsum : Summable (fun z : ℤ => ν z * F z) := by
    simpa [ν] using dilationReference_mul_summable X W k F
  have hdiff : (∑' z : ℤ, μ z * F z) - (∑' z : ℤ, ν z * F z) =
      ∑' z : ℤ, (μ z - ν z) * F z := by
    rw [← hμsum.tsum_sub hνsum]
    apply tsum_congr
    intro z
    ring
  rw [hdiff]
  exact tsum_mul_sub_bound_of_support μ ν F support M hμ hν hF

private theorem prime_insertion_fixed_dilation_mass {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K) (hli : l < i) (B : ℕ) :
    ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      Nat.Coprime k (primorial (N + 1)) →
      k ≤ ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B →
      (((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℕ) : ℝ) ^ C *
        arithmeticL1
          (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
          (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
        ≤ ε := by
  intro C hC ε hε
  let size : ℕ → ℕ := fun N =>
    (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l
  let Kseq : ℕ → ℕ := fun N => size N ^ B
  let Vseq : ℕ → ℕ := size
  let Hseq : ℕ → ℕ := fun _ => 1
  let Wseq : ℕ → ℕ := fun N => primorial (N + 1)
  let Xseq : ℕ → ℕ := fun N => S.core.parameters.X N i
  have hsz : ∀ N, 2 ≤ size N := by
    intro N
    dsimp [size]
    unfold FromArithmetic.masterScaleV
    omega
  have hWsize : ∀ N, Wseq N ≤ size N := by
    intro N
    dsimp [Wseq, size]
    have hWM := S.core.parameters.Wle N
    unfold FromArithmetic.masterScaleV
    omega
  have hdominance := prime_sampling_scale_dominance S l i hli B
  have hDomX : OAI.MicrocellScale.Dominates
      (fun N => (Xseq N : ℝ))
      (fun N => (2 + Wseq N + Kseq N + Hseq N + Vseq N : ℝ)) := by
    have heq :
        (fun N => (2 + Wseq N + Kseq N + Hseq N + Vseq N : ℝ)) =
        (fun N => (2 + primorial (N + 1) +
          ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B + 1 +
          (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) := by
      funext N
      dsimp [Wseq, Kseq, Hseq, Vseq, size]
      push_cast
      ring
    rw [heq]
    exact hdominance.1
  have hDomLog : OAI.MicrocellScale.Dominates
      (fun N => Real.log (Xseq N : ℝ))
      (fun N => (2 + Wseq N + Kseq N + Vseq N : ℝ)) := by
    have heq :
        (fun N => (2 + Wseq N + Kseq N + Vseq N : ℝ)) =
        (fun N => (2 + primorial (N + 1) +
          ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B +
          (S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) := by
      funext N
      dsimp [Wseq, Kseq, Vseq, size]
      push_cast
      ring
    rw [heq]
    exact hdominance.2
  have hXevent : ∀ᶠ N in atTop, 2 ≤ Xseq N := by
    apply Filter.Eventually.of_forall
    intro N
    dsimp [Xseq]
    have hcut := S.gapStage.valid_raw_cutoffs N i
    have hWpos : 1 ≤ primorial (N + 1) := by
      have hp : 0 < primorial (N + 1) := primorial_pos _
      omega
    omega
  have hloglarge : ∀ᶠ N in atTop, 1 ≤ Real.log (Xseq N : ℝ) := by
    have h := (hDomLog 1 (by norm_num)).eventually_ge_atTop 1
    filter_upwards [h] with N hN
    have hscale : 1 ≤ (2 + Wseq N + Kseq N + Vseq N : ℝ) := by
      have hWnonneg : 0 ≤ (Wseq N : ℝ) := by positivity
      have hKnonneg : 0 ≤ (Kseq N : ℝ) := by positivity
      have hVnonneg : 0 ≤ (Vseq N : ℝ) := by positivity
      linarith
    have hratio : 1 ≤ Real.log (Xseq N : ℝ) /
        (2 + Wseq N + Kseq N + Vseq N : ℝ) := by
      simpa [Real.rpow_one] using hN
    have hscaleLog : (2 + Wseq N + Kseq N + Vseq N : ℝ) ≤
        Real.log (Xseq N : ℝ) := (one_le_div (by positivity)).mp hratio
    exact le_trans hscale hscaleLog
  have hden : ∀ᶠ N in atTop,
      Real.log (Xseq N : ℝ) > (Wseq N : ℝ) / Xseq N := by
    filter_upwards [hloglarge] with N hlog
    have hcut : 4 * (Wseq N : ℝ) ≤ (Xseq N : ℝ) := by
      exact_mod_cast S.gapStage.valid_raw_cutoffs N i
    have hXpos : 0 < (Xseq N : ℝ) := by
      have hWpos : 0 < (Wseq N : ℝ) := by exact_mod_cast primorial_pos (N + 1)
      nlinarith
    have hfrac : (Wseq N : ℝ) / Xseq N ≤ 1 / 4 := by
      apply (div_le_iff₀ hXpos).2
      nlinarith
    linarith
  have hsam := FromArithmetic.sampling_asymptotics Wseq Kseq Hseq Vseq Xseq
    (by intro N; dsimp [Kseq]; exact one_le_pow₀ (by have h := hsz N; omega))
    (by intro N; rfl)
    (by
      intro N
      dsimp [Vseq, size]
      have hv : 2 ≤ FromArithmetic.masterScaleV S.core.parameters N l := by
        unfold FromArithmetic.masterScaleV
        omega
      omega)
    (by intro N; rfl)
    hXevent hden hDomX hDomLog
  have hsmall := hsam.2.2.1
  have hKleX : ∀ᶠ N in atTop, Kseq N ≤ Xseq N := by
    have h := (hDomX 1 (by norm_num)).eventually_ge_atTop 1
    filter_upwards [h] with N hN
    have hscale : 0 < (2 + Wseq N + Kseq N + Hseq N + Vseq N : ℝ) := by positivity
    have hratio : (2 + Wseq N + Kseq N + Hseq N + Vseq N : ℝ) ≤ (Xseq N : ℝ) := by
      have h' : 1 ≤ (Xseq N : ℝ) /
          (2 + Wseq N + Kseq N + Hseq N + Vseq N : ℝ) := by
        simpa [Real.rpow_one] using hN
      exact (one_le_div hscale).mp h'
    have hnat : Kseq N ≤ 2 + Wseq N + Kseq N + Hseq N + Vseq N := by omega
    have hnatX : 2 + Wseq N + Kseq N + Hseq N + Vseq N ≤ Xseq N := by exact_mod_cast hratio
    exact le_trans hnat hnatX
  have heps : ∀ᶠ N in atTop,
      (size N : ℝ) ^ C *
        FromArithmetic.harmonicDilationUniformError (Xseq N) (Wseq N) (Kseq N) < ε := by
    have h := (hsmall C hC).eventually (Iio_mem_nhds hε)
    filter_upwards [h] with N hN
    simpa [mul_comm, Vseq, size] using hN
  filter_upwards [hXevent, hden, hKleX, heps] with N hX hdenN hKleXN hepsN
  intro k hk hcop hkb
  have hkX : k ≤ Xseq N := le_trans hkb hKleXN
  have hBounds : FromArithmetic.SamplingPointwiseBounds (Xseq N) (Wseq N) :=
    FromArithmetic.sampling_pointwise_claim (Xseq N) (Wseq N)
      (primorial_pos (N + 1)) hX hdenN
  have hpoint := hBounds.dilation hX hdenN k
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk)) hkX hcop
  have hkR : (k : ℝ) ≤ (Kseq N : ℝ) := by exact_mod_cast hkb
  have hlogk : Real.log (k : ℝ) ≤ Real.log (Kseq N : ℝ) :=
    Real.log_le_log (by exact_mod_cast hk) hkR
  have hmul : (Wseq N : ℝ) * k ≤ (Wseq N : ℝ) * (Kseq N : ℝ) :=
    mul_le_mul_of_nonneg_left hkR (by positivity)
  have hdiv : (Wseq N : ℝ) * k / Xseq N ≤
      (Wseq N : ℝ) * (Kseq N : ℝ) / Xseq N :=
    div_le_div_of_nonneg_right hmul (by positivity)
  have hfactor : 0 ≤ 1 + 1 / (Xseq N : ℝ) := by positivity
  have htail : ((Wseq N : ℝ) * k / Xseq N) * (1 + 1 / (Xseq N : ℝ)) ≤
      ((Wseq N : ℝ) * (Kseq N : ℝ) / Xseq N) * (1 + 1 / (Xseq N : ℝ)) :=
    mul_le_mul_of_nonneg_right hdiv hfactor
  have hnum : 2 * Real.log (k : ℝ) +
      ((Wseq N : ℝ) * k / Xseq N) * (1 + 1 / (Xseq N : ℝ)) ≤
      2 * Real.log (Kseq N : ℝ) +
      ((Wseq N : ℝ) * (Kseq N : ℝ) / Xseq N) * (1 + 1 / (Xseq N : ℝ)) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hlogk (by norm_num)) htail
  have hformula :
      ((2 * Real.log (k : ℝ) + (Wseq N : ℝ) * k / Xseq N *
        (1 + 1 / Xseq N)) / (Real.log (Xseq N : ℝ) - (Wseq N : ℝ) / Xseq N)) ≤
      FromArithmetic.harmonicDilationUniformError (Xseq N) (Wseq N) (Kseq N) := by
    unfold FromArithmetic.harmonicDilationUniformError
    exact div_le_div_of_nonneg_right (by nlinarith [hnum]) (le_of_lt (sub_pos.mpr hdenN))
  have htotal : arithmeticL1
      (dilatedLaw (harmonicLaw (Xseq N) (Wseq N)) k)
      (dilationReference (harmonicLaw (Xseq N) (Wseq N)) k) ≤
      FromArithmetic.harmonicDilationUniformError (Xseq N) (Wseq N) (Kseq N) :=
    le_trans hpoint.1 hformula
  calc
    (size N : ℝ) ^ C * arithmeticL1
        (dilatedLaw (harmonicLaw (Xseq N) (Wseq N)) k)
        (dilationReference (harmonicLaw (Xseq N) (Wseq N)) k) ≤
      (size N : ℝ) ^ C * FromArithmetic.harmonicDilationUniformError (Xseq N) (Wseq N) (Kseq N) :=
        mul_le_mul_of_nonneg_left htotal (Real.rpow_nonneg (by positivity) C)
    _ ≤ ε := le_of_lt hepsN

theorem prime_insertion_fixed_dilation_aux {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K) (hli : l < i) (B : ℕ) :
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      Nat.Coprime k (primorial (N + 1)) →
      k ≤ ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B →
      (((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℕ) : ℝ) ^ C *
        arithmeticL1
          (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
          (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
        ≤ ε) ∧
    ∀ A : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      Nat.Coprime k (primorial (N + 1)) →
      k ≤ ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B →
      ∀ F : ℤ → ℝ, (∀ y, |F y| ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A) →
        |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            F ((k : ℤ) * y)) -
          ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            ((if (k : ℤ) ∣ y then (k : ℝ) else 0) * F y)| ≤ ε := by
  constructor
  · exact prime_insertion_fixed_dilation_mass S l i hli B
  · intro A ε hε
    let C : ℝ := max A 1
    have hC : 0 < C := by
      dsimp [C]
      exact lt_of_lt_of_le zero_lt_one (le_max_right A 1)
    have hAC : A ≤ C := le_max_left A 1
    have hmass := prime_insertion_fixed_dilation_mass S l i hli B C hC ε hε
    filter_upwards [hmass] with N hmassN
    intro k hk hcop hkb F hF
    let sizeN : ℕ := (S.primeStage.pool N l).upper +
      FromArithmetic.masterScaleV S.core.parameters N l
    have hsize1 : 1 ≤ (sizeN : ℝ) := by
      have hs : 1 ≤ sizeN := by dsimp [sizeN]; unfold FromArithmetic.masterScaleV; omega
      exact_mod_cast hs
    let V : ℝ := (FromArithmetic.masterScaleV S.core.parameters N l : ℝ)
    have hV1 : 1 ≤ V := by
      dsimp [V]
      exact_mod_cast (show 1 ≤ FromArithmetic.masterScaleV S.core.parameters N l by
        unfold FromArithmetic.masterScaleV
        omega)
    have hVle : V ≤ (sizeN : ℝ) := by
      dsimp [V, sizeN]
      exact_mod_cast Nat.le_add_left _ _
    have hMle : V ^ A ≤ (sizeN : ℝ) ^ C := by
      by_cases hAnon : A ≤ 0
      · have hVA : V ^ A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hV1 hAnon
        exact hVA.trans (Real.one_le_rpow hsize1 (le_of_lt hC))
      · have hApos : 0 ≤ A := le_of_not_ge hAnon
        have hVA : V ^ A ≤ (sizeN : ℝ) ^ A :=
          Real.rpow_le_rpow (by linarith [hV1]) hVle hApos
        exact hVA.trans (Real.rpow_le_rpow_of_exponent_le hsize1 hAC)
    have hL1nonneg : 0 ≤ arithmeticL1
        (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
        (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k) := by
      unfold arithmeticL1
      exact tsum_nonneg (fun _ => abs_nonneg _)
    have hF' : ∀ y, |F y| ≤ V ^ A := by simpa [V] using hF
    have hbound := dilation_expectation_bound
      (S.core.parameters.X N i) (primorial (N + 1)) k hk F (V ^ A) hF'
    have hmassBound := hmassN k hk hcop hkb
    have hscale : V ^ A * arithmeticL1
        (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
        (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k) ≤
      ((sizeN : ℝ) ^ C) * arithmeticL1
        (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
        (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k) :=
      mul_le_mul_of_nonneg_right hMle hL1nonneg
    calc
      |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
          F ((k : ℤ) * y)) -
        ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
          ((if (k : ℤ) ∣ y then (k : ℝ) else 0) * F y)| ≤
        V ^ A * arithmeticL1
          (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
          (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k) := hbound
      _ ≤ (((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℕ) : ℝ) ^ C *
          arithmeticL1
            (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
            (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k) := by
        simpa [sizeN, V] using hscale
      _ ≤ ε := hmassBound

theorem prime_insertion_average_aux {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K) (hli : l < i) (A : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ F : ℤ → ℝ,
      (∀ y, |F y| ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A) →
      |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y * F y) -
        poolAverage S l N (fun p =>
          ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            F ((p : ℤ) * y))| ≤ ε := by
  intro ε hε
  let X : ℕ → ℕ := fun N => S.core.parameters.X N i
  let W : ℕ → ℕ := fun N => primorial (N + 1)
  have hX : ∀ N, 2 ≤ X N := by
    intro N
    dsimp [X]
    have hcut := S.gapStage.valid_raw_cutoffs N i
    have hWpos : 1 ≤ primorial (N + 1) := by
      have hp : 0 < primorial (N + 1) := primorial_pos _
      omega
    omega
  have hraw := S.gapStage.raw_cutoff_log_dominates_gap i
  have hloglarge : ∀ᶠ N in atTop, 1 ≤ Real.log (X N : ℝ) := by
    have h := (hraw 1 (by norm_num)).eventually_ge_atTop 1
    filter_upwards [h] with N hN
    have hHpos : 0 < (S.core.parameters.H N i : ℝ) := by
      exact_mod_cast S.core.parameters.Hpos N i
    have hHoneNat : 1 ≤ S.core.parameters.H N i :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (S.core.parameters.Hpos N i))
    have hHone : 1 ≤ (S.core.parameters.H N i : ℝ) := by exact_mod_cast hHoneNat
    have hratio : 1 ≤ Real.log (X N : ℝ) /
        (S.core.parameters.H N i : ℝ) := by
      simpa [X, Real.rpow_one] using hN
    exact le_trans hHone ((one_le_div hHpos).mp hratio)
  have hlog : ∀ᶠ N in atTop,
      Real.log (X N : ℝ) > (W N : ℝ) / X N := by
    filter_upwards [hloglarge] with N hlarge
    have hcut := S.gapStage.valid_raw_cutoffs N i
    have hWpos : 0 < (W N : ℝ) := by
      dsimp [W]
      exact_mod_cast primorial_pos (N + 1)
    have hcutR : 4 * (W N : ℝ) ≤ (X N : ℝ) := by
      exact_mod_cast hcut
    have hXpos : 0 < (X N : ℝ) := by nlinarith
    have hfrac : (W N : ℝ) / X N ≤ 1 / 4 := by
      apply (div_le_iff₀ hXpos).2
      nlinarith
    linarith
  have hpool := prime_pool_eventual_data S l
  have hdilation :=
    (prime_insertion_fixed_dilation_aux S l i hli 1).2 A (ε / 2) (by linarith)
  have hdeviation := primeDivWeight_deviation_small S l i hli A (ε / 4) (by linarith)
  filter_upwards [hpool, hdilation, hdeviation, hlog] with N hpoolN hdilationN hdeviationN hlogN
  intro F hF
  let lo : ℕ := (S.primeStage.pool N l).lower
  let hi : ℕ := (S.primeStage.pool N l).upper
  let P : Finset ℕ := primeSupport lo hi
  let mass : ℝ := primePoolMass lo hi
  let μ : ℤ → ℝ := harmonicLaw (X N) (W N)
  let weight : ℤ → ℝ := primeDivisibilityWeight P mass
  let f : ℕ → ℝ := fun p => ∑' y : ℤ, μ y * F ((p : ℤ) * y)
  let g : ℕ → ℝ := fun p =>
    ∑' y : ℤ, μ y * ((if (p : ℤ) ∣ y then (p : ℝ) else 0) * F y)
  let reference : ℝ := ∑' y : ℤ, μ y * (weight y * F y)
  have hmassOne : 1 ≤ mass := by simpa [mass, lo, hi] using hpoolN.1
  have hmassPos : 0 < mass := lt_of_lt_of_le (by norm_num) hmassOne
  have hprimeData : ∀ p ∈ P,
      Nat.Prime p ∧ Nat.Coprime p (W N) ∧ p ≤ hi + FromArithmetic.masterScaleV S.core.parameters N l := by
    intro p hp
    have hpFilter : p ∈ (Finset.Ico lo hi).filter Nat.Prime := by
      simpa [P, primeSupport] using hp
    have hpIco := (Finset.mem_filter.mp hpFilter).1
    have hpPrime := (Finset.mem_filter.mp hpFilter).2
    have hpCop : Nat.Coprime p (W N) := by
      simpa [W] using hpoolN.2 p (by simpa [P, lo, hi, primeSupport] using hp)
    have hpLe : p ≤ hi + FromArithmetic.masterScaleV S.core.parameters N l := by
      exact le_trans (Nat.le_of_lt (Finset.mem_Ico.mp hpIco).2) (Nat.le_add_right _ _)
    exact ⟨hpPrime, hpCop, hpLe⟩
  have hfg : ∀ p ∈ P, |f p - g p| ≤ ε / 2 := by
    intro p hp
    obtain ⟨hpPrime, hpCop, hpLe⟩ := hprimeData p hp
    have hkbound : p ≤ (hi + FromArithmetic.masterScaleV S.core.parameters N l) ^ 1 := by
      simpa [pow_one] using hpLe
    have hd := hdilationN p hpPrime.pos hpCop hkbound F (by simpa [W, X] using hF)
    simpa [f, g, μ, X, W] using hd
  have haverage : |poolAverage S l N f - ∑' p : ℕ,
      primePoolLaw lo hi p * g p| ≤ ε / 2 := by
    simpa [poolAverage, f, g, μ, X, W, lo, hi] using
      primePool_tsum_average_error lo hi hmassPos f g (ε / 2) hfg
  have hreference : (∑' p : ℕ, primePoolLaw lo hi p * g p) = reference := by
    dsimp [reference, g, μ, weight, P]
    exact primePoolAverage_reference_eq_weighted (X N) (W N) lo hi F hmassPos
  have hweightDeviation :
      |(∑' y : ℤ, μ y * F y) - reference| ≤ ε / 4 := by
    calc
      |(∑' y : ℤ, μ y * F y) - reference| ≤
          (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A *
            ∑ y ∈ harmonicSupport (X N), μ y * |weight y - 1| := by
        exact harmonic_function_deviation_bound (X N) (W N)
          (by dsimp [W]; exact primorial_pos (N + 1)) (hX N) hlogN weight F
          ((FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A) (by simpa [W, X] using hF)
      _ ≤ ε / 4 := by
        simpa [μ, weight, P, mass, lo, hi, X, W] using hdeviationN
  have hreferenceError : |reference - poolAverage S l N f| ≤ ε / 2 := by
    calc
      |reference - poolAverage S l N f| =
          |(∑' p : ℕ, primePoolLaw lo hi p * g p) - poolAverage S l N f| := by
            rw [hreference]
      _ = |poolAverage S l N f - ∑' p : ℕ, primePoolLaw lo hi p * g p| :=
        abs_sub_comm _ _
      _ ≤ ε / 2 := haverage
  calc
    |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y * F y) -
        poolAverage S l N (fun p =>
          ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            F ((p : ℤ) * y))| =
        |((∑' y : ℤ, μ y * F y) - reference) +
          (reference - poolAverage S l N f)| := by
            congr 1 <;> simp [f, μ, X, W] <;> ring
    _ ≤ |(∑' y : ℤ, μ y * F y) - reference| +
        |reference - poolAverage S l N f| := abs_add_le _ _
    _ ≤ ε / 4 + ε / 2 := add_le_add hweightDeviation hreferenceError
    _ ≤ ε := by linarith

end HindmanSumsProducts
