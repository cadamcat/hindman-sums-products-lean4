import HindmanSumsProducts.Arithmetic.Defs
import HindmanSumsProducts.Arithmetic.Outside.AP
import PrimeNumberTheoremAnd.Wiener
import PrimeNumberTheoremAnd.Erdos970.Wiener
import OAI.NumberTheory.Jacobsthal.Sieve.PrimeFibreBrunBound

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts.Arithmetic.Outside
noncomputable section

private theorem psi_nat_sub_one_eq_vonMangoldt_sum {n : ℕ} (hn : 0 < n) :
    Chebyshev.psi ((n - 1 : ℕ) : ℝ) =
      cumsum ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast, cumsum]
  rw [← Nat.range_eq_Icc_zero_sub_one n (by omega)]

private theorem psi_nat_sub_one_div_tendsto :
    Tendsto (fun n : ℕ => Chebyshev.psi ((n - 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  apply WeakPNT.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [psi_nat_sub_one_eq_vonMangoldt_sum hn]

private theorem theta_nat_sub_one_div_tendsto :
    Tendsto (fun n : ℕ => Chebyshev.theta ((n - 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hψ := psi_nat_sub_one_div_tendsto
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hnat)
  have hsmall : Tendsto (fun n : ℕ => |C| / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul |C| hinv
  have hle : (fun n : ℕ => Chebyshev.psi ((n - 1 : ℕ) : ℝ) / (n : ℝ) -
      |C| / Real.sqrt (n : ℝ)) ≤ᶠ[atTop]
      (fun n : ℕ => Chebyshev.theta ((n - 1 : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hxle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sub_le n 1
    have hsqrt : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt hxle
    have hbound : Chebyshev.psi ((n - 1 : ℕ) : ℝ) -
        Chebyshev.theta ((n - 1 : ℕ) : ℝ) ≤ |C| * Real.sqrt (n : ℝ) := by
      calc
        _ ≤ C * Real.sqrt ((n - 1 : ℕ) : ℝ) := hC _
        _ ≤ |C| * Real.sqrt ((n - 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
        _ ≤ |C| * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C)
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    have hratio : |C| * Real.sqrt (n : ℝ) / (n : ℝ) =
        |C| / Real.sqrt (n : ℝ) := by
      field_simp [hsqrtpos.ne']
      rw [Real.sq_sqrt hnR.le]
    rw [← hratio, ← sub_div]
    apply (div_le_div_iff_of_pos_right hnR).2
    linarith
  have hge : (fun n : ℕ => Chebyshev.theta ((n - 1 : ℕ) : ℝ) / (n : ℝ)) ≤ᶠ[atTop]
      (fun n : ℕ => Chebyshev.psi ((n - 1 : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact (div_le_div_iff_of_pos_right hnR).2
      (Chebyshev.theta_le_psi ((n - 1 : ℕ) : ℝ))
  have hlow : Tendsto
      (fun n : ℕ => Chebyshev.psi ((n - 1 : ℕ) : ℝ) / (n : ℝ) -
        |C| / Real.sqrt (n : ℝ)) atTop (𝓝 (1 - 0)) := by
    simpa using hψ.sub hsmall
  have hupp : Tendsto
      (fun n : ℕ => Chebyshev.psi ((n - 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 (1 - 0)) := by
    simpa using hψ
  have hθ := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n : ℕ => Chebyshev.theta ((n - 1 : ℕ) : ℝ) / (n : ℝ))
    (g := fun n : ℕ => Chebyshev.psi ((n - 1 : ℕ) : ℝ) / (n : ℝ) -
      |C| / Real.sqrt (n : ℝ))
    (h := fun n : ℕ => Chebyshev.psi ((n - 1 : ℕ) : ℝ) / (n : ℝ))
    hlow hupp hle hge
  simpa using hθ

private theorem theta_dyadic_interval_eq (Y : ℕ) :
    (∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime, Real.log (p : ℝ)) =
      Chebyshev.theta ((2 * Y - 1 : ℕ) : ℝ) -
        Chebyshev.theta ((Y - 1 : ℕ) : ℝ) := by
  let S := (Finset.Ico Y (2 * Y)).filter Nat.Prime
  let U := Nat.primesLE (2 * Y - 1)
  let L := Nat.primesLE (Y - 1)
  have hset : S = U \ L := by
    ext p
    simp only [S, U, L, Finset.mem_filter, Finset.mem_Ico, Finset.mem_sdiff,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hY, h2Y⟩, hp⟩
      refine ⟨⟨by omega, hp⟩, ?_⟩
      intro h
      omega
    · rintro ⟨⟨h2Y, hp⟩, hnot⟩
      refine ⟨⟨?_, ?_⟩, hp⟩
      · by_contra h
        apply hnot
        exact ⟨by omega, hp⟩
      · have hp2 : 2 ≤ p := hp.two_le
        have hYpos : 0 < Y := by omega
        omega
  have hsub : L ⊆ U := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum := Finset.sum_sdiff (s₁ := L) (s₂ := U)
    (f := fun p : ℕ => Real.log (p : ℝ)) hsub
  have hdiff : (∑ p ∈ U \ L, Real.log (p : ℝ)) =
      (∑ p ∈ U, Real.log (p : ℝ)) - (∑ p ∈ L, Real.log (p : ℝ)) := by
    linarith
  have hU : Chebyshev.theta ((2 * Y - 1 : ℕ) : ℝ) =
      ∑ p ∈ U, Real.log (p : ℝ) := by
    simpa [U, Nat.floor_natCast] using
      (Chebyshev.theta_eq_sum_primesLE ((2 * Y - 1 : ℕ) : ℝ))
  have hL : Chebyshev.theta ((Y - 1 : ℕ) : ℝ) =
      ∑ p ∈ L, Real.log (p : ℝ) := by
    simpa [L, Nat.floor_natCast] using
      (Chebyshev.theta_eq_sum_primesLE ((Y - 1 : ℕ) : ℝ))
  calc
    _ = ∑ p ∈ S, Real.log (p : ℝ) := rfl
    _ = ∑ p ∈ U \ L, Real.log (p : ℝ) := by rw [hset]
    _ = (∑ p ∈ U, Real.log (p : ℝ)) - (∑ p ∈ L, Real.log (p : ℝ)) := hdiff
    _ = Chebyshev.theta ((2 * Y - 1 : ℕ) : ℝ) -
        Chebyshev.theta ((Y - 1 : ℕ) : ℝ) := by rw [← hU, ← hL]

private theorem theta_dyadic_interval_div_tendsto :
    Tendsto (fun Y : ℕ =>
      (∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime, Real.log (p : ℝ)) /
        (Y : ℝ)) atTop (𝓝 1) := by
  have hdouble : Tendsto (fun Y : ℕ => 2 * Y) atTop atTop :=
    Filter.tendsto_atTop_mono (f := fun Y : ℕ => Y) (g := fun Y => 2 * Y)
      (by intro Y; omega) tendsto_id
  have htop := theta_nat_sub_one_div_tendsto.comp hdouble
  have htop2 : Tendsto (fun Y : ℕ => 2 *
      (Chebyshev.theta ((2 * Y - 1 : ℕ) : ℝ) / ((2 * Y : ℕ) : ℝ)))
      atTop (𝓝 2) := by
    simpa using Filter.Tendsto.const_mul 2 htop
  have htop3 : Tendsto (fun Y : ℕ =>
      Chebyshev.theta ((2 * Y - 1 : ℕ) : ℝ) / (Y : ℝ)) atTop (𝓝 2) := by
    apply htop2.congr'
    filter_upwards [eventually_gt_atTop 0] with Y hY
    have hYR : (Y : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hY)
    push_cast
    field_simp [hYR]
  have hsub := htop3.sub theta_nat_sub_one_div_tendsto
  have heq : (fun Y : ℕ =>
      Chebyshev.theta ((2 * Y - 1 : ℕ) : ℝ) / (Y : ℝ) -
        Chebyshev.theta ((Y - 1 : ℕ) : ℝ) / (Y : ℝ)) =ᶠ[atTop]
      (fun Y : ℕ =>
        (∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime, Real.log (p : ℝ)) /
          (Y : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with Y hY
    rw [theta_dyadic_interval_eq]
    ring
  have hlim : (2 : ℝ) - 1 = 1 := by norm_num
  simpa only [hlim] using hsub.congr' heq

private theorem theta_dyadic_interval_eventually_bounds :
    ∀ᶠ Y : ℕ in atTop,
      (Y : ℝ) / 2 ≤
          (∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime, Real.log (p : ℝ)) ∧
        (∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime, Real.log (p : ℝ)) ≤
          2 * (Y : ℝ) := by
  have h := theta_dyadic_interval_div_tendsto.eventually
    (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with Y hlim hY
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  constructor
  · have hmul := (lt_div_iff₀ hYpos).mp hlim.1
    nlinarith
  · have hmul := (div_lt_iff₀ hYpos).mp hlim.2
    nlinarith

private theorem dyadic_harmonic_bounds_of_weighted
    (Y : ℕ) (hY : 2 ≤ Y)
    (hTlow : (Y : ℝ) / 2 ≤
      ∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime, Real.log (p : ℝ))
    (hThigh :
      ∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime, Real.log (p : ℝ) ≤
        2 * (Y : ℝ)) :
    (1 / 8 : ℝ) / Real.log Y ≤ primePoolMass Y (2 * Y) ∧
      primePoolMass Y (2 * Y) ≤ 8 / Real.log Y ∧
      ∀ p, Y ≤ p → p < 2 * Y → p.Prime →
        primePoolLaw Y (2 * Y) p ≤ 8 * Real.log Y / Y := by
  let S := (Finset.Ico Y (2 * Y)).filter Nat.Prime
  let T := ∑ p ∈ S, Real.log (p : ℝ)
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlog2Y : 0 < Real.log ((2 * Y : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * Y by omega))
  have hlog2le : Real.log 2 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hY)
  have hlog2bound : Real.log ((2 * Y : ℕ) : ℝ) ≤ 2 * Real.log (Y : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hden₁ : 0 < 2 * (Y : ℝ) * Real.log ((2 * Y : ℕ) : ℝ) := by positivity
  have hden₂ : 0 < (Y : ℝ) * Real.log (Y : ℝ) := by positivity
  have hpointLow : ∀ p ∈ S,
      Real.log (p : ℝ) / (2 * (Y : ℝ) * Real.log ((2 * Y : ℕ) : ℝ)) ≤
        1 / (p : ℝ) := by
    intro p hp
    have hpI := Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1
    have hpP := (Finset.mem_filter.mp hp).2
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpP.pos
    have hp2 : (p : ℝ) ≤ (2 * Y : ℕ) := by exact_mod_cast hpI.2.le
    have hlogp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hpP.one_lt)
    have hlogp2 : Real.log (p : ℝ) ≤ Real.log ((2 * Y : ℕ) : ℝ) :=
      Real.log_le_log hpPos hp2
    have hprod := mul_le_mul hp2 hlogp2 (le_of_lt hlogp) (by positivity)
    apply (div_le_div_iff₀ hden₁ hpPos).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  have hpointHigh : ∀ p ∈ S,
      1 / (p : ℝ) ≤ Real.log (p : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) := by
    intro p hp
    have hpI := Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1
    have hpP := (Finset.mem_filter.mp hp).2
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpP.pos
    have hYp : (Y : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpI.1
    have hlogp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hpP.one_lt)
    have hlogYp : Real.log (Y : ℝ) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < Y)) hYp
    have hprod := mul_le_mul hYp hlogYp (le_of_lt hlogY) (le_of_lt hpPos)
    apply (div_le_div_iff₀ hpPos hden₂).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  have hmassLowRaw : T / (2 * (Y : ℝ) * Real.log ((2 * Y : ℕ) : ℝ)) ≤
      primePoolMass Y (2 * Y) := by
    change (∑ p ∈ S, Real.log (p : ℝ)) /
        (2 * (Y : ℝ) * Real.log ((2 * Y : ℕ) : ℝ)) ≤ _
    calc
      _ = ∑ p ∈ S,
          Real.log (p : ℝ) / (2 * (Y : ℝ) * Real.log ((2 * Y : ℕ) : ℝ)) := by
            rw [Finset.sum_div]
      _ ≤ ∑ p ∈ S, 1 / (p : ℝ) := Finset.sum_le_sum hpointLow
      _ = primePoolMass Y (2 * Y) := rfl
  have hmassHighRaw : primePoolMass Y (2 * Y) ≤ T / ((Y : ℝ) * Real.log (Y : ℝ)) := by
    change _ ≤ (∑ p ∈ S, Real.log (p : ℝ)) / ((Y : ℝ) * Real.log (Y : ℝ))
    calc
      primePoolMass Y (2 * Y) = ∑ p ∈ S, 1 / (p : ℝ) := rfl
      _ ≤ ∑ p ∈ S, Real.log (p : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) :=
        Finset.sum_le_sum hpointHigh
      _ = _ := by rw [Finset.sum_div]
  have hlowratio : (1 / (8 * Real.log (Y : ℝ))) ≤
      ((Y : ℝ) / 2) / (2 * (Y : ℝ) * Real.log ((2 * Y : ℕ) : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) hden₁).2
    have hmul := mul_le_mul_of_nonneg_left hlog2bound (by positivity : 0 ≤ 2 * (Y : ℝ))
    nlinarith [hmul]
  have hTlowRatio : ((Y : ℝ) / 2) /
      (2 * (Y : ℝ) * Real.log ((2 * Y : ℕ) : ℝ)) ≤
        T / (2 * (Y : ℝ) * Real.log ((2 * Y : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_right hTlow (le_of_lt hden₁)
  have hmassLow : 1 / (8 * Real.log (Y : ℝ)) ≤ primePoolMass Y (2 * Y) :=
    hlowratio.trans (hTlowRatio.trans hmassLowRaw)
  have hmassHigh : primePoolMass Y (2 * Y) ≤ 2 / Real.log (Y : ℝ) := by
    calc
      _ ≤ T / ((Y : ℝ) * Real.log (Y : ℝ)) := hmassHighRaw
      _ ≤ (2 * (Y : ℝ)) / ((Y : ℝ) * Real.log (Y : ℝ)) :=
        div_le_div_of_nonneg_right hThigh (le_of_lt hden₂)
      _ = 2 / Real.log (Y : ℝ) := by field_simp [hYpos.ne', hlogY.ne']
  have hmassLow' : (1 / 8 : ℝ) / Real.log (Y : ℝ) ≤ primePoolMass Y (2 * Y) := by
    calc
      _ = 1 / (8 * Real.log (Y : ℝ)) := by field_simp [hlogY.ne']
      _ ≤ _ := hmassLow
  have hmassHigh' : primePoolMass Y (2 * Y) ≤ 8 / Real.log (Y : ℝ) :=
    hmassHigh.trans (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 8)
      (le_of_lt hlogY))
  refine ⟨hmassLow', hmassHigh', ?_⟩
  intro p hpY hp2 hpP
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpP.pos
  have hYp : (Y : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpY
  have hrecip : 1 / (p : ℝ) ≤ 1 / (Y : ℝ) :=
    (div_le_div_iff₀ hpPos hYpos).2 (by norm_num; linarith)
  have hmassPos : 0 < primePoolMass Y (2 * Y) :=
    lt_of_lt_of_le (by positivity) hmassLow
  have hscale : 1 / (Y : ℝ) ≤
      (8 * Real.log (Y : ℝ) / (Y : ℝ)) * primePoolMass Y (2 * Y) := by
    have hcoef : 0 ≤ 8 * Real.log (Y : ℝ) / (Y : ℝ) :=
      div_nonneg (by positivity : 0 ≤ 8 * Real.log (Y : ℝ)) (le_of_lt hYpos)
    have hmul := mul_le_mul_of_nonneg_left hmassLow hcoef
    have heq : (8 * Real.log (Y : ℝ) / (Y : ℝ)) *
        (1 / (8 * Real.log (Y : ℝ))) = 1 / (Y : ℝ) := by
      field_simp [hYpos.ne', hlogY.ne']
    rw [heq] at hmul
    exact hmul
  have hprob : (1 / (p : ℝ)) / primePoolMass Y (2 * Y) ≤
      8 * Real.log (Y : ℝ) / (Y : ℝ) := by
    apply (div_le_iff₀ hmassPos).2
    exact hrecip.trans hscale
  simpa [primePoolLaw, hpY, hp2, hpP] using hprob

/-- Prime number theorem in dyadic intervals, in the exact harmonic form used for
the maximum atom and positive pool mass in `lem:master-scales` and
`lem:rough-coprimality` (§3 lines 284–294, 373–377). -/
theorem dyadic_harmonic_prime_mass_and_atom_bound :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ Y : ℕ in atTop,
      c / Real.log Y ≤ primePoolMass Y (2 * Y) ∧
      primePoolMass Y (2 * Y) ≤ C / Real.log Y ∧
      ∀ p, Y ≤ p → p < 2 * Y → p.Prime →
        primePoolLaw Y (2 * Y) p ≤ C * Real.log Y / Y := by
  refine ⟨8, 1 / 8, by norm_num, by norm_num, ?_⟩
  filter_upwards [theta_dyadic_interval_eventually_bounds,
    eventually_ge_atTop (2 : ℕ)] with Y hT hY
  exact dyadic_harmonic_bounds_of_weighted Y hY hT.1 hT.2

/-- Selberg's prime number theorem in arithmetic progressions, equation (1.1),
followed by partial summation: the harmonic prime law on `[Y,2Y)` approaches
uniform measure on unit classes modulo every fixed Q. Used in `lem:master-scales`
(§3 lines 283–294). -/
theorem harmonic_prime_residue_equidistribution (Q : ℕ) (hQ : 0 < Q) :
    Tendsto (fun Y : ℕ => finiteL1
      (primePoolResidueLaw Y (2 * Y) Q)
      (uniformUnitResidueLaw Q)) atTop (𝓝 0) := by
  classical
  have hsum : Tendsto (fun Y : ℕ =>
      ∑ a : Fin Q,
        |primePoolResidueLaw Y (2 * Y) Q a - uniformUnitResidueLaw Q a|)
      atTop (𝓝 (∑ _a : Fin Q, (0 : ℝ))) := by
    apply tendsto_finsetSum Finset.univ
    intro a ha
    have hconst : Tendsto (fun _ : ℕ => uniformUnitResidueLaw Q a)
        atTop (𝓝 (uniformUnitResidueLaw Q a)) := tendsto_const_nhds
    have hdiff : Tendsto
        (fun Y : ℕ => primePoolResidueLaw Y (2 * Y) Q a - uniformUnitResidueLaw Q a)
        atTop (𝓝 0) := by
      simpa using (primePoolResidueLaw_tendsto Q hQ a).sub hconst
    simpa using hdiff.abs
  simpa [finiteL1] using hsum

/-- Interval Brun–Titchmarsh bound for the harmonic prime law on `[Y,2Y)`.
For a prime p with p²≤Y, every nonzero residue class has probability O(1/p).
This is Theorem 2 of Yamada, used in `lem:rough-coprimality` (§3 lines 379–389). -/
theorem harmonic_prime_brun_titchmarsh :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℕ in atTop,
      ∀ p, p.Prime → p ^ 2 ≤ Y → ∀ a : Fin p, 0 < a.val →
        (∑ q ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
          if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) ≤ C / p := by
  obtain ⟨Cmass, cmass, hCmass, hcmass, hmassEvent⟩ :=
    dyadic_harmonic_prime_mass_and_atom_bound
  obtain ⟨Cbt, B, hCbt, hB, hbt⟩ :=
    OAI.Erdos970.ErdosPrimeInputs.BrunTitchmarshUpper.brun_titchmarsh_upper
  have hsqrtEvent : ∀ᶠ Y : ℕ in atTop, B ≤ Real.sqrt (Y : ℝ) := by
    have htend : Tendsto (fun Y : ℕ => Real.sqrt (Y : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop B
  refine ⟨4 * Cbt * Cmass, by positivity, ?_⟩
  filter_upwards [hmassEvent, hsqrtEvent, eventually_ge_atTop (2 : ℕ)]
    with Y hmass hBsqrt hY
  intro p hp hpSq a ha
  have hpNat : 2 ≤ p := hp.two_le
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hYPos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hYLog : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hsqrtPos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYPos
  have hpSqR : (p : ℝ) ^ 2 ≤ (Y : ℝ) := by exact_mod_cast hpSq
  have hpSqrt : (p : ℝ) ≤ Real.sqrt (Y : ℝ) := Real.le_sqrt_of_sq_le hpSqR
  have hYp : Real.sqrt (Y : ℝ) ≤ (Y : ℝ) / p := by
    have hmul := mul_le_mul_of_nonneg_left hpSqrt (Real.sqrt_nonneg (Y : ℝ))
    have hsquare : Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) = Y := by
      nlinarith [Real.sq_sqrt (le_of_lt hYPos)]
    apply (le_div_iff₀ hpPos).2
    calc
      Real.sqrt (Y : ℝ) * p ≤
          Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) := hmul
      _ = Y := hsquare
  have hBHp : B ≤ (Y : ℝ) / p := hBsqrt.trans hYp
  have hLogSqrt : Real.log (Real.sqrt (Y : ℝ)) ≤ Real.log ((Y : ℝ) / p) :=
    Real.log_le_log hsqrtPos hYp
  have hLogSqrtEq : Real.log (Real.sqrt (Y : ℝ)) = Real.log (Y : ℝ) / 2 := by
    rw [Real.log_sqrt (le_of_lt hYPos)]
  have hLogHalf : Real.log (Y : ℝ) / 2 ≤ Real.log ((Y : ℝ) / p) := by
    simpa [hLogSqrtEq] using hLogSqrt
  have hLogRatio : Real.log (Y : ℝ) ≤ 2 * Real.log ((Y : ℝ) / p) := by
    linarith
  have hArgPos : 1 < (Y : ℝ) / p := lt_of_lt_of_le hB hBHp
  have hLogArg : 0 < Real.log ((Y : ℝ) / p) := Real.log_pos hArgPos
  have hPhiPos : 0 < (p.totient : ℝ) := by
    rw [Nat.totient_prime hp]
    exact_mod_cast (by omega : 0 < p - 1)
  have hPhiBound : (p : ℝ) ≤ 2 * (p.totient : ℝ) := by
    rw [Nat.totient_prime hp]
    exact_mod_cast (by omega : p ≤ 2 * (p - 1))
  have hNumBound : Real.log (Y : ℝ) * (p : ℝ) ≤
      4 * (p.totient : ℝ) * Real.log ((Y : ℝ) / p) := by
    calc
      _ ≤ (2 * Real.log ((Y : ℝ) / p)) * (2 * (p.totient : ℝ)) :=
        mul_le_mul hLogRatio hPhiBound (by positivity) (by positivity)
      _ = _ := by ring
  have hscaledBound : (Cbt * Cmass * Real.log (Y : ℝ)) /
        ((p.totient : ℝ) * Real.log ((Y : ℝ) / p)) ≤
      4 * Cbt * Cmass / (p : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hPhiPos hLogArg) hpPos).2
    calc
      (Cbt * Cmass * Real.log (Y : ℝ)) * (p : ℝ) =
          (Cbt * Cmass) * (Real.log (Y : ℝ) * (p : ℝ)) := by ring
      _ ≤ (Cbt * Cmass) *
          (4 * (p.totient : ℝ) * Real.log ((Y : ℝ) / p)) :=
        mul_le_mul_of_nonneg_left hNumBound (by positivity)
      _ = (4 * Cbt * Cmass) *
          ((p.totient : ℝ) * Real.log ((Y : ℝ) / p)) := by ring
  let S := (Finset.Ico Y (2 * Y)).filter Nat.Prime
  let T := S.filter (fun q => q % p = a.val)
  let U := OAI.Erdos970.ErdosPrimeInputs.BrunTitchmarshUpper.intervalPrimes
    ((Y - 1 : ℕ) : ℝ) (Y : ℝ) p (a.val : ℤ)
  have hTsub : T ⊆ U := by
    intro q hq
    have hqS := (Finset.mem_filter.mp hq).1
    have hqa := (Finset.mem_filter.mp hq).2
    have hqI := Finset.mem_Ico.mp (Finset.mem_filter.mp hqS).1
    have hqP := (Finset.mem_filter.mp hqS).2
    apply (OAI.Erdos970.ErdosPrimeInputs.BrunTitchmarshUpper.mem_intervalPrimes
      _ _ _ _ q).2
    refine ⟨hqP, ?_, ?_, ?_⟩
    · have h : Y - 1 < q := by omega
      exact_mod_cast h
    · have h : q ≤ (Y - 1) + Y := by omega
      exact_mod_cast h
    · change Int.ModEq (p : ℤ) (q : ℤ) (a.val : ℤ)
      apply Int.natCast_modEq_iff.mpr
      change q % p = a.val % p
      rw [Nat.mod_eq_of_lt a.isLt]
      exact hqa
  have hbtCard : (U.card : ℝ) ≤
      Cbt * (Y : ℝ) /
        ((p.totient : ℝ) * Real.log ((Y : ℝ) / p)) := by
    simpa [U] using hbt ((Y - 1 : ℕ) : ℝ) (Y : ℝ) p (a.val : ℤ)
      hp.pos hBHp
  have hTcard : (T.card : ℝ) ≤
      Cbt * (Y : ℝ) /
        ((p.totient : ℝ) * Real.log ((Y : ℝ) / p)) := by
    calc
      (T.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_le_card hTsub
      _ ≤ _ := hbtCard
  have hsumEq :
      (∑ q ∈ S, if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) =
        ∑ q ∈ T, primePoolLaw Y (2 * Y) q := by
    simp [S, T, Finset.sum_filter]
  have hsumBound :
      (∑ q ∈ T, primePoolLaw Y (2 * Y) q) ≤
        (T.card : ℝ) * (Cmass * Real.log (Y : ℝ) / Y) := by
    calc
      _ ≤ ∑ _q ∈ T, Cmass * Real.log (Y : ℝ) / Y :=
        Finset.sum_le_sum fun q hq => by
          have hqI := Finset.mem_Ico.mp (Finset.mem_filter.mp
            (Finset.mem_filter.mp hq).1).1
          have hqP := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
          exact hmass.2.2 q hqI.1 hqI.2 hqP
      _ = _ := by simp
  have hscaledCard :
      (T.card : ℝ) * (Cmass * Real.log (Y : ℝ) / Y) ≤
        (Cbt * (Y : ℝ) /
          ((p.totient : ℝ) * Real.log ((Y : ℝ) / p))) *
            (Cmass * Real.log (Y : ℝ) / Y) :=
    mul_le_mul_of_nonneg_right hTcard (by positivity)
  calc
    (∑ q ∈ S, if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) =
        ∑ q ∈ T, primePoolLaw Y (2 * Y) q := hsumEq
    _ ≤ (T.card : ℝ) * (Cmass * Real.log (Y : ℝ) / Y) := hsumBound
    _ ≤ _ := hscaledCard
    _ = (Cbt * Cmass * Real.log (Y : ℝ)) /
        ((p.totient : ℝ) * Real.log ((Y : ℝ) / p)) := by
      field_simp [hYPos.ne']
    _ ≤ 4 * Cbt * Cmass / (p : ℝ) := hscaledBound

/-- Divergence of the reciprocal-prime series, used to make the union of complete
dyadic intervals in each pool have arbitrary prescribed harmonic mass
(`lem:master-scales`, §3 line 291). -/
theorem reciprocalPrimeSeries_tendsto_atTop :
    Tendsto (fun Y : ℕ => ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, 1 / (p : ℝ))
      atTop atTop := by
  have hf : ∀ n : ℕ, 0 ≤
      Set.indicator {p : ℕ | p.Prime} (fun p => 1 / (p : ℝ)) n := by
    intro n
    by_cases hn : n.Prime <;> simp [hn]
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp
    not_summable_one_div_on_primes
  convert hdiv.comp (tendsto_add_atTop_nat 1) using 1 with Y
  ext Y
  simp [Finset.sum_filter, Set.indicator]

end
end HindmanSumsProducts.Arithmetic.Outside
