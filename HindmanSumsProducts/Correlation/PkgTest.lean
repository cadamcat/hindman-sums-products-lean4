import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.FromArithmetic

/-! Helper lemmas for the §4 proof package `Test` (owned by its proof lane). -/

namespace HindmanSumsProducts

theorem arithmeticL1_triangle_shift {α : Type*} (μ ν ρ : α → ℝ)
    (hμν : Summable fun x => |μ x - ν x|)
    (hνρ : Summable fun x => |ν x - ρ x|) :
    arithmeticL1 μ ρ ≤ arithmeticL1 μ ν + arithmeticL1 ν ρ := by
  unfold arithmeticL1
  have hsum : Summable fun x => |μ x - ν x| + |ν x - ρ x| := hμν.add hνρ
  have hμρ : Summable fun x => |μ x - ρ x| :=
    hsum.of_nonneg_of_le (fun x => abs_nonneg _) (fun x => abs_sub_le _ _ _)
  calc
    (∑' x, |μ x - ρ x|) ≤ ∑' x, (|μ x - ν x| + |ν x - ρ x|) := by
      exact hμρ.tsum_le_tsum (fun x => abs_sub_le _ _ _) hsum
    _ = (∑' x, |μ x - ν x|) + ∑' x, |ν x - ρ x| := by
      exact hμν.tsum_add hνρ

theorem arithmeticL1_translate_int (μ ν : ℤ → ℝ) (h : ℤ) :
    arithmeticL1 (translatedLaw μ h) (translatedLaw ν h) = arithmeticL1 μ ν := by
  unfold arithmeticL1 translatedLaw
  change (∑' z : ℤ, |μ (z - h) - ν (z - h)|) = ∑' z : ℤ, |μ z - ν z|
  let e : ℤ ≃ ℤ :=
    { toFun := fun z => z - h
      invFun := fun z => z + h
      left_inv := by intro z; dsimp; omega
      right_inv := by intro z; dsimp; omega }
  change (∑' z : ℤ, (fun z => |μ z - ν z|) (e z)) = _
  exact e.tsum_eq (fun z : ℤ => |μ z - ν z|)

private lemma harmonicLaw_support {X W : ℕ} {z : ℤ}
    (hz : harmonicLaw X W z ≠ 0) :
    0 ≤ z ∧ (X : ℤ) ≤ z ∧ z < (X ^ 2 : ℤ) := by
  unfold harmonicLaw at hz
  by_cases hc : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W
  · rcases hc with ⟨hz0, hX, htop, _⟩
    have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have hX' : (X : ℤ) ≤ (z.toNat : ℤ) := by exact_mod_cast hX
    have htop' : (z.toNat : ℤ) < (X ^ 2 : ℤ) := by exact_mod_cast htop
    exact ⟨hz0, by simpa [hcast] using hX', by simpa [hcast] using htop'⟩
  · simp [hc] at hz

private lemma harmonicLaw_nat_cast (X W n : ℕ) :
    harmonicLaw X W (n : ℤ) =
      if X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W then
        1 / ((n : ℝ) * harmonicNormalizer X W) else 0 := by
  simp [harmonicLaw]

private lemma harmonicLaw_nat_cast_zero_of_not {X W n : ℕ}
    (h : ¬ (X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W)) :
    harmonicLaw X W (n : ℤ) = 0 := by
  rw [harmonicLaw_nat_cast]
  simp only [if_neg h]

private lemma harmonicLaw_nat_cast_value {X W n : ℕ}
    (hlo : X ≤ n) (hhi : n < X ^ 2) (hcop : Nat.Coprime n W) :
    harmonicLaw X W (n : ℤ) = 1 / ((n : ℝ) * harmonicNormalizer X W) := by
  rw [harmonicLaw_nat_cast]
  have hcond : X ≤ n ∧ (n < X ^ 2 ∧ Nat.Coprime n W) := ⟨hlo, ⟨hhi, hcop⟩⟩
  simp only [if_pos hcond]

private noncomputable def correlationRootLowBoundary (X W k h : ℕ) : ℕ → ℝ :=
  fun n => if n ∈ Finset.Ico (X - h) X ∧ n % k = 0 ∧ Nat.Coprime n W then
    (k : ℝ) / ((n : ℝ) * harmonicNormalizer X W) else 0

private noncomputable def correlationRootHighBoundary (X W k h : ℕ) : ℕ → ℝ :=
  fun n => if n ∈ Finset.Ico (X ^ 2 - h) (X ^ 2) ∧ n % k = 0 ∧ Nat.Coprime n W then
    (k : ℝ) / ((n : ℝ) * harmonicNormalizer X W) else 0

theorem correlation_root_log_condition {X W : ℕ} (hW : 0 < W)
    (hX : 4 * W ≤ X) : (W : ℝ) / X < Real.log X := by
  have hW1 : 1 ≤ W := Nat.succ_le_iff.mpr hW
  have hX4 : 4 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hWover : (W : ℝ) / X ≤ 1 / 4 := by
    apply (div_le_iff₀ hXpos).2
    have hXcast : 4 * (W : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    nlinarith
  have hlog2 : (69 / 100 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog4 : 1 < Real.log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    nlinarith
  have hlogX : 1 < Real.log (X : ℝ) := by
    calc
      1 < Real.log (4 : ℝ) := hlog4
      _ ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hX4)
  exact lt_of_le_of_lt hWover (lt_trans (by norm_num : (1 / 4 : ℝ) < 1) hlogX)

theorem correlation_root_log_lower_one {X W : ℕ} (hW : 0 < W)
    (hX : 4 * W ≤ X) : 1 < Real.log X := by
  have hX4 : 4 ≤ X := by
    have hW1 : 1 ≤ W := Nat.succ_le_iff.mpr hW
    omega
  have hlog2 : (69 / 100 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog4 : 1 < Real.log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    nlinarith
  exact lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by exact_mod_cast hX4))

theorem correlationRoot_log_endpoint_low (X H h : ℕ) (hX4 : 4 ≤ X)
    (hh : h ≤ H) (hHX : 2 * H < X) :
    Real.log ((X : ℝ) / (X - h)) ≤ 2 * (H : ℝ) / X := by
  have hhX : h < X := by omega
  have hAposN : 0 < X - h := Nat.sub_pos_of_lt hhX
  have hAcast : ((X - h : ℕ) : ℝ) = (X : ℝ) - h := by
    rw [Nat.cast_sub (Nat.le_of_lt hhX)]
  have hApos : (0 : ℝ) < (X : ℝ) - h := by
    rw [← hAcast]
    exact_mod_cast hAposN
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXcast : (X : ℝ) / 2 ≤ (X : ℝ) - h := by
    have hhR : (h : ℝ) ≤ H := by exact_mod_cast hh
    have hHXr : 2 * (H : ℝ) < X := by exact_mod_cast hHX
    nlinarith
  have hratioPos : 0 < (X : ℝ) / ((X : ℝ) - h) := div_pos hXpos hApos
  have heq : (X : ℝ) / (X - h) - 1 = (h : ℝ) / (X - h) := by
    field_simp [ne_of_gt hApos]
    ring
  have hfrac : (h : ℝ) / ((X : ℝ) - h) ≤ 2 * (H : ℝ) / X := by
    have hhR : (h : ℝ) ≤ H := by exact_mod_cast hh
    have hXle : (X : ℝ) ≤ 2 * ((X : ℝ) - h) := by nlinarith [hXcast]
    rw [div_le_div_iff₀ hApos hXpos]
    have h1 : (h : ℝ) * X ≤ H * X := mul_le_mul_of_nonneg_right hhR hXpos.le
    have h2 : H * X ≤ H * (2 * ((X : ℝ) - h)) :=
      mul_le_mul_of_nonneg_left hXle (by positivity)
    nlinarith
  calc
    Real.log ((X : ℝ) / (X - h)) ≤ (X : ℝ) / (X - h) - 1 :=
      Real.log_le_sub_one_of_pos hratioPos
    _ = (h : ℝ) / (X - h) := heq
    _ ≤ 2 * (H : ℝ) / X := hfrac

theorem correlationRoot_log_endpoint_high (X H h : ℕ) (hX4 : 4 ≤ X)
    (hh : h ≤ H) (hHX : 2 * H < X) :
    Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h)) ≤ 2 * (H : ℝ) / X ^ 2 := by
  have hhX : h < X := by omega
  have hXsqLt : X < X ^ 2 := by nlinarith
  have hhSq : h < X ^ 2 := lt_trans hhX hXsqLt
  have hAposN : 0 < X ^ 2 - h := Nat.sub_pos_of_lt hhSq
  have hAcast : ((X ^ 2 - h : ℕ) : ℝ) = (X ^ 2 : ℝ) - h := by
    rw [Nat.cast_sub (Nat.le_of_lt hhSq), Nat.cast_pow]
  have hApos : (0 : ℝ) < (X ^ 2 : ℝ) - h := by
    rw [← hAcast]
    exact_mod_cast hAposN
  have hXsqPos : (0 : ℝ) < X ^ 2 := by positivity
  have hXcast : (X ^ 2 : ℝ) / 2 ≤ (X ^ 2 : ℝ) - h := by
    have hhR : (h : ℝ) ≤ H := by exact_mod_cast hh
    have hHXr : 2 * (H : ℝ) < X := by exact_mod_cast hHX
    have hX4r : (4 : ℝ) ≤ X := by exact_mod_cast hX4
    have hXsqGe : (X : ℝ) ≤ (X ^ 2 : ℝ) := by nlinarith [hX4r]
    have hhHalf : (h : ℝ) < X / 2 := by nlinarith
    nlinarith [hXsqGe, hhHalf]
  have hratioPos : 0 < (X ^ 2 : ℝ) / (X ^ 2 - h) := div_pos hXsqPos hApos
  have heq : (X ^ 2 : ℝ) / (X ^ 2 - h) - 1 = (h : ℝ) / (X ^ 2 - h) := by
    field_simp [ne_of_gt hApos]
    ring
  have hfrac : (h : ℝ) / (X ^ 2 - h) ≤ 2 * (H : ℝ) / X ^ 2 := by
    have hhR : (h : ℝ) ≤ H := by exact_mod_cast hh
    have hXle : (X ^ 2 : ℝ) ≤ 2 * ((X ^ 2 : ℝ) - h) := by nlinarith [hXcast]
    rw [div_le_div_iff₀ hApos hXsqPos]
    have h1 : (h : ℝ) * X ^ 2 ≤ H * X ^ 2 := mul_le_mul_of_nonneg_right hhR (by positivity)
    have h2 : H * X ^ 2 ≤ H * (2 * ((X ^ 2 : ℝ) - h)) :=
      mul_le_mul_of_nonneg_left hXle (by positivity)
    nlinarith
  calc
    Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h)) ≤ (X ^ 2 : ℝ) / (X ^ 2 - h) - 1 :=
      Real.log_le_sub_one_of_pos hratioPos
    _ = (h : ℝ) / (X ^ 2 - h) := heq
    _ ≤ 2 * (H : ℝ) / X ^ 2 := hfrac

private lemma periodicHarmonic_tsum_nat_interval (W k a A B : ℕ) :
    (∑' n : ℕ, if (A : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
        Nat.Coprime n W ∧ n % k = a then 1 / (n : ℝ) else 0) =
      ∑ n ∈ Finset.Ico A B,
        if Nat.Coprime n W ∧ n % k = a then 1 / (n : ℝ) else 0 := by
  classical
  have hz (n : ℕ) (hn : n ∉ Finset.Ico A B) :
      (if (A : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
        Nat.Coprime n W ∧ n % k = a then 1 / (n : ℝ) else 0) = 0 := by
    have hnot : ¬ (A ≤ n ∧ n < B) := by simpa [Finset.mem_Ico] using hn
    by_cases hA : A ≤ n
    · have hB : ¬ n < B := by
        intro hB
        exact hnot ⟨hA, hB⟩
      have hBcast : ¬ (n : ℝ) < (B : ℝ) := by
        intro hBreal
        exact hB (by exact_mod_cast hBreal)
      simp [hBcast]
    · have hAcast : ¬ (A : ℝ) ≤ (n : ℝ) := by
        intro hAreal
        exact hA (by exact_mod_cast hAreal)
      simp [hAcast]
  calc
    _ = ∑ n ∈ Finset.Ico A B,
          (if (A : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
            Nat.Coprime n W ∧ n % k = a then 1 / (n : ℝ) else 0) :=
      tsum_eq_sum (s := Finset.Ico A B) hz
    _ = ∑ n ∈ Finset.Ico A B,
          if Nat.Coprime n W ∧ n % k = a then 1 / (n : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      have hA : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1
      have hB : (n : ℝ) < B := by exact_mod_cast hn'.2
      simp [hA, hB]

private lemma sumBoundary_eq_factor (X W k A B : ℕ) (Z : ℝ)
    (hZ : 0 < Z) (hA : 0 < A) (hsub : Finset.Ico A B ⊆ Finset.Ico 0 (X ^ 2)) :
    (∑ n ∈ Finset.Ico 0 (X ^ 2),
      if n ∈ Finset.Ico A B ∧ n % k = 0 ∧ Nat.Coprime n W then
        (k : ℝ) / ((n : ℝ) * Z) else 0) =
      ((k : ℝ) / Z) * ∑ n ∈ Finset.Ico A B,
        if n % k = 0 ∧ Nat.Coprime n W then 1 / (n : ℝ) else 0 := by
  classical
  let p : ℕ → Prop := fun n => n % k = 0 ∧ Nat.Coprime n W
  have hfilter :
      (Finset.Ico 0 (X ^ 2)).filter (fun n => n ∈ Finset.Ico A B ∧ p n) =
        (Finset.Ico A B).filter p := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, ⟨hn, hp⟩⟩
      exact ⟨hn, hp⟩
    · rintro ⟨hn, hp⟩
      exact ⟨hsub hn, ⟨hn, hp⟩⟩
  have hsum :
      (∑ n ∈ Finset.Ico 0 (X ^ 2),
        if n ∈ Finset.Ico A B ∧ p n then (k : ℝ) / ((n : ℝ) * Z) else 0) =
        ∑ n ∈ Finset.Ico A B, if p n then (k : ℝ) / ((n : ℝ) * Z) else 0 := by
    rw [← Finset.sum_filter, hfilter, Finset.sum_filter]
  have hfactor (n : ℕ) (hn : n ∈ Finset.Ico A B) :
      (k : ℝ) / ((n : ℝ) * Z) = ((k : ℝ) / Z) * (1 / (n : ℝ)) := by
    have hnpos : 0 < (n : ℝ) := by
      have hn' := Finset.mem_Ico.mp hn
      have hnposN : 0 < n := by omega
      exact_mod_cast hnposN
    field_simp [ne_of_gt hZ, ne_of_gt hnpos]
  rw [hsum]
  calc
    (∑ n ∈ Finset.Ico A B, if p n then (k : ℝ) / ((n : ℝ) * Z) else 0) =
        ∑ n ∈ Finset.Ico A B, if p n then ((k : ℝ) / Z) * (1 / (n : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hp : p n <;> simp [hp, hfactor n hn]
    _ = ((k : ℝ) / Z) * ∑ n ∈ Finset.Ico A B,
        if p n then 1 / (n : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hp : p n <;> simp [hp]

private lemma sumBoundary_periodic_bound {X W k A B : ℕ} (Z : ℝ)
    (hZ : 0 < Z) (hA : 0 < A) (hAB : A < B)
    (hsub : Finset.Ico A B ⊆ Finset.Ico 0 (X ^ 2))
    (Samp : FromArithmetic.SamplingPointwiseBounds X W)
    (hcop : Nat.Coprime k W) (hk : 0 < k) :
    (∑ n ∈ Finset.Ico 0 (X ^ 2),
      if n ∈ Finset.Ico A B ∧ n % k = 0 ∧ Nat.Coprime n W then
        (k : ℝ) / ((n : ℝ) * Z) else 0) ≤
      ((k : ℝ) / Z) *
        ((Nat.totient W : ℝ) / W / k * Real.log ((B : ℝ) / A) +
          (Nat.totient W : ℝ) / A) := by
  have hper := Samp.periodic_harmonic k 0 (A : ℝ) (B : ℝ) hcop (by omega)
    (by exact_mod_cast hA) (by exact_mod_cast hAB)
  rw [periodicHarmonic_tsum_nat_interval W k 0 A B] at hper
  have hupper :
      (∑ n ∈ Finset.Ico A B,
        if Nat.Coprime n W ∧ n % k = 0 then 1 / (n : ℝ) else 0) ≤
          (Nat.totient W : ℝ) / W / k * Real.log ((B : ℝ) / A) +
            (Nat.totient W : ℝ) / A := by
    linarith [(abs_le.mp hper).2]
  calc
    _ = ((k : ℝ) / Z) * ∑ n ∈ Finset.Ico A B,
          if Nat.Coprime n W ∧ n % k = 0 then 1 / (n : ℝ) else 0 :=
      by simpa [and_comm] using sumBoundary_eq_factor X W k A B Z hZ hA hsub
    _ ≤ ((k : ℝ) / Z) *
          ((Nat.totient W : ℝ) / W / k * Real.log ((B : ℝ) / A) +
            (Nat.totient W : ℝ) / A) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [and_comm] using hupper

theorem dilatedLaw_support {X W k : ℕ} (hk : 0 < k) {z : ℤ}
    (hz : dilatedLaw (harmonicLaw X W) k z ≠ 0) :
    0 ≤ z ∧ ((k * X : ℕ) : ℤ) ≤ z ∧ z < ((k * X ^ 2 : ℕ) : ℤ) := by
  unfold dilatedLaw at hz
  by_cases hmod : z % (k : ℤ) = 0
  · have hzμ : harmonicLaw X W (z / (k : ℤ)) ≠ 0 := by
      intro hzero
      simp [hmod, hzero] at hz
    have hμ := harmonicLaw_support hzμ
    have hdiv : (k : ℤ) ∣ z := Int.dvd_iff_emod_eq_zero.mpr hmod
    have hzEq : z = z / (k : ℤ) * (k : ℤ) := (Int.ediv_mul_cancel hdiv).symm
    have hkI : (0 : ℤ) < k := by exact_mod_cast hk
    refine ⟨?_, ?_, ?_⟩
    · rw [hzEq]
      exact mul_nonneg hμ.1 (by positivity)
    · rw [hzEq]
      have ht := mul_le_mul_of_nonneg_right hμ.2.1 (le_of_lt hkI)
      simpa [Nat.cast_mul, mul_comm] using ht
    · rw [hzEq]
      have ht := mul_lt_mul_of_pos_right hμ.2.2 hkI
      simpa [Nat.cast_mul, Nat.cast_pow, mul_comm] using ht
  · simp [hmod] at hz

theorem dilationReference_support {X W k : ℕ} {z : ℤ}
    (hz : dilationReference (harmonicLaw X W) k z ≠ 0) :
    0 ≤ z ∧ (X : ℤ) ≤ z ∧ z < (X ^ 2 : ℤ) := by
  unfold dilationReference at hz
  by_cases hd : (k : ℤ) ∣ z
  · have hzμ : harmonicLaw X W z ≠ 0 := by
      intro hzero
      simp [hd, hzero] at hz
    exact harmonicLaw_support hzμ
  · simp [hd] at hz

theorem progressionReference_support {X W k : ℕ} {h z : ℤ}
    (hz : progressionReference (harmonicLaw X W) k h z ≠ 0) :
    0 ≤ z ∧ (X : ℤ) ≤ z ∧ z < (X ^ 2 : ℤ) := by
  unfold progressionReference at hz
  by_cases hd : (k : ℤ) ∣ z - h
  · have hzμ : harmonicLaw X W z ≠ 0 := by
      intro hzero
      simp [hd, hzero] at hz
    exact harmonicLaw_support hzμ
  · simp [hd] at hz

theorem translated_support {μ : ℤ → ℝ} {h B : ℤ} (hh : 0 ≤ h)
    (hs : ∀ z, μ z ≠ 0 → 0 ≤ z ∧ z < B) {z : ℤ}
    (hz : translatedLaw μ h z ≠ 0) : 0 ≤ z ∧ z < B + h := by
  have hμ : μ (z - h) ≠ 0 := by simpa [translatedLaw] using hz
  have hs' := hs (z - h) hμ
  constructor <;> omega

private lemma summable_abs_sub_Icc {f g : ℤ → ℝ} (B : ℤ)
    (hf : ∀ z, f z ≠ 0 → 0 ≤ z ∧ z ≤ B)
    (hg : ∀ z, g z ≠ 0 → 0 ≤ z ∧ z ≤ B) :
    Summable fun z => |f z - g z| := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 0 B)
  intro z hz
  have hzNot : ¬ (0 ≤ z ∧ z ≤ B) := by simpa [Finset.mem_Icc] using hz
  have hz' : z < 0 ∨ B < z := by
    by_cases hz0 : 0 ≤ z
    · right
      have hnotB : ¬ z ≤ B := by intro hB; exact hzNot ⟨hz0, hB⟩
      exact lt_of_not_ge hnotB
    · left
      omega
  have hfz : f z = 0 := by
    by_contra hne
    have hs := hf z hne
    omega
  have hgz : g z = 0 := by
    by_contra hne
    have hs := hg z hne
    omega
  simp [hfz, hgz]

theorem arithmeticL1_triangle_of_Icc_support {f g h : ℤ → ℝ} (B : ℤ)
    (hf : ∀ z, f z ≠ 0 → 0 ≤ z ∧ z ≤ B)
    (hg : ∀ z, g z ≠ 0 → 0 ≤ z ∧ z ≤ B)
    (hh : ∀ z, h z ≠ 0 → 0 ≤ z ∧ z ≤ B) :
    arithmeticL1 f h ≤ arithmeticL1 f g + arithmeticL1 g h := by
  exact arithmeticL1_triangle_shift f g h
    (summable_abs_sub_Icc B hf hg) (summable_abs_sub_Icc B hg hh)

private lemma sum_intIco_natCast (A B : ℕ) (f : ℤ → ℝ) :
    (∑ z ∈ Finset.Ico (A : ℤ) (B : ℤ), f z) =
      ∑ n ∈ Finset.Ico A B, f (n : ℤ) := by
  classical
  have hmap : (Finset.Ico A B).map Nat.castEmbedding = Finset.Ico (A : ℤ) (B : ℤ) := by
    simpa [Nat.ModEq, Int.ModEq, Nat.mod_one, Int.emod_one] using
      (Nat.Ico_filter_modEq_cast A B (r := 1) (v := 0))
  rw [← hmap]
  simp

private lemma tsum_intIco_natCast (A B : ℕ) (f : ℤ → ℝ)
    (hzero : ∀ z, z ∉ Finset.Ico (A : ℤ) (B : ℤ) → f z = 0) :
    (∑' z : ℤ, f z) = ∑ n ∈ Finset.Ico A B, f (n : ℤ) := by
  calc
    (∑' z : ℤ, f z) = ∑ z ∈ Finset.Ico (A : ℤ) (B : ℤ), f z :=
      tsum_eq_sum (s := Finset.Ico (A : ℤ) (B : ℤ)) hzero
    _ = ∑ n ∈ Finset.Ico A B, f (n : ℤ) := sum_intIco_natCast A B f

private lemma natCoprime_add_dvd {a b n : ℕ} (h : n ∣ b) :
    Nat.Coprime (a + b) n ↔ Nat.Coprime a n := by
  obtain ⟨c, rfl⟩ := h
  simpa [Nat.mul_comm] using Nat.coprime_add_mul_left_left a n c

private lemma int_unit_shift {W : ℕ} {h t : ℤ} (hh : 0 ≤ h)
    (hW : (W : ℤ) ∣ h) (ht : 0 ≤ t) :
    Nat.Coprime t.toNat W ↔ Nat.Coprime (t + h).toNat W := by
  have hcast : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh
  have hdiv' : (W : ℤ) ∣ (h.toNat : ℤ) := by simpa [hcast] using hW
  have hdivNat : W ∣ h.toNat := Int.natCast_dvd_natCast.mp hdiv'
  have hadd : (t + h).toNat = t.toNat + h.toNat := by
    have hc : ((t + h).toNat : ℤ) = ((t.toNat + h.toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ t + h), Int.natCast_add,
        Int.toNat_of_nonneg ht, Int.toNat_of_nonneg hh]
    exact_mod_cast hc
  rw [hadd]
  exact (natCoprime_add_dvd hdivNat).symm

private lemma arithmeticL1_reference_shift_sum (X W k H : ℕ) (h : ℤ)
    (h0 : 0 ≤ h) (hH : h ≤ H) (hHX : 2 * H < X) :
    arithmeticL1 (translatedLaw (dilationReference (harmonicLaw X W) k) h)
        (progressionReference (harmonicLaw X W) k h) =
      ∑ n ∈ Finset.Ico 0 (X ^ 2),
        |dilationReference (harmonicLaw X W) k (n : ℤ) -
          progressionReference (harmonicLaw X W) k h ((n : ℤ) + h)| := by
  let R : ℤ → ℝ := dilationReference (harmonicLaw X W) k
  let P : ℤ → ℝ := progressionReference (harmonicLaw X W) k h
  let e : ℤ ≃ ℤ :=
    { toFun := fun z => z + h
      invFun := fun z => z - h
      left_inv := by intro z; dsimp; omega
      right_inv := by intro z; dsimp; omega }
  have hshift : arithmeticL1 (translatedLaw R h) P =
      ∑' z : ℤ, |R z - P (z + h)| := by
    unfold arithmeticL1 translatedLaw
    change (∑' z : ℤ, |R (z - h) - P z|) = _
    rw [← e.tsum_eq (fun z : ℤ => |R (z - h) - P z|)]
    simp [e]
  have hRsupport (z : ℤ) (hz : R z ≠ 0) : 0 ≤ z ∧ z < (X ^ 2 : ℤ) := by
    have hs := dilationReference_support (by simpa [R] using hz)
    exact ⟨hs.1, hs.2.2⟩
  have hPsupport (z : ℤ) (hz : P (z + h) ≠ 0) :
      0 ≤ z ∧ z < (X ^ 2 : ℤ) := by
    have hs := progressionReference_support (by simpa [P] using hz)
    rcases hs with ⟨hs0, hsX, hsTop⟩
    constructor
    · omega
    · omega
  have hzero (z : ℤ) (hz : z ∉ Finset.Ico (0 : ℤ) (X ^ 2 : ℤ)) :
      |R z - P (z + h)| = 0 := by
    have hz' : z < 0 ∨ (X ^ 2 : ℤ) ≤ z := by
      by_cases hz0 : 0 ≤ z
      · right
        have hnot : ¬ z < (X ^ 2 : ℤ) := by
          intro hlt
          exact hz (Finset.mem_Ico.mpr ⟨hz0, hlt⟩)
        omega
      · left
        omega
    have hRzero : R z = 0 := by
      by_contra hr
      have hs := hRsupport z hr
      omega
    have hPzero : P (z + h) = 0 := by
      by_contra hp
      have hs := hPsupport z hp
      omega
    simp [hRzero, hPzero]
  rw [hshift, tsum_intIco_natCast 0 (X ^ 2) (fun z : ℤ => |R z - P (z + h)|) hzero]

private lemma correlationRoot_reference_summand_le
    (X W k H h : ℕ) (hX4 : 4 ≤ X) (hk : 0 < k)
    (hh : h ≤ H) (hHX : 2 * H < X)
    (hZ : 0 < harmonicNormalizer X W) (hdiv : W ∣ h)
    (n : ℕ) (hn : n ∈ Finset.Ico 0 (X ^ 2)) :
    |dilationReference (harmonicLaw X W) k (n : ℤ) -
        progressionReference (harmonicLaw X W) k (h : ℤ) ((n : ℤ) + h)| ≤
      (H : ℝ) / X * dilationReference (harmonicLaw X W) k (n : ℤ) +
        correlationRootLowBoundary X W k h n +
        correlationRootHighBoundary X W k h n := by
  classical
  have hR : dilationReference (harmonicLaw X W) k (n : ℤ) =
      if k ∣ n then (k : ℝ) * harmonicLaw X W (n : ℤ) else 0 := by
    simp [dilationReference, Int.natCast_dvd_natCast]
  have hP : progressionReference (harmonicLaw X W) k (h : ℤ) ((n : ℤ) + h) =
      if k ∣ n then (k : ℝ) * harmonicLaw X W ((n : ℤ) + h) else 0 := by
    simp [progressionReference, Int.natCast_dvd_natCast]
  have haddCast : ((n : ℤ) + (h : ℤ)) = ((n + h : ℕ) : ℤ) := by simp
  have hunitShift := natCoprime_add_dvd hdiv (a := n) (b := h) (n := W)
  have hmodOfDvd : k ∣ n → n % k = 0 := fun hd => Nat.dvd_iff_mod_eq_zero.mp hd
  have hmodNotOfNotDvd : ¬ k ∣ n → n % k ≠ 0 := by
    intro hd hmod
    exact hd (Nat.dvd_iff_mod_eq_zero.mpr hmod)
  rw [hR, hP]
  by_cases hkd : k ∣ n
  · have hmod : n % k = 0 := hmodOfDvd hkd
    simp only [if_pos hkd]
    by_cases hcop : Nat.Coprime n W
    · by_cases hnX : n < X
      · by_cases hplusX : n + h < X
        · have hμ0 : harmonicLaw X W (n : ℤ) = 0 :=
            harmonicLaw_nat_cast_zero_of_not (by
              intro hc
              exact (not_le_of_gt hnX) hc.1)
          have hμ1Nat : harmonicLaw X W ((n + h : ℕ) : ℤ) = 0 :=
            harmonicLaw_nat_cast_zero_of_not (by
              intro hc
              omega)
          have hμ1 : harmonicLaw X W ((n : ℤ) + h) = 0 := by
            rw [haddCast]
            exact hμ1Nat
          have hnotLow : n ∉ Finset.Ico (X - h) X := by
            simp only [Finset.mem_Ico]
            omega
          have hXhTop : X + h < X ^ 2 := by nlinarith
          have hhighLower : X ≤ X ^ 2 - h := by omega
          have hnotHigh : n ∉ Finset.Ico (X ^ 2 - h) (X ^ 2) := by
            intro hmem
            have hm := Finset.mem_Ico.mp hmem
            omega
          have hlowzero : correlationRootLowBoundary X W k h n = 0 := by
            simp [correlationRootLowBoundary, hnotLow]
          have hhighzero : correlationRootHighBoundary X W k h n = 0 := by
            simp [correlationRootHighBoundary, hnotHigh]
          rw [hμ0, hμ1, hlowzero, hhighzero]
          simp
        · have hplusX' : X ≤ n + h := by omega
          have hplusTop : n + h < X ^ 2 := by nlinarith
          have hlow : n ∈ Finset.Ico (X - h) X := by
            simp only [Finset.mem_Ico]
            omega
          have hμ0 : harmonicLaw X W (n : ℤ) = 0 :=
            harmonicLaw_nat_cast_zero_of_not (by
              intro hc
              exact (not_le_of_gt hnX) hc.1)
          have hplusCop : Nat.Coprime (n + h) W := (hunitShift).mpr hcop
          have hμ1Nat : harmonicLaw X W ((n + h : ℕ) : ℤ) =
              1 / ((n + h : ℝ) * harmonicNormalizer X W) := by
            simpa [Nat.cast_add] using
              harmonicLaw_nat_cast_value hplusX' hplusTop hplusCop
          have hμ1 : harmonicLaw X W ((n : ℤ) + h) =
              1 / ((n + h : ℝ) * harmonicNormalizer X W) := by
            rw [haddCast]
            exact hμ1Nat
          have hnpos : 0 < (n : ℝ) := by
            have hnposN : 0 < n := by omega
            exact_mod_cast hnposN
          have hden0 : 0 < (n : ℝ) * harmonicNormalizer X W := mul_pos hnpos hZ
          have hden1 : 0 < (n + h : ℝ) * harmonicNormalizer X W := by positivity
          have hdenLe : (n : ℝ) * harmonicNormalizer X W ≤
              (n + h : ℝ) * harmonicNormalizer X W := by
            apply mul_le_mul_of_nonneg_right _ hZ.le
            exact_mod_cast (show n ≤ n + h by omega)
          have hfrac : (k : ℝ) / ((n + h : ℝ) * harmonicNormalizer X W) ≤
              (k : ℝ) / ((n : ℝ) * harmonicNormalizer X W) := by
            rw [div_le_div_iff₀ hden1 hden0]
            exact mul_le_mul_of_nonneg_left hdenLe (by positivity)
          have hlowval : correlationRootLowBoundary X W k h n =
              (k : ℝ) / ((n : ℝ) * harmonicNormalizer X W) := by
            simp [correlationRootLowBoundary, hlow, hmod, hcop]
          have hhighval : correlationRootHighBoundary X W k h n = 0 := by
            have hnot : n ∉ Finset.Ico (X ^ 2 - h) (X ^ 2) := by
              simp only [Finset.mem_Ico]
              omega
            simp [correlationRootHighBoundary, hnot]
          rw [hμ0, hμ1, hlowval, hhighval]
          have hμ1nonneg : 0 ≤ (k : ℝ) *
              (1 / ((n + h : ℝ) * harmonicNormalizer X W)) := by positivity
          have hAbs : |(k : ℝ) * 0 - (k : ℝ) *
              (1 / ((n + h : ℝ) * harmonicNormalizer X W))| =
                (k : ℝ) / ((n + h : ℝ) * harmonicNormalizer X W) := by
            rw [show (k : ℝ) * 0 = 0 by ring, zero_sub, abs_neg,
              abs_of_nonneg hμ1nonneg]
            ring
          rw [hAbs]
          simpa using hfrac
      · have hnX' : X ≤ n := by omega
        by_cases hplusTop : n + h < X ^ 2
        · have hμ0 : harmonicLaw X W (n : ℤ) =
              1 / ((n : ℝ) * harmonicNormalizer X W) :=
            harmonicLaw_nat_cast_value hnX' (Finset.mem_Ico.mp hn).2 hcop
          have hμ1Nat : harmonicLaw X W ((n + h : ℕ) : ℤ) =
              1 / ((n + h : ℝ) * harmonicNormalizer X W) := by
            have hplusCop : Nat.Coprime (n + h) W := (hunitShift).mpr hcop
            simpa [Nat.cast_add] using
              harmonicLaw_nat_cast_value (by omega) hplusTop hplusCop
          have hμ1 : harmonicLaw X W ((n : ℤ) + h) =
              1 / ((n + h : ℝ) * harmonicNormalizer X W) := by
            rw [haddCast]
            exact hμ1Nat
          have hnpos : 0 < (n : ℝ) := by
            have hnposN : 0 < n := by omega
            exact_mod_cast hnposN
          have hden0 : 0 < (n : ℝ) * harmonicNormalizer X W := mul_pos hnpos hZ
          have hplusPos : 0 < n + h := by omega
          have hden1 : 0 < (n + h : ℝ) * harmonicNormalizer X W := by
            exact mul_pos (by exact_mod_cast hplusPos) hZ
          have hdenLe : (n : ℝ) * harmonicNormalizer X W ≤
              (n + h : ℝ) * harmonicNormalizer X W := by
            apply mul_le_mul_of_nonneg_right _ hZ.le
            exact_mod_cast (show n ≤ n + h by omega)
          have hdiff : (1 / ((n + h : ℝ) * harmonicNormalizer X W)) ≤
              (1 / ((n : ℝ) * harmonicNormalizer X W)) := by
            rw [div_le_div_iff₀ hden1 hden0]
            nlinarith [hdenLe]
          have hratio : (h : ℝ) / (n + h : ℝ) ≤ (H : ℝ) / X := by
            have hXle : (X : ℝ) ≤ (n + h : ℝ) := by exact_mod_cast (show X ≤ n + h by omega)
            have hhR : (h : ℝ) ≤ H := by exact_mod_cast hh
            rw [div_le_div_iff₀ (by positivity : 0 < (n + h : ℝ)) (by positivity : (0 : ℝ) < X)]
            nlinarith [mul_le_mul hhR hXle (by positivity : (0 : ℝ) ≤ (X : ℝ))
              (by positivity : (0 : ℝ) ≤ (H : ℝ))]
          have hidentity :
                1 / ((n : ℝ) * harmonicNormalizer X W) -
                1 / ((n + h : ℝ) * harmonicNormalizer X W) =
                (1 / ((n : ℝ) * harmonicNormalizer X W)) * ((h : ℝ) / (n + h : ℝ)) := by
            field_simp
            ring
          have hcommon :
              |(k : ℝ) * (1 / ((n : ℝ) * harmonicNormalizer X W)) -
                (k : ℝ) * (1 / ((n + h : ℝ) * harmonicNormalizer X W))| ≤
              (H : ℝ) / X * ((k : ℝ) *
                (1 / ((n : ℝ) * harmonicNormalizer X W))) := by
            have hnonneg : 0 ≤ (k : ℝ) *
                (1 / ((n : ℝ) * harmonicNormalizer X W) -
                  1 / ((n + h : ℝ) * harmonicNormalizer X W)) :=
              mul_nonneg (by positivity) (sub_nonneg.mpr hdiff)
            calc
              |(k : ℝ) * (1 / ((n : ℝ) * harmonicNormalizer X W)) -
                  (k : ℝ) * (1 / ((n + h : ℝ) * harmonicNormalizer X W))|
                  = (k : ℝ) *
                    (1 / ((n : ℝ) * harmonicNormalizer X W) -
                      1 / ((n + h : ℝ) * harmonicNormalizer X W)) := by
                    rw [← mul_sub, abs_of_nonneg hnonneg]
              _ = (k : ℝ) * (1 / ((n : ℝ) * harmonicNormalizer X W)) *
                    ((h : ℝ) / (n + h : ℝ)) := by rw [hidentity]; ring
              _ ≤ (k : ℝ) * (1 / ((n : ℝ) * harmonicNormalizer X W)) *
                    ((H : ℝ) / X) :=
                    mul_le_mul_of_nonneg_left hratio (by positivity)
              _ = (H : ℝ) / X * ((k : ℝ) *
                    (1 / ((n : ℝ) * harmonicNormalizer X W))) := by ring
          have hlowval : correlationRootLowBoundary X W k h n = 0 := by
            have hnot : n ∉ Finset.Ico (X - h) X := by
              simp only [Finset.mem_Ico]
              omega
            simp [correlationRootLowBoundary, hnot]
          have hhighval : correlationRootHighBoundary X W k h n = 0 := by
            have hnot : n ∉ Finset.Ico (X ^ 2 - h) (X ^ 2) := by
              by_contra hmem
              simp only [Finset.mem_Ico] at hmem
              omega
            simp [correlationRootHighBoundary, hnot]
          rw [hμ0, hμ1, hlowval, hhighval]
          simpa using hcommon
        · have hhigh : n ∈ Finset.Ico (X ^ 2 - h) (X ^ 2) := by
            simp only [Finset.mem_Ico]
            constructor
            · omega
            · exact (Finset.mem_Ico.mp hn).2
          have hnTop : n < X ^ 2 := (Finset.mem_Ico.mp hn).2
          have hμ0 : harmonicLaw X W (n : ℤ) =
              1 / ((n : ℝ) * harmonicNormalizer X W) :=
            harmonicLaw_nat_cast_value hnX' hnTop hcop
          have hμ1Nat : harmonicLaw X W ((n + h : ℕ) : ℤ) = 0 :=
            harmonicLaw_nat_cast_zero_of_not (by
              intro hc
              omega)
          have hμ1 : harmonicLaw X W ((n : ℤ) + h) = 0 := by
            rw [haddCast]
            exact hμ1Nat
          have hhighval : correlationRootHighBoundary X W k h n =
              (k : ℝ) / ((n : ℝ) * harmonicNormalizer X W) := by
            simp [correlationRootHighBoundary, hhigh, hmod, hcop]
          have hlowval : correlationRootLowBoundary X W k h n = 0 := by
            have hnot : n ∉ Finset.Ico (X - h) X := by
              simp only [Finset.mem_Ico]
              omega
            simp [correlationRootLowBoundary, hnot]
          rw [hμ0, hμ1, hlowval, hhighval]
          have hμ0nonneg : 0 ≤ (k : ℝ) *
              (1 / ((n : ℝ) * harmonicNormalizer X W)) := by positivity
          have hAbs : |(k : ℝ) * (1 / ((n : ℝ) * harmonicNormalizer X W)) -
              (k : ℝ) * 0| = (k : ℝ) / ((n : ℝ) * harmonicNormalizer X W) := by
            rw [show (k : ℝ) * 0 = 0 by ring, sub_zero,
              abs_of_nonneg hμ0nonneg]
            ring
          have hmul : (k : ℝ) *
              (1 / ((n : ℝ) * harmonicNormalizer X W)) =
                (k : ℝ) / ((n : ℝ) * harmonicNormalizer X W) := by
            rw [div_eq_mul_inv]
            ring
          rw [hAbs, hmul]
          have hterm : 0 ≤ (H : ℝ) / X *
              ((k : ℝ) / ((n : ℝ) * harmonicNormalizer X W)) := by positivity
          nlinarith [hterm]
    · have hcopPlus : ¬ Nat.Coprime (n + h) W := by
        intro hp
        exact hcop ((natCoprime_add_dvd hdiv).mp hp)
      have hμ0 : harmonicLaw X W (n : ℤ) = 0 :=
        harmonicLaw_nat_cast_zero_of_not (by
          intro hc
          exact hcop hc.2.2)
      have hμ1Nat : harmonicLaw X W ((n + h : ℕ) : ℤ) = 0 :=
        harmonicLaw_nat_cast_zero_of_not (by
          intro hc
          exact hcopPlus hc.2.2)
      have hμ1 : harmonicLaw X W ((n : ℤ) + h) = 0 := by
        rw [haddCast]
        exact hμ1Nat
      have hlowzero : correlationRootLowBoundary X W k h n = 0 := by
        simp [correlationRootLowBoundary, hcop]
      have hhighzero : correlationRootHighBoundary X W k h n = 0 := by
        simp [correlationRootHighBoundary, hcop]
      rw [hμ0, hμ1, hlowzero, hhighzero]
      norm_num
  · have hmod : n % k ≠ 0 := hmodNotOfNotDvd hkd
    simp [hkd, hmod, correlationRootLowBoundary, correlationRootHighBoundary]

theorem correlationRoot_reference_shift_bound
    (X W k H : ℕ) (h : ℤ) (hW : 0 < W) (hX : 4 * W ≤ X)
    (hk : 0 < k) (hkX : k ≤ X) (hcop : Nat.Coprime k W)
    (h0 : 0 ≤ h) (hH : h ≤ H) (hdiv : (W : ℤ) ∣ h) (hHX : 2 * H < X) :
    (((Nat.totient W : ℝ) / W) * (Real.log X - (W : ℝ) / X) ≤ harmonicNormalizer X W) ∧
    arithmeticL1 (translatedLaw (dilationReference (harmonicLaw X W) k) h)
        (progressionReference (harmonicLaw X W) k h) ≤
      (H : ℝ) / X * (1 + FromArithmetic.harmonicResidueError X W k) +
        ((k : ℝ) / harmonicNormalizer X W) *
          ((Nat.totient W : ℝ) / W / k *
              Real.log ((X : ℝ) / (X - h.toNat)) +
            (Nat.totient W : ℝ) / (X - h.toNat)) +
        ((k : ℝ) / harmonicNormalizer X W) *
          ((Nat.totient W : ℝ) / W / k *
              Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat)) +
            (Nat.totient W : ℝ) / (X ^ 2 - h.toNat)) := by
  have hlog := correlation_root_log_condition hW hX
  have hX2 : 2 ≤ X := by omega
  have hD : 0 < Real.log X - (W : ℝ) / X := sub_pos.mpr hlog
  have hδ : 0 < (Nat.totient W : ℝ) / W := by
    exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
  have hsample := FromArithmetic.sampling_pointwise_claim X W hW hX2 hlog
  have hnorm := hsample.normalizer hX2 hlog
  have hZlower : ((Nat.totient W : ℝ) / W) *
      (Real.log X - (W : ℝ) / X) ≤ harmonicNormalizer X W := by
    have hbound := (abs_le.mp hnorm).1
    have heq : ((Nat.totient W : ℝ) / W) *
        (Real.log X - (W : ℝ) / X) =
          (Nat.totient W : ℝ) / W * Real.log X - (Nat.totient W : ℝ) / X := by
      have hWne : (W : ℝ) ≠ 0 := by positivity
      have hXne : (X : ℝ) ≠ 0 := by positivity
      field_simp [hWne, hXne]
    rw [heq]
    linarith
  have hZ : 0 < harmonicNormalizer X W := lt_of_lt_of_le (mul_pos hδ hD) hZlower
  have hNatCast : (h.toNat : ℤ) = h := Int.toNat_of_nonneg h0
  have hNatHInt : (h.toNat : ℤ) ≤ H := by rw [hNatCast]; exact hH
  have hNatH : h.toNat ≤ H := by exact_mod_cast hNatHInt
  have hWNatInt : (W : ℤ) ∣ (h.toNat : ℤ) := by rw [hNatCast]; exact hdiv
  have hWNat : W ∣ h.toNat := Int.natCast_dvd_natCast.mp hWNatInt
  have hX4 : 4 ≤ X := by
    have hW1 : 1 ≤ W := Nat.succ_le_iff.mpr hW
    omega
  refine ⟨hZlower, ?_⟩
  by_cases hzero : h.toNat = 0
  · have hhzero : h = 0 := by
      have hcast := hNatCast
      rw [hzero] at hcast
      exact hcast.symm
    subst h
    have heq : translatedLaw (dilationReference (harmonicLaw X W) k) 0 =
        dilationReference (harmonicLaw X W) k := by funext z; simp [translatedLaw]
    have hprog : progressionReference (harmonicLaw X W) k 0 =
        dilationReference (harmonicLaw X W) k := by
      funext z
      simp [progressionReference, dilationReference]
    rw [heq, hprog]
    unfold arithmeticL1
    simp
    have hE : 0 ≤ FromArithmetic.harmonicResidueError X W k := by
      unfold FromArithmetic.harmonicResidueError
      positivity
    positivity
  · have hNatPos : 0 < h.toNat := Nat.pos_of_ne_zero hzero
    have hNatLtX : h.toNat < X := by omega
    have hA0pos : 0 < X - h.toNat := Nat.sub_pos_of_lt hNatLtX
    have hA0lt : X - h.toNat < X := Nat.sub_lt_self hNatPos (Nat.le_of_lt hNatLtX)
    have hA0cast : ((X - h.toNat : ℕ) : ℝ) = (X : ℝ) - h.toNat := by
      rw [Nat.cast_sub (Nat.le_of_lt hNatLtX)]
    have hXsq : X < X ^ 2 := by nlinarith
    have hNatLtSq : h.toNat < X ^ 2 := lt_trans hNatLtX hXsq
    have hA1pos : 0 < X ^ 2 - h.toNat := Nat.sub_pos_of_lt hNatLtSq
    have hA1lt : X ^ 2 - h.toNat < X ^ 2 :=
      Nat.sub_lt_self hNatPos (Nat.le_of_lt hNatLtSq)
    have hA1cast : ((X ^ 2 - h.toNat : ℕ) : ℝ) = (X ^ 2 : ℝ) - h.toNat := by
      rw [Nat.cast_sub (Nat.le_of_lt hNatLtSq), Nat.cast_pow]
    have hsub0 : Finset.Ico (X - h.toNat) X ⊆ Finset.Ico 0 (X ^ 2) := by
      intro n hn
      simp only [Finset.mem_Ico] at hn ⊢
      omega
    have hsub1 : Finset.Ico (X ^ 2 - h.toNat) (X ^ 2) ⊆
        Finset.Ico 0 (X ^ 2) := by
      intro n hn
      simp only [Finset.mem_Ico] at hn ⊢
      omega
    let R : ℤ → ℝ := dilationReference (harmonicLaw X W) k
    have hmassEq : (∑' z : ℤ, R z) =
        ∑ n ∈ Finset.Ico 0 (X ^ 2), R (n : ℤ) := by
      apply tsum_intIco_natCast 0 (X ^ 2)
      intro z hz
      have hz' : z < 0 ∨ (X ^ 2 : ℤ) ≤ z := by
        by_cases hz0 : 0 ≤ z
        · right
          have hnot : ¬ z < (X ^ 2 : ℤ) := by
            intro hlt
            exact hz (Finset.mem_Ico.mpr ⟨hz0, hlt⟩)
          omega
        · left
          omega
      by_contra hRz
      have hs := dilationReference_support (by simpa [R] using hRz)
      rcases hz' with hzneg | hzupper <;> omega
    have hdil := hsample.dilation hX2 hlog k (by omega) hkX hcop
    have hmassErr := hdil.2
    have hmassR : (∑' z : ℤ, R z) ≤ 1 + FromArithmetic.harmonicResidueError X W k := by
      have hupper := (abs_le.mp (by simpa [R] using hmassErr)).2
      linarith
    have hshiftEq := arithmeticL1_reference_shift_sum X W k H h h0 hH hHX
    have hpoint (n : ℕ) (hn : n ∈ Finset.Ico 0 (X ^ 2)) :=
      correlationRoot_reference_summand_le X W k H h.toNat hX4 hk hNatH hHX hZ
        hWNat n hn
    have hsum : arithmeticL1 (translatedLaw R h)
        (progressionReference (harmonicLaw X W) k h) ≤
        (H : ℝ) / X * (∑ n ∈ Finset.Ico 0 (X ^ 2), R (n : ℤ)) +
          (∑ n ∈ Finset.Ico 0 (X ^ 2), correlationRootLowBoundary X W k h.toNat
            n) +
          ∑ n ∈ Finset.Ico 0 (X ^ 2), correlationRootHighBoundary X W k h.toNat
            n := by
      have hshiftEq' : arithmeticL1 (translatedLaw R h)
          (progressionReference (harmonicLaw X W) k h) =
          ∑ n ∈ Finset.Ico 0 (X ^ 2),
            |R (n : ℤ) - progressionReference (harmonicLaw X W) k h ((n : ℤ) + h)| := by
        simpa [R] using hshiftEq
      rw [hshiftEq']
      calc
        _ ≤ ∑ n ∈ Finset.Ico 0 (X ^ 2),
              ((H : ℝ) / X * R (n : ℤ) +
                correlationRootLowBoundary X W k h.toNat n +
                correlationRootHighBoundary X W k h.toNat n) :=
          Finset.sum_le_sum fun n hn => by simpa [R, hNatCast] using hpoint n hn
        _ = (H : ℝ) / X * (∑ n ∈ Finset.Ico 0 (X ^ 2), R (n : ℤ)) +
              (∑ n ∈ Finset.Ico 0 (X ^ 2), correlationRootLowBoundary X W k h.toNat n) +
              ∑ n ∈ Finset.Ico 0 (X ^ 2), correlationRootHighBoundary X W k h.toNat n := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.mul_sum]
    have hlow := sumBoundary_periodic_bound (X := X) (W := W) (k := k)
      (A := X - h.toNat) (B := X)
      (harmonicNormalizer X W) hZ hA0pos hA0lt hsub0 hsample hcop hk
    have hhigh := sumBoundary_periodic_bound (X := X) (W := W) (k := k)
      (A := X ^ 2 - h.toNat) (B := X ^ 2)
      (harmonicNormalizer X W) hZ hA1pos hA1lt hsub1 hsample hcop hk
    have hlow' :
        (∑ n ∈ Finset.Ico 0 (X ^ 2), correlationRootLowBoundary X W k h.toNat n) ≤
          ((k : ℝ) / harmonicNormalizer X W) *
            ((Nat.totient W : ℝ) / W / k *
                Real.log ((X : ℝ) / (X - h.toNat)) +
              (Nat.totient W : ℝ) / (X - h.toNat)) := by
      simpa [correlationRootLowBoundary, hA0cast] using hlow
    have hhigh' :
        (∑ n ∈ Finset.Ico 0 (X ^ 2), correlationRootHighBoundary X W k h.toNat n) ≤
          ((k : ℝ) / harmonicNormalizer X W) *
            ((Nat.totient W : ℝ) / W / k *
                Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat)) +
              (Nat.totient W : ℝ) / (X ^ 2 - h.toNat)) := by
      simpa [correlationRootHighBoundary, hA1cast] using hhigh
    have hmassCoeff : 0 ≤ (H : ℝ) / X := by positivity
    have hmassScaled : (H : ℝ) / X * (∑' z : ℤ, R z) ≤
        (H : ℝ) / X * (1 + FromArithmetic.harmonicResidueError X W k) :=
      mul_le_mul_of_nonneg_left hmassR hmassCoeff
    calc
      arithmeticL1 (translatedLaw R h)
          (progressionReference (harmonicLaw X W) k h) ≤ _ := hsum
      _ = (H : ℝ) / X * (∑' z : ℤ, R z) +
          (∑ n ∈ Finset.Ico 0 (X ^ 2), correlationRootLowBoundary X W k h.toNat n) +
          ∑ n ∈ Finset.Ico 0 (X ^ 2), correlationRootHighBoundary X W k h.toNat n := by
        rw [← hmassEq]
      _ ≤ (H : ℝ) / X * (1 + FromArithmetic.harmonicResidueError X W k) +
          ((k : ℝ) / harmonicNormalizer X W) *
            ((Nat.totient W : ℝ) / W / k *
                Real.log ((X : ℝ) / (X - h.toNat)) +
              (Nat.totient W : ℝ) / (X - h.toNat)) +
          ((k : ℝ) / harmonicNormalizer X W) *
            ((Nat.totient W : ℝ) / W / k *
                Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat)) +
              (Nat.totient W : ℝ) / (X ^ 2 - h.toNat)) := by
        exact add_le_add (add_le_add hmassScaled hlow') hhigh'

set_option maxHeartbeats 0 in
theorem correlationRoot_reference_shift_numeric_bound
    (X W k H : ℕ) (h : ℤ) (hW : 0 < W) (hX : 4 * W ≤ X)
    (hk : 0 < k) (hkX : k ≤ X) (hcop : Nat.Coprime k W)
    (h0 : 0 ≤ h) (hH : h ≤ H) (hdiv : (W : ℤ) ∣ h) (hHX : 2 * H < X) :
    arithmeticL1 (translatedLaw (dilationReference (harmonicLaw X W) k) h)
        (progressionReference (harmonicLaw X W) k h) ≤
      7 * (H : ℝ) / X + 7 * (W : ℝ) * k / (X * Real.log X) := by
  have hlog := correlation_root_log_condition hW hX
  have hLone := correlation_root_log_lower_one hW hX
  have hX4 : 4 ≤ X := by
    have hW1 : 1 ≤ W := Nat.succ_le_iff.mpr hW
    omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hWover : (W : ℝ) / X ≤ 1 / 4 := by
    apply (div_le_iff₀ hXpos).2
    have hXcast : 4 * (W : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  let L : ℝ := Real.log X
  let D : ℝ := Real.log X - (W : ℝ) / X
  have hDpos : 0 < D := sub_pos.mpr hlog
  have hDlower : (3 / 4 : ℝ) * L ≤ D := by
    dsimp [D, L]
    nlinarith [hWover, hLone]
  have hDinv : 1 / D ≤ 4 / (3 * L) := by
    have hden : 0 < (3 : ℝ) * L := by positivity
    rw [div_le_div_iff₀ hDpos hden]
    dsimp [D, L]
    nlinarith [hDlower]
  have hDinvConst : 1 / D ≤ 4 / 3 := by
    have hLpos : 0 < L := by dsimp [L]; linarith
    have hInvL : 1 / L ≤ 1 := by
      rw [div_le_iff₀ hLpos]
      linarith [hLone]
    calc
      1 / D ≤ 4 / (3 * L) := hDinv
      _ = (4 / 3) * (1 / L) := by field_simp <;> ring
      _ ≤ (4 / 3 : ℝ) := by
        calc
          (4 / 3 : ℝ) * (1 / L) ≤ (4 / 3 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hInvL (by positivity)
          _ = 4 / 3 := by ring
  have hRef := correlationRoot_reference_shift_bound X W k H h hW hX hk hkX hcop
    h0 hH hdiv hHX
  rcases hRef with ⟨hZlower, hRefBound⟩
  have hHXr : 2 * (H : ℝ) < X := by exact_mod_cast hHX
  have hZ : 0 < harmonicNormalizer X W := by
    have hδ : 0 < (Nat.totient W : ℝ) / (W : ℝ) := by
      apply div_pos
      · exact_mod_cast (Nat.totient_pos.mpr hW)
      · exact_mod_cast hW
    exact lt_of_lt_of_le (mul_pos hδ hDpos) hZlower
  have hZlowerD : (Nat.totient W : ℝ) / W * D ≤ harmonicNormalizer X W := by
    dsimp [D]
    exact hZlower
  have hδZ : (Nat.totient W : ℝ) / W / harmonicNormalizer X W ≤ 1 / D := by
    rw [div_le_div_iff₀ hZ hDpos]
    simpa using hZlowerD
  have hphiD : (Nat.totient W : ℝ) * D ≤ (W : ℝ) * harmonicNormalizer X W := by
    have hWmul := mul_le_mul_of_nonneg_left hZlowerD (by positivity : (0 : ℝ) ≤ W)
    have heq : (W : ℝ) * ((Nat.totient W : ℝ) / W * D) =
        (Nat.totient W : ℝ) * D := by
      field_simp [ne_of_gt (show (0 : ℝ) < W by exact_mod_cast hW)] <;> ring
    rw [heq] at hWmul
    exact hWmul
  have hphiZ : (Nat.totient W : ℝ) / harmonicNormalizer X W ≤ (W : ℝ) / D := by
    rw [div_le_div_iff₀ hZ hDpos]
    exact hphiD
  have hden : 0 < (X : ℝ) * D := mul_pos hXpos hDpos
  have hEupper : FromArithmetic.harmonicResidueError X W k ≤
      2 * (W : ℝ) * k / ((X : ℝ) * D) := by
    have hkplus : k + 1 ≤ 2 * k := by omega
    have hkplusR : (k + 1 : ℝ) ≤ 2 * k := by exact_mod_cast hkplus
    have hnum : (W : ℝ) * (k + 1 : ℝ) ≤ 2 * (W : ℝ) * k := by
      have hh := mul_le_mul_of_nonneg_left hkplusR (by positivity : (0 : ℝ) ≤ W)
      nlinarith
    unfold FromArithmetic.harmonicResidueError
    simp only [Nat.cast_add, Nat.cast_one]
    rw [div_le_div_iff₀ hden hden]
    exact mul_le_mul_of_nonneg_right hnum hden.le
  have hHover : (H : ℝ) / X ≤ 1 / 2 := by
    rw [div_le_iff₀ hXpos]
    nlinarith [hHXr]
  have hHE : (H : ℝ) / X * FromArithmetic.harmonicResidueError X W k ≤
      (W : ℝ) * k / ((X : ℝ) * D) := by
    calc
      _ ≤ (H : ℝ) / X * (2 * (W : ℝ) * k / ((X : ℝ) * D)) :=
        mul_le_mul_of_nonneg_left hEupper (by positivity)
      _ ≤ (1 / 2) * (2 * (W : ℝ) * k / ((X : ℝ) * D)) :=
        mul_le_mul_of_nonneg_right hHover (by positivity)
      _ = (W : ℝ) * k / ((X : ℝ) * D) := by ring
  have hNatCast : (h.toNat : ℤ) = h := Int.toNat_of_nonneg h0
  have hNatHInt : (h.toNat : ℤ) ≤ H := by rw [hNatCast]; exact hH
  have hNatH : h.toNat ≤ H := by exact_mod_cast hNatHInt
  have hLowLog := correlationRoot_log_endpoint_low X H h.toNat hX4 hNatH hHX
  have hHighLog := correlationRoot_log_endpoint_high X H h.toNat hX4 hNatH hHX
  have hA0lt : h.toNat < X := by omega
  have hA0cast : ((X - h.toNat : ℕ) : ℝ) = (X : ℝ) - h.toNat := by
    rw [Nat.cast_sub (Nat.le_of_lt hA0lt)]
  have hA0posN : 0 < X - h.toNat := Nat.sub_pos_of_lt hA0lt
  have hA0pos : (0 : ℝ) < (X : ℝ) - h.toNat := by
    rw [← hA0cast]
    exact_mod_cast hA0posN
  have hA0lower : (X : ℝ) / 2 ≤ (X : ℝ) - h.toNat := by
    have hNatHReal : (h.toNat : ℝ) ≤ H := by exact_mod_cast hNatH
    have hHhalf : (h.toNat : ℝ) < X / 2 := by linarith [hNatHReal, hHXr]
    apply (le_sub_iff_add_le).2
    linarith [hHhalf]
  have hInvA0 : 1 / ((X : ℝ) - h.toNat) ≤ 2 / X := by
    rw [div_le_div_iff₀ hA0pos hXpos]
    nlinarith [hA0lower]
  have hSqLt : h.toNat < X ^ 2 := by
    have hXsq : X < X ^ 2 := by nlinarith
    exact lt_trans hA0lt hXsq
  have hA1cast : ((X ^ 2 - h.toNat : ℕ) : ℝ) = (X ^ 2 : ℝ) - h.toNat := by
    rw [Nat.cast_sub (Nat.le_of_lt hSqLt), Nat.cast_pow]
  have hA1posN : 0 < X ^ 2 - h.toNat := Nat.sub_pos_of_lt hSqLt
  have hA1pos : (0 : ℝ) < (X ^ 2 : ℝ) - h.toNat := by
    rw [← hA1cast]
    exact_mod_cast hA1posN
  have hXge1 : (1 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hXge2 : (2 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show 2 ≤ X by omega)
  have hXsqGe : (X : ℝ) ≤ (X ^ 2 : ℝ) := by
    calc
      (X : ℝ) = (X : ℝ) * 1 := by ring
      _ ≤ (X : ℝ) * (X : ℝ) := mul_le_mul_of_nonneg_left hXge1 (by positivity)
      _ = (X ^ 2 : ℝ) := by ring
  have hA1lower : (X : ℝ) / 2 ≤ (X ^ 2 : ℝ) - h.toNat := by
    have hNatHReal : (h.toNat : ℝ) ≤ H := by exact_mod_cast hNatH
    have hHhalf : (h.toNat : ℝ) < (X : ℝ) / 2 := by
      calc
        (h.toNat : ℝ) ≤ H := hNatHReal
        _ < (X : ℝ) / 2 := by linarith [hHXr]
    have hsum : (X : ℝ) / 2 + (h.toNat : ℝ) ≤ X := by linarith [hHhalf]
    apply (le_sub_iff_add_le).2
    exact le_trans hsum hXsqGe
  have hInvA1 : 1 / ((X ^ 2 : ℝ) - h.toNat) ≤ 2 / X := by
    rw [div_le_div_iff₀ hA1pos hXpos]
    nlinarith [hA1lower]
  have hA0le : (X : ℝ) - (h.toNat : ℝ) ≤ (X : ℝ) := by
    have hn : (0 : ℝ) ≤ (h.toNat : ℝ) := by exact_mod_cast (Nat.zero_le h.toNat)
    linarith
  have hA1le : (X ^ 2 : ℝ) - (h.toNat : ℝ) ≤ (X ^ 2 : ℝ) := by
    have hn : (0 : ℝ) ≤ (h.toNat : ℝ) := by exact_mod_cast (Nat.zero_le h.toNat)
    linarith
  have hlogLowNonneg : 0 ≤ Real.log ((X : ℝ) / (X - h.toNat)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hA0pos]
    simpa using hA0le
  have hlogHighNonneg : 0 ≤ Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hA1pos]
    simpa using hA1le
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hLowMain : ((k : ℝ) / harmonicNormalizer X W) *
        ((Nat.totient W : ℝ) / W / k *
          Real.log ((X : ℝ) / (X - h.toNat))) ≤
      2 * (H : ℝ) / ((X : ℝ) * D) := by
    have heq : ((k : ℝ) / harmonicNormalizer X W) *
        ((Nat.totient W : ℝ) / W / k *
          Real.log ((X : ℝ) / (X - h.toNat))) =
        ((Nat.totient W : ℝ) / W / harmonicNormalizer X W) *
          Real.log ((X : ℝ) / (X - h.toNat)) := by
      field_simp [ne_of_gt hkR, ne_of_gt hZ] <;> ring
    rw [heq]
    calc
      _ ≤ (1 / D) * Real.log ((X : ℝ) / (X - h.toNat)) :=
        mul_le_mul_of_nonneg_right hδZ hlogLowNonneg
      _ ≤ (1 / D) * (2 * (H : ℝ) / X) :=
        mul_le_mul_of_nonneg_left hLowLog (by positivity)
      _ = 2 * (H : ℝ) / ((X : ℝ) * D) := by field_simp <;> ring
  have hHighMain : ((k : ℝ) / harmonicNormalizer X W) *
        ((Nat.totient W : ℝ) / W / k *
          Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat))) ≤
      2 * (H : ℝ) / ((X : ℝ) * D) := by
    have heq : ((k : ℝ) / harmonicNormalizer X W) *
        ((Nat.totient W : ℝ) / W / k *
          Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat))) =
        ((Nat.totient W : ℝ) / W / harmonicNormalizer X W) *
          Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat)) := by
      field_simp [ne_of_gt hkR, ne_of_gt hZ] <;> ring
    rw [heq]
    calc
      _ ≤ (1 / D) * Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat)) :=
        mul_le_mul_of_nonneg_right hδZ hlogHighNonneg
      _ ≤ (1 / D) * (2 * (H : ℝ) / X ^ 2) :=
        mul_le_mul_of_nonneg_left hHighLog (by positivity)
      _ ≤ 2 * (H : ℝ) / ((X : ℝ) * D) := by
        have hInvXsq : 1 / (X ^ 2 : ℝ) ≤ 1 / (X : ℝ) := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (X ^ 2 : ℝ)) hXpos]
          nlinarith [hXsqGe]
        calc
          (1 / D) * (2 * (H : ℝ) / X ^ 2) = (2 * (H : ℝ) / D) * (1 / (X ^ 2 : ℝ)) := by ring
          _ ≤ (2 * (H : ℝ) / D) * (1 / (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hInvXsq (by positivity)
          _ = 2 * (H : ℝ) / ((X : ℝ) * D) := by field_simp <;> ring
  have hLowErr : ((k : ℝ) / harmonicNormalizer X W) *
        ((Nat.totient W : ℝ) / (X - h.toNat)) ≤
      2 * (W : ℝ) * k / ((X : ℝ) * D) := by
    have heq : ((k : ℝ) / harmonicNormalizer X W) *
        ((Nat.totient W : ℝ) / (X - h.toNat)) =
        (k : ℝ) * ((Nat.totient W : ℝ) / harmonicNormalizer X W) *
          (1 / ((X : ℝ) - h.toNat)) := by
      field_simp [ne_of_gt hZ, ne_of_gt hA0pos] <;> ring
    rw [heq]
    calc
      _ ≤ (k : ℝ) * ((W : ℝ) / D) * (1 / ((X : ℝ) - h.toNat)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hphiZ (by positivity)) (by positivity)
      _ ≤ (k : ℝ) * ((W : ℝ) / D) * (2 / X) :=
        mul_le_mul_of_nonneg_left hInvA0 (by positivity)
      _ = 2 * (W : ℝ) * k / ((X : ℝ) * D) := by field_simp <;> ring
  have hHighErr : ((k : ℝ) / harmonicNormalizer X W) *
        ((Nat.totient W : ℝ) / (X ^ 2 - h.toNat)) ≤
      2 * (W : ℝ) * k / ((X : ℝ) * D) := by
    have heq : ((k : ℝ) / harmonicNormalizer X W) *
        ((Nat.totient W : ℝ) / (X ^ 2 - h.toNat)) =
        (k : ℝ) * ((Nat.totient W : ℝ) / harmonicNormalizer X W) *
          (1 / ((X ^ 2 : ℝ) - h.toNat)) := by
      field_simp [ne_of_gt hZ, ne_of_gt hA1pos] <;> ring
    rw [heq]
    calc
      _ ≤ (k : ℝ) * ((W : ℝ) / D) * (1 / ((X ^ 2 : ℝ) - h.toNat)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hphiZ (by positivity)) (by positivity)
      _ ≤ (k : ℝ) * ((W : ℝ) / D) * (2 / X) :=
        mul_le_mul_of_nonneg_left hInvA1 (by positivity)
      _ = 2 * (W : ℝ) * k / ((X : ℝ) * D) := by field_simp <;> ring
  have hRef := (correlationRoot_reference_shift_bound X W k H h hW hX hk hkX hcop
    h0 hH hdiv hHX).2
  have hRefUpper : arithmeticL1 (translatedLaw (dilationReference (harmonicLaw X W) k) h)
      (progressionReference (harmonicLaw X W) k h) ≤
      (H : ℝ) / X + 4 * (H : ℝ) / ((X : ℝ) * D) +
        5 * (W : ℝ) * k / ((X : ℝ) * D) := by
    have hterms := add_le_add (add_le_add hLowMain hLowErr) (add_le_add hHighMain hHighErr)
    have hbase : (H : ℝ) / X * (1 + FromArithmetic.harmonicResidueError X W k) =
        (H : ℝ) / X + (H : ℝ) / X * FromArithmetic.harmonicResidueError X W k := by ring
    rw [hbase] at hRef
    let lowTerm : ℝ := (k : ℝ) / harmonicNormalizer X W *
      ((Nat.totient W : ℝ) / W / k * Real.log ((X : ℝ) / (X - h.toNat)) +
        (Nat.totient W : ℝ) / (X - h.toNat))
    let highTerm : ℝ := (k : ℝ) / harmonicNormalizer X W *
      ((Nat.totient W : ℝ) / W / k * Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat)) +
        (Nat.totient W : ℝ) / (X ^ 2 - h.toNat))
    have hRefCompact : arithmeticL1
        (translatedLaw (dilationReference (harmonicLaw X W) k) h)
        (progressionReference (harmonicLaw X W) k h) ≤
        (H : ℝ) / X + (H : ℝ) / X * FromArithmetic.harmonicResidueError X W k +
          (lowTerm + highTerm) := by
      simpa [lowTerm, highTerm, add_assoc] using hRef
    have htermsCompact : lowTerm + highTerm ≤
        4 * (H : ℝ) / ((X : ℝ) * D) + 4 * (W : ℝ) * k / ((X : ℝ) * D) := by
      calc
        lowTerm + highTerm =
            ((k : ℝ) / harmonicNormalizer X W *
                ((Nat.totient W : ℝ) / W / k * Real.log ((X : ℝ) / (X - h.toNat))) +
              (k : ℝ) / harmonicNormalizer X W *
                ((Nat.totient W : ℝ) / (X - h.toNat))) +
            ((k : ℝ) / harmonicNormalizer X W *
                ((Nat.totient W : ℝ) / W / k * Real.log ((X ^ 2 : ℝ) / (X ^ 2 - h.toNat))) +
              (k : ℝ) / harmonicNormalizer X W *
                ((Nat.totient W : ℝ) / (X ^ 2 - h.toNat))) := by
                  simp [lowTerm, highTerm]
                  ring
        _ ≤ (2 * (H : ℝ) / ((X : ℝ) * D) + 2 * (W : ℝ) * k / ((X : ℝ) * D)) +
            (2 * (H : ℝ) / ((X : ℝ) * D) + 2 * (W : ℝ) * k / ((X : ℝ) * D)) := hterms
        _ = 4 * (H : ℝ) / ((X : ℝ) * D) +
            4 * (W : ℝ) * k / ((X : ℝ) * D) := by ring
    have hfinal : (H : ℝ) / X + (H : ℝ) / X *
        FromArithmetic.harmonicResidueError X W k + (lowTerm + highTerm) ≤
        (H : ℝ) / X + 4 * (H : ℝ) / ((X : ℝ) * D) +
          5 * (W : ℝ) * k / ((X : ℝ) * D) := by
      calc
        (H : ℝ) / X + (H : ℝ) / X * FromArithmetic.harmonicResidueError X W k +
            (lowTerm + highTerm) ≤
            (H : ℝ) / X + (H : ℝ) / X * FromArithmetic.harmonicResidueError X W k +
                  (4 * (H : ℝ) / ((X : ℝ) * D) +
                4 * (W : ℝ) * k / ((X : ℝ) * D)) :=
                  add_le_add (le_refl _) htermsCompact
        _ = ((H : ℝ) / X + 4 * (H : ℝ) / ((X : ℝ) * D)) +
              ((H : ℝ) / X * FromArithmetic.harmonicResidueError X W k +
                4 * (W : ℝ) * k / ((X : ℝ) * D)) := by ring
        _ ≤ ((H : ℝ) / X + 4 * (H : ℝ) / ((X : ℝ) * D)) +
              ((W : ℝ) * k / ((X : ℝ) * D) +
                4 * (W : ℝ) * k / ((X : ℝ) * D)) :=
                  add_le_add (le_refl _) (add_le_add hHE (le_refl _))
        _ = (H : ℝ) / X + 4 * (H : ℝ) / ((X : ℝ) * D) +
              5 * (W : ℝ) * k / ((X : ℝ) * D) := by ring
    exact le_trans hRefCompact hfinal
  have hInvDL : 1 / D ≤ 4 / (3 * L) := by
    rw [div_le_div_iff₀ hDpos (mul_pos (by norm_num : (0 : ℝ) < 3) (by positivity))]
    dsimp [D, L]
    nlinarith [hDlower]
  have hHDivBound : (H : ℝ) / ((X : ℝ) * D) ≤
      (4 / 3 : ℝ) * ((H : ℝ) / X) := by
    have heq : (H : ℝ) / ((X : ℝ) * D) = (H : ℝ) / X * (1 / D) := by
      field_simp [ne_of_gt hXpos, ne_of_gt hDpos] <;> ring
    rw [heq]
    calc
      (H : ℝ) / X * (1 / D) ≤ (H : ℝ) / X * (4 / 3) :=
        mul_le_mul_of_nonneg_left hDinvConst (by positivity)
      _ = (4 / 3 : ℝ) * ((H : ℝ) / X) := by ring
  have hWkDivBound : (W : ℝ) * k / ((X : ℝ) * D) ≤
      (4 / 3 : ℝ) * ((W : ℝ) * k / (X * L)) := by
    have heq : (W : ℝ) * k / ((X : ℝ) * D) = ((W : ℝ) * k / X) * (1 / D) := by
      field_simp [ne_of_gt hXpos, ne_of_gt hDpos] <;> ring
    rw [heq]
    calc
      ((W : ℝ) * k / X) * (1 / D) ≤ ((W : ℝ) * k / X) * (4 / (3 * L)) :=
        mul_le_mul_of_nonneg_left hInvDL (by positivity)
      _ = (4 / 3 : ℝ) * ((W : ℝ) * k / (X * L)) := by field_simp <;> ring
  have hRefFinal : arithmeticL1 (translatedLaw (dilationReference (harmonicLaw X W) k) h)
      (progressionReference (harmonicLaw X W) k h) ≤
      7 * (H : ℝ) / X + 7 * ((W : ℝ) * k / (X * L)) := by
    have hcalc := hRefUpper
    have hMain : (H : ℝ) / X + 4 * (H : ℝ) / ((X : ℝ) * D) ≤
        7 * (H : ℝ) / X := by
      have hHr : 0 ≤ (H : ℝ) / X := by positivity
      have hdiv4 := mul_le_mul_of_nonneg_left hHDivBound (by norm_num : (0 : ℝ) ≤ 4)
      have hdiv4' : 4 * (H : ℝ) / ((X : ℝ) * D) ≤
          4 * ((4 / 3 : ℝ) * ((H : ℝ) / X)) := by
        calc
          4 * (H : ℝ) / ((X : ℝ) * D) = 4 * ((H : ℝ) / ((X : ℝ) * D)) := by ring
          _ ≤ 4 * ((4 / 3 : ℝ) * ((H : ℝ) / X)) := hdiv4
      calc
        (H : ℝ) / X + 4 * (H : ℝ) / ((X : ℝ) * D) ≤
            (H : ℝ) / X + 4 * ((4 / 3 : ℝ) * ((H : ℝ) / X)) :=
              add_le_add (le_rfl) hdiv4'
        _ = (1 + 4 * (4 / 3 : ℝ)) * ((H : ℝ) / X) := by ring
        _ ≤ 7 * ((H : ℝ) / X) := by
          apply mul_le_mul_of_nonneg_right
          · norm_num
          · exact hHr
        _ = 7 * (H : ℝ) / X := by ring
    have hErr : 5 * (W : ℝ) * k / ((X : ℝ) * D) ≤
        7 * ((W : ℝ) * k / (X * L)) := by
      have hWr : 0 ≤ (W : ℝ) * k / (X * L) := by positivity
      have hcoeff : (5 : ℝ) * (4 / 3 : ℝ) ≤ 7 := by norm_num
      have hcoeffBound := mul_le_mul_of_nonneg_right hcoeff hWr
      calc
        5 * (W : ℝ) * k / ((X : ℝ) * D) ≤
            5 * (4 / 3 : ℝ) * ((W : ℝ) * k / (X * L)) := by
              calc
                5 * (W : ℝ) * k / ((X : ℝ) * D) =
                    5 * ((W : ℝ) * k / ((X : ℝ) * D)) := by ring
                _ ≤ 5 * ((4 / 3 : ℝ) * ((W : ℝ) * k / (X * L))) :=
                    mul_le_mul_of_nonneg_left hWkDivBound (by norm_num)
                _ = 5 * (4 / 3 : ℝ) * ((W : ℝ) * k / (X * L)) := by ring
        _ ≤ 7 * ((W : ℝ) * k / (X * L)) := by
              calc
                5 * (4 / 3 : ℝ) * ((W : ℝ) * k / (X * L)) =
                    (5 * (4 / 3 : ℝ)) * ((W : ℝ) * k / (X * L)) := by ring
                _ ≤ _ := hcoeffBound
    calc
      arithmeticL1 (translatedLaw (dilationReference (harmonicLaw X W) k) h)
          (progressionReference (harmonicLaw X W) k h) ≤
          (H : ℝ) / X + 4 * (H : ℝ) / ((X : ℝ) * D) +
            5 * (W : ℝ) * k / ((X : ℝ) * D) := hcalc
      _ ≤ 7 * (H : ℝ) / X + 7 * ((W : ℝ) * k / (X * L)) := add_le_add hMain hErr
  calc
    arithmeticL1 (translatedLaw (dilationReference (harmonicLaw X W) k) h)
        (progressionReference (harmonicLaw X W) k h) ≤
        7 * (H : ℝ) / X + 7 * ((W : ℝ) * k / (X * L)) := hRefFinal
    _ = 7 * (H : ℝ) / X + 7 * (W : ℝ) * k / ((X : ℝ) * Real.log X) := by
      simp [L]
      ring

theorem correlationRoot_error_comparison (X W k H : ℕ)
    (hW : 0 < W) (hX : 4 * W ≤ X) (hk : 0 < k) :
    (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) /
        (Real.log X - (W : ℝ) / X) +
      7 * (H : ℝ) / X + 7 * (W : ℝ) * k / (X * Real.log X) ≤
      10 * (Real.log (2 * k) / Real.log X + (H : ℝ) / X +
        (W : ℝ) * (k : ℝ) ^ 2 /
          ((Nat.totient W : ℝ) / W * X * Real.log X)) := by
  have hlog := correlation_root_log_condition hW hX
  have hLone := correlation_root_log_lower_one hW hX
  have hX4 : 4 ≤ X := by
    have hW1 : 1 ≤ W := Nat.succ_le_iff.mpr hW
    omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hWover : (W : ℝ) / X ≤ 1 / 4 := by
    apply (div_le_iff₀ hXpos).2
    have hXcast : 4 * (W : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  let L : ℝ := Real.log X
  let D : ℝ := Real.log X - (W : ℝ) / X
  let R : ℝ := Real.log (2 * k) / L
  let Q : ℝ := (W : ℝ) * k / ((X : ℝ) * L)
  let T : ℝ := (W : ℝ) * (k : ℝ) ^ 2 /
    ((Nat.totient W : ℝ) / W * (X : ℝ) * L)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hDpos : 0 < D := by dsimp [D]; exact sub_pos.mpr hlog
  have hDlower : (3 / 4 : ℝ) * L ≤ D := by
    dsimp [D, L]
    nlinarith [hWover, hLone]
  have hDinv : 1 / D ≤ 4 / (3 * L) := by
    rw [div_le_div_iff₀ hDpos (mul_pos (by norm_num : (0 : ℝ) < 3) hLpos)]
    dsimp [D, L]
    nlinarith [hDlower]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkRone : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hk)
  have hkLe2 : (k : ℝ) ≤ 2 * (k : ℝ) := by nlinarith [hkRone]
  have hLogK : Real.log (k : ℝ) ≤ Real.log (2 * k) :=
    Real.log_le_log hkR hkLe2
  have hLogKnonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkRone
  have hRnonneg : 0 ≤ R := by
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * k by omega)
    · exact hLpos.le
  have hlogPart : 2 * Real.log (k : ℝ) / D ≤ 3 * R := by
    calc
      2 * Real.log (k : ℝ) / D =
          (2 * Real.log (k : ℝ)) * (1 / D) := by field_simp [ne_of_gt hDpos]
      _ ≤ (2 * Real.log (k : ℝ)) * (4 / (3 * L)) :=
        mul_le_mul_of_nonneg_left hDinv (by positivity)
      _ = (8 / 3 : ℝ) * (Real.log (k : ℝ) / L) := by field_simp [ne_of_gt hLpos]; ring
      _ ≤ (8 / 3 : ℝ) * R := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        dsimp [R]
        exact div_le_div_of_nonneg_right hLogK hLpos.le
      _ ≤ 3 * R := by nlinarith [hRnonneg]
  have hfac : 1 + 1 / (X : ℝ) ≤ 5 / 4 := by
    have hX4R : (4 : ℝ) ≤ X := by exact_mod_cast hX4
    have hInvX : 1 / (X : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hXpos]
      nlinarith
    nlinarith [hInvX]
  have hApos : 0 ≤ (W : ℝ) * k / (X : ℝ) := by positivity
  have hQnonneg : 0 ≤ Q := by dsimp [Q]; positivity
  have hboundaryPart :
      ((W : ℝ) * k / X * (1 + 1 / X)) / D ≤ 2 * Q := by
    calc
      ((W : ℝ) * k / X * (1 + 1 / X)) / D =
          ((W : ℝ) * k / X) * (1 + 1 / X) * (1 / D) := by
            field_simp [ne_of_gt hDpos]
      _ ≤ ((W : ℝ) * k / X) * (5 / 4) * (1 / D) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac hApos) (by positivity)
      _ ≤ ((W : ℝ) * k / X) * (5 / 4) * (4 / (3 * L)) :=
        mul_le_mul_of_nonneg_left hDinv (by positivity)
      _ = (5 / 3 : ℝ) * Q := by
        dsimp [Q]
        field_simp [ne_of_gt hXpos, ne_of_gt hLpos] <;> ring
      _ ≤ 2 * Q := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (5 / 3 : ℝ) ≤ 2) hQnonneg
  have hDilation :
      (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) / D ≤ 3 * R + 2 * Q := by
    have hdecomp :
        (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) / D =
          2 * Real.log k / D + ((W : ℝ) * k / X * (1 + 1 / X)) / D := by
      field_simp [ne_of_gt hDpos] <;> ring
    rw [hdecomp]
    exact add_le_add hlogPart hboundaryPart
  have hφpos : 0 < (Nat.totient W : ℝ) / (W : ℝ) :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) hWpos
  have hφle : (Nat.totient W : ℝ) / (W : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hWpos]
    have ht : (Nat.totient W : ℝ) ≤ W := by exact_mod_cast Nat.totient_le W
    nlinarith
  have hδk : (Nat.totient W : ℝ) / W * k ≤ (k : ℝ) ^ 2 := by
    calc
      (Nat.totient W : ℝ) / W * k ≤ 1 * k :=
        mul_le_mul_of_nonneg_right hφle (by positivity)
      _ = k := by ring
      _ ≤ (k : ℝ) * k := by nlinarith [hkRone]
      _ = (k : ℝ) ^ 2 := by ring
  have hQT : Q ≤ T := by
    rw [div_le_div_iff₀ (mul_pos hXpos hLpos)
      (mul_pos (mul_pos hφpos hXpos) hLpos)]
    calc
      (W : ℝ) * k * ((Nat.totient W : ℝ) / W * X * L) =
          (W : ℝ) * (X * L) * ((Nat.totient W : ℝ) / W * k) := by ring
      _ ≤ (W : ℝ) * (X * L) * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hδk (by positivity)
      _ = (W : ℝ) * (k : ℝ) ^ 2 * (X * L) := by ring
  have hHnonneg : 0 ≤ (H : ℝ) / X := by positivity
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hCombined :
      (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) / D +
        7 * (H : ℝ) / X + 7 * Q ≤ 10 * (R + (H : ℝ) / X + T) := by
    have hRcoef : 3 * R ≤ 10 * R := by nlinarith [hRnonneg]
    have hHcoef : 7 * (H : ℝ) / X ≤ 10 * ((H : ℝ) / X) := by
      calc
        7 * (H : ℝ) / X = 7 * ((H : ℝ) / X) := by ring
        _ ≤ 10 * ((H : ℝ) / X) := by nlinarith [hHnonneg]
    have hQTcoef : 9 * Q ≤ 10 * T := by
      calc
        9 * Q ≤ 9 * T := mul_le_mul_of_nonneg_left hQT (by norm_num)
        _ ≤ 10 * T := by nlinarith [hTnonneg]
    calc
      (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) / D +
          7 * (H : ℝ) / X + 7 * Q ≤
          (3 * R + 2 * Q) + 7 * (H : ℝ) / X + 7 * Q := by
            exact add_le_add (add_le_add hDilation (le_refl _)) (le_refl _)
      _ = 3 * R + 7 * (H : ℝ) / X + 9 * Q := by ring
      _ ≤ 10 * R + 10 * ((H : ℝ) / X) + 10 * T :=
        add_le_add (add_le_add hRcoef hHcoef) hQTcoef
      _ = 10 * (R + (H : ℝ) / X + T) := by ring
  convert hCombined using 1 <;> ring

end HindmanSumsProducts
