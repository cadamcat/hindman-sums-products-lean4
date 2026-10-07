import HindmanSumsProducts.Arithmetic.Defs

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section

/-- Error term `E_X(k)` in the harmonic residue estimate (§3, `lem:sampling`). -/
def harmonicResidueError (X W k : ℕ) : ℝ :=
  (W : ℝ) * (k + 1 : ℕ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X))

/-- The pointwise clauses of the harmonic sampling lemma. -/
structure SamplingPointwiseBounds (X W : ℕ) : Prop where
  periodic_harmonic : ∀ (k a : ℕ) (A B : ℝ), Nat.Coprime k W → a < k → 0 < A → A < B →
    |(∑' n : ℕ, if A ≤ n ∧ (n : ℝ) < B ∧ Nat.Coprime n W ∧ n % k = a
        then 1 / (n : ℝ) else 0) -
      ((Nat.totient W : ℝ) / W / k * Real.log (B / A))| ≤ (Nat.totient W : ℝ) / A
  normalizer : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X →
    |harmonicNormalizer X W - (Nat.totient W : ℝ) / W * Real.log X| ≤ (Nat.totient W : ℝ) / X
  residue_pointwise : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X → ∀ k a : ℕ,
    Nat.Coprime k W → 0 < k → (ha : a < k) →
      |(k : ℝ) * harmonicResidueLaw (harmonicLaw X W) k ⟨a, ha⟩ - 1| ≤
        harmonicResidueError X W k
  residue_total_mass : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X → ∀ k : ℕ,
    Nat.Coprime k W → 0 < k →
      finiteL1 (harmonicResidueLaw (harmonicLaw X W) k) (uniformResidueLaw k) ≤
        harmonicResidueError X W k
  translation : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X → ∀ h : ℤ,
    (∃ m : ℤ, h = (W : ℤ) * m) →
      arithmeticL1 (translatedLaw (harmonicLaw X W) h) (harmonicLaw X W) ≤
        min 2 (2 * |(h : ℝ)| / ((X : ℝ) * (Real.log X - (W : ℝ) / X)))
  dilation : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X → ∀ k : ℕ,
    1 ≤ k → k ≤ X → Nat.Coprime k W →
      arithmeticL1 (dilatedLaw (harmonicLaw X W) k) (dilationReference (harmonicLaw X W) k) ≤
        (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) /
          (Real.log X - (W : ℝ) / X) ∧
      |(∑' z : ℤ, dilationReference (harmonicLaw X W) k z) - 1| ≤
        harmonicResidueError X W k

/-- Why `sampling_pointwise_claim` assumes `0 < W` (in the paper `W` is a primorial): without it
the statement fails at `W = 0`.
For that value, `Nat.Coprime 1 0` leaves the single term `n = 1`, while its
claimed error bound is zero. -/
theorem sampling_pointwise_bounds_zero_false : ¬ SamplingPointwiseBounds 2 0 := by
  intro h
  have hh := h.periodic_harmonic 1 0 (1 / 2) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hs : (∑' n : ℕ, if (1 / 2 : ℝ) ≤ n ∧ (n : ℝ) < 2 ∧
      Nat.Coprime n 0 ∧ n % 1 = 0 then 1 / (n : ℝ) else 0) = 1 := by
    rw [tsum_eq_single 1]
    · norm_num [Nat.Coprime]
    · intro n hn
      simp [Nat.Coprime, hn]
  rw [hs] at hh
  norm_num at hh

/-- Pointwise harmonic estimates underlying Lemma `lem:sampling`. -/
theorem sampling_pointwise_claim (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log X > (W : ℝ) / X) : SamplingPointwiseBounds X W := by
  sorry

private theorem interval_residue_card_error (a T k r : ℕ) (hk : 0 < k)
    (hr : r < k) :
    |(({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℝ) - (T : ℝ) / k)| ≤ 1 := by
  let A : ℚ := ((a : ℚ) - r) / k
  let B : ℚ := ((a + T : ℕ) - r) / k
  have hrel : B = A + (T : ℚ) / k := by
    dsimp [A, B]
    push_cast
    field_simp
    ring
  have hset : {n ∈ Finset.Ico a (a + T) | n % k = r} =
      {n ∈ Finset.Ico a (a + T) | n ≡ r [MOD k]} := by
    ext n
    simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
  have hceil : ⌈A⌉ ≤ ⌈B⌉ := Int.ceil_mono (by
    rw [hrel]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity)))
  have hcardZ :
      (({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℕ) : ℤ) = ⌈B⌉ - ⌈A⌉ := by
    rw [hset]
    have hc := Nat.Ico_filter_modEq_card a (a + T) hk r
    rw [show (↑(a + T : ℕ) - ↑r : ℚ) / ↑k = B by rfl,
      show (↑(a : ℕ) - ↑r : ℚ) / ↑k = A by rfl] at hc
    rw [max_eq_left (sub_nonneg.mpr hceil)] at hc
    exact hc
  have hcardR :
      (({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℕ) : ℝ) =
        (⌈B⌉ : ℤ) - ⌈A⌉ := by exact_mod_cast hcardZ
  have hAlo : (A : ℝ) ≤ (⌈A⌉ : ℝ) := by exact_mod_cast (Int.le_ceil A)
  have hAhi : (⌈A⌉ : ℝ) < (A : ℝ) + 1 := by exact_mod_cast (Int.ceil_lt_add_one A)
  have hBlo : (B : ℝ) ≤ (⌈B⌉ : ℝ) := by exact_mod_cast (Int.le_ceil B)
  have hBhi : (⌈B⌉ : ℝ) < (B : ℝ) + 1 := by exact_mod_cast (Int.ceil_lt_add_one B)
  have hrelR : (B : ℝ) = (A : ℝ) + (T : ℝ) / k := by
    calc
      (B : ℝ) = ((A + (T : ℚ) / k : ℚ) : ℝ) := congrArg (fun x : ℚ => (x : ℝ)) hrel
      _ = (A : ℝ) + (T : ℝ) / k := by simp only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast]
  rw [hcardR, abs_le]
  constructor <;> nlinarith [hrelR]

/-- Uniform sampling on an integer interval: residue total-mass error and translation error
from §3 lines 132–143. -/
theorem uniform_interval_sampling_bounds (a T k : ℕ) (hT : 0 < T) (hk : 0 < k) :
    finiteL1
        (fun r : Fin k =>
          ∑ n ∈ (Finset.Ico a (a + T)), if n % k = r.val then 1 / (T : ℝ) else 0)
        (uniformResidueLaw k) ≤ 2 * k / T := by
  classical
  have hmass (r : Fin k) :
      (∑ n ∈ Finset.Ico a (a + T), if n % k = r.val then 1 / (T : ℝ) else 0) =
        (({n ∈ Finset.Ico a (a + T) | n % k = r.val}.card : ℝ) / T) := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hdev (r : Fin k) :
      |(∑ n ∈ Finset.Ico a (a + T), if n % k = r.val then 1 / (T : ℝ) else 0) -
        1 / (k : ℝ)| ≤ 1 / (T : ℝ) := by
    rw [hmass r]
    have hr := interval_residue_card_error a T k r.val hk r.isLt
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h' : |(↑({n ∈ Finset.Ico a (a + T) | n % k = r.val}.card : ℝ) - (T : ℝ) / k) / T| ≤
        1 / T := by
      rw [abs_div, abs_of_pos hTr]
      exact div_le_div_of_nonneg_right hr hTr.le
    have heq : ((↑({n ∈ Finset.Ico a (a + T) | n % k = r.val}.card : ℝ) / T) - 1 / k) =
        (↑({n ∈ Finset.Ico a (a + T) | n % k = r.val}.card : ℝ) - (T : ℝ) / k) / T := by
      field_simp [ne_of_gt hTr, ne_of_gt hkr]
    rw [heq]
    exact h'
  unfold finiteL1 uniformResidueLaw
  change (∑ r : Fin k, |(∑ n ∈ Finset.Ico a (a + T),
    if n % k = r.val then 1 / (T : ℝ) else 0) - 1 / (k : ℝ)|) ≤ 2 * (k : ℝ) / T
  calc
    (∑ r : Fin k, |(∑ n ∈ Finset.Ico a (a + T), if n % k = r.val then 1 / (T : ℝ) else 0) - 1 / (k : ℝ)|)
        ≤ ∑ r : Fin k, 1 / (T : ℝ) := Finset.sum_le_sum fun r _ => hdev r
    _ = (k : ℝ) / T := by simp [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (k : ℝ) / T := by
      have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
      have hn : 0 ≤ (k : ℝ) / T := div_nonneg hkR hTR.le
      rw [show 2 * (k : ℝ) / T = 2 * ((k : ℝ) / T) by ring]
      nlinarith

/-- Translating a uniform integer interval by u changes its probability law in total-mass
norm by at most `2 min(1,|u|/T)` (§3 lines 137–140). -/
def uniformIntegerIntervalLaw (a : ℤ) (T : ℕ) (z : ℤ) : ℝ :=
  if a ≤ z ∧ z < a + T then 1 / (T : ℝ) else 0

theorem uniform_interval_translation_bound (a u : ℤ) (T : ℕ) (hT : 0 < T) :
    arithmeticL1 (translatedLaw (uniformIntegerIntervalLaw a T) u)
      (uniformIntegerIntervalLaw a T) ≤
      2 * min 1 (|u| / (T : ℝ)) := by
  classical
  let I : Finset ℤ := Finset.Ico a (a + T)
  let J : Finset ℤ := Finset.Ico (a + u) (a + u + T)
  let D : Finset ℤ := (J \ I) ∪ (I \ J)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hIcard : I.card = T := by
    have h : (I.card : ℤ) = (T : ℤ) := by
      dsimp [I]
      rw [Int.card_Ico_of_le a (a + (T : ℤ)) (by omega)
      ]
      simp
    exact_mod_cast h
  have hJcard : J.card = T := by
    have h : (J.card : ℤ) = (T : ℤ) := by
      dsimp [J]
      rw [Int.card_Ico_of_le (a + u) (a + u + (T : ℤ)) (by omega)]
      simp
    exact_mod_cast h
  have hshift (z : ℤ) :
      uniformIntegerIntervalLaw a T (z - u) = if z ∈ J then 1 / (T : ℝ) else 0 := by
    simp only [uniformIntegerIntervalLaw, J, Finset.mem_Ico]
    by_cases hz : a ≤ z - u ∧ z - u < a + (T : ℤ)
    · have hz' : a + u ≤ z ∧ z < a + u + (T : ℤ) := by omega
      simp [hz, hz']
    · have hz' : ¬ (a + u ≤ z ∧ z < a + u + (T : ℤ)) := by omega
      simp [hz, hz']
  have horig (z : ℤ) :
      uniformIntegerIntervalLaw a T z = if z ∈ I then 1 / (T : ℝ) else 0 := by
    simp only [uniformIntegerIntervalLaw, I, Finset.mem_Ico]
  have hterm (z : ℤ) :
      |(if z ∈ J then 1 / (T : ℝ) else 0) - (if z ∈ I then 1 / (T : ℝ) else 0)| =
        if z ∈ D then 1 / (T : ℝ) else 0 := by
    by_cases hj : z ∈ J <;> by_cases hi : z ∈ I <;>
      simp [D, hj, hi, abs_of_pos hTpos]
  have hL1 : arithmeticL1 (translatedLaw (uniformIntegerIntervalLaw a T) u)
      (uniformIntegerIntervalLaw a T) = (D.card : ℝ) / T := by
    unfold arithmeticL1 translatedLaw
    simp_rw [hshift, horig, hterm]
    rw [tsum_eq_sum (s := D) (fun z hz => by simp [hz])]
    calc
      (∑ z ∈ D, if z ∈ D then 1 / (T : ℝ) else 0) =
          (D.card : ℝ) * (1 / (T : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (D.card : ℝ) / T := by ring
  have hDlarge : D.card ≤ 2 * T := by
    calc
      D.card ≤ (J \ I).card + (I \ J).card := Finset.card_union_le _ _
      _ ≤ J.card + I.card := Nat.add_le_add
        (Finset.card_mono (Finset.sdiff_subset)) (Finset.card_mono (Finset.sdiff_subset))
      _ = 2 * T := by rw [hJcard, hIcard]; omega
  have hDsmall (hm : u.natAbs < T) : D.card = 2 * u.natAbs := by
    have hdis : Disjoint (J \ I) (I \ J) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [Finset.mem_sdiff] at hz1 hz2
      exact hz1.2 hz2.1
    have hUnion := Finset.card_union_of_disjoint hdis
    by_cases hu : 0 ≤ u
    · have huNat : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu
      have hInter : I ∩ J = Finset.Ico (a + u) (a + (T : ℤ)) := by
        dsimp [I, J]
        rw [Finset.Ico_inter_Ico]
        congr 1
        · simp [max_eq_right (by omega : a ≤ a + u)]
        · simp [min_eq_left (by omega : a + (T : ℤ) ≤ a + u + (T : ℤ))]
      have hInterCard : (I ∩ J).card = T - u.natAbs := by
        have hmZ : (u.natAbs : ℤ) < (T : ℤ) := by exact_mod_cast hm
        have hle : a + u ≤ a + (T : ℤ) := by rw [← huNat]; omega
        have hraw : ((I ∩ J).card : ℤ) = (T : ℤ) - u := by
          rw [hInter, Int.card_Ico_of_le (a + u) (a + (T : ℤ)) hle]
          omega
        have hsub : ((T - u.natAbs : ℕ) : ℤ) = (T : ℤ) - u := by
          rw [Nat.cast_sub (Nat.le_of_lt hm)]
          simp [huNat]
        exact_mod_cast hraw.trans hsub.symm
      have h1 : (I \ J).card + (I ∩ J).card = T := by
        simpa [hIcard] using Finset.card_sdiff_add_card_inter I J
      have h2 : (J \ I).card + (I ∩ J).card = T := by
        simpa [hJcard, Finset.inter_comm] using Finset.card_sdiff_add_card_inter J I
      rw [hUnion]
      omega
    · have hu' : u ≤ 0 := le_of_not_ge hu
      have huNat : (u.natAbs : ℤ) = -u := by
        simpa only [Int.natAbs_neg] using
          (Int.natAbs_of_nonneg (neg_nonneg_of_nonpos hu'))
      have hInter : I ∩ J = Finset.Ico a (a + u + (T : ℤ)) := by
        dsimp [I, J]
        rw [Finset.Ico_inter_Ico]
        congr 1
        · simp [max_eq_left (by omega : a + u ≤ a)]
        · simp [min_eq_right (by omega : a + u + (T : ℤ) ≤ a + (T : ℤ))]
      have hInterCard : (I ∩ J).card = T - u.natAbs := by
        have hle : a ≤ a + u + (T : ℤ) := by
          have hm' : (u.natAbs : ℤ) < (T : ℤ) := by exact_mod_cast hm
          rw [huNat] at hm'
          omega
        have hraw : ((I ∩ J).card : ℤ) = (T : ℤ) - u.natAbs := by
          rw [hInter, Int.card_Ico_of_le a (a + u + (T : ℤ)) hle]
          rw [huNat]
          omega
        have hsub : ((T - u.natAbs : ℕ) : ℤ) = (T : ℤ) - u.natAbs := by
          rw [Nat.cast_sub (Nat.le_of_lt hm)]
        exact_mod_cast hraw.trans hsub.symm
      have h1 : (I \ J).card + (I ∩ J).card = T := by
        simpa [hIcard] using Finset.card_sdiff_add_card_inter I J
      have h2 : (J \ I).card + (I ∩ J).card = T := by
        simpa [hJcard, Finset.inter_comm] using Finset.card_sdiff_add_card_inter J I
      rw [hUnion]
      omega
  have huAbs : ((|u| : ℤ) : ℝ) = (u.natAbs : ℝ) := by
    exact congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs u).symm
  by_cases hm : u.natAbs < T
  · have hratio : (u.natAbs : ℝ) / T < 1 := (div_lt_one hTpos).2 (by exact_mod_cast hm)
    rw [hL1, hDsmall hm, huAbs, min_eq_right hratio.le]
    exact le_of_eq (by push_cast; ring)
  · have hratio : 1 ≤ (u.natAbs : ℝ) / T :=
      (one_le_div hTpos).2 (by exact_mod_cast (Nat.le_of_not_gt hm))
    rw [hL1, huAbs, min_eq_left hratio]
    have hDreal : (D.card : ℝ) ≤ 2 * (T : ℝ) := by exact_mod_cast hDlarge
    exact (div_le_iff₀ hTpos).2 (by simpa using hDreal)

/-- Telescoping bound for the total-mass distance of product laws, used for fixed disjoint
block families in §3 lines 139–143. -/
theorem finite_product_l1_telescoping {ι α : Type*} [Fintype ι] [Fintype α]
    [Fintype (ι → α)] [DecidableEq ι]
    (μ ν : ι → α → ℝ) :
    finiteL1 (fun x : ι → α => ∏ i, μ i (x i)) (fun x => ∏ i, ν i (x i)) ≤
      ∑ i, finiteL1 (μ i) (ν i) *
        ∏ j ∈ Finset.univ.erase i, max (∑ a, |μ j a|) (∑ a, |ν j a|) := by
  sorry

/-- Worst-case residue error for `k≤K` in the asymptotic part of `lem:sampling`. -/
def harmonicResidueUniformError (X W K : ℕ) : ℝ := harmonicResidueError X W K

/-- Worst-case translation error for `|h|≤H` in the asymptotic part of `lem:sampling`. -/
def harmonicTranslationUniformError (X W H : ℕ) : ℝ :=
  min 2 (2 * (H : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X)))

/-- Worst-case dilation error for `k≤K` in the asymptotic part of `lem:sampling`. -/
def harmonicDilationUniformError (X W K : ℕ) : ℝ :=
  (2 * Real.log K + (W : ℝ) * K / X * (1 + 1 / X)) /
    (Real.log X - (W : ℝ) / X)

/-- Super-polynomial residue, translation, and dilation conclusions of `lem:sampling`.
The first two use power domination by `X`; dilation uses power domination by `log X`. -/
theorem sampling_asymptotics
    (W K H V X : ℕ → ℕ)
    (hK : ∀ n, 1 ≤ K n) (hH : ∀ n, 1 ≤ H n) (hV : ∀ n, 1 ≤ V n)
    (hW : ∀ n, W n = primorial (n + 1))
    (hX : ∀ᶠ n in atTop, 2 ≤ X n)
    (hden : ∀ᶠ n in atTop, Real.log (X n) > (W n : ℝ) / X n)
    (hDomX : OAI.MicrocellScale.Dominates (fun n => (X n : ℝ))
      (fun n => 2 + W n + K n + H n + V n))
    (hDomLogX : OAI.MicrocellScale.Dominates (fun n => Real.log (X n : ℝ))
      (fun n => 2 + W n + K n + V n)) :
    SuperPolynomialSmall
        (fun n => harmonicResidueUniformError (X n) (W n) (K n)) (fun n => (V n : ℝ)) ∧
    SuperPolynomialSmall
        (fun n => harmonicTranslationUniformError (X n) (W n) (H n)) (fun n => (V n : ℝ)) ∧
    SuperPolynomialSmall
        (fun n => harmonicDilationUniformError (X n) (W n) (K n)) (fun n => (V n : ℝ)) ∧
    (∀ A : ℝ, 0 < A →
      Tendsto (fun n => (V n : ℝ) ^ A *
        (harmonicResidueUniformError (X n) (W n) (K n) +
          harmonicTranslationUniformError (X n) (W n) (H n) +
          harmonicDilationUniformError (X n) (W n) (K n))) atTop (𝓝 0)) := by
  sorry

/-- Lemma `lem:sampling`: exact periodic harmonic, residue, translation, and dilation
bounds together with the super-polynomial asymptotic conclusions and their stated growth
conditions (§3 lines 34–129). -/
theorem lem_sampling (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log X > (W : ℝ) / X) :
    SamplingPointwiseBounds X W ∧
    (∀ (Wseq K H V Xseq : ℕ → ℕ),
      (∀ n, 1 ≤ K n) → (∀ n, 1 ≤ H n) → (∀ n, 1 ≤ V n) →
      (∀ n, Wseq n = primorial (n + 1)) →
      (∀ᶠ n in atTop, 2 ≤ Xseq n) →
      (∀ᶠ n in atTop, Real.log (Xseq n) > (Wseq n : ℝ) / Xseq n) →
      OAI.MicrocellScale.Dominates (fun n => (Xseq n : ℝ))
        (fun n => 2 + Wseq n + K n + H n + V n) →
      OAI.MicrocellScale.Dominates (fun n => Real.log (Xseq n : ℝ))
        (fun n => 2 + Wseq n + K n + V n) →
      SuperPolynomialSmall
        (fun n => harmonicResidueUniformError (Xseq n) (Wseq n) (K n))
        (fun n => (V n : ℝ)) ∧
      SuperPolynomialSmall
        (fun n => harmonicTranslationUniformError (Xseq n) (Wseq n) (H n))
        (fun n => (V n : ℝ)) ∧
      SuperPolynomialSmall
        (fun n => harmonicDilationUniformError (Xseq n) (Wseq n) (K n))
        (fun n => (V n : ℝ)) ∧
      (∀ A : ℝ, 0 < A →
        Tendsto (fun n => (V n : ℝ) ^ A *
          (harmonicResidueUniformError (Xseq n) (Wseq n) (K n) +
            harmonicTranslationUniformError (Xseq n) (Wseq n) (H n) +
            harmonicDilationUniformError (Xseq n) (Wseq n) (K n))) atTop (𝓝 0))) := by
  refine ⟨sampling_pointwise_claim X W hW hX hlog, ?_⟩
  intro Wseq K H V Xseq hK hH hV hW hXseq hden hDomX hDomLogX
  exact sampling_asymptotics Wseq K H V Xseq hK hH hV hW hXseq hden hDomX hDomLogX

end
end HindmanSumsProducts
