import HindmanSumsProducts.Arithmetic

/-!
# The §3 results used by §4 (copies)

§4 may import only the frozen `HindmanSumsProducts.Arithmetic.Defs`; the other §3 files are still
being proved or repaired. This file copies the §3 declarations that §4 states or proves against,
in the namespace `HindmanSumsProducts.FromArithmetic`, so it elaborates next to
`HindmanSumsProducts.Arithmetic` without a name clash.

Every copy names its source `HindmanSumsProducts.<name>` (`Arithmetic/<File>.lean`) and says
whether it is the same statement as on `main` at `1e75bc3` (repaired §3, merge of
`lane/repair-master`). "Same" means the same text up to the namespace, so replacing the copy
by an import is mechanical. The only copies that differ are `WeightedLinearFormsData`,
`weightedLinearFormsAverage` and `prop_linear_forms`: §4 needs rows whose coefficients depend on
`N` and on the prime slots (see `WeightedLinearFormsData`).
-/

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts.FromArithmetic
noncomputable section

/-! ## `Arithmetic/Sampling.lean`

Copies of `harmonicResidueError`, `SamplingPointwiseBounds`, `sampling_pointwise_claim`,
`uniform_interval_sampling_bounds` (with its proof and private helper),
`uniformIntegerIntervalLaw`, `uniform_interval_translation_bound` (with its proof),
`finite_product_l1_telescoping`, `harmonicResidueUniformError`,
`harmonicTranslationUniformError`, `harmonicDilationUniformError`, `sampling_asymptotics` and
`lem_sampling` (with its proof). All are the same statements as on `main`; the counterexample
`sampling_pointwise_bounds_zero_false` is not copied. -/

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

/-- Pointwise harmonic estimates underlying Lemma `lem:sampling`. -/
-- Copy of `HindmanSumsProducts.sampling_pointwise_claim` (`Arithmetic/Sampling.lean`);
-- same statement as on `main`.
theorem sampling_pointwise_claim (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log X > (W : ℝ) / X) : SamplingPointwiseBounds X W := by
  have h := HindmanSumsProducts.sampling_pointwise_claim X W hW hX hlog
  exact ⟨h.periodic_harmonic, h.normalizer, h.residue_pointwise, h.residue_total_mass,
    h.translation, h.dilation⟩

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
-- Copy of `HindmanSumsProducts.uniform_interval_sampling_bounds` (`Arithmetic/Sampling.lean`);
-- same statement as on `main`.
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

-- Copy of `HindmanSumsProducts.uniform_interval_translation_bound` (`Arithmetic/Sampling.lean`);
-- same statement as on `main`.
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
-- Copy of `HindmanSumsProducts.finite_product_l1_telescoping` (`Arithmetic/Sampling.lean`);
-- same statement as on `main`.
theorem finite_product_l1_telescoping {ι α : Type*} [Fintype ι] [Fintype α]
    [Fintype (ι → α)] [DecidableEq ι]
    (μ ν : ι → α → ℝ) :
    finiteL1 (fun x : ι → α => ∏ i, μ i (x i)) (fun x => ∏ i, ν i (x i)) ≤
      ∑ i, finiteL1 (μ i) (ν i) *
        ∏ j ∈ Finset.univ.erase i, max (∑ a, |μ j a|) (∑ a, |ν j a|) := by
  exact HindmanSumsProducts.finite_product_l1_telescoping μ ν

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
-- Copy of `HindmanSumsProducts.sampling_asymptotics` (`Arithmetic/Sampling.lean`);
-- same statement as on `main`.
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
  exact HindmanSumsProducts.sampling_asymptotics W K H V X hK hH hV hW hX hden hDomX hDomLogX

/-- Lemma `lem:sampling`: exact periodic harmonic, residue, translation, and dilation
bounds together with the super-polynomial asymptotic conclusions and their stated growth
conditions (§3 lines 34–129). -/
-- Copy of `HindmanSumsProducts.lem_sampling` (`Arithmetic/Sampling.lean`);
-- same statement as on `main`.
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

/-! ## `Arithmetic/ProductLaw.lean` -/

/-- Copy of `HindmanSumsProducts.parameterTailProductLaw` (`Arithmetic/ProductLaw.lean`), same
definition. It is the law of the tail product `t_T`, so `nuB (parameterTailProductLaw A N T)` is
the paper's divisor weight `ν_B` for a block `B = T ∪ {i}`. -/
def parameterTailProductLaw {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n)) (σ : ℕ) : ℝ :=
  ∑' t : Fin n → ℕ,
    (if (∏ j ∈ T, t j) = σ then 1 else 0) *
      ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)

/-! ## `Arithmetic/MasterScales.lean`

Copies of `masterScaleV`, `masterCRTModulus`, `uniformSmallPrimeException`,
`primeSmallDivisibilityEvent`, `polynomialZeroOrRepeated`, `MasterScaleCore`,
`MasterScalePrimeStage`, `MasterScaleGapStage`, `MasterScales` and `lem_master_scales`, as
repaired on `main` (`1e75bc3`): `chain_coefficients` and `coefficient_divides_modulus` hold for
all sufficiently large `N`. All are the same statements as on `main`. No §4 statement needs the
old non-eventual forms: every §4 conclusion is asserted for all sufficiently large `N`. -/

/-- `V_l=2+M+∏_{j<l}X_j²` from §3. -/
def masterScaleV {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (l : Fin n) : ℕ :=
  2 + A.M N + ∏ j ∈ (Finset.univ.filter (fun j : Fin n => j < l)), (A.X N j) ^ 2

/-- `Q_l=W^{e₀}∏_{w<p≤V_l}p`, with the paper's `w=N+1`. The product runs over
`w<p≤V+1`, one more than the paper's `p≤V_l`; this only adds a prime below every pool
prime and matches `CRTPrimeRange` in `LinearForms.lean`. -/
def masterCRTModulus (w e V : ℕ) : ℕ :=
  (primorial w) ^ e *
    ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p

/-- Small-prime divisibility event for a finite polynomial template on uniform unit slots. -/
def uniformSmallPrimeException {m : ℕ} (D : Finset (IntegerPolynomial m))
    (w e : ℕ) (u : Fin m → Fin ((primorial w) ^ e)) : Prop :=
  ∃ p, p.Prime ∧ p ≤ w ∧ ∃ P ∈ D,
    ((p ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial P (fun i => ((u i).val : ℤ))

/-- The same small-prime event for actual prime slots in a pool. -/
def primeSmallDivisibilityEvent {m : ℕ} (D : Finset (IntegerPolynomial m))
    (w e : ℕ) (p : Fin m → ℕ) : Prop :=
  ∃ q, q.Prime ∧ q ≤ w ∧ ∃ P ∈ D,
    ((q ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial P (fun i => (p i : ℤ))

/-- A polynomial vanishes, or two prime slots repeat. -/
def polynomialZeroOrRepeated {m : ℕ} (D : Finset (IntegerPolynomial m))
    (p : Fin m → ℕ) : Prop :=
  (∃ P ∈ D, evalIntegerPolynomial P (fun i => (p i : ℤ)) = 0) ∨
    (∃ i j, i ≠ j ∧ p i = p j)

/-- Algebraic and admissibility part of the master scales. It is one component of the result
`MasterScales`; it is not chosen before the prime pools, since `parameters.H` and
`parameters.X` are the gap lengths and cutoffs chosen after each pool (§3 lines 283–302).
The chain coefficients are integers only for all sufficiently large `w` (§3 lines 210–211,
262–266; §2 lines 80–88). -/
structure MasterScaleCore (n : ℕ) (Aset : Finset ℚ) where
  parameters : OAI.SourceAdmissible.Parameters n
  height_formula : ∀ N (j : Fin n),
    parameters.ht N j =
      (primorial (N + 1) : ℤ) ^ ((N + 1) * 2 ^ (n - j.val - 1))
  modulus_power : ∀ N, ∃ e : ℕ,
    parameters.M N = (primorial (N + 1)) ^ e
  adding_pair_ratio : ∀ N (B : OAI.SourceBlocks.Block n)
      (S : Finset (Fin n)),
    OAI.SourceBlocks.Added B.1 B.2.val S →
      ∃ d : ℤ,
        OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (parameters.ht N) S =
          OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (parameters.ht N) B.set *
              ((primorial (N + 1) : ℤ) ^ (N + 1) * d)
  chain_coefficients : ∀ᶠ N in atTop, ∀ r (C : MasterChain n r) (a : Fin r → ℚ),
    (∀ d, a d ∈ Aset) →
    ∃ c : Fin r → ℤ,
      (∀ d, (c d : ℚ) =
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (parameters.ht N) (C.block d).set : ℚ) * a d) ∧
      (∀ d, 0 < c d) ∧
      (∀ u d, u < d →
        ∃ k : ℕ, c u = (primorial (N + 1) : ℤ) * (k : ℤ) * c d)

/-- Prime-pool component of the master scales: `e₀`, the pools, their CRT accuracy and their
polynomial exceptional events (§3 lines 212–238, 247–251). -/
structure MasterScalePrimeStage {n : ℕ} {Aset : Finset ℚ}
    (C : MasterScaleCore n Aset) (m : ℕ) (D : Finset (IntegerPolynomial m)) where
  e0 : ℕ → ℕ
  pool : ℕ → Fin n → PrimePool
  e0_pos : ∀ N, 1 ≤ e0 N
  uniform_small_prime_exception : Tendsto
    (fun N => uniformUnitTupleProbability
      ((primorial (N + 1)) ^ e0 N) m
      (uniformSmallPrimeException D (N + 1) (e0 N))) atTop (𝓝 0)
  pool_lower_dominates : ∀ l,
    OAI.MicrocellScale.Dominates
      (fun N => ((pool N l).lower : ℝ))
      (fun N => (masterScaleV C.parameters N l : ℝ))
  pool_harmonic_mass_dominates : ∀ l,
    OAI.MicrocellScale.Dominates
      (fun N => primePoolMass (pool N l).lower (pool N l).upper)
      (fun N => (masterScaleV C.parameters N l : ℝ))
  pool_residue_error : ∀ l,
    SuperPolynomialSmall
      (fun N => finiteL1
        (primePoolResidueLaw (pool N l).lower (pool N l).upper
          (masterCRTModulus (N + 1) (e0 N) (masterScaleV C.parameters N l)))
        (uniformUnitResidueLaw
          (masterCRTModulus (N + 1) (e0 N) (masterScaleV C.parameters N l))))
      (fun N => (masterScaleV C.parameters N l : ℝ))
  actual_small_prime_exception : ∀ l, Tendsto
    (fun N => independentPrimePoolProbability
      (fun _ : Fin m => (pool N l).lower)
      (fun _ : Fin m => (pool N l).upper)
      (primeSmallDivisibilityEvent D (N + 1) (e0 N))) atTop (𝓝 0)
  zero_and_repeat_probability : ∀ l,
    SuperPolynomialSmall
      (fun N => independentPrimePoolProbability
        (fun _ : Fin m => (pool N l).lower)
        (fun _ : Fin m => (pool N l).upper)
        (polynomialZeroOrRepeated D))
      (fun N => (masterScaleV C.parameters N l : ℝ))

/-- Gap-length and cutoff component of the master scales (§3 lines 219, 239–246, 296–302).
`W^{e₀+1}c_d ∣ M` holds only for all sufficiently large `w`: the fixed numerators of
`𝒜` must be `w`-smooth with bounded valuations (§3 lines 262–266, 280–281). -/
structure MasterScaleGapStage {n : ℕ} {Aset : Finset ℚ}
    (C : MasterScaleCore n Aset) {m : ℕ} {D : Finset (IntegerPolynomial m)}
    (P : MasterScalePrimeStage C m D) : Prop where
  gap_dominates_pool_and_bound : ∀ l,
    OAI.MicrocellScale.Dominates
      (fun N => (C.parameters.H N l : ℝ))
      (fun N => ((P.pool N l).upper + masterScaleV C.parameters N l : ℝ))
  gap_modulus_divides : ∀ N l, C.parameters.M N ∣ C.parameters.H N l
  earlier_gaps_divide : ∀ N (i j : Fin n), i < j →
    C.parameters.H N i ∣ C.parameters.H N j
  polynomial_values_divide_gap : ∀ N l (p : Fin m → ℕ) (Q : IntegerPolynomial m),
    Q ∈ D →
    (∀ i, (P.pool N l).lower ≤ p i ∧ p i < (P.pool N l).upper ∧ (p i).Prime) →
    evalIntegerPolynomial Q (fun i => (p i : ℤ)) ≠ 0 →
    C.parameters.M N * (evalIntegerPolynomial Q (fun i => (p i : ℤ))).natAbs ∣
      C.parameters.H N l
  raw_cutoff_log_dominates_gap : ∀ l,
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (C.parameters.X N l : ℝ))
      (fun N => (C.parameters.H N l : ℝ))
  coefficient_divides_modulus : ∀ᶠ N in atTop, ∀ r (chain : MasterChain n r)
      (a : Fin r → ℚ), (∀ d, a d ∈ Aset) → ∀ c : Fin r → ℤ,
    (∀ d, (c d : ℚ) =
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (C.parameters.ht N) (chain.block d).set : ℚ) * a d) →
    ∀ d, ((primorial (N + 1) ^ (P.e0 N + 1) : ℕ) : ℤ) * c d ∣
      (C.parameters.M N : ℤ)
  valid_raw_cutoffs : ∀ N l,
    4 * primorial (N + 1) ≤ C.parameters.X N l

/-- Complete sequential master-scale data: an OAI admissible family plus the stronger
prime-pool and divisibility certificates required in §3. -/
structure MasterScales (n : ℕ) (Aset : Finset ℚ) (m : ℕ)
    (D : Finset (IntegerPolynomial m)) where
  core : MasterScaleCore n Aset
  primeStage : MasterScalePrimeStage core m D
  gapStage : MasterScaleGapStage core primeStage

/-- Copy of `HindmanSumsProducts.lem_master_scales` (`Arithmetic/MasterScales.lean`), Lemma
`lem:master-scales` (§3 lines 197–316); same statement as on `main` (`1e75bc3`). -/
theorem lem_master_scales (n : ℕ) (Aset : Finset ℚ)
    (hA : ∀ a ∈ Aset, 0 < a) (m : ℕ)
    (D : Finset (IntegerPolynomial m)) (hD : ∀ P ∈ D, P ≠ 0) :
    Nonempty (MasterScales n Aset m D) := by
  rcases HindmanSumsProducts.lem_master_scales n Aset hA m D hD with ⟨S⟩
  let C : MasterScaleCore n Aset :=
    { parameters := S.core.parameters
      height_formula := S.core.height_formula
      modulus_power := S.core.modulus_power
      adding_pair_ratio := S.core.adding_pair_ratio
      chain_coefficients := S.core.chain_coefficients }
  let P : MasterScalePrimeStage C m D :=
    { e0 := S.primeStage.e0
      pool := S.primeStage.pool
      e0_pos := S.primeStage.e0_pos
      uniform_small_prime_exception := S.primeStage.uniform_small_prime_exception
      pool_lower_dominates := S.primeStage.pool_lower_dominates
      pool_harmonic_mass_dominates := S.primeStage.pool_harmonic_mass_dominates
      pool_residue_error := S.primeStage.pool_residue_error
      actual_small_prime_exception := S.primeStage.actual_small_prime_exception
      zero_and_repeat_probability := S.primeStage.zero_and_repeat_probability }
  have G : MasterScaleGapStage C P :=
    { gap_dominates_pool_and_bound := S.gapStage.gap_dominates_pool_and_bound
      gap_modulus_divides := S.gapStage.gap_modulus_divides
      earlier_gaps_divide := S.gapStage.earlier_gaps_divide
      polynomial_values_divide_gap := S.gapStage.polynomial_values_divide_gap
      raw_cutoff_log_dominates_gap := S.gapStage.raw_cutoff_log_dominates_gap
      coefficient_divides_modulus := S.gapStage.coefficient_divides_modulus
      valid_raw_cutoffs := S.gapStage.valid_raw_cutoffs }
  exact ⟨{ core := C, primeStage := P, gapStage := G }⟩

/-! ## `Arithmetic/LinearForms.lean`

Copies of `rationalResidue`, `DivisorTemplate`, `divisorTemplateLaw`, `CRTPrimeRange`,
`CRTResidues`, `integerCRTResidues`, `primeTupleCRTLaw`, `uniformPrimeTupleCRTLaw`,
`integerResidue`, `baseResidueLaw` and `uniformBaseResidueLaw` (same definitions as on `main`),
then the data, average and statement of Proposition `prop:linear-forms`, which differ from `main`
(see `WeightedLinearFormsData`). -/

section LinearForms
attribute [local instance] Classical.propDecidable

/-- Reduction of a rational coefficient modulo a prime where its denominator is a unit. -/
noncomputable def rationalResidue (p : ℕ) (hp : p.Prime) (r : ℚ) : ZMod p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact (r.num : ZMod p) / (r.den : ZMod p)

/-- A product of at most b independent raw harmonic W-unit variables, identified by their
master cutoffs. -/
structure DivisorTemplate (n b : ℕ) where
  arity : ℕ
  arity_le : arity ≤ b
  cutoff : Fin arity → Fin n

/-- Divisor law for one fresh occurrence of a weight, at the parameter cutoffs. -/
def divisorTemplateLaw {n b : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (D : DivisorTemplate n b) (σ : ℕ) : ℝ :=
  harmonicProductLaw (primorial (N + 1))
    (fun i => A.X N (D.cutoff i)) σ

/-- CRT residue vectors for all primes `w<p≤V`, with residues in their prime fields. -/
abbrev CRTPrimeRange (w V : ℕ) :=
  {p : ℕ // p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime}

/-- Residues modulo each prime in the CRT range. -/
abbrev CRTResidues (w V : ℕ) := ∀ p : CRTPrimeRange w V, Fin p.val

/-- CRT residue tuple of one integer. -/
noncomputable def integerCRTResidues (w V x : ℕ) : CRTResidues w V := by
  intro p
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  exact ⟨x % p.val, Nat.mod_lt _ hp.pos⟩

/-- Actual joint CRT law of independent prime slots from their assigned pools. -/
def primeTupleCRTLaw {m : ℕ} (lo hi : Fin m → ℕ) (w V : ℕ)
    (r : Fin m → CRTResidues w V) : ℝ :=
  ∑' p : Fin m → ℕ,
    independentPrimePoolMass lo hi p *
      if (fun i => integerCRTResidues w V (p i)) = r then 1 else 0

/-- Independent uniform unit law on all slot-prime CRT coordinates. -/
def uniformPrimeTupleCRTLaw {m : ℕ} (w V : ℕ)
    (r : Fin m → CRTResidues w V) : ℝ :=
  ∏ i, ∏ p : CRTPrimeRange w V,
    if Nat.Coprime (r i p).val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0

/-- Integer residue in `Fin K`, using Euclidean remainder for signed base variables. -/
def integerResidue (K : ℕ) (hK : 0 < K) (z : ℤ) : Fin K := by
  have hKz : (0 : ℤ) < (K : ℤ) := by exact_mod_cast hK
  have hz0 : 0 ≤ z % (K : ℤ) := Int.emod_nonneg z (Int.ne_of_gt hKz)
  have hzlt : z % (K : ℤ) < (K : ℤ) := Int.emod_lt_of_pos z hKz
  refine ⟨(z % (K : ℤ)).toNat, ?_⟩
  have hcast : (((z % (K : ℤ)).toNat : ℕ) : ℤ) = z % (K : ℤ) :=
    Int.toNat_of_nonneg hz0
  exact Nat.cast_lt.mp (by rw [hcast]; exact hzlt)

/-- Conditional residue mass of the base variables modulo a divisor product. -/
def baseResidueLaw {d : ℕ} (K : ℕ) (hK : 0 < K)
    (baseMass : (Fin d → ℤ) → ℝ) (r : Fin d → Fin K) : ℝ :=
  ∑' x : Fin d → ℤ,
    baseMass x * if (fun i => integerResidue K hK (x i)) = r then 1 else 0

/-- Uniform law on all residue vectors modulo K. -/
def uniformBaseResidueLaw (K d : ℕ) (_r : Fin d → Fin K) : ℝ :=
  1 / (K : ℝ) ^ d

/-- Value of the row `ℓ_u(x;p)=∑_j a_{u,j}(N,p) x_j` with rational coefficients. -/
def linearRowValue {q d s : ℕ} (rowCoeff : ℕ → (Fin s → ℕ) → Fin q → Fin d → ℚ)
    (N : ℕ) (p : Fin s → ℕ) (u : Fin q) (x : Fin d → ℤ) : ℚ :=
  ∑ j, rowCoeff N p u j * (x j : ℚ)

/-- Data and hypotheses of Proposition `prop:linear-forms` (§3 lines 463–519).

Copy of `HindmanSumsProducts.WeightedLinearFormsData` (`Arithmetic/LinearForms.lean`) that
**differs from `main`**: the field `row : Fin q → RationalLinearRow d m` (fixed polynomial
coefficients in the prime slots) is replaced by `rowCoeff`, coefficients depending on `N` and on
the prime tuple, as in the paper's `ℓ_u(x;p)`. §4 needs this: its rows have the coefficients
`(c_k/c_{a(R)})A_{R,k}(p)`, where the scale ratios `c_k/c_{a(R)}` change with `N`, and the
responses `ℓ_I(v_R)` contain `M(p)=M|D(p)|_{>w}`, which is not a polynomial in `p`
(04:337–354, 483–507; 03:681–689). The field names `row_integer_on_support`,
`row_denominators_are_units`, `row_primitive` and `pairwise_row_tests` keep their meaning with
`rowCoeff` in place of `row`; all other fields are as on `main`. -/
structure WeightedLinearFormsData {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    (S : MasterScales n Aset m tests) where
  gap : Fin m → Fin n
  rowCoeff : ℕ → (Fin m → ℕ) → Fin q → Fin d → ℚ
  divisor : Fin q → DivisorTemplate n b
  V : ℕ → ℕ
  epsilonBase : ℕ → ℝ
  epsilonCRT : ℕ → ℝ
  baseMass : ℕ → (Fin m → ℕ) → (Fin d → ℤ) → ℝ
  goodDomain : ℕ → (Fin m → ℕ) → Prop
  epsilonBase_nonnegative : ∀ N, 0 ≤ epsilonBase N
  V_lower : ∀ N, S.core.parameters.M N ≤ V N
  V_tendsto : Tendsto (fun N => V N) atTop atTop
  slot_gap_bound : ∀ N i, V N ≤ masterScaleV S.core.parameters N (gap i)
  base_nonnegative : ∀ N p x, 0 ≤ baseMass N p x
  base_normalized : ∀ N p, ∑' x : Fin d → ℤ, baseMass N p x = 1
  divisor_positive : ∀ N u σ, divisorTemplateLaw S.core.parameters N (divisor u) σ ≠ 0 → 1 ≤ σ
  divisor_bounded : ∀ N u σ,
    divisorTemplateLaw S.core.parameters N (divisor u) σ ≠ 0 → σ ≤ V N
  base_residue_uniform : ∀ N p (σ : Fin q → ℕ),
    goodDomain N p →
    (∀ u, divisorTemplateLaw S.core.parameters N (divisor u) (σ u) ≠ 0) →
    (hσ : ∀ u, 0 < σ u) →
    finiteL1
      (baseResidueLaw (∏ u, σ u) (by exact Finset.prod_pos fun u _ => hσ u)
        (baseMass N p))
      (uniformBaseResidueLaw (∏ u, σ u) d) ≤ epsilonBase N
  row_integer_on_support : ∀ N p x, goodDomain N p → baseMass N p x ≠ 0 →
    ∀ u, (linearRowValue rowCoeff N p u x).den = 1
  row_denominators_are_units : ∀ N p, goodDomain N p → ∀ r (_hr : r.Prime),
    N + 1 < r → r ≤ V N → ∀ u j, Nat.Coprime (rowCoeff N p u j).den r
  row_primitive : ∀ N p, goodDomain N p → ∀ r (hr : r.Prime),
    N + 1 < r → r ≤ V N → ∀ u, ∃ j, rationalResidue r hr (rowCoeff N p u j) ≠ 0
  pairwise_row_tests : ∀ N p, goodDomain N p → ∀ r (hr : r.Prime),
    N + 1 < r → r ≤ V N →
      (∀ Q ∈ tests, ¬ ((r : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
      ∀ u v, u ≠ v → ∃ i j,
        rationalResidue r hr (rowCoeff N p u i) * rationalResidue r hr (rowCoeff N p v j) ≠
          rationalResidue r hr (rowCoeff N p u j) * rationalResidue r hr (rowCoeff N p v i)
  crt_error_bound : ∀ N,
    finiteL1
      (primeTupleCRTLaw
        (fun i => (S.primeStage.pool N (gap i)).lower)
        (fun i => (S.primeStage.pool N (gap i)).upper) (N + 1) (V N))
      (uniformPrimeTupleCRTLaw (N + 1) (V N)) ≤ epsilonCRT N
  epsilonBase_superpolynomial : SuperPolynomialSmall epsilonBase (fun N => (V N : ℝ))
  epsilonCRT_superpolynomial : SuperPolynomialSmall epsilonCRT (fun N => (V N : ℝ))

/-- Copy of `HindmanSumsProducts.weightedLinearFormsAverage`, differing from `main` only through
`linearRowValue D.rowCoeff` in place of `rationalRowIntegerValue (D.row u)`: the `ν`-weighted
row average over a prime-only event. -/
def weightedLinearFormsAverage {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (E : (Fin m → ℕ) → Prop) : ℝ :=
  ∑' p : Fin m → ℕ,
    independentPrimePoolMass
      (fun i => (S.primeStage.pool N (D.gap i)).lower)
      (fun i => (S.primeStage.pool N (D.gap i)).upper) p *
      (if E p then 1 else 0) *
      (∑' x : Fin d → ℤ,
        D.baseMass N p x *
          ∏ u, nuB
            (divisorTemplateLaw S.core.parameters N (D.divisor u))
            (linearRowValue D.rowCoeff N p u x).num)

/-- Copy of `HindmanSumsProducts.weightedLinearFormsEventProbability`, same definition. -/
def weightedLinearFormsEventProbability {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (E : (Fin m → ℕ) → Prop) : ℝ :=
  independentPrimePoolProbability
    (fun i => (S.primeStage.pool N (D.gap i)).lower)
    (fun i => (S.primeStage.pool N (D.gap i)).upper) E

/-- Proposition `prop:linear-forms` (§3 lines 463–519): the weighted product of divisor weights
has mean `P(E)` up to the absolute error `O(1/w + V^q(ε_base+ε_CRT))`, uniformly over prime-only
events `E ⊆ G`. Copy of `HindmanSumsProducts.prop_linear_forms`; the conclusion is the same text
as on `main`, but it is about the generalized data above, so it **differs from `main`** in
strength: rows may depend on `N` and on the prime tuple, as in the paper. -/
theorem prop_linear_forms {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) :
    ∃ C : ℝ, 0 < C ∧ ∀ N (E : (Fin m → ℕ) → Prop),
      (∀ p, E p → D.goodDomain N p) →
      |weightedLinearFormsAverage D N E - weightedLinearFormsEventProbability D N E| ≤
        C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ q *
          (D.epsilonBase N + D.epsilonCRT N)) := by
  let core : HindmanSumsProducts.MasterScaleCore n Aset :=
    { parameters := S.core.parameters
      height_formula := S.core.height_formula
      modulus_power := S.core.modulus_power
      adding_pair_ratio := S.core.adding_pair_ratio
      chain_coefficients := S.core.chain_coefficients }
  let primeStage : HindmanSumsProducts.MasterScalePrimeStage core m tests :=
    { e0 := S.primeStage.e0
      pool := S.primeStage.pool
      e0_pos := S.primeStage.e0_pos
      uniform_small_prime_exception := S.primeStage.uniform_small_prime_exception
      pool_lower_dominates := S.primeStage.pool_lower_dominates
      pool_harmonic_mass_dominates := S.primeStage.pool_harmonic_mass_dominates
      pool_residue_error := S.primeStage.pool_residue_error
      actual_small_prime_exception := S.primeStage.actual_small_prime_exception
      zero_and_repeat_probability := S.primeStage.zero_and_repeat_probability }
  have gapStage : HindmanSumsProducts.MasterScaleGapStage core primeStage :=
    { gap_dominates_pool_and_bound := S.gapStage.gap_dominates_pool_and_bound
      gap_modulus_divides := S.gapStage.gap_modulus_divides
      earlier_gaps_divide := S.gapStage.earlier_gaps_divide
      polynomial_values_divide_gap := S.gapStage.polynomial_values_divide_gap
      raw_cutoff_log_dominates_gap := S.gapStage.raw_cutoff_log_dominates_gap
      coefficient_divides_modulus := S.gapStage.coefficient_divides_modulus
      valid_raw_cutoffs := S.gapStage.valid_raw_cutoffs }
  let scales : HindmanSumsProducts.MasterScales n Aset m tests :=
    { core := core, primeStage := primeStage, gapStage := gapStage }
  let data : HindmanSumsProducts.WeightedLinearFormsData (q := q) (d := d) (b := b) scales :=
    { gap := D.gap
      rowCoeff := D.rowCoeff
      divisor := fun u =>
        { arity := (D.divisor u).arity
          arity_le := (D.divisor u).arity_le
          cutoff := (D.divisor u).cutoff }
      V := D.V
      epsilonBase := D.epsilonBase
      epsilonCRT := D.epsilonCRT
      baseMass := D.baseMass
      goodDomain := D.goodDomain
      epsilonBase_nonnegative := D.epsilonBase_nonnegative
      V_lower := D.V_lower
      V_tendsto := D.V_tendsto
      slot_gap_bound := D.slot_gap_bound
      base_nonnegative := D.base_nonnegative
      base_normalized := D.base_normalized
      divisor_positive := D.divisor_positive
      divisor_bounded := D.divisor_bounded
      base_residue_uniform := D.base_residue_uniform
      row_integer_on_support := D.row_integer_on_support
      row_denominators_are_units := D.row_denominators_are_units
      row_primitive := D.row_primitive
      pairwise_row_tests := D.pairwise_row_tests
      crt_error_bound := D.crt_error_bound
      epsilonBase_superpolynomial := D.epsilonBase_superpolynomial
      epsilonCRT_superpolynomial := D.epsilonCRT_superpolynomial }
  have hAverage (N : ℕ) (E : (Fin m → ℕ) → Prop) :
      HindmanSumsProducts.weightedLinearFormsAverage data N E =
        weightedLinearFormsAverage D N E := by
    rfl
  have hProbability (N : ℕ) (E : (Fin m → ℕ) → Prop) :
      HindmanSumsProducts.weightedLinearFormsEventProbability data N E =
        weightedLinearFormsEventProbability D N E := by
    rfl
  rcases HindmanSumsProducts.prop_linear_forms data with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N E hE
  have hE' : ∀ p, E p → data.goodDomain N p := by
    simpa [data] using hE
  have h := hbound N E hE'
  rw [← hAverage N E, ← hProbability N E]
  exact h

end LinearForms

end
end HindmanSumsProducts.FromArithmetic
