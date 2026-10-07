import HindmanSumsProducts.Prediction.Subgroup
import OAI.Combinatorics.SumProduct.Alignment.ProductExposure03

/-! Helper lemmas for the §5 proof package S5-H (owned by its proof lane). -/

open Filter
open MeasureTheory
open scoped Topology

namespace HindmanSumsProducts.Prediction

noncomputable section

/-- A positive denominator can be decreased in a domination estimate. -/
theorem dominates_of_le_denominator {f S T : ℕ → ℝ}
    (h : OAI.MicrocellScale.Dominates f S)
    (hT : ∀ N, 0 < T N) (hTS : ∀ N, T N ≤ S N)
    (hf : ∀ᶠ N in atTop, 0 ≤ f N) :
    OAI.MicrocellScale.Dominates f T := by
  intro C hC
  have hratio : ∀ᶠ N in atTop, f N / S N ^ C ≤ f N / T N ^ C := by
    filter_upwards [hf] with N hN
    have hp := Real.rpow_le_rpow (le_of_lt (hT N)) (hTS N) hC.le
    exact div_le_div_of_nonneg_left hN (Real.rpow_pos_of_pos (hT N) C) hp
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [(h C hC).eventually_gt_atTop b, hratio] with N hN hr
  exact (le_of_lt hN).trans hr

/-- Images of the added-block relation under a strictly increasing embedding. -/
theorem added_map_strictMono {n k : ℕ} (f : Fin n → Fin k) (hf : StrictMono f)
    {i : Fin n} {T S : Finset (Fin n)}
    (h : OAI.SourceBlocks.Added i T S) :
    OAI.SourceBlocks.Added (f i) (T.map ⟨f, hf.injective⟩) (S.map ⟨f, hf.injective⟩) := by
  obtain ⟨P, j, hP, hPT, hTj, hji, rfl⟩ := h
  let e : Fin n ↪ Fin k := ⟨f, hf.injective⟩
  refine ⟨P.map e, f j, ?_, ?_, ?_, hf hji, ?_⟩
  · obtain ⟨p, hp⟩ := hP
    exact ⟨f p, Finset.mem_map.mpr ⟨p, hp, rfl⟩⟩
  · intro p hp t ht
    rcases Finset.mem_map.mp hp with ⟨p', hp', rfl⟩
    rcases Finset.mem_map.mp ht with ⟨t', ht', rfl⟩
    exact hf (hPT p' hp' t' ht')
  · intro t ht
    rcases Finset.mem_map.mp ht with ⟨t', ht', rfl⟩
    exact hf (hTj t' ht')
  · simp [e]

/-- Reindexing the coordinates in a height agrees with mapping its finite support. -/
theorem height_map_embedding {n k : ℕ} (f : Fin n ↪ Fin k) (h : Fin k → ℤ)
    (S : Finset (Fin n)) :
    OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (fun i => h (f i)) S =
      OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height h (S.map f) := by
  simp [OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height,
    Finset.prod_map]

private theorem nat_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc
        k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ k * 2 := by
          have hp : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_two_pow (n := k)
          nlinarith [hp]

/-- Repair the finite initial cutoff exceptions of an admissible parameter sequence. -/
theorem parameters_allRawCutoffs_eventually_eq {n : ℕ} (A : Parameters n) :
    ∃ Aplus : Parameters n, (∀ N i, 4 * primorial (N + 1) ≤ Aplus.X N i) ∧
      ∀ᶠ N in atTop, Aplus.X N = A.X N := by
  classical
  let Xplus : ℕ → Fin n → ℕ := fun N i =>
    if h : ∀ j, 4 * primorial (N + 1) ≤ A.X N j then A.X N i
    else 2 ^ (4 * primorial (N + 1))
  have hcutEvent : ∀ᶠ N in atTop,
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        4 * primorial (N + 1) ≤ A.X N i := by
    apply (eventually_all_finset (Finset.univ : Finset (Fin n))).2
    intro i hi
    exact A.eventual_X i
  have hXeq : ∀ᶠ N in atTop, Xplus N = A.X N := by
    filter_upwards [hcutEvent] with N hN
    have hcut : ∀ i, 4 * primorial (N + 1) ≤ A.X N i := fun i =>
      hN i (Finset.mem_univ i)
    funext i
    simp [Xplus, hcut]
  have hcutPlus (N : ℕ) (i : Fin n) : 4 * primorial (N + 1) ≤ Xplus N i := by
    dsimp [Xplus]
    split_ifs with h
    · exact h i
    · exact nat_le_two_pow _
  let Aplus : Parameters n := {
    M := A.M
    ht := A.ht
    H := A.H
    X := Xplus
    Mpos := A.Mpos
    htpos := A.htpos
    Hpos := A.Hpos
    Xpow := by
      intro N i
      by_cases h : ∀ j, 4 * primorial (N + 1) ≤ A.X N j
      · dsimp [Xplus]
        rw [if_pos h]
        exact A.Xpow N i
      · exact ⟨4 * primorial (N + 1), by simp [Xplus, h]⟩
    Msmooth := A.Msmooth
    htsmooth := A.htsmooth
    Mdiv := A.Mdiv
    htdiv := A.htdiv
    singleton_bound := A.singleton_bound
    block_bound := A.block_bound
    ratio := A.ratio
    Hdiv := A.Hdiv
    Hdom := by
      intro i
      intro C hC
      have hprev : ∀ᶠ N in atTop,
          OAI.SourceAdmissible.previous (Xplus N) i =
            OAI.SourceAdmissible.previous (A.X N) i := by
        filter_upwards [hXeq] with N hN
        rw [hN]
      have hscale : ∀ᶠ N in atTop,
          OAI.AdmissibleMicrocellBoundary.earlierScale A.M
              (fun N => OAI.SourceAdmissible.previous (Xplus N) i) N =
            OAI.AdmissibleMicrocellBoundary.earlierScale A.M
              (fun N => OAI.SourceAdmissible.previous (A.X N) i) N := by
        filter_upwards [hprev] with N hN
        simp [OAI.AdmissibleMicrocellBoundary.earlierScale, hN]
      have hratio : ∀ᶠ N in atTop,
          (A.H N i : ℝ) /
              (OAI.AdmissibleMicrocellBoundary.earlierScale A.M
                (fun N => OAI.SourceAdmissible.previous (A.X N) i) N) ^ C =
            (A.H N i : ℝ) /
              (OAI.AdmissibleMicrocellBoundary.earlierScale A.M
                (fun N => OAI.SourceAdmissible.previous (Xplus N) i) N) ^ C := by
        filter_upwards [hscale] with N hN
        rw [← hN]
      apply (A.Hdom i C hC).congr'
      exact hratio
    Xdom := by
      intro i
      intro C hC
      have hratio : ∀ᶠ N in atTop,
          Real.log (A.X N i : ℝ) / (A.H N i : ℝ) ^ C =
            Real.log (Xplus N i : ℝ) / (A.H N i : ℝ) ^ C := by
        filter_upwards [hXeq] with N hN
        rw [← hN]
      apply (A.Xdom i C hC).congr'
      exact hratio }
  refine ⟨Aplus, ?_, ?_⟩
  · intro N i
    exact hcutPlus N i
  · exact hXeq

/-- An eventual denominator bound preserves domination. -/
theorem dominates_of_eventually_le_denominator {f S T : ℕ → ℝ}
    (h : OAI.MicrocellScale.Dominates f S)
    (hf : ∀ᶠ N in atTop, 0 ≤ f N)
    (hT : ∀ᶠ N in atTop, 0 < T N)
    (hTS : ∀ᶠ N in atTop, T N ≤ S N) :
    OAI.MicrocellScale.Dominates f T := by
  intro C hC
  have hlim := h C hC
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [hlim.eventually_gt_atTop b, hf, hT, hTS]
    with N hN hfN hTN hle
  have hp := Real.rpow_le_rpow (le_of_lt hTN) hle hC.le
  exact (le_of_lt hN).trans
    (div_le_div_of_nonneg_left hfN (Real.rpow_pos_of_pos hTN C) hp)

/-- `rationalModelValue` is exactly `atQ` of the integer model. -/
theorem rationalModelValue_eq_atQ {n r s : ℕ}
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {Fm : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r Fm)
    (N : ℕ) (B : FrameworkBlock n) (v : ℚ) (c : Fin r) (q : ℚ) :
    rationalModelValue S N B v c q = atQ (fun y => S.model N B v c y) q := by
  classical
  by_cases hq : ∃ z : ℤ, (z : ℚ) = q
  · have hden : q.den = 1 := by
      obtain ⟨z, hz⟩ := hq
      rw [← hz]
      simp
    have hqCast : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hden
    have hnum : Classical.choose hq = q.num := by
      exact Int.cast_injective ((Classical.choose_spec hq).trans hqCast.symm)
    simp [rationalModelValue, atQ, hq, hden, hnum]
  · have hden : q.den ≠ 1 := by
      intro hd
      apply hq
      exact ⟨q.num, (Rat.den_eq_one_iff q).mp hd⟩
    simp [rationalModelValue, atQ, hq, hden]

/-- Extension by zero preserves the unit interval bound on an integer family. -/
theorem atQ_mem_Icc_of_mem (f : ℤ → ℝ) (q : ℚ)
    (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1) : atQ f q ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold atQ
  split_ifs with hq
  · exact hf q.num
  · norm_num

/-- The raw harmonic weights are nonnegative, including when the interval is empty. -/
theorem harmonicNatLaw_nonneg (X W n : ℕ) : 0 ≤ harmonicNatLaw X W n := by
  have hnorm : 0 ≤ harmonicNormalizer X W := by
    unfold harmonicNormalizer
    exact Finset.sum_nonneg fun j hj => div_nonneg (by norm_num) (by positivity)
  unfold harmonicNatLaw
  split_ifs with h
  · exact div_nonneg (by norm_num) (mul_nonneg (by positivity) hnorm)
  · positivity

/-- The tail-product mass induced by harmonic coordinates is nonnegative. -/
theorem parameterTailProductLaw_nonneg {n : ℕ} (A : Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (σ : ℕ) : 0 ≤ parameterTailProductLaw A N T σ := by
  unfold parameterTailProductLaw
  apply tsum_nonneg
  intro t
  apply mul_nonneg
  · split_ifs <;> positivity
  · exact Finset.prod_nonneg fun j hj => harmonicNatLaw_nonneg (A.X N j)
      (primorial (N + 1)) (t j)

/-- Nonnegative tail masses induce a nonnegative divisor weight. -/
theorem nuB_nonneg_of_nonneg (tailLaw : TailProductLaw) (hTail : ∀ σ, 0 ≤ tailLaw σ)
    (y : ℤ) : 0 ≤ nuB tailLaw y := by
  unfold nuB
  apply tsum_nonneg
  intro σ
  apply mul_nonneg
  · exact mul_nonneg (hTail σ) (by positivity)
  · split_ifs <;> positivity

/-- The divisor weights used by Prediction are nonnegative. -/
theorem nu_nonneg {n : ℕ} (A : Parameters n) (N : ℕ) (B : Block n) (y : ℤ) :
    0 ≤ nu A N B y := by
  exact nuB_nonneg_of_nonneg (parameterTailProductLaw A N B.2.val)
    (parameterTailProductLaw_nonneg A N B.2.val) y

/-- The correlation package's copied tail law is definitionally the §3 tail law. -/
@[simp] theorem fromArithmetic_parameterTailProductLaw_eq {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n)) (σ : ℕ) :
    FromArithmetic.parameterTailProductLaw A N T σ =
      HindmanSumsProducts.parameterTailProductLaw A N T σ := by
  rfl

@[simp] theorem fromArithmetic_parameterTailProductLaw_fun_eq {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n)) :
    FromArithmetic.parameterTailProductLaw A N T =
      HindmanSumsProducts.parameterTailProductLaw A N T := by
  funext σ
  rfl

/-- An atom of OpenAI's raw harmonic law is the explicit §3 harmonic weight. -/
theorem rawHarmonicLaw_atom {X W k : ℕ} (hW : 0 < W) (hX : 4 * W ≤ X)
    (hk : k ∈ OAI.RawHarmonicProbability.units X W) :
    (OAI.RawHarmonicProbability.law X W hW hX : Measure ℕ).real {k} =
      harmonicNatLaw X W k := by
  have hmass : OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W = harmonicNormalizer X W := by
    calc
      OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W =
          ∑ n ∈ OAI.RawHarmonicProbability.units X W, (n : ℝ)⁻¹ :=
        OAI.RawHarmonicProbability.mass_units X W
      _ = harmonicNormalizer X W := by
        simp [harmonicNormalizer, OAI.RawHarmonicProbability.units,
          Nat.coprime_comm, one_div]
  have hkIco : k ∈ Finset.Ico X (X ^ 2) :=
    (Finset.mem_filter.mp hk).1
  letI : DecidablePred (fun p : ℕ => p ∈ ({k} : Set ℕ)) :=
    fun p => Classical.propDecidable (p ∈ ({k} : Set ℕ))
  have hnum :
      (∑ p ∈ Finset.Ico X (X ^ 2),
        if W.Coprime p ∧ p ∈ ({k} : Set ℕ) then (p : ℝ)⁻¹ else 0) =
        (k : ℝ)⁻¹ := by
    rw [Finset.sum_eq_single k]
    · simp [Nat.coprime_comm, (Finset.mem_filter.mp hk).2]
    · intro n hn hnk
      simp [hnk]
    · intro hnot
      exact False.elim (hnot hkIco)
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have hXpos : 0 < X := by omega
    exact_mod_cast (lt_of_lt_of_le hXpos (Finset.mem_Ico.mp hkIco).1)
  have hnormpos : 0 < harmonicNormalizer X W := by
    have h := OAI.RawHarmonicProbability.mass_pos X W hW hX
    simpa [hmass] using h
  rw [OAI.RawHarmonicProbability.law_apply]
  calc
    (∑ p ∈ Finset.Ico X (X ^ 2),
        if W.Coprime p ∧ p ∈ ({k} : Set ℕ) then (p : ℝ)⁻¹ else 0) /
        OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W =
        ((k : ℝ)⁻¹) / harmonicNormalizer X W := by
          rw [hmass]
          congr 1
    _ = harmonicNatLaw X W k := by
      have hkvalid : X ≤ k ∧ k < X ^ 2 ∧ Nat.Coprime k W :=
        ⟨(Finset.mem_Ico.mp hkIco).1, (Finset.mem_Ico.mp hkIco).2,
          Nat.coprime_comm.mp (Finset.mem_filter.mp hk).2⟩
      unfold harmonicNatLaw
      rw [if_pos hkvalid]
      field_simp [ne_of_gt hkpos, ne_of_gt hnormpos]

/-- Integrating against a product of OAI's raw harmonic laws is a finite weighted sum. -/
theorem integral_outsideLaw_eq_sum {n : ℕ} (X : Fin n → ℕ) (W : ℕ)
    (hW : 0 < W) (hX : ∀ i, 4 * W ≤ X i) (f : (Fin n → ℕ) → ℝ) :
    ∫ t, f t ∂OAI.ProductExposureLaw.outsideLaw X W hW hX =
      ∑ t ∈ OAI.ProductExposureLaw.outsideDomain X W,
        (∏ i, harmonicNatLaw (X i) W (t i)) * f t := by
  classical
  let D := OAI.ProductExposureLaw.outsideDomain X W
  haveI : IsProbabilityMeasure (OAI.ProductExposureLaw.outsideLaw X W hW hX) :=
    OAI.ProductExposureLaw.outsideLaw_probability X W hW hX
  have hdom : ∀ᵐ t ∂OAI.ProductExposureLaw.outsideLaw X W hW hX, t ∈ D := by
    simpa [D] using OAI.ProductExposureLaw.outside_ae_domain X W hW hX
  have hint : Integrable f (OAI.ProductExposureLaw.outsideLaw X W hW hX) := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      (∑ t ∈ D, ‖f t‖) ?_
    filter_upwards [hdom] with t ht
    exact Finset.single_le_sum (f := fun t => ‖f t‖)
      (fun t ht => norm_nonneg _) ht
  have hatom (t : Fin n → ℕ) (ht : t ∈ D) :
      (OAI.ProductExposureLaw.outsideLaw X W hW hX).real {t} =
        ∏ i, harmonicNatLaw (X i) W (t i) := by
    rw [measureReal_def, OAI.ProductExposureLaw.outsideLaw, Measure.pi_singleton,
      ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact rawHarmonicLaw_atom hW (hX i)
      (Fintype.mem_piFinset.mp ht i)
  have hzero (t : Fin n → ℕ) (ht : t ∉ D) :
      (OAI.ProductExposureLaw.outsideLaw X W hW hX).real {t} • f t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ OAI.RawHarmonicProbability.units
        (X i) W := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hnull : (OAI.RawHarmonicProbability.law (X i) W hW (hX i) : Measure ℕ)
        {t i} = 0 := by
      have hae := OAI.ProductExposureLabels.law_ae_units (X i) W hW (hX i)
      rw [ae_iff, ← measureReal_eq_zero_iff] at hae
      have hsub : ({t i} : Set ℕ) ⊆ (OAI.RawHarmonicProbability.units (X i) W : Set ℕ)ᶜ := by
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact hi
      have hreal : ((OAI.RawHarmonicProbability.law (X i) W hW (hX i) : Measure ℕ).real
          ((OAI.RawHarmonicProbability.units (X i) W : Set ℕ)ᶜ)) = 0 := hae
      have hmeasure : (OAI.RawHarmonicProbability.law (X i) W hW (hX i) : Measure ℕ)
          ((OAI.RawHarmonicProbability.units (X i) W : Set ℕ)ᶜ) = 0 := by
        rw [← measureReal_eq_zero_iff]
        exact hreal
      exact measure_mono_null hsub hmeasure
    have hmass : (OAI.ProductExposureLaw.outsideLaw X W hW hX).real {t} = 0 := by
      rw [measureReal_def, OAI.ProductExposureLaw.outsideLaw, Measure.pi_singleton,
        ENNReal.toReal_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [hnull]
    simp [hmass]
  rw [MeasureTheory.integral_countable hint]
  rw [tsum_eq_sum (s := D) hzero]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hatom t ht]
  simp

/-- The preceding finite-sum identity for `Parameters.law`. -/
theorem integral_parameterLaw_eq_sum {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i)
    (f : (Fin n → ℕ) → ℝ) :
    ∫ t, f t ∂A.law N hX =
      ∑ t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)),
        (∏ i, harmonicNatLaw (A.X N i) (primorial (N + 1)) (t i)) * f t := by
  simpa [OAI.SourceAdmissible.Parameters.law] using
    integral_outsideLaw_eq_sum (A.X N) (primorial (N + 1)) (primorial_pos _) hX f

/-- The independent pivot marginals of `Parameters.law` form the corresponding raw product law. -/
theorem pivotMarginals_eq_outsideLaw {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i)
    (B : Fin m → OAI.SourceBlocks.Block n) :
    Measure.pi (fun d => Measure.map (fun t : Fin n → ℕ => t (B d).1) (A.law N hX)) =
      OAI.ProductExposureLaw.outsideLaw (fun d => A.X N (B d).1)
        (primorial (N + 1)) (primorial_pos _) (fun d => hX (B d).1) := by
  rw [OAI.ProductExposureLaw.outsideLaw]
  congr 1
  funext d
  unfold OAI.SourceAdmissible.Parameters.law OAI.ProductExposureLaw.outsideLaw
  exact (measurePreserving_eval _ (B d).1).map_eq

/-- The pivot-coordinate integral is the finite sum over their independent harmonic weights. -/
theorem integral_pivotMarginals_eq_sum {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i)
    (B : Fin m → OAI.SourceBlocks.Block n) (f : (Fin m → ℕ) → ℝ) :
    ∫ z, f z ∂Measure.pi
        (fun d => Measure.map (fun t : Fin n → ℕ => t (B d).1) (A.law N hX)) =
      ∑ z ∈ OAI.ProductExposureLaw.outsideDomain
        (fun d => A.X N (B d).1) (primorial (N + 1)),
        (∏ d, harmonicNatLaw (A.X N (B d).1) (primorial (N + 1)) (z d)) * f z := by
  rw [pivotMarginals_eq_outsideLaw]
  exact integral_outsideLaw_eq_sum _ _ (primorial_pos _) (fun d => hX (B d).1) f

/-- The signed vector of block products sampled from the ambient coordinates. -/
def blockProductTuple {n m : ℕ} (B : Fin m → FrameworkBlock n)
    (t : Fin n → ℕ) : Fin m → ℤ := fun d => Int.ofNat (∏ j ∈ (B d).set, t j)

/-- The joint block-product mass is the singleton mass of the pushforward by block products. -/
theorem parameterJointBlockProductMass_eq_map_real {n m : ℕ}
    (A : Parameters n) (N : ℕ) (B : Fin m → FrameworkBlock n)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) (z : Fin m → ℤ) :
    parameterJointBlockProductMass A N B hX z =
      (Measure.map (blockProductTuple B) (A.law N hX)).real {z} := by
  classical
  have hmeas : Measurable (blockProductTuple B) := measurable_of_countable _
  have hpre : {t : Fin n → ℕ | blockProductTuple B t = z} =
      {t | ∀ d, 0 ≤ z d ∧ (∏ j ∈ (B d).set, t j) = (z d).toNat} := by
    ext t
    constructor
    · intro h d
      have hEq : blockProductTuple B t d = z d := congrFun h d
      change Int.ofNat (∏ j ∈ (B d).set, t j) = z d at hEq
      refine ⟨?_, ?_⟩
      · rw [← hEq]
        exact Int.natCast_nonneg _
      · have htoNat := congrArg Int.toNat hEq
        change (∏ j ∈ (B d).set, t j) = (z d).toNat at htoNat
        exact htoNat
    · intro h
      apply funext
      intro d
      rcases h d with ⟨hd, hprod⟩
      dsimp [blockProductTuple]
      calc
        Int.ofNat (∏ j ∈ (B d).set, t j) = Int.ofNat ((z d).toNat) :=
          congrArg Int.ofNat hprod
        _ = z d := Int.natCast_toNat_eq_self.mpr hd
  have hpre' : blockProductTuple B ⁻¹' ({z} : Set (Fin m → ℤ)) =
      {t : Fin n → ℕ | ∀ d, 0 ≤ z d ∧ (∏ j ∈ (B d).set, t j) = (z d).toNat} := by
    ext t
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] using
      (Set.ext_iff.mp hpre t)
  unfold parameterJointBlockProductMass
  simp only [measureReal_def, Measure.map_apply hmeas (measurableSet_singleton z), hpre']

/-- Push an integrable countable-valued observable through its law and sum its singleton masses. -/
theorem integral_eq_tsum_map_real_singleton {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → ℝ)
    (hg : Integrable g (Measure.map f μ)) :
    ∫ x, g (f x) ∂μ = ∑' y, (Measure.map f μ).real {y} * g y := by
  have hstrong : StronglyMeasurable g := (measurable_of_countable _).stronglyMeasurable
  calc
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂Measure.map f μ :=
      (integral_map_of_stronglyMeasurable hf hstrong).symm
    _ = ∑' y, (Measure.map f μ).real {y} * g y := by
      rw [MeasureTheory.integral_countable hg]
      simp only [smul_eq_mul]

/-- The joint block-product distribution has finite support under the raw parameter law. -/
theorem parameterJointBlockProductMass_support_finite {n m : ℕ}
    (A : Parameters n) (N : ℕ) (B : Fin m → FrameworkBlock n)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) :
    {z : Fin m → ℤ | parameterJointBlockProductMass A N B hX z ≠ 0}.Finite := by
  classical
  let D := OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1))
  let S := D.image (blockProductTuple B)
  have hdom : ∀ᵐ t ∂A.law N hX, t ∈ D := by
    simpa [D, OAI.SourceAdmissible.Parameters.law] using
      OAI.ProductExposureLaw.outside_ae_domain (A.X N) (primorial (N + 1))
        (primorial_pos _) hX
  have hnull : (A.law N hX) {t | t ∉ D} = 0 := ae_iff.mp hdom
  have hmeas : Measurable (blockProductTuple B) := measurable_of_countable _
  have hzero (z : Fin m → ℤ) (hz : z ∉ S) :
      parameterJointBlockProductMass A N B hX z = 0 := by
    rw [parameterJointBlockProductMass_eq_map_real]
    rw [measureReal_def, Measure.map_apply hmeas (measurableSet_singleton z)]
    have hsub : blockProductTuple B ⁻¹' ({z} : Set (Fin m → ℤ)) ⊆ {t | t ∉ D} := by
      intro t ht
      intro htD
      apply hz
      apply Finset.mem_image.mpr
      exact ⟨t, htD, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using ht⟩
    have hmass := measure_mono_null hsub hnull
    simp [hmass]
  apply (Finset.finite_toSet S).subset
  intro z hz
  by_contra hzS
  exact hz (hzero z hzS)

/-- A bounded test function changes its expectation by at most the total-mass `l1` distance. -/
theorem abs_tsum_mul_sub_le_tsum_abs_diff {α : Type*} [DecidableEq α]
    (μ ν f : α → ℝ)
    (hμ : {x | μ x ≠ 0}.Finite) (hν : {x | ν x ≠ 0}.Finite)
    (hf : ∀ x, |f x| ≤ 1) :
    |(∑' x, μ x * f x) - ∑' x, ν x * f x| ≤ ∑' x, |μ x - ν x| := by
  classical
  let S : Finset α := hμ.toFinset ∪ hν.toFinset
  have hμzero (x : α) (hx : x ∉ S) : μ x = 0 := by
    by_contra hne
    have hmem : x ∈ hμ.toFinset := (Set.Finite.mem_toFinset hμ).mpr hne
    exact hx (Finset.mem_union_left _ hmem)
  have hνzero (x : α) (hx : x ∉ S) : ν x = 0 := by
    by_contra hne
    have hmem : x ∈ hν.toFinset := (Set.Finite.mem_toFinset hν).mpr hne
    exact hx (Finset.mem_union_right _ hmem)
  have htermμ (x : α) (hx : x ∉ S) : μ x * f x = 0 := by simp [hμzero x hx]
  have htermν (x : α) (hx : x ∉ S) : ν x * f x = 0 := by simp [hνzero x hx]
  have hterm (x : α) (hx : x ∉ S) : |μ x - ν x| = 0 := by
    simp [hμzero x hx, hνzero x hx]
  rw [tsum_eq_sum (s := S) htermμ, tsum_eq_sum (s := S) htermν,
    tsum_eq_sum (s := S) hterm]
  have hsum :
      (∑ x ∈ S, μ x * f x) - ∑ x ∈ S, ν x * f x =
        ∑ x ∈ S, (μ x - ν x) * f x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  calc
    |(∑ x ∈ S, μ x * f x) - ∑ x ∈ S, ν x * f x| =
        |∑ x ∈ S, (μ x - ν x) * f x| := by rw [hsum]
    _ ≤ ∑ x ∈ S, |(μ x - ν x) * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S, |μ x - ν x| := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        |(μ x - ν x) * f x| = |μ x - ν x| * |f x| := abs_mul _ _
        _ ≤ |μ x - ν x| * 1 := mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
        _ = |μ x - ν x| := mul_one _

/-- Projection of a finite product law onto an injective list of coordinates is the product law
on that list. -/
theorem parameterLaw_map_injective {K n : ℕ} (A : Parameters K) (A' : Parameters n)
    (N : ℕ) (prin : Fin n → Fin K) (hprin : Function.Injective prin)
    (hXeq : ∀ i, A'.X N i = A.X N (prin i))
    (hXA : ∀ j, 4 * primorial (N + 1) ≤ A.X N j)
    (hXA' : ∀ i, 4 * primorial (N + 1) ≤ A'.X N i) :
    Measure.map (fun t : Fin K → ℕ => fun i => t (prin i)) (A.law N hXA) =
      A'.law N hXA' := by
  classical
  let e : Fin n ↪ Fin K := ⟨prin, hprin⟩
  let P : Finset (Fin K) := Finset.univ.map e
  have hP (i : Fin n) : prin i ∈ P :=
    Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let f : Fin n → P := fun i => ⟨prin i, hP i⟩
  have hfInj : Function.Injective f := by
    intro i j hij
    exact hprin (congrArg Subtype.val hij)
  have hfSurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.2
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hij
  let eP : Fin n ≃ P := Equiv.ofBijective f ⟨hfInj, hfSurj⟩
  have hinvVal (j : P) : prin (eP.symm j) = j.1 := by
    have h := congrArg Subtype.val (eP.apply_symm_apply j)
    exact h
  have hinvPrin (i : Fin n) : eP.symm ⟨prin i, hP i⟩ = i := by
    apply eP.injective
    calc
      eP (eP.symm ⟨prin i, hP i⟩) = ⟨prin i, hP i⟩ := eP.apply_symm_apply _
      _ = eP i := by apply Subtype.ext; rfl
  let S : (Fin n → ℕ) → Fin K → Set ℕ := fun x j =>
    if hj : j ∈ P then {x (eP.symm ⟨j, hj⟩)} else Set.univ
  have hpre (x : Fin n → ℕ) :
      (fun t : Fin K → ℕ => fun i => t (prin i)) ⁻¹' {x} = Set.pi Set.univ (S x) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ]
    rw [funext_iff]
    constructor
    · intro h j
      by_cases hj : j ∈ P
      · have hv := hinvVal ⟨j, hj⟩
        simpa [S, hj, hv] using h (eP.symm ⟨j, hj⟩)
      · simp [S, hj]
    · intro h i
      have hpi := h (prin i)
      simpa [S, hP i, hinvPrin i] using hpi
  let μK : Fin K → Measure ℕ := fun j =>
    (OAI.RawHarmonicProbability.law (A.X N j) (primorial (N + 1))
      (primorial_pos _) (hXA j) : Measure ℕ)
  let μn : Fin n → Measure ℕ := fun i =>
    (OAI.RawHarmonicProbability.law (A'.X N i) (primorial (N + 1))
      (primorial_pos _) (hXA' i) : Measure ℕ)
  have hsel (x : Fin n → ℕ) :
      (∏ j ∈ P, μK j (S x j)) =
        ∏ i, μK (prin i) {x i} := by
    symm
    apply Finset.prod_bij (fun i _ => prin i)
    · intro i hi
      exact hP i
    · intro i hi j hj hEq
      exact hprin hEq
    · intro j hj
      obtain ⟨i, hi, hEq⟩ := Finset.mem_map.mp hj
      exact ⟨i, Finset.mem_univ i, hEq⟩
    · intro i hi
      simp [S, hP, hinvPrin]
  have hrest (j : Fin K) : μK j Set.univ = 1 := by
    dsimp [μK]
    exact MeasureTheory.measure_univ
  have hprod (x : Fin n → ℕ) :
      (∏ j, μK j (S x j)) = ∏ i, μn i {x i} := by
    calc
      (∏ j, μK j (S x j)) =
          (∏ j ∈ P, μK j (S x j)) *
            ∏ j ∈ Pᶜ, μK j Set.univ := by
        rw [← Finset.prod_mul_prod_compl P (fun j => μK j (S x j))]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        have hnot : j ∉ P := Finset.mem_compl.mp hj
        simp [S, hnot, hrest j]
      _ = (∏ i, μK (prin i) {x i}) * 1 := by
        have hcompl : ∏ j ∈ Pᶜ, μK j Set.univ = 1 := by
          apply Finset.prod_eq_one
          intro j hj
          exact hrest j
        rw [hcompl]
        congr 1
        simpa [S] using hsel x
      _ = ∏ i, μn i {x i} := by
        rw [mul_one]
        apply Finset.prod_congr rfl
        intro i hi
        simp [μK, μn, hXeq i]
  change Measure.map (fun t : Fin K → ℕ => fun i => t (prin i))
      (OAI.ProductExposureLaw.outsideLaw (A.X N) (primorial (N + 1))
        (primorial_pos _) hXA) =
    OAI.ProductExposureLaw.outsideLaw (A'.X N) (primorial (N + 1))
      (primorial_pos _) hXA'
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete, hpre]
  rw [OAI.ProductExposureLaw.outsideLaw, Measure.pi_pi]
  rw [OAI.ProductExposureLaw.outsideLaw, Measure.pi_singleton]
  exact hprod x

/-- The explicit harmonic weight vanishes outside the support of the raw law. -/
theorem harmonicNatLaw_zero_of_not_unit {X W k : ℕ}
    (hk : k ∉ OAI.RawHarmonicProbability.units X W) : harmonicNatLaw X W k = 0 := by
  by_cases h : X ≤ k ∧ k < X ^ 2 ∧ Nat.Coprime k W
  · exact False.elim (hk (Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, by
        simpa [Nat.coprime_comm] using h.2.2⟩))
  · simp [harmonicNatLaw, h]

/-- The tail-product law is a finite pushforward sum of the raw harmonic weights. -/
theorem parameterTailProductLaw_eq_sum {n : ℕ} (A : Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (σ : ℕ) :
    parameterTailProductLaw A N T σ =
      ∑ t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)),
        (if (∏ j ∈ T, t j) = σ then 1 else 0) *
          ∏ i, harmonicNatLaw (A.X N i) (primorial (N + 1)) (t i) := by
  classical
  let D := OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1))
  have hzero (t : Fin n → ℕ) (ht : t ∉ D) :
      (if (∏ j ∈ T, t j) = σ then 1 else 0) *
        ∏ i, harmonicNatLaw (A.X N i) (primorial (N + 1)) (t i) = 0 := by
    have hnot : ¬ ∀ i, t i ∈ OAI.RawHarmonicProbability.units
        (A.X N i) (primorial (N + 1)) := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hz := harmonicNatLaw_zero_of_not_unit hi
    have hprod : ∏ i, harmonicNatLaw (A.X N i) (primorial (N + 1)) (t i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hprod]
    simp
  unfold parameterTailProductLaw
  rw [tsum_eq_sum (s := D) hzero]

/-- Under the raw admissible law, a divisor weight is exactly the §3 tail-law weight. -/
theorem divisorWeightUnder_eq_nu {n : ℕ} (A : Parameters n) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) (B : FrameworkBlock n) (y : ℤ) :
    divisorWeightUnder (A.law N hX) B y = nu A N B y := by
  classical
  let D := OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1))
  let p : (Fin n → ℕ) → ℕ := fun t => ∏ j ∈ B.2.val, t j
  let S : Finset ℕ := D.image p
  have htailZero (σ : ℕ) (hσ : σ ∉ S) :
      parameterTailProductLaw A N B.2.val σ = 0 := by
    rw [parameterTailProductLaw_eq_sum]
    apply Finset.sum_eq_zero
    intro t ht
    have hne : p t ≠ σ := by
      intro heq
      exact hσ (Finset.mem_image.mpr ⟨t, ht, heq⟩)
    simp [p, hne]
  have hnuZero (σ : ℕ) (hσ : σ ∉ S) :
      parameterTailProductLaw A N B.2.val σ * (σ : ℝ) *
        (if (σ : ℤ) ∣ y then 1 else 0) = 0 := by
    simp [htailZero σ hσ]
  have htailExpansion (σ : ℕ) :
      parameterTailProductLaw A N B.2.val σ =
        ∑ t ∈ D, (if p t = σ then 1 else 0) *
          ∏ i, harmonicNatLaw (A.X N i) (primorial (N + 1)) (t i) := by
    simpa [D, p] using parameterTailProductLaw_eq_sum A N B.2.val σ
  rw [divisorWeightUnder, integral_parameterLaw_eq_sum]
  unfold nu nuB
  rw [tsum_eq_sum (s := S) hnuZero]
  simp_rw [htailExpansion]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p t ∈ S := Finset.mem_image.mpr ⟨t, ht, rfl⟩
  rw [Finset.sum_eq_single (p t)]
  · simp [p, tailValue]
  · intro σ hσ hne
    simp [hne, eq_comm]
  · intro hnot
    exact False.elim (hnot hpt)

/-- Divisor weights on a restricted block agree with the master weight on its mapped block. -/
theorem divisorWeightUnder_principal {K n : ℕ} (A : Parameters K) (A' : Parameters n)
    (N : ℕ) (prin : Fin n → Fin K) (hprin : Function.Injective prin)
    (hXeq : ∀ i, A'.X N i = A.X N (prin i))
    (hXA : ∀ j, 4 * primorial (N + 1) ≤ A.X N j)
    (hXA' : ∀ i, 4 * primorial (N + 1) ≤ A'.X N i)
    (B' : FrameworkBlock n) (B : FrameworkBlock K)
    (hTail : B.2.val = B'.2.val.map ⟨prin, hprin⟩) (y : ℤ) :
    divisorWeightUnder (A'.law N hXA') B' y = nu A N B y := by
  have hmap := parameterLaw_map_injective A A' N prin hprin hXeq hXA hXA'
  have htailValue (t : Fin K → ℕ) :
      tailValue B' (fun i => t (prin i)) = tailValue B t := by
    simp [HindmanSumsProducts.tailValue, hTail]
  have hstrong : StronglyMeasurable (fun t : Fin n → ℕ =>
      if (tailValue B' t : ℤ) ∣ y then (tailValue B' t : ℝ) else 0) :=
    (measurable_of_countable _).stronglyMeasurable
  change (∫ t, (if (tailValue B' t : ℤ) ∣ y then (tailValue B' t : ℝ) else 0)
      ∂A'.law N hXA') = nu A N B y
  rw [← hmap]
  rw [MeasureTheory.integral_map_of_stronglyMeasurable
    (measurable_of_countable _) hstrong]
  have hfun : (fun t : Fin K → ℕ =>
      if (tailValue B' (fun i => t (prin i)) : ℤ) ∣ y then
        (tailValue B' (fun i => t (prin i)) : ℝ) else 0) =
    fun t => if (tailValue B t : ℤ) ∣ y then (tailValue B t : ℝ) else 0 := by
    funext t
    rw [htailValue t]
  rw [hfun]
  change divisorWeightUnder (A.law N hXA) B y = nu A N B y
  exact divisorWeightUnder_eq_nu A N hXA B y

/-- The rational extension by zero of a restricted divisor weight agrees with `atQ` of the
master divisor weight. -/
theorem rationalDivisorWeightUnder_principal {K n : ℕ} (A : Parameters K)
    (A' : Parameters n) (N : ℕ) (prin : Fin n → Fin K)
    (hprin : Function.Injective prin) (hXeq : ∀ i, A'.X N i = A.X N (prin i))
    (hXA : ∀ j, 4 * primorial (N + 1) ≤ A.X N j)
    (hXA' : ∀ i, 4 * primorial (N + 1) ≤ A'.X N i)
    (B' : FrameworkBlock n) (B : FrameworkBlock K)
    (hTail : B.2.val = B'.2.val.map ⟨prin, hprin⟩) (q : ℚ) :
    rationalDivisorWeightUnder (A'.law N hXA') B' q = atQ (nu A N B) q := by
  classical
  by_cases hden : q.den = 1
  · have hqCast : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hden
    have hq : ∃ z : ℤ, (z : ℚ) = q := ⟨q.num, hqCast⟩
    unfold rationalDivisorWeightUnder
    rw [dif_pos hq]
    have hz : Classical.choose hq = q.num := by
      exact Int.cast_injective ((Classical.choose_spec hq).trans hqCast.symm)
    rw [hz, divisorWeightUnder_principal A A' N prin hprin hXeq hXA hXA' B' B hTail]
    simp [atQ, hden]
  · have hqNo : ¬ ∃ z : ℤ, (z : ℚ) = q := by
      rintro ⟨z, hz⟩
      apply hden
      rw [← hz]
      simp
    unfold rationalDivisorWeightUnder
    rw [dif_neg hqNo]
    simp [atQ, hden]

/-- The signed-integer pivot sum is the same finite sum as the raw natural pivot law. -/
theorem pivotMass_tsum_eq_nat_sum {n m : ℕ} (A : Parameters n)
    (C : MasterChain n m) (N : ℕ) (f : (Fin m → ℤ) → ℝ) :
    ∑' z : Fin m → ℤ, pivotMass A C N z * f z =
      ∑ t ∈ OAI.ProductExposureLaw.outsideDomain
        (fun d => A.X N (C.block d).1) (primorial (N + 1)),
        (∏ d, harmonicNatLaw (A.X N (C.block d).1) (primorial (N + 1)) (t d)) *
          f (fun d => (t d : ℤ)) := by
  classical
  let W := primorial (N + 1)
  let D : Finset (Fin m → ℕ) :=
    OAI.ProductExposureLaw.outsideDomain (fun d => A.X N (C.block d).1) W
  let castVec : (Fin m → ℕ) → (Fin m → ℤ) := fun t d => (t d : ℤ)
  let Dℤ := D.image castVec
  have hNatUnit (t : Fin m → ℕ) (ht : t ∈ D) (d : Fin m) :
      t d ∈ OAI.RawHarmonicProbability.units (A.X N (C.block d).1) W :=
    Fintype.mem_piFinset.mp ht d
  have hAtom (t : Fin m → ℕ) (ht : t ∈ D) (d : Fin m) :
      harmonicLaw (A.X N (C.block d).1) W (t d : ℤ) =
        harmonicNatLaw (A.X N (C.block d).1) W (t d) := by
    have hu := hNatUnit t ht d
    simp [harmonicLaw, harmonicNatLaw, hu]
  have hzero (z : Fin m → ℤ) (hz : z ∉ Dℤ) :
      pivotMass A C N z * f z = 0 := by
    by_cases hp : pivotMass A C N z = 0
    · simp [hp]
    · have hAll : ∀ d, harmonicLaw (A.X N (C.block d).1) W (z d) ≠ 0 := by
        intro d
        have hp' : ∏ d, harmonicLaw (A.X N (C.block d).1) W (z d) ≠ 0 := by
          simpa [pivotMass, W] using hp
        exact (Finset.prod_ne_zero_iff.mp hp') d (Finset.mem_univ d)
      have hcond (d : Fin m) :
          0 ≤ z d ∧ A.X N (C.block d).1 ≤ (z d).toNat ∧
            (z d).toNat < (A.X N (C.block d).1) ^ 2 ∧
              Nat.Coprime (z d).toNat W := by
        by_contra hn
        have hz0 : harmonicLaw (A.X N (C.block d).1) W (z d) = 0 := by
          simp [harmonicLaw, hn]
        exact hAll d hz0
      let t : Fin m → ℕ := fun d => (z d).toNat
      have ht : t ∈ D := Fintype.mem_piFinset.mpr fun d => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ?_, ?_⟩
        · exact ⟨(hcond d).2.1, (hcond d).2.2.1⟩
        · simpa [Nat.coprime_comm] using (hcond d).2.2.2
      have hcast : castVec t = z := by
        funext d
        exact Int.toNat_of_nonneg (hcond d).1
      exact False.elim (hz (Finset.mem_image.mpr ⟨t, ht, hcast⟩))
  have hinj : Function.Injective castVec := by
    intro t u h
    funext d
    have hd : (t d : ℤ) = (u d : ℤ) := by
      simpa [castVec] using congrFun h d
    exact_mod_cast hd
  have hsum :
      ∑ t ∈ D, (∏ d, harmonicNatLaw (A.X N (C.block d).1) W (t d)) *
        f (castVec t) =
      ∑ z ∈ Dℤ, pivotMass A C N z * f z := by
    apply Finset.sum_bij (fun t _ => castVec t)
    · intro t ht
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    · intro t ht u hu heq
      exact hinj heq
    · intro z hz
      rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    · intro t ht
      have hprod : pivotMass A C N (castVec t) =
          ∏ d, harmonicNatLaw (A.X N (C.block d).1) W (t d) := by
        unfold pivotMass
        apply Finset.prod_congr rfl
        intro d hd
        exact hAtom t ht d
      rw [hprod]
  rw [tsum_eq_sum (s := Dℤ) hzero]
  simpa [D, Dℤ, castVec, W] using hsum.symm

/-- The product over nonempty supports splits into singleton and nonsingleton factors. -/
theorem prod_nonempty_eq_singleton_nonsingleton {m : ℕ}
    (g : Finset (Fin m) → ℝ) :
    (∏ J ∈ Finset.univ.filter Finset.Nonempty, g J) =
      (∏ d : Fin m, g {d}) *
        ∏ J : NonsingletonSubsets m, g J.1 := by
  classical
  let E : Finset (Finset (Fin m)) := Finset.univ.filter Finset.Nonempty
  let Singles : Finset (Finset (Fin m)) := Finset.univ.image fun d : Fin m => ({d} : Finset (Fin m))
  let Nonsingles : Finset (Finset (Fin m)) := Finset.univ.filter (fun J => 2 ≤ J.card)
  have hpart : E = Singles ∪ Nonsingles := by
    ext J
    constructor
    · intro hJ
      have hnon : J.Nonempty := (Finset.mem_filter.mp hJ).2
      by_cases hcard : 2 ≤ J.card
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩))
      · have hcard1 : J.card = 1 := by
          have hpos : 0 < J.card := Finset.card_pos.mpr hnon
          omega
        obtain ⟨d, hEq⟩ := Finset.card_eq_one.mp hcard1
        subst J
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩))
    · intro hJ
      rcases Finset.mem_union.mp hJ with hS | hN
      · change J ∈ Finset.univ.image (fun d : Fin m => ({d} : Finset (Fin m))) at hS
        obtain ⟨d, hd, hEq⟩ := Finset.mem_image.mp hS
        subst J
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨d, Finset.mem_singleton_self d⟩⟩
      · change J ∈ Finset.univ.filter (fun J : Finset (Fin m) => 2 ≤ J.card) at hN
        have hcard : 2 ≤ J.card := (Finset.mem_filter.mp hN).2
        have hnon : J.Nonempty := Finset.card_pos.mp (by omega)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnon⟩
  have hdisj : Disjoint Singles Nonsingles := by
    apply Finset.disjoint_left.mpr
    intro J hS hN
    change J ∈ Finset.univ.image (fun d : Fin m => ({d} : Finset (Fin m))) at hS
    obtain ⟨d, hd, hEq⟩ := Finset.mem_image.mp hS
    change J ∈ Finset.univ.filter (fun J : Finset (Fin m) => 2 ≤ J.card) at hN
    have hcard : 2 ≤ J.card := (Finset.mem_filter.mp hN).2
    rw [← hEq] at hcard
    simp at hcard
  have hsingle :
      (∏ J ∈ Singles, g J) = ∏ d : Fin m, g {d} := by
    symm
    apply Finset.prod_bij (fun d _ => ({d} : Finset (Fin m)) )
    · intro d hd
      exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩
    · intro d hd d' hd' hEq
      exact Finset.singleton_injective hEq
    · intro J hJ
      change J ∈ Finset.univ.image (fun d : Fin m => ({d} : Finset (Fin m))) at hJ
      obtain ⟨d, hd, hEq⟩ := Finset.mem_image.mp hJ
      exact ⟨d, Finset.mem_univ d, hEq⟩
    · intro d hd
      rfl
  have hnonsingle :
      (∏ J ∈ Nonsingles, g J) = ∏ J : NonsingletonSubsets m, g J.1 := by
    exact Finset.prod_subtype Nonsingles (by
      intro J
      simp [Nonsingles, NonsingletonSubsets]) g
  calc
    (∏ J ∈ E, g J) = ∏ J ∈ Singles ∪ Nonsingles, g J := by rw [hpart]
    _ = (∏ J ∈ Singles, g J) * ∏ J ∈ Nonsingles, g J := Finset.prod_union hdisj
    _ = (∏ d : Fin m, g {d}) * ∏ J : NonsingletonSubsets m, g J.1 := by
      rw [hsingle, hnonsingle]

/-- `productMask` is the finite product over the nonempty supports. -/
theorem productMask_eq_filteredProduct {m r : ℕ} (χ : ℕ → Fin r) (c : Fin r)
    (coeff : Fin m → ℚ) (z : Fin m → ℕ) :
    productMask χ c coeff z =
      ∏ U ∈ Finset.univ.filter Finset.Nonempty,
        rationalColorIndicator χ c (∏ k ∈ U, coeff k * (z k : ℚ)) := by
  classical
  unfold productMask
  simpa [NonemptySubsets] using
    (Finset.prod_subtype (Finset.univ.filter Finset.Nonempty)
      (fun U => by simp) (fun U =>
        rationalColorIndicator χ c (∏ k ∈ U, coeff k * (z k : ℚ)))).symm

/-- `atQ` distributes a rational color factor into an integer-valued family. -/
theorem atQ_mul_rationalColorIndicator {r : ℕ} (ν : ℤ → ℝ)
    (χ : ℕ → Fin r) (c : Fin r) (a q : ℚ) :
    atQ (fun y => ν y * rationalColorIndicator χ c (a * (y : ℚ))) q =
      rationalColorIndicator χ c (a * q) * atQ ν q := by
  classical
  by_cases hq : q.den = 1
  · have hqCast : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hq
    simp [atQ, hq, hqCast]
    ring
  · simp [atQ, hq]

set_option maxHeartbeats 1000000 in
/-- The measure-form weighted integrand is the corresponding master correlation summand. -/
theorem weightedCountIntegrandUnder_eq_maskedCorrelationTerm
    {K n m r : ℕ} (A : Parameters K) (A' : Parameters n) (N : ℕ)
    (hXA : ∀ j, 4 * primorial (N + 1) ≤ A.X N j)
    (hXA' : ∀ i, 4 * primorial (N + 1) ≤ A'.X N i)
    (prin : Fin n → Fin K) (hprin : Function.Injective prin)
    (hXeq : ∀ i, A'.X N i = A.X N (prin i))
    (C : MasterChain K m) (B' : Fin m → FrameworkBlock n)
    (b : FrameworkScale n) (χ : ℕ → Fin r) (c : Fin r)
    (a : Fin m → ℚ)
    (hscale : ∀ d,
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A'.ht N) (B' d).set : ℚ) * blockScale b (B' d) = chainScale A C a N d)
    (hTail : ∀ d, (C.block d).2.val = (B' d).2.val.map ⟨prin, hprin⟩)
    (t : Fin m → ℕ) :
    weightedCountIntegrandUnder A' (A'.law N hXA') N χ c b B' t =
      (∏ U ∈ Finset.univ.filter Finset.Nonempty,
        countMask A χ C a N c U (∏ k ∈ U, (t k : ℤ))) *
      ∏ J ∈ Finset.univ.filter Finset.Nonempty,
        atQ (countFunctions A C a N c (rho A χ N) J)
          (chainForm (chainScale A C a N) J (fun k => (t k : ℤ))) := by
  classical
  let coeff' : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A'.ht N) (B' d).set : ℚ) * blockScale b (B' d)
  let coeff : Fin m → ℚ := chainScale A C a N
  let zInt : Fin m → ℤ := fun d => (t d : ℤ)
  let rootFactor : Finset (Fin m) → ℝ := fun J =>
    atQ (countFunctions A C a N c (rho A χ N) J) (chainForm coeff J zInt)
  let rootMask : ℝ := ∏ U ∈ Finset.univ.filter Finset.Nonempty,
    countMask A χ C a N c U (∏ k ∈ U, zInt k)
  let weightedNonsingle : NonsingletonSubsets m → ℝ := fun J => by
    have hJ : J.val.Nonempty := Finset.card_pos.mp
      (lt_of_lt_of_le (by decide) J.property)
    let d := J.val.max' hJ
    exact rationalColorIndicator χ c (coeff' d * sumForm coeff' J.val hJ t) *
      rationalDivisorWeightUnder (A'.law N hXA') (B' d) (sumForm coeff' J.val hJ t)
  change productMask χ c coeff' t *
      (∏ d, rationalDivisorWeightUnder (A'.law N hXA') (B' d) (t d : ℚ)) *
      (∏ J : NonsingletonSubsets m, weightedNonsingle J) =
    rootMask * ∏ U ∈ Finset.univ.filter Finset.Nonempty, rootFactor U
  have hcoeff (d : Fin m) : coeff' d = coeff d := hscale d
  have hArg (U : Finset (Fin m)) :
      (∏ k ∈ U, coeff' k * (t k : ℚ)) =
        (∏ k ∈ U, coeff k) * ((∏ k ∈ U, zInt k : ℤ) : ℚ) := by
    calc
      (∏ k ∈ U, coeff' k * (t k : ℚ)) =
          (∏ k ∈ U, coeff' k) * (∏ k ∈ U, (t k : ℚ)) := Finset.prod_mul_distrib
      _ = (∏ k ∈ U, coeff k) * (∏ k ∈ U, (zInt k : ℚ)) := by
        congr 1
        · exact Finset.prod_congr rfl fun k hk => hcoeff k
      _ = (∏ k ∈ U, coeff k) * ((∏ k ∈ U, zInt k : ℤ) : ℚ) := by
        congr 1
        simp [zInt, Int.cast_prod]
  have hmask : productMask χ c coeff' t = rootMask := by
    rw [productMask_eq_filteredProduct]
    apply Finset.prod_congr rfl
    intro U hU
    unfold countMask
    rw [hArg U]
  have hcolorZero : rationalColorIndicator χ c 0 = 0 := by
    unfold rationalColorIndicator rationalColorHit
    split_ifs with h
    · rcases h with ⟨x, hx, hx0, _⟩
      have : x = 0 := by exact_mod_cast hx0
      omega
    · rfl
  have hcenter (d : Fin m) (hcoeffNe : coeff' d ≠ 0) :
      rationalDivisorWeightUnder (A'.law N hXA') (B' d) (t d : ℚ) =
        rootFactor {d} := by
    have hmasterNe : coeff d ≠ 0 := by simpa [hcoeff d] using hcoeffNe
    have hform : chainForm coeff ({d} : Finset (Fin m)) zInt = (t d : ℚ) := by
      have hJ : ({d} : Finset (Fin m)).Nonempty := ⟨d, Finset.mem_singleton_self d⟩
      simp [chainForm, zInt, hJ, hmasterNe]
    have hcount : countFunctions A C a N c (rho A χ N) ({d} : Finset (Fin m)) =
        nu A N (C.block d) := by
      simp [countFunctions]
    have hdiv := rationalDivisorWeightUnder_principal A A' N prin hprin hXeq
      hXA hXA' (B' d) (C.block d) (hTail d) (t d : ℚ)
    simpa [rootFactor, hcount, hform] using hdiv
  have hnonFactor (J : NonsingletonSubsets m) : weightedNonsingle J = rootFactor J.val := by
    let hJ : J.val.Nonempty := Finset.card_pos.mp
      (lt_of_lt_of_le (by decide) J.property)
    let d := J.val.max' hJ
    let q := sumForm coeff' J.val hJ t
    have hcard : 2 ≤ J.val.card := J.property
    have hmax : anchor J.val hcard = d := by
      change J.val.max' (nonempty_of_two_le_card hcard) = J.val.max' hJ
      exact congrArg J.val.max' (Subsingleton.elim _ _)
    have hform : chainForm coeff J.val zInt = q := by
      simp [chainForm, sumForm, hJ, q, zInt, coeff, coeff', hcoeff]
    have hcount : countFunctions A C a N c (rho A χ N) J.val =
        rho A χ N (C.block d) (a d) c := by
      unfold countFunctions
      rw [dif_pos hcard, hmax]
    have hdiv := rationalDivisorWeightUnder_principal A A' N prin hprin hXeq
      hXA hXA' (B' d) (C.block d) (hTail d) q
    have hAt := atQ_mul_rationalColorIndicator
      (nu A N (C.block d)) χ c (coeff' d) q
    change rationalColorIndicator χ c (coeff' d * q) *
      rationalDivisorWeightUnder (A'.law N hXA') (B' d) q = _
    calc
      _ = rationalColorIndicator χ c (coeff' d * q) * atQ (nu A N (C.block d)) q := by rw [hdiv]
      _ = atQ (fun y => nu A N (C.block d) y *
          rationalColorIndicator χ c (coeff' d * (y : ℚ))) q := hAt.symm
      _ = rootFactor J.val := by
        dsimp [rootFactor]
        rw [hform]
        rw [hcount]
        apply congrArg (fun F : ℤ → ℝ => atQ F q)
        funext y
        simp [rho, colorFactor, chainScale, coeff, hcoeff]
  by_cases hnonzero : ∀ d, coeff' d ≠ 0
  · have hcenters :
        (∏ d, rationalDivisorWeightUnder (A'.law N hXA') (B' d) (t d : ℚ)) =
          ∏ d, rootFactor {d} := by
      apply Finset.prod_congr rfl
      intro d hd
      exact hcenter d (hnonzero d)
    have hnonsingle :
        (∏ J : NonsingletonSubsets m, weightedNonsingle J) =
          ∏ J : NonsingletonSubsets m, rootFactor J.val := by
      apply Finset.prod_congr rfl
      intro J hJ
      exact hnonFactor J
    rw [hmask, prod_nonempty_eq_singleton_nonsingleton (g := rootFactor), hcenters, hnonsingle]
    ring
  · push_neg at hnonzero
    obtain ⟨d, hd⟩ := hnonzero
    have hmaskZero : productMask χ c coeff' t = 0 := by
      rw [productMask_eq_filteredProduct]
      let U : Finset (Fin m) := {d}
      have hU : U ∈ Finset.univ.filter Finset.Nonempty := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, ⟨d, Finset.mem_singleton_self d⟩⟩
      apply Finset.prod_eq_zero hU
      simp [U, hd, hcolorZero]
    rw [hmask]
    have hrootMaskZero : rootMask = 0 := hmask.symm.trans hmaskZero
    simp [hrootMaskZero]

/-- A zero upper bound on absolute values gives convergence to zero. -/
theorem filterUpperBound_abs_tendsto_zero {L : Filter ℕ} {f : ℕ → ℝ}
    (h : FilterUpperBound L (fun N => |f N|) 0) : Tendsto f L (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    have hε : 0 < -b / 2 := by linarith
    filter_upwards [h (-b / 2) hε] with N hN
    have hAbs := abs_le.mp (by simpa using hN)
    linarith
  · intro b hb
    have hε : 0 < b / 2 := by linarith
    filter_upwards [h (b / 2) hε] with N hN
    have hAbs := abs_le.mp (by simpa using hN)
    linarith

/-- A harmonic pivot weight has finite integer support. -/
theorem harmonicLaw_support_finite (X W : ℕ) :
    {z : ℤ | harmonicLaw X W z ≠ 0}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (X ^ 2 : ℤ))
  intro z hz
  have hcond : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W := by
    by_contra hn
    have hzero : harmonicLaw X W z = 0 := by simp [harmonicLaw, hn]
    exact hz hzero
  refine ⟨hcond.1, ?_⟩
  have hlt : (z.toNat : ℤ) < (X ^ 2 : ℤ) := by exact_mod_cast hcond.2.2.1
  rw [Int.toNat_of_nonneg hcond.1] at hlt
  exact hlt.le

/-- A pivot tuple mass has finite support because each coordinate has finite harmonic support. -/
theorem pivotMass_support_finite {n m : ℕ} (A : Parameters n) (C : MasterChain n m)
    (N : ℕ) : {z : Fin m → ℤ | pivotMass A C N z ≠ 0}.Finite := by
  have hfinite : {z : Fin m → ℤ | ∀ d,
      z d ∈ {y : ℤ | harmonicLaw (A.X N (C.block d).1) (primorial (N + 1)) y ≠ 0}}.Finite :=
    Set.Finite.pi' fun d => harmonicLaw_support_finite _ _
  apply hfinite.subset
  intro z hz
  simp only [Set.mem_setOf_eq]
  intro d
  by_contra hmem
  have hzero : harmonicLaw (A.X N (C.block d).1) (primorial (N + 1)) (z d) = 0 := by
    simpa only [Set.mem_setOf_eq] using hmem
  have hprod : pivotMass A C N z = 0 := by
    unfold pivotMass
    exact Finset.prod_eq_zero (Finset.mem_univ d) hzero
  exact hz hprod

/-- A tuple of weighted pivot laws has finite support. -/
theorem weightedPivotTupleMass_support_finite {n m : ℕ}
    (A : Parameters n) (N : ℕ) (B : Fin m → FrameworkBlock n) :
    {z : Fin m → ℤ | weightedPivotTupleMass A N B z ≠ 0}.Finite := by
  classical
  have hfinite : {z : Fin m → ℤ | ∀ d,
      z d ∈ {y : ℤ | harmonicLaw (A.X N (B d).1) (primorial (N + 1)) y ≠ 0}}.Finite :=
    Set.Finite.pi' fun d => harmonicLaw_support_finite _ _
  apply hfinite.subset
  intro z hz
  simp only [Set.mem_setOf_eq]
  intro d
  by_contra hmem
  have hzero : harmonicLaw (A.X N (B d).1) (primorial (N + 1)) (z d) = 0 := by
    simpa only [Set.mem_setOf_eq] using hmem
  have hprod : weightedPivotTupleMass A N B z = 0 := by
    unfold weightedPivotTupleMass
    refine Finset.prod_eq_zero (Finset.mem_univ d) ?_
    simp [weightedPivotMass, hzero]
  exact hz hprod

/-- Multiplication by any real-valued function preserves the finite support of pivot mass. -/
theorem summable_pivotMass_mul {n m : ℕ} (A : Parameters n) (C : MasterChain n m)
    (N : ℕ) (f : (Fin m → ℤ) → ℝ) :
    Summable (fun z => pivotMass A C N z * f z) := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (pivotMass_support_finite A C N)
  intro z hz
  by_contra hmass
  have hzero : pivotMass A C N z = 0 := by
    apply not_ne_iff.mp
    exact hmass
  simp [hzero] at hz

/-- The extension by zero `atQ` respects subtraction. -/
theorem atQ_sub (f g : ℤ → ℝ) (q : ℚ) :
    atQ (fun y => f y - g y) q = atQ f q - atQ g q := by
  by_cases hq : q.den = 1 <;> simp [atQ, hq]

/-- Replacing one factor in a finite product turns the difference into a product with that
factor replaced by its difference. -/
theorem finset_prod_sub_single_factor {α : Type*} [DecidableEq α] (s : Finset α)
    (j : α) (hj : j ∈ s) (f g h : α → ℝ)
    (hrest : ∀ x, x ∈ s.erase j → f x = h x ∧ g x = h x)
    (hjval : h j = f j - g j) :
    (∏ x ∈ s, f x) - ∏ x ∈ s, g x = ∏ x ∈ s, h x := by
  have hf : (∏ x ∈ s.erase j, f x) = ∏ x ∈ s.erase j, h x := by
    apply Finset.prod_congr rfl
    intro x hx
    exact (hrest x hx).1
  have hg : (∏ x ∈ s.erase j, g x) = ∏ x ∈ s.erase j, h x := by
    apply Finset.prod_congr rfl
    intro x hx
    exact (hrest x hx).2
  rw [← Finset.prod_erase_mul s f hj, ← Finset.prod_erase_mul s g hj,
    ← Finset.prod_erase_mul s h hj, hf, hg, hjval]
  ring

/-- Exact linearity of `maskedCorrelation` in one nonempty support factor. -/
theorem maskedCorrelation_replace_factor {n m : ℕ} (A : Parameters n)
    (C : MasterChain n m) (a : Fin m → ℚ) (N : ℕ)
    (b : Finset (Fin m) → ℤ → ℝ) (j : Finset (Fin m)) (hj : j.Nonempty)
    (g₁ g₂ gd : Finset (Fin m) → ℤ → ℝ)
    (hjval : gd j = g₁ j - g₂ j)
    (hrest : ∀ J, J.Nonempty → J ≠ j → g₁ J = gd J ∧ g₂ J = gd J) :
    maskedCorrelation A C a N b g₁ - maskedCorrelation A C a N b g₂ =
      maskedCorrelation A C a N b gd := by
  classical
  let s : Finset (Finset (Fin m)) := Finset.univ.filter Finset.Nonempty
  let mask (z : Fin m → ℤ) := ∏ U ∈ Finset.univ.filter Finset.Nonempty,
    b U (∏ k ∈ U, z k)
  let factor (g : Finset (Fin m) → ℤ → ℝ) (z : Fin m → ℤ) (J : Finset (Fin m)) :=
    atQ (g J) (chainForm (chainScale A C a N) J z)
  have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hprod (z : Fin m → ℤ) :
      (∏ J ∈ s, factor g₁ z J) - ∏ J ∈ s, factor g₂ z J = ∏ J ∈ s, factor gd z J := by
    apply finset_prod_sub_single_factor s j hjs (factor g₁ z) (factor g₂ z) (factor gd z)
    · intro J hJ
      have hJerase := Finset.mem_erase.mp hJ
      have hJnon : J.Nonempty := (Finset.mem_filter.mp hJerase.2).2
      have hfunctions := hrest J hJnon hJerase.1
      exact ⟨congrArg (fun f : ℤ → ℝ => atQ f (chainForm (chainScale A C a N) J z))
          hfunctions.1,
        congrArg (fun f : ℤ → ℝ => atQ f (chainForm (chainScale A C a N) J z))
          hfunctions.2⟩
    ·
      change atQ (gd j) (chainForm (chainScale A C a N) j z) = _
      rw [hjval]
      exact atQ_sub (g₁ j) (g₂ j) (chainForm (chainScale A C a N) j z)
  have hs₁ : Summable (fun z : Fin m → ℤ =>
      pivotMass A C N z * (mask z * ∏ J ∈ s, factor g₁ z J)) :=
    summable_pivotMass_mul A C N (fun z => mask z * ∏ J ∈ s, factor g₁ z J)
  have hs₂ : Summable (fun z : Fin m → ℤ =>
      pivotMass A C N z * (mask z * ∏ J ∈ s, factor g₂ z J)) :=
    summable_pivotMass_mul A C N (fun z => mask z * ∏ J ∈ s, factor g₂ z J)
  change (∑' z : Fin m → ℤ, pivotMass A C N z * (mask z * ∏ J ∈ s, factor g₁ z J)) -
      ∑' z : Fin m → ℤ, pivotMass A C N z * (mask z * ∏ J ∈ s, factor g₂ z J) =
    ∑' z : Fin m → ℤ, pivotMass A C N z * (mask z * ∏ J ∈ s, factor gd z J)
  rw [← hs₁.tsum_sub hs₂]
  apply tsum_congr
  intro z
  calc
    pivotMass A C N z * (mask z * ∏ J ∈ s, factor g₁ z J) -
        pivotMass A C N z * (mask z * ∏ J ∈ s, factor g₂ z J) =
      pivotMass A C N z * (mask z * ((∏ J ∈ s, factor g₁ z J) - ∏ J ∈ s, factor g₂ z J)) := by ring
    _ = pivotMass A C N z * (mask z * ∏ J ∈ s, factor gd z J) := by rw [hprod z]

/-- Applying a positive real power preserves a filter upper bound, with the bound evaluated
at its nonnegative part. -/
theorem filterUpperBound_rpow {L : Filter ℕ} {f : ℕ → ℝ} {b C θ : ℝ}
    (h : FilterUpperBound L (fun N => |f N|) b) (hC : 0 ≤ C) (hθ : 0 < θ) :
    FilterUpperBound L (fun N => C * |f N| ^ θ) (C * (max b 0) ^ θ) := by
  intro ε hε
  let x := max b 0
  have hx : 0 ≤ x := le_max_right _ _
  have hcont : ContinuousAt (fun δ : ℝ => C * (x + δ) ^ θ) 0 := by
    have hout := Real.continuousAt_rpow_const x θ (Or.inr hθ.le)
    have hin : ContinuousAt (fun δ : ℝ => x + δ) 0 := by fun_prop
    have hp := hout.comp_of_eq hin (by simp)
    exact continuousAt_const.mul hp
  have hval : C * (x + (0 : ℝ)) ^ θ = C * x ^ θ := by simp
  have hnhds : Set.Iio (C * x ^ θ + ε) ∈ 𝓝 (C * (x + (0 : ℝ)) ^ θ) := by
    rw [hval]
    exact Iio_mem_nhds (by linarith)
  rcases Metric.mem_nhds_iff.mp (hcont.eventually hnhds) with ⟨δ, hδ, hδball⟩
  let η := δ / 2
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hηball : η ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [η]
    rw [abs_of_pos (by positivity)]
    linarith
  have hηbound : C * (x + η) ^ θ < C * x ^ θ + ε := by
    have h := hδball hηball
    simpa [η] using h
  filter_upwards [h η hηpos] with N hN
  have hbase : |f N| ≤ x + η := by
    have hb : b ≤ x := le_max_left _ _
    linarith
  have hpow : |f N| ^ θ ≤ (x + η) ^ θ :=
    Real.rpow_le_rpow (abs_nonneg _) hbase (le_of_lt hθ)
  have hlt : C * |f N| ^ θ < C * x ^ θ + ε := by
    calc
      C * |f N| ^ θ ≤ C * (x + η) ^ θ := mul_le_mul_of_nonneg_left hpow hC
      _ < C * x ^ θ + ε := hηbound
  exact hlt.le

/-- A finite sum of consecutive differences telescopes. -/
theorem sum_fin_telescope (n : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin n, (f (i.val + 1) - f i.val)) = f n - f 0 := by
  revert f
  induction n with
  | zero =>
      intro f
      simp
  | succ n ih =>
      intro f
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.zero_add, Fin.val_succ]
      rw [ih (fun k => f (k + 1))]
      ring

open scoped BigOperators NNReal

variable {K sl r : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

set_option maxHeartbeats 1000000 in
theorem chainCount_telescope_helper (m : ℕ) (MS : MasterScales K As sl Dm)
    (hlist : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card), Allowed Dm (corrTemplate m J hJ))
    (χ : ℕ → Fin r) (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ k, a k ∈ As) (c : Fin r)
    (L : Filter ℕ) (hL : L ≤ atTop) (J0 : ℕ) (hJ0 : 0 < J0) (G₁ G₂ : BlockFamily K r)
    (hG₁ : ∀ N B b c y, |G₁ N B b c y| ≤ 1 + nu MS.core.parameters N B y)
    (hG₂ : ∀ N B b c y, |G₂ N B b c y| ≤ 1 + nu MS.core.parameters N B y)
    (hG : ∀ N B b c y, |G₁ N B b c y - G₂ N B b c y| ≤ 1 + nu MS.core.parameters N B y)
    (bound : Finset (Fin m) → ℝ)
    (hcube : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card),
      FilterUpperBound L (fun N => |cubeAverage MS (corrTemplate m J hJ) C.gap
        (C.block (anchor J hJ)).1 J0 N (fun y =>
          G₁ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
            G₂ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y)|) (bound J)) :
    FilterUpperBound L
      (fun N => |chainCount MS.core.parameters χ C a N c (G₁ N) -
        chainCount MS.core.parameters χ C a N c (G₂ N)|)
      (∑ J : {J : Finset (Fin m) // 2 ≤ J.card},
        corrConst m J.1 J.2 * (max (bound J.1) 0) ^ corrExponent m J.1 J.2) := by
  classical
  let A := MS.core.parameters
  let α := {J : Finset (Fin m) // 2 ≤ J.card}
  let q := Fintype.card α
  let e : Fin q ≃ α := (Fintype.equivFin α).symm
  let idx : α ≃ Fin q := e.symm
  let stage : ℕ → ℕ → Finset (Fin m) → ℤ → ℝ := fun k N J y => by
    classical
    by_cases hJ : 2 ≤ J.card
    · let j : α := ⟨J, hJ⟩
      exact if (idx j).val < k then
        G₁ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y
      else G₂ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y
    · by_cases hJne : J.Nonempty
      · exact nu A N (C.block (J.max' hJne)) y
      · exact 1
  let stageCount (k N : ℕ) : ℝ :=
    maskedCorrelation A C a N (countMask A χ C a N c) (stage k N)
  have hstage0 (N : ℕ) : stage 0 N = countFunctions A C a N c (G₂ N) := by
    funext J y
    classical
    by_cases hJ : 2 ≤ J.card
    · simp [stage, hJ, countFunctions]
    · by_cases hJne : J.Nonempty <;> simp [stage, hJ, hJne, countFunctions]
  have hstageq (N : ℕ) : stage q N = countFunctions A C a N c (G₁ N) := by
    funext J y
    classical
    by_cases hJ : 2 ≤ J.card
    · have hidx : (idx ⟨J, hJ⟩).val < q := (idx ⟨J, hJ⟩).isLt
      simp [stage, hJ, hidx, countFunctions]
    · by_cases hJne : J.Nonempty <;> simp [stage, hJ, hJne, countFunctions]
  have hcount0 (N : ℕ) : stageCount 0 N = chainCount A χ C a N c (G₂ N) := by
    simp [stageCount, chainCount, hstage0]
  have hcountq (N : ℕ) : stageCount q N = chainCount A χ C a N c (G₁ N) := by
    simp [stageCount, chainCount, hstageq]
  have htel (N : ℕ) :
      stageCount q N - stageCount 0 N =
        ∑ k ∈ Finset.range q, (stageCount (k + 1) N - stageCount k N) := by
    exact (Finset.sum_range_sub (fun k => stageCount k N) q).symm
  let term (J : α) : ℝ :=
    corrConst m J.1 J.2 * (max (bound J.1) 0) ^ corrExponent m J.1 J.2
  have hstep (i : Fin q) :
      FilterUpperBound L
        (fun N => |stageCount (i.val + 1) N - stageCount i.val N|)
        (term (e i)) := by
    intro ε hε
    let Jstar : Finset (Fin m) := (e i).1
    have hJstar : 2 ≤ Jstar.card := (e i).2
    have hJstarNon : Jstar.Nonempty := Finset.card_pos.mp (by omega)
    have hiIndex : idx ⟨Jstar, hJstar⟩ = i := by simp [idx, Jstar, e]
    have hiVal : (idx ⟨Jstar, hJstar⟩).val = i.val := congrArg Fin.val hiIndex
    have hnew (N : ℕ) : stage (i.val + 1) N Jstar =
        fun y => G₁ N (C.block (anchor Jstar hJstar)) (a (anchor Jstar hJstar)) c y := by
      funext y
      unfold stage
      rw [dif_pos hJstar]
      change (if (idx (⟨Jstar, hJstar⟩ : α)).val < i.val + 1 then
          G₁ N (C.block (anchor Jstar hJstar)) (a (anchor Jstar hJstar)) c y
        else G₂ N (C.block (anchor Jstar hJstar)) (a (anchor Jstar hJstar)) c y) = _
      rw [hiVal]
      simp
    have hold (N : ℕ) : stage i.val N Jstar =
        fun y => G₂ N (C.block (anchor Jstar hJstar)) (a (anchor Jstar hJstar)) c y := by
      funext y
      unfold stage
      rw [dif_pos hJstar]
      change (if (idx (⟨Jstar, hJstar⟩ : α)).val < i.val then
          G₁ N (C.block (anchor Jstar hJstar)) (a (anchor Jstar hJstar)) c y
        else G₂ N (C.block (anchor Jstar hJstar)) (a (anchor Jstar hJstar)) c y) = _
      rw [hiVal]
      simp
    have hstage_unchanged (N : ℕ) (J : Finset (Fin m)) (hJ : 2 ≤ J.card)
        (hJne : J ≠ Jstar) : stage (i.val + 1) N J = stage i.val N J := by
      funext y
      let j : α := ⟨J, hJ⟩
      have hjne : idx j ≠ i := by
        intro heq
        apply hJne
        have hiidx : idx (e i) = i := by simp [idx]
        have hEq : j = e i := idx.injective (heq.trans hiidx.symm)
        exact congrArg Subtype.val hEq
      have hvalne : (idx j).val ≠ i.val := by
        intro heq
        exact hjne (Fin.ext heq)
      by_cases hbelow : (idx j).val < i.val
      · have hbelow' : (idx j).val < i.val + 1 := by omega
        simp [stage, j, hJ, hbelow, hbelow']
      · have habove : i.val < (idx j).val := by omega
        have hnotbelow' : ¬ (idx j).val < i.val + 1 := by omega
        simp [stage, j, hJ, hbelow, hnotbelow']
    let gd (N : ℕ) : Finset (Fin m) → ℤ → ℝ := fun J y => by
      classical
      by_cases hJ : 2 ≤ J.card
      · exact if hEq : J = Jstar then
          G₁ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
            G₂ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y
        else stage i.val N J y
      · exact stage i.val N J y
    have hjval (N : ℕ) : gd N Jstar = stage (i.val + 1) N Jstar - stage i.val N Jstar := by
      funext y
      simp [gd, Jstar, hJstar, hnew, hold]
    have hrest (N : ℕ) : ∀ J, J.Nonempty → J ≠ Jstar →
        stage (i.val + 1) N J = gd N J ∧ stage i.val N J = gd N J := by
      intro J hJnon hJne
      by_cases hJ : 2 ≤ J.card
      · have hs := hstage_unchanged N J hJ hJne
        have hgd : gd N J = stage i.val N J := by simp [gd, hJ, hJne]
        exact ⟨hs.trans hgd.symm, hgd.symm⟩
      · have hs : stage (i.val + 1) N J = stage i.val N J := by
          funext y
          simp [stage, hJ, hJnon]
        have hgd : gd N J = stage i.val N J := by simp [gd, hJ]
        exact ⟨hs.trans hgd.symm, hgd.symm⟩
    have hstep_eq (N : ℕ) :
        stageCount (i.val + 1) N - stageCount i.val N =
          maskedCorrelation A C a N (countMask A χ C a N c) (gd N) := by
      exact maskedCorrelation_replace_factor A C a N (countMask A χ C a N c)
        Jstar hJstarNon (stage (i.val + 1) N) (stage i.val N) (gd N) (hjval N) (hrest N)
    have hcube := hcube Jstar hJstar
    have hθ : 0 < corrExponent m Jstar hJstar := by
      dsimp [corrExponent]
      positivity
    have hC : 0 ≤ corrConst m Jstar hJstar := (corrConst_pos m Jstar hJstar).le
    have hpow := filterUpperBound_rpow hcube hC hθ
    obtain ⟨ι, hlisted⟩ := hlist Jstar hJstar
    have htest : ∀ δ > 0, ∀ᶠ N in atTop,
        |maskedCorrelation A C a N (countMask A χ C a N c) (gd N)| ≤
      δ + corrConst m Jstar hJstar *
            |cubeAverage MS (corrTemplate m Jstar hJstar) C.gap
              (C.block (anchor Jstar hJstar)).1 J0 N (gd N Jstar)| ^
                corrExponent m Jstar hJstar := by
      intro δ hδ
      have hRawFamily :=
        (uniform_correlation_test m Jstar hJstarNon hJstar).choose_spec.2.2.choose_spec.2.choose_spec
          (K := K) (s := sl) (Aset := As) (Dm := Dm)
          (corrScales MS) ι hlisted C a ha
      have hraw := hRawFamily.2.2.2 {J0}
        (by intro x hx; simp at hx; subst x; exact hJ0) δ hδ
      filter_upwards [hraw] with N hN
      have hN' := hN J0 (Finset.mem_singleton_self J0)
        (countMask A χ C a N c) (gd N) (by
          constructor
          · intro U hU y
            have hh := rationalColorIndicator_mem_Icc χ c
              ((∏ k ∈ U, chainScale A C a N k) * (y : ℚ))
            have hlow : -(1 : ℝ) ≤ rationalColorIndicator χ c
                ((∏ k ∈ U, chainScale A C a N k) * (y : ℚ)) := by
              have hminus : -(1 : ℝ) ≤ 0 := by norm_num
              exact hminus.trans hh.1
            simpa [countMask] using abs_le.mpr ⟨hlow, hh.2⟩
          · intro J hJ y
            by_cases hJ2 : 2 ≤ J.card
            · by_cases hEq : J = Jstar
              · subst J
                simpa [gd, hJstar, anchor, chainWeight, nu, corrScales,
                  fromArithmetic_parameterTailProductLaw_eq] using
                  (hG (N) (C.block (anchor Jstar hJstar))
                    (a (anchor Jstar hJstar)) c y)
              · let j : α := ⟨J, hJ2⟩
                have hjne : idx j ≠ i := by
                  intro heq
                  apply hEq
                  have hiidx : idx (e i) = i := by simp [idx]
                  exact congrArg Subtype.val (idx.injective (heq.trans hiidx.symm))
                have hvalne : (idx j).val ≠ i.val := by
                  intro heq
                  exact hjne (Fin.ext heq)
                by_cases hbelow : (idx j).val < i.val
                · have hgd : gd N J y = G₁ N (C.block (anchor J hJ2))
                    (a (anchor J hJ2)) c y := by
                      have hbelowFin : idx j < i := Fin.lt_iff_val_lt_val.mpr hbelow
                      simp [gd, hJ2, hEq, stage, j, hbelowFin]
                  rw [hgd]
                  simpa [anchor, chainWeight, nu, corrScales,
                    fromArithmetic_parameterTailProductLaw_eq] using
                    (hG₁ N (C.block (anchor J hJ2)) (a (anchor J hJ2)) c y)
                · have habove : i.val < (idx j).val := by omega
                  have hnot : ¬ (idx j).val < i.val := by omega
                  have hgd : gd N J y = G₂ N (C.block (anchor J hJ2))
                    (a (anchor J hJ2)) c y := by
                      have hnotFin : ¬ idx j < i := by
                        intro h
                        exact hnot (Fin.lt_iff_val_lt_val.mp h)
                      simp [gd, hJ2, hEq, stage, j, hnotFin]
                  rw [hgd]
                  simpa [anchor, chainWeight, nu, corrScales,
                    fromArithmetic_parameterTailProductLaw_eq] using
                    (hG₂ N (C.block (anchor J hJ2)) (a (anchor J hJ2)) c y)
            · have hν := nu_nonneg A N (C.block (J.max' hJ)) y
              have hgd : gd N J y = nu A N (C.block (J.max' hJ)) y := by
                simp [gd, hJ2, stage, hJ]
              rw [hgd, abs_of_nonneg hν]
              simp [anchor, chainWeight, nu, corrScales,
                fromArithmetic_parameterTailProductLaw_eq]
              linarith
        )
      simpa [A, corrScales, corrTemplate, corrConst, corrExponent, cubeAverage, anchor,
        HindmanSumsProducts.parameterTailProductLaw, FromArithmetic.parameterTailProductLaw] using hN'
    have htestL (δ : ℝ) (hδ : 0 < δ) :
        ∀ᶠ N in L,
          |maskedCorrelation A C a N (countMask A χ C a N c) (gd N)| ≤
            δ + corrConst m Jstar hJstar *
            |cubeAverage MS (corrTemplate m Jstar hJstar) C.gap
                (C.block (anchor Jstar hJstar)).1 J0 N (gd N Jstar)| ^
                  corrExponent m Jstar hJstar := hL (htest δ hδ)
    have hstepbound : FilterUpperBound L
        (fun N => |stageCount (i.val + 1) N - stageCount i.val N|) (term ⟨Jstar, hJstar⟩) := by
      intro ε hε
      have hhalf : 0 < ε / 2 := by positivity
      filter_upwards [htestL (ε / 2) hhalf, hpow (ε / 2) hhalf] with N hc hp
      rw [hstep_eq N]
      have hgdstar : gd N Jstar = fun y =>
          G₁ N (C.block (anchor Jstar hJstar)) (a (anchor Jstar hJstar)) c y -
            G₂ N (C.block (anchor Jstar hJstar)) (a (anchor Jstar hJstar)) c y := by
        simp [gd, Jstar, hJstar]
      calc
        |maskedCorrelation A C a N (countMask A χ C a N c) (gd N)| ≤
            ε / 2 + corrConst m Jstar hJstar *
              |cubeAverage MS (corrTemplate m Jstar hJstar) C.gap
                (C.block (anchor Jstar hJstar)).1 J0 N (gd N Jstar)| ^
                  corrExponent m Jstar hJstar := hc
        _ ≤ term ⟨Jstar, hJstar⟩ + ε := by
          have hp' : corrConst m Jstar hJstar *
              |cubeAverage MS (corrTemplate m Jstar hJstar) C.gap
                (C.block (anchor Jstar hJstar)).1 J0 N (gd N Jstar)| ^
                  corrExponent m Jstar hJstar ≤ term ⟨Jstar, hJstar⟩ + ε / 2 := by
            simpa [term, Jstar, hJstar, anchor, hgdstar] using hp
          linarith [hc, hp']
    simpa [term, Jstar, hJstar] using hstepbound ε hε
  have hsumEquiv : (∑ i : Fin q, term (e i)) = ∑ J : α, term J :=
    Fintype.sum_equiv e (fun i => term (e i)) term (fun _ => rfl)
  have htelFin (N : ℕ) : stageCount q N - stageCount 0 N =
      ∑ i : Fin q, (stageCount (i.val + 1) N - stageCount i.val N) := by
    exact (sum_fin_telescope q (fun k => stageCount k N)).symm
  intro ε hε
  let δ : ℝ := ε / ((q : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hqδ : (q : ℝ) * δ ≤ ε := by
    have hqle : (q : ℝ) ≤ (q : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) q]
    have hden : 0 < (q : ℝ) + 1 := by positivity
    dsimp [δ]
    calc
      (q : ℝ) * (ε / ((q : ℝ) + 1)) ≤ ((q : ℝ) + 1) * (ε / ((q : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hqle (by positivity)
      _ = ε := by field_simp [ne_of_gt hden]
  have hall : ∀ᶠ N in L, ∀ i : Fin q,
      |stageCount (i.val + 1) N - stageCount i.val N| ≤ term (e i) + δ := by
    apply Filter.eventually_all.mpr
    intro i
    exact hstep i δ hδ
  filter_upwards [hall] with N hN
  rw [← hcountq N, ← hcount0 N]
  calc
    |stageCount q N - stageCount 0 N| =
        |∑ i : Fin q, (stageCount (i.val + 1) N - stageCount i.val N)| :=
          congrArg abs (htelFin N)
    _ ≤ ∑ i : Fin q, |stageCount (i.val + 1) N - stageCount i.val N| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin q, (term (e i) + δ) := Finset.sum_le_sum fun i hi => hN i
    _ = (∑ i : Fin q, term (e i)) + (q : ℝ) * δ := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (∑ i : Fin q, term (e i)) + ε := add_le_add_right hqδ _
    _ = (∑ J : α, term J) + ε := by rw [hsumEquiv]
end

end HindmanSumsProducts.Prediction

#print axioms HindmanSumsProducts.Prediction.dominates_of_le_denominator
#print axioms HindmanSumsProducts.Prediction.added_map_strictMono
#print axioms HindmanSumsProducts.Prediction.height_map_embedding
#print axioms HindmanSumsProducts.Prediction.parameters_allRawCutoffs_eventually_eq
#print axioms HindmanSumsProducts.Prediction.dominates_of_eventually_le_denominator
#print axioms HindmanSumsProducts.Prediction.rationalModelValue_eq_atQ
#print axioms HindmanSumsProducts.Prediction.atQ_mem_Icc_of_mem
#print axioms HindmanSumsProducts.Prediction.parameterJointBlockProductMass_support_finite
#print axioms HindmanSumsProducts.Prediction.weightedPivotTupleMass_support_finite
#print axioms HindmanSumsProducts.Prediction.abs_tsum_mul_sub_le_tsum_abs_diff
#print axioms HindmanSumsProducts.Prediction.harmonicNatLaw_nonneg
#print axioms HindmanSumsProducts.Prediction.parameterTailProductLaw_nonneg
#print axioms HindmanSumsProducts.Prediction.nuB_nonneg_of_nonneg
#print axioms HindmanSumsProducts.Prediction.nu_nonneg
#print axioms HindmanSumsProducts.Prediction.filterUpperBound_abs_tendsto_zero
#print axioms HindmanSumsProducts.Prediction.harmonicLaw_support_finite
#print axioms HindmanSumsProducts.Prediction.pivotMass_support_finite
#print axioms HindmanSumsProducts.Prediction.summable_pivotMass_mul
#print axioms HindmanSumsProducts.Prediction.atQ_sub
#print axioms HindmanSumsProducts.Prediction.finset_prod_sub_single_factor
#print axioms HindmanSumsProducts.Prediction.maskedCorrelation_replace_factor
#print axioms HindmanSumsProducts.Prediction.filterUpperBound_rpow
#print axioms HindmanSumsProducts.Prediction.chainCount_telescope_helper
#print axioms HindmanSumsProducts.Prediction.subgroup_inverse
#print axioms HindmanSumsProducts.cor_product_law
#print axioms HindmanSumsProducts.Prediction.sum_fin_telescope
#print axioms HindmanSumsProducts.Prediction.fromArithmetic_parameterTailProductLaw_eq
#print axioms HindmanSumsProducts.Prediction.fromArithmetic_parameterTailProductLaw_fun_eq
#print axioms HindmanSumsProducts.Prediction.rawHarmonicLaw_atom
#print axioms HindmanSumsProducts.Prediction.integral_outsideLaw_eq_sum
#print axioms HindmanSumsProducts.Prediction.integral_parameterLaw_eq_sum
#print axioms HindmanSumsProducts.Prediction.pivotMarginals_eq_outsideLaw
#print axioms HindmanSumsProducts.Prediction.integral_pivotMarginals_eq_sum
#print axioms HindmanSumsProducts.Prediction.parameterJointBlockProductMass_eq_map_real
#print axioms HindmanSumsProducts.Prediction.integral_eq_tsum_map_real_singleton
#print axioms HindmanSumsProducts.Prediction.parameterLaw_map_injective
#print axioms HindmanSumsProducts.Prediction.divisorWeightUnder_eq_nu
#print axioms HindmanSumsProducts.Prediction.divisorWeightUnder_principal
#print axioms HindmanSumsProducts.Prediction.rationalDivisorWeightUnder_principal
#print axioms HindmanSumsProducts.Prediction.pivotMass_tsum_eq_nat_sum
#print axioms HindmanSumsProducts.Prediction.atQ_mul_rationalColorIndicator
#print axioms HindmanSumsProducts.Prediction.prod_nonempty_eq_singleton_nonsingleton
#print axioms HindmanSumsProducts.uniform_correlation_test
