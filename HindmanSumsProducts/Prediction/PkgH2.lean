import HindmanSumsProducts.Prediction.PkgH
import OAI.Combinatorics.SumProduct.Alignment.ProductExposure03

open Filter MeasureTheory
open scoped BigOperators NNReal Topology

namespace HindmanSumsProducts.Prediction

noncomputable section

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
      (∏ j ∈ P, μK j (S x j)) = ∏ i, μK (prin i) {x i} := by
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
          (∏ j ∈ P, μK j (S x j)) * ∏ j ∈ Pᶜ, μK j Set.univ := by
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

/-- Every charted representing family takes values in the unit interval. -/
theorem RepFamily.eval_mem_Icc {K s : ℕ} {A : Parameters K} {l : Fin K}
    {Fm : Menu s} {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (N : ℕ) (y : ℤ) :
    Φ.eval N y ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [RepFamily.eval]
  let P := Φ.piece N (y / (A.H N l : ℤ)) (y % (A.M N : ℤ))
  have h := P.range (P.g ^ ((y - y % (A.M N : ℤ)) / (A.M N : ℤ)) • P.x)
  simpa [P, OAI.SourceMenuLiteral.CosetPiece.eval] using h

/-- The Lipschitz cutoff used for calibration: it is one through `2τ` and zero from `3τ` onward. -/
def calibrationCutoff (τ x : ℝ) : ℝ := max 0 (min 1 ((3 * τ - x) / τ))

theorem calibrationCutoff_lipschitz (τ : ℝ) (hτ : 0 < τ) :
    LipschitzWith (Real.toNNReal (τ⁻¹)) (calibrationCutoff τ) := by
  have hlinear : LipschitzWith (Real.toNNReal (τ⁻¹))
      (fun x : ℝ => (3 * τ - x) / τ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hcoe : (Real.toNNReal (τ⁻¹) : ℝ) = τ⁻¹ :=
      Real.coe_toNNReal _ (inv_nonneg.mpr hτ.le)
    rw [Real.dist_eq, Real.dist_eq, hcoe]
    have hdiff : (3 * τ - x) / τ - (3 * τ - y) / τ = (y - x) / τ := by ring
    rw [hdiff, abs_div, abs_of_pos hτ]
    calc
      |y - x| / τ = τ⁻¹ * |x - y| := by rw [abs_sub_comm]; simp [div_eq_mul_inv, mul_comm]
      _ ≤ τ⁻¹ * |x - y| := le_rfl
  change LipschitzWith (Real.toNNReal (τ⁻¹))
    (fun x : ℝ => max 0 (min 1 ((3 * τ - x) / τ)))
  convert (hlinear.min_const 1).const_max 0 using 1
  funext x
  simp [min_comm]

theorem calibrationCutoff_mem_Icc (τ x : ℝ) :
    calibrationCutoff τ x ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [calibrationCutoff, Set.mem_Icc]
  constructor
  · exact le_max_left _ _
  · exact (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩

theorem calibrationCutoff_eq_one {τ x : ℝ} (hτ : 0 < τ) (hx : x ≤ 2 * τ) :
    calibrationCutoff τ x = 1 := by
  have hlin : 1 ≤ (3 * τ - x) / τ := by
    rw [le_div_iff₀ hτ]
    nlinarith
  simp [calibrationCutoff, min_eq_left hlin]

theorem calibrationCutoff_eq_zero {τ x : ℝ} (hτ : 0 < τ) (hx : 3 * τ ≤ x) :
    calibrationCutoff τ x = 0 := by
  have hnum : 3 * τ - x ≤ 0 := by linarith
  have hlin : (3 * τ - x) / τ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hτ.le
  rw [calibrationCutoff, min_eq_right (hlin.trans (by norm_num)), max_eq_left hlin]

/-- A bounded sequence lies below every uniform pointwise upper bound at its ultralimit. -/
theorem ulim_le_of_bounded {U : Ultrafilter ℕ} (f : ℕ → ℝ) (C : ℝ)
    (hbound : ∃ D, ∀ N, |f N| ≤ D) (hpoint : ∀ N, f N ≤ C) : ulim U f ≤ C := by
  exact le_of_tendsto_of_tendsto' (ulim_tendsto_of_bounded U f hbound)
    tendsto_const_nhds hpoint

/-- Expectation against the finite harmonic pivot law preserves constant upper bounds. -/
theorem Emu_le_const {K : ℕ} (A : Parameters K) (N : ℕ) (i : Fin K)
    (f : ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ y, f y ≤ C) :
    Emu A N i f ≤ C := by
  rw [Emu_eq_sum_support]
  calc
    (∑ y ∈ muSupport A N i, mu A N i y * f y) ≤
        ∑ y ∈ muSupport A N i, mu A N i y * C := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hf y) (mu_nonneg A N i y)
    _ = (∑ y ∈ muSupport A N i, mu A N i y) * C := by rw [← Finset.sum_mul]
    _ ≤ 1 * C := by
      have hmass : (∑ y ∈ muSupport A N i, mu A N i y) ≤ 1 := by
        simpa [Emu_eq_sum_support] using Emu_mass_le_one A N i
      exact mul_le_mul_of_nonneg_right hmass hC
    _ = C := one_mul C

/-- The bounded ultralimit is additive, in the form needed for the calibration pairing. -/
theorem ulim_add_of_bounded (U : Ultrafilter ℕ) (f g : ℕ → ℝ)
    (hf : ∃ C, ∀ N, |f N| ≤ C) (hg : ∃ C, ∀ N, |g N| ≤ C) :
    ulim U (fun N => f N + g N) = ulim U f + ulim U g := by
  obtain ⟨Cf, hCf⟩ := hf
  obtain ⟨Cg, hCg⟩ := hg
  have hsum : ∃ C, ∀ N, |f N + g N| ≤ C := by
    refine ⟨|Cf| + |Cg|, fun N => ?_⟩
    calc
      |f N + g N| ≤ |f N| + |g N| := abs_add_le _ _
      _ ≤ |Cf| + |Cg| := add_le_add (le_trans (hCf N) (le_abs_self Cf))
        (le_trans (hCg N) (le_abs_self Cg))
  have hft := ulim_tendsto_of_bounded U f ⟨Cf, hCf⟩
  have hgt := ulim_tendsto_of_bounded U g ⟨Cg, hCg⟩
  have hst := ulim_tendsto_of_bounded U (fun N => f N + g N) hsum
  have hsumt := hft.add hgt
  exact tendsto_nhds_unique hst hsumt

/-- Dominance survives an eventual decrease of a positive denominator. -/
theorem dominates_of_eventually_le_denominator {f S T : ℕ → ℝ}
    (h : OAI.MicrocellScale.Dominates f S) (hT : ∀ N, 0 < T N)
    (hTS : ∀ᶠ N in atTop, T N ≤ S N) (hf : ∀ᶠ N in atTop, 0 ≤ f N) :
    OAI.MicrocellScale.Dominates f T := by
  intro C hC
  have hratio : ∀ᶠ N in atTop, f N / S N ^ C ≤ f N / T N ^ C := by
    filter_upwards [hTS, hf] with N hNS hN
    have hp := Real.rpow_le_rpow (le_of_lt (hT N)) hNS hC.le
    exact div_le_div_of_nonneg_left hN (Real.rpow_pos_of_pos (hT N) C) hp
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [(h C hC).eventually_gt_atTop b, hratio] with N hN hratio
  exact (le_of_lt hN).trans hratio

/-- Growth dominance is transitive through an everywhere positive intermediate scale. -/
theorem dominates_transitive {f S T : ℕ → ℝ} (hS : ∀ N, 0 < S N) (hT : ∀ N, 0 < T N)
    (h₁ : OAI.MicrocellScale.Dominates f S) (h₂ : OAI.MicrocellScale.Dominates S T) :
    OAI.MicrocellScale.Dominates f T := by
  intro C hC
  have h₁' := h₁ 1 (by norm_num)
  have h₂' := h₂ C hC
  have hmul := h₁'.atTop_mul_atTop₀ h₂'
  apply hmul.congr'
  filter_upwards [] with N
  have hSN := (hS N).ne'
  have hTN : T N ^ C ≠ 0 := (Real.rpow_pos_of_pos (hT N) C).ne'
  rw [Real.rpow_one]
  field_simp [hSN, hTN]

/-- A finite-support total-variation bound controls expectations of functions in `[−1,1]`. -/
theorem tsum_mass_expectation_diff_bound {α : Type*} [DecidableEq α]
    (μ ν f : α → ℝ) (s : Finset α)
    (hμ : ∀ x, x ∉ s → μ x = 0) (hν : ∀ x, x ∉ s → ν x = 0)
    (hf : ∀ x, |f x| ≤ 1) :
    |(∑' x, μ x * f x) - ∑' x, ν x * f x| ≤ arithmeticL1 μ ν := by
  have hμsum : ∑' x, μ x * f x = ∑ x ∈ s, μ x * f x :=
    tsum_eq_sum (s := s) (fun x hx => by simp [hμ x hx])
  have hνsum : ∑' x, ν x * f x = ∑ x ∈ s, ν x * f x :=
    tsum_eq_sum (s := s) (fun x hx => by simp [hν x hx])
  have hL1 : arithmeticL1 μ ν = ∑ x ∈ s, |μ x - ν x| := by
    unfold arithmeticL1
    exact tsum_eq_sum (s := s) (fun x hx => by simp [hμ x hx, hν x hx])
  rw [hμsum, hνsum, hL1]
  calc
    |(∑ x ∈ s, μ x * f x) - ∑ x ∈ s, ν x * f x| =
        |∑ x ∈ s, (μ x - ν x) * f x| := by
      congr 1
      have hsum : ∑ x ∈ s, (μ x - ν x) * f x =
          (∑ x ∈ s, μ x * f x) - ∑ x ∈ s, ν x * f x := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsum]
    _ ≤ ∑ x ∈ s, |(μ x - ν x) * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ s, |μ x - ν x| := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      calc
        |μ x - ν x| * |f x| ≤ |μ x - ν x| * 1 :=
          mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
        _ = |μ x - ν x| := mul_one _

/-- The finite harmonic expectation of a function bounded by one is itself bounded by one. -/
theorem Emu_abs_le_one {K : ℕ} (A : Parameters K) (N : ℕ) (i : Fin K)
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) : |Emu A N i f| ≤ 1 := by
  rw [Emu_eq_sum_support]
  have hmass : (∑ y ∈ muSupport A N i, mu A N i y) ≤ 1 := by
    simpa [Emu_eq_sum_support] using Emu_mass_le_one A N i
  calc
    |∑ y ∈ muSupport A N i, mu A N i y * f y| ≤
        ∑ y ∈ muSupport A N i, |mu A N i y * f y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ muSupport A N i, mu A N i y := by
      apply Finset.sum_le_sum
      intro y hy
      rw [abs_mul, abs_of_nonneg (mu_nonneg A N i y)]
      calc
        mu A N i y * |f y| ≤ mu A N i y * 1 :=
          mul_le_mul_of_nonneg_left (hf y) (mu_nonneg A N i y)
        _ = mu A N i y := mul_one _
    _ ≤ 1 := hmass

/-- Cofinite consequences of an at-top estimate hold in every ultrafilter extending cofinite. -/
theorem eventually_atTop_ultrafilter {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ Filter.cofinite) {p : ℕ → Prop}
    (hp : ∀ᶠ N in atTop, p N) : ∀ᶠ N in (U : Filter ℕ), p N := by
  have hc : ∀ᶠ N in Filter.cofinite, p N := by
    simpa [Nat.cofinite_eq_atTop] using hp
  exact hc.filter_mono hU

/-- The harmonic pivot law is zero away from its declared finite support. -/
theorem mu_zero_of_not_mem_support {K : ℕ} (A : Parameters K) (N : ℕ) (i : Fin K)
    (y : ℤ) (hy : y ∉ muSupport A N i) : mu A N i y = 0 := by
  unfold mu harmonicLaw
  split_ifs with h
  · apply False.elim
    apply hy
    unfold muSupport
    apply Finset.mem_image.mpr
    refine ⟨y.toNat, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.2.1, h.2.2.1⟩,
      h.2.2.2⟩, ?_⟩
    exact Int.natCast_toNat_eq_self.mpr h.1
  · rfl

/-- The vector of block products induced by a sample of the master coordinates. -/
def blockProductVector {K r : ℕ} (B : Fin r → FrameworkBlock K)
    (t : Fin K → ℕ) : Fin r → ℤ :=
  fun d => ((∏ j ∈ (B d).set, t j : ℕ) : ℤ)

theorem natCast_eq_int_iff (q : ℕ) (z : ℤ) :
    (q : ℤ) = z ↔ 0 ≤ z ∧ q = z.toNat := by
  constructor
  · intro h
    constructor
    · rw [← h]
      exact Int.natCast_nonneg q
    · have hc := congrArg Int.toNat h
      simpa using hc
  · rintro ⟨hz, hq⟩
    calc
      (q : ℤ) = (z.toNat : ℤ) := by exact_mod_cast hq
      _ = z := Int.natCast_toNat_eq_self.mpr hz

/-- The actual product-law mass is the atom mass of the block-product pushforward. -/
theorem parameterJointBlockProductMass_eq_map_atom {K r : ℕ}
    (A : OAI.SourceAdmissible.Parameters K) (N : ℕ)
    (B : Fin r → FrameworkBlock K)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : Fin r → ℤ) :
    parameterJointBlockProductMass A N B hX z =
      (Measure.map (blockProductVector B) (A.law N hX)).real {z} := by
  unfold parameterJointBlockProductMass
  rw [MeasureTheory.map_measureReal_apply (measurable_of_countable _) MeasurableSet.of_discrete]
  congr 1
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext d
    exact (natCast_eq_int_iff _ _).2 (h d)
  · intro h d
    exact (natCast_eq_int_iff _ _).1 (congrFun h d)

/-- The same increasing block map used by the assembly in `Completion.lean`. -/
def calibrationMapBlock {n K : ℕ} (prin : Fin n → Fin K)
    (hprin : StrictMono prin) (B : Block n) : Block K :=
  ⟨prin B.1, ⟨B.2.val.map ⟨prin, hprin.injective⟩, B.2.property.1.map, by
    intro j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
    exact hprin (B.2.property.2 j' hj')⟩⟩

/-- The one-block case of `cor_product_law` gives an error tending to zero. -/
theorem calibration_product_error_tendsto {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (l : Fin K) (hgap : ValidGap B l) :
    Tendsto (fun N => arithmeticL1
      (parameterJointBlockProductMass MS.core.parameters N (fun _ : Fin 1 => B)
        (fun j => MS.gapStage.valid_raw_cutoffs N j))
      (weightedPivotTupleMass MS.core.parameters N (fun _ : Fin 1 => B)))
      atTop (𝓝 0) := by
  let A := MS.core.parameters
  let BV : Fin 1 → FrameworkBlock K := fun _ => B
  let tailProduct : ℕ → ℕ := fun N =>
    ∏ j ∈ B.2.val, (A.X N j) ^ 2
  let prefixProduct : ℕ → ℕ := fun N =>
    ∏ j ∈ (Finset.univ.filter (fun j : Fin K => j < B.1)), (A.X N j) ^ 2
  let target : ℕ → ℝ := fun N =>
    2 + (primorial (N + 1) : ℝ) + (tailProduct N : ℝ) + 1
  let masterV : ℕ → ℝ := fun N => (masterScaleV A N B.1 : ℝ)
  have hTailSubset (N : ℕ) :
      B.2.val ⊆ Finset.univ.filter (fun j : Fin K => j < B.1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hgap.1 j hj).trans hgap.2
  have hTailProduct (N : ℕ) : tailProduct N ≤ prefixProduct N := by
    apply Finset.prod_le_prod_of_subset_of_one_le (hTailSubset N)
    intro j hj hnot
    exact one_le_pow_of_one_le' (Nat.one_le_iff_ne_zero.mpr (A.Xpos N j).ne') 2
  have hTargetPositive (N : ℕ) : 0 < target N := by
    dsimp [target]
    positivity
  have hHnonneg : ∀ N, 0 ≤ (A.H N B.1 : ℝ) := by
    intro N
    exact_mod_cast (Nat.zero_le (A.H N B.1))
  have hTargetLeMaster : ∀ᶠ N in atTop, target N ≤ masterV N := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hWtwo : 2 ≤ primorial (N + 1) := by
      calc
        2 = primorial 2 := by simp
        _ ≤ primorial (N + 1) := primorial_mono (by omega)
    have hWmul : 2 * primorial (N + 1) ≤
        primorial (N + 1) * primorial (N + 1) := by
      nlinarith [Nat.mul_le_mul_left (primorial (N + 1)) hWtwo]
    have hWplus : primorial (N + 1) + 1 ≤
        primorial (N + 1) * primorial (N + 1) := by
      have hlin : primorial (N + 1) + 1 ≤ 2 * primorial (N + 1) := by omega
      exact hlin.trans hWmul
    have hpowle : (primorial (N + 1)) ^ 2 ≤
        (primorial (N + 1)) ^ (N + 1) := by
      exact pow_le_pow_right' (by omega) (by omega)
    have hM : primorial (N + 1) + 1 ≤ A.M N := by
      calc
        primorial (N + 1) + 1 ≤ (primorial (N + 1)) ^ 2 := by simpa [pow_two] using hWplus
        _ ≤ (primorial (N + 1)) ^ (N + 1) := hpowle
        _ ≤ A.M N := Nat.le_of_dvd (A.Mpos N) (A.Mdiv N)
    have hNat : 3 + primorial (N + 1) + tailProduct N ≤
        2 + A.M N + prefixProduct N := by
      have htailN := hTailProduct N
      omega
    have htargetEq : target N =
        ((3 + primorial (N + 1) + tailProduct N : ℕ) : ℝ) := by
      dsimp [target]
      push_cast
      ring
    have hmasterEq : masterV N =
        ((2 + A.M N + prefixProduct N : ℕ) : ℝ) := by
      dsimp [masterV]
      exact_mod_cast (show masterScaleV A N B.1 =
        2 + A.M N + prefixProduct N by rfl)
    have hReal : target N ≤ masterV N := by
      rw [htargetEq, hmasterEq]
      exact_mod_cast hNat
    exact hReal
  have hHdominates : OAI.MicrocellScale.Dominates
      (fun N => (A.H N B.1 : ℝ)) target := by
    apply dominates_of_eventually_le_denominator
      (MS.gapStage.gap_dominates_pool_and_bound B.1) hTargetPositive ?_
      (Filter.Eventually.of_forall hHnonneg)
    filter_upwards [hTargetLeMaster] with N hN
    have hle : masterV N ≤
        ((MS.primeStage.pool N B.1).upper + masterScaleV A N B.1 : ℝ) := by
      dsimp [masterV]
      exact le_add_of_nonneg_left (by positivity)
    exact hN.trans hle
  have hDom : OAI.MicrocellScale.Dominates
      (fun N => Real.log (A.X N B.1 : ℝ)) target := by
    exact dominates_transitive
      (f := fun N => Real.log (A.X N B.1 : ℝ))
      (S := fun N => (A.H N B.1 : ℝ)) (T := target)
      (fun N => by exact_mod_cast (A.Hpos N B.1)) hTargetPositive
      (MS.gapStage.raw_cutoff_log_dominates_gap B.1) hHdominates
  have hdisj : ∀ i j : Fin 1, i ≠ j → Disjoint (BV i).set (BV j).set := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hV : ∀ _N : ℕ, 1 ≤ (1 : ℕ) := fun _ => le_rfl
  have hVdom : ∀ d : Fin 1, OAI.MicrocellScale.Dominates
      (fun N => Real.log (A.X N (BV d).1 : ℝ))
      (fun N => (2 + primorial (N + 1) +
        (∏ j ∈ (BV d).2.val, (A.X N j) ^ 2 : ℕ) + ((1 : ℕ) : ℝ))) := by
    intro d
    have hd : d = ⟨0, by omega⟩ := Subsingleton.elim _ _
    subst d
    simpa [target, tailProduct, BV] using hDom
  have hsuper := cor_product_law A BV hdisj
    (fun N j => MS.gapStage.valid_raw_cutoffs N j) (fun _ => 1) hV hVdom
  have hsmall := hsuper 1 (by norm_num)
  simpa [A, BV, Real.one_rpow] using hsmall

/-- Calibration follows by replacing the block-product law, testing the cutoff model, and using
the coarse projection estimate. -/
theorem calibration_from_testing_helper {K sl r : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} {n s : ℕ}
    (MS : MasterScales K As sl Dm)
    (h1 : (1 : IntegerPolynomial sl) ∈ Dm) (χ : ℕ → Fin r)
    (F : BlockFamily K r) (hF : IsDenseModel MS χ F)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    {A' : Parameters n} (pad prin : Fin n → Fin K)
    (hprin : StrictMono prin) (hpad : ∀ u, pad u < prin u)
    (hinter : ∀ u v, u < v → prin u < pad v)
    (hht : ∀ N u, A'.ht N u = MS.core.parameters.ht N (prin u))
    (hXeq : ∀ N u, A'.X N u = MS.core.parameters.X N (prin u))
    (vs : Finset ℚ) (hvs : vs ⊆ As) {Fm : Menu s} {Km : ℝ≥0}
    (S : ModelsSystem A' vs r Fm)
    (Φ : (u : Fin n) → Block K → ℚ → Fin r →
      RepFamily MS.core.parameters (pad u) Fm Km)
    (hS : ∀ N (B' : Block n) (v : ℚ), v ∈ vs → ∀ (c : Fin r) (y : ℤ),
      S.model N B' v c y =
        (Φ B'.1 (calibrationMapBlock prin hprin B') v c).eval N y)
    (B' : Block n) (a : ℚ) (ha : a ∈ vs) (c : Fin r) (τ ε : ℝ) (hτ : 0 < τ)
    (hproj : projNorm MS.core.parameters U (prin B'.1) (pad B'.1) s
      (fun N y => F N (calibrationMapBlock prin hprin B') a c y -
        (Φ B'.1 (calibrationMapBlock prin hprin B') a c).eval N y) ≤ ε)
    (μ : ℕ → Measure (Fin n → ℕ))
    (hμ : ∀ N (hX : ∀ i, 4 * primorial (N + 1) ≤ A'.X N i),
      μ N = A'.law N hX) :
    UltrafilterUpperBound U
      (fun N => calibrationProbabilityUnder (μ N) S χ N B' a c τ) (3 * τ + ε) := by
  classical
  let A : Parameters K := MS.core.parameters
  let BM : Block K := calibrationMapBlock prin hprin B'
  let i : Fin K := prin B'.1
  let l : Fin K := pad B'.1
  let e : Fin n ↪ Fin K := ⟨prin, hprin.injective⟩
  let BV : Fin 1 → Block K := fun _ => BM
  let B'V : Fin 1 → Block n := fun _ => B'
  let extract : (Fin K → ℕ) → (Fin n → ℕ) := fun t u => t (prin u)
  have hXA : ∀ N j, 4 * primorial (N + 1) ≤ A.X N j :=
    fun N j => MS.gapStage.valid_raw_cutoffs N j
  have hXA' : ∀ N u, 4 * primorial (N + 1) ≤ A'.X N u := by
    intro N u
    rw [hXeq N u]
    exact hXA N (prin u)
  have hmapLaw (N : ℕ) : Measure.map extract (A.law N (hXA N)) =
      A'.law N (hXA' N) := by
    exact parameterLaw_map_injective A A' N prin hprin.injective
      (hXeq N) (hXA N) (hXA' N)
  have hset : OAI.SourceBlocks.Block.set BM =
      (OAI.SourceBlocks.Block.set B').map e := by
    simp [BM, calibrationMapBlock, OAI.SourceBlocks.Block.set, e]
  have hBtail : BM.2.val = B'.2.val.map e := by
    rfl
  have hgap : ValidGap BM l := by
    constructor
    · intro j hj
      rw [hBtail] at hj
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hj
      exact hinter u B'.1 (B'.2.property.2 u hu)
    · exact hpad B'.1
  have hheight (N : ℕ) :
      height (A'.ht N) (OAI.SourceBlocks.Block.set B') =
        height (A.ht N) (OAI.SourceBlocks.Block.set BM) := by
    change (∏ u ∈ OAI.SourceBlocks.Block.set B', A'.ht N u) =
      ∏ j ∈ OAI.SourceBlocks.Block.set BM, A.ht N j
    rw [hset, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro u hu
    exact hht N u
  have hProductMap (t : Fin K → ℕ) :
      blockProductVector B'V (extract t) = blockProductVector BV t := by
    funext d
    have hd : d = ⟨0, by omega⟩ := Subsingleton.elim _ _
    subst d
    simp only [blockProductVector, B'V, BV]
    congr 1
    symm
    rw [hset, Finset.prod_map]
    simp [e, extract]
  let Phi : RepFamily A l Fm Km := Φ B'.1 BM a c
  let lip : ℝ≥0 := Real.toNNReal (τ⁻¹)
  obtain ⟨Ψ, hΨ⟩ := RepFamily.comp_exists Phi (calibrationCutoff τ) lip
    (calibrationCutoff_lipschitz τ hτ)
    (fun x hx => calibrationCutoff_mem_Icc τ x)
  let V : ℕ → ℤ → ℝ := fun N y => Ψ.eval N y
  have hΨspec (N : ℕ) (y : ℤ) :
      V N y = calibrationCutoff τ (Phi.eval N y) := by
    exact hΨ N y
  have haMaster : a ∈ As := hvs ha
  have hnil : ∀ η₀ : ℝ, 0 < η₀ → ∀ᶠ N in atTop,
      |Emu A N i (fun y => (rho A χ N BM a c y - F N BM a c y) * V N y)| ≤ η₀ := by
    intro η₀ hη₀
    have htest := nilsequence_testing MS h1 χ F hF BM a haMaster c l hgap
      Fm (lip * Km) η₀ hη₀
    filter_upwards [htest] with N hN
    simpa [A, i, BM, V, calibrationMapBlock] using hN Ψ
  let qDense : ℕ → ℝ := fun N => Emu A N i
    (fun y => F N BM a c y * V N y)
  let qModel : ℕ → ℝ := fun N => Emu A N i
    (fun y => Phi.eval N y * V N y)
  let qProjection : ℕ → ℝ := fun N => Emu A N i
    (fun y => (F N BM a c y - Phi.eval N y) * V N y)
  have hFunit (N : ℕ) (y : ℤ) : F N BM a c y ∈ Set.Icc (0 : ℝ) 1 :=
    hF.1 N BM a c y
  have hPhiunit (N : ℕ) (y : ℤ) : Phi.eval N y ∈ Set.Icc (0 : ℝ) 1 :=
    Phi.eval_mem_Icc N y
  have hVunit (N : ℕ) (y : ℤ) : V N y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [V] using Ψ.eval_mem_Icc N y
  have hVabs (N : ℕ) (y : ℤ) : |V N y| ≤ 1 := by
    rw [abs_of_nonneg (hVunit N y).1]
    exact (hVunit N y).2
  have hDiffabs (N : ℕ) (y : ℤ) : |F N BM a c y - Phi.eval N y| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(hFunit N y).1, (hFunit N y).2,
      (hPhiunit N y).1, (hPhiunit N y).2]
  have hDenseIntegrandAbs (N : ℕ) (y : ℤ) :
      |F N BM a c y * V N y| ≤ 1 := by
    rw [abs_mul]
    have hFabs : |F N BM a c y| ≤ 1 := by
      rw [abs_of_nonneg (hFunit N y).1]
      exact (hFunit N y).2
    exact mul_le_one₀ hFabs (abs_nonneg _) (hVabs N y)
  have hModelIntegrandAbs (N : ℕ) (y : ℤ) :
      |Phi.eval N y * V N y| ≤ 1 := by
    rw [abs_mul]
    have hΦabs : |Phi.eval N y| ≤ 1 := by
      rw [abs_of_nonneg (hPhiunit N y).1]
      exact (hPhiunit N y).2
    exact mul_le_one₀ hΦabs (abs_nonneg _) (hVabs N y)
  have hProjectionIntegrandAbs (N : ℕ) (y : ℤ) :
      |(F N BM a c y - Phi.eval N y) * V N y| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (hDiffabs N y) (abs_nonneg _) (hVabs N y)
  have hqDenseBound : ∃ C, ∀ N, |qDense N| ≤ C := by
    refine ⟨1, fun N => Emu_abs_le_one A N i _ (hDenseIntegrandAbs N)⟩
  have hqModelBound : ∃ C, ∀ N, |qModel N| ≤ C := by
    refine ⟨1, fun N => Emu_abs_le_one A N i _ (hModelIntegrandAbs N)⟩
  have hqProjectionBound : ∃ C, ∀ N, |qProjection N| ≤ C := by
    refine ⟨1, fun N => Emu_abs_le_one A N i _ (hProjectionIntegrandAbs N)⟩
  have hmodelProduct (N : ℕ) (y : ℤ) :
      Phi.eval N y * V N y ≤ 3 * τ := by
    by_cases hbelow : Phi.eval N y < 3 * τ
    · calc
        Phi.eval N y * V N y ≤ Phi.eval N y * 1 :=
          mul_le_mul_of_nonneg_left (hVunit N y).2 (hPhiunit N y).1
        _ = Phi.eval N y := mul_one _
        _ ≤ 3 * τ := le_of_lt hbelow
    · have hge : 3 * τ ≤ Phi.eval N y := le_of_not_gt hbelow
      rw [hΨspec N y, calibrationCutoff_eq_zero hτ hge]
      nlinarith [sq_nonneg (Phi.eval N y)]
  have hqModelPoint : ∀ N, qModel N ≤ 3 * τ := by
    intro N
    exact Emu_le_const A N i (fun y => Phi.eval N y * V N y) (3 * τ)
      (by positivity) (hmodelProduct N)
  have hqModelLimit : ulim U qModel ≤ 3 * τ :=
    ulim_le_of_bounded (U := U) qModel (3 * τ) hqModelBound hqModelPoint
  have hVspan : V ∈ repSpan A l s := by
    change (fun N y => Ψ.eval N y) ∈ repSpan A l s
    unfold repSpan
    apply Submodule.subset_span
    exact ⟨Fm, lip * Km, Ψ, rfl⟩
  have hVnorm : familyInner A U i V V ≤ 1 := by
    change ulim U (fun N => Emu A N i (fun y => V N y * V N y)) ≤ 1
    apply ulim_le_of_bounded (U := U) _ 1 ?_ ?_
    · refine ⟨1, fun N => Emu_abs_le_one A N i _ ?_⟩
      intro y
      rw [abs_of_nonneg (mul_nonneg (hVunit N y).1 (hVunit N y).1)]
      nlinarith [(hVunit N y).1, (hVunit N y).2]
    · intro N
      apply Emu_le_const A N i (fun y => V N y * V N y) 1 (by norm_num)
      intro y
      nlinarith [(hVunit N y).1, (hVunit N y).2]
  have hprojInner : familyInner A U i
      (fun N y => F N BM a c y - Phi.eval N y) V ≤ ε := by
    calc
      _ ≤ projNorm A U i l s (fun N y => F N BM a c y - Phi.eval N y) :=
        le_projNorm A U i l s (fun N y => F N BM a c y - Phi.eval N y) V
          ⟨1, fun N y => hDiffabs N y⟩ hVspan hVnorm
      _ ≤ ε := by simpa [A, i, l, BM, Phi] using hproj
  have hqDecomp (N : ℕ) : qDense N = qModel N + qProjection N := by
    dsimp [qDense, qModel, qProjection]
    calc
      Emu A N i (fun y => F N BM a c y * V N y) =
          Emu A N i (fun y => Phi.eval N y * V N y +
            (F N BM a c y - Phi.eval N y) * V N y) := by
        congr 1
        funext y
        ring
      _ = Emu A N i (fun y => Phi.eval N y * V N y) +
          Emu A N i (fun y => (F N BM a c y - Phi.eval N y) * V N y) :=
        Emu_add A N i _ _
  have hlimAdd : ulim U qDense = ulim U qModel + ulim U qProjection := by
    have h := ulim_add_of_bounded U qModel qProjection hqModelBound hqProjectionBound
    calc
      ulim U qDense = ulim U (fun N => qDense N) := rfl
      _ = ulim U (fun N => qModel N + qProjection N) :=
        congrArg (ulim U) (funext hqDecomp)
      _ = ulim U qModel + ulim U qProjection := h
  have hqDenseLimit : ulim U qDense ≤ 3 * τ + ε := by
    rw [hlimAdd]
    exact add_le_add hqModelLimit hprojInner
  have hqDenseTendsto : Tendsto qDense (U : Filter ℕ) (𝓝 (ulim U qDense)) :=
    ulim_tendsto_of_bounded U qDense hqDenseBound
  intro δ hδ
  let α : ℝ := δ / 3
  have hα : 0 < α := by dsimp [α]; positivity
  have hDenseEvent : ∀ᶠ N in (U : Filter ℕ), qDense N ≤ 3 * τ + ε + α := by
    have hnear : ∀ᶠ N in (U : Filter ℕ), qDense N < ulim U qDense + α :=
      hqDenseTendsto.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hnear] with N hN
    linarith [hqDenseLimit]
  have hNilEvent : ∀ᶠ N in (U : Filter ℕ),
      |Emu A N i (fun y => (rho A χ N BM a c y - F N BM a c y) * V N y)| ≤ α := by
    exact eventually_atTop_ultrafilter hU (hnil α hα)
  have hErrorEvent : ∀ᶠ N in (U : Filter ℕ),
      arithmeticL1
        (parameterJointBlockProductMass A N BV (hXA N))
        (weightedPivotTupleMass A N BV) ≤ α := by
    have hsmall := (calibration_product_error_tendsto MS BM l hgap).eventually
      (Iio_mem_nhds hα)
    exact eventually_atTop_ultrafilter hU (hsmall.mono fun N hN => le_of_lt hN)
  let pMaster : (Fin K → ℕ) → Fin 1 → ℤ := blockProductVector BV
  let pRestricted : (Fin n → ℕ) → Fin 1 → ℤ := blockProductVector B'V
  let E : ℕ → Set (Fin 1 → ℤ) := fun N =>
    {z | rationalColorHit χ c
        ((height (A.ht N) (OAI.SourceBlocks.Block.set BM) : ℚ) * a * (z 0 : ℚ)) ∧
      Phi.eval N (z 0) ≤ 2 * τ}
  have hcolorArg (N : ℕ) (t : Fin n → ℕ) :
      (height (A'.ht N) (OAI.SourceBlocks.Block.set B') : ℚ) * a *
          ((∏ j ∈ OAI.SourceBlocks.Block.set B', t j : ℕ) : ℚ) =
        (height (A.ht N) (OAI.SourceBlocks.Block.set BM) : ℚ) * a *
          ((pRestricted t 0 : ℤ) : ℚ) := by
    rw [hheight N]
    simp [pRestricted, blockProductVector, B'V]
  have hsample (N : ℕ) (t : Fin n → ℕ) :
      height (fun u => (t u : ℤ)) (OAI.SourceBlocks.Block.set B') = pRestricted t 0 := by
    simp [pRestricted, blockProductVector, B'V, height,
      OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height]
  have hmodelEq (N : ℕ) (t : Fin n → ℕ) :
      S.model N B' a c
          (height (fun u => (t u : ℤ)) (OAI.SourceBlocks.Block.set B')) =
        Phi.eval N (pRestricted t 0) := by
    calc
      _ = Phi.eval N
          (height (fun u => (t u : ℤ)) (OAI.SourceBlocks.Block.set B')) :=
        hS N B' a ha c _
      _ = Phi.eval N (pRestricted t 0) := by rw [hsample N t]
  have hFailureSet (N : ℕ) :
      calibrationFailureSet S χ N B' a c τ =
        pRestricted ⁻¹' E N := by
    ext t
    simp only [calibrationFailureSet, Set.mem_setOf_eq, Set.mem_preimage, E]
    constructor
    · rintro ⟨hc, hm⟩
      constructor
      · rw [← hcolorArg N t]
        exact hc
      · rw [hmodelEq N t] at hm
        exact hm
    · rintro ⟨hc, hm⟩
      constructor
      · rw [hcolorArg N t]
        exact hc
      · rw [hmodelEq N t]
        exact hm
  have hMapProductLaw (N : ℕ) :
      Measure.map pRestricted (A'.law N (hXA' N)) =
        Measure.map pMaster (A.law N (hXA N)) := by
    rw [← hmapLaw N]
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext t
    exact hProductMap t
  have hProbabilityEq (N : ℕ) :
      calibrationProbabilityUnder (μ N) S χ N B' a c τ =
        (Measure.map pMaster (A.law N (hXA N))).real (E N) := by
    unfold calibrationProbabilityUnder
    rw [hμ N (hXA' N), hFailureSet N]
    rw [← MeasureTheory.map_measureReal_apply (measurable_of_countable _)
      MeasurableSet.of_discrete]
    rw [hMapProductLaw N]
  let g : ℕ → (Fin 1 → ℤ) → ℝ := fun N z =>
    rationalColorIndicator χ c
      ((height (A.ht N) (OAI.SourceBlocks.Block.set BM) : ℚ) * a * (z 0 : ℚ)) *
        Ψ.eval N (z 0)
  have hgUnit (N : ℕ) (z : Fin 1 → ℤ) : g N z ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [g]
    have hc := rationalColorIndicator_mem_Icc χ c
      ((height (A.ht N) (OAI.SourceBlocks.Block.set BM) : ℚ) * a * (z 0 : ℚ))
    have hv := Ψ.eval_mem_Icc N (z 0)
    exact ⟨mul_nonneg hc.1 hv.1, mul_le_one₀ hc.2 hv.1 hv.2⟩
  have hgAbs (N : ℕ) (z : Fin 1 → ℤ) : |g N z| ≤ 1 := by
    rw [abs_of_nonneg (hgUnit N z).1]
    exact (hgUnit N z).2
  have hIndicatorLe (N : ℕ) (z : Fin 1 → ℤ) :
      (E N).indicator (fun _ => (1 : ℝ)) z ≤ g N z := by
    by_cases hz : z ∈ E N
    · change rationalColorHit χ c
        ((height (A.ht N) (OAI.SourceBlocks.Block.set BM) : ℚ) * a * (z 0 : ℚ)) ∧
          Phi.eval N (z 0) ≤ 2 * τ at hz
      have hcut : Ψ.eval N (z 0) = 1 := by
        calc
          Ψ.eval N (z 0) = calibrationCutoff τ (Phi.eval N (z 0)) := hΨ N (z 0)
          _ = 1 := calibrationCutoff_eq_one hτ hz.2
      simp [E, hz.1, hz.2, hcut, g, rationalColorIndicator]
    · simp [hz]
      exact (hgUnit N z).1
  let mActual : ℕ → (Fin 1 → ℤ) → ℝ := fun N z =>
    parameterJointBlockProductMass A N BV (hXA N) z
  let mReference : ℕ → (Fin 1 → ℤ) → ℝ := fun N z =>
    weightedPivotTupleMass A N BV z
  have hReferenceEmu (N : ℕ) :
      (∑' z, mReference N z * g N z) =
        Emu A N i (fun y => rho A χ N BM a c y * V N y) := by
    let e₁ : ℤ ≃ (Fin 1 → ℤ) :=
      (Equiv.piUnique (fun _ : Fin 1 => ℤ)).symm
    rw [← e₁.tsum_eq (f := fun z : Fin 1 → ℤ => mReference N z * g N z)]
    change (∑' y : ℤ,
        mReference N (e₁ y) * g N (e₁ y)) =
      ∑' y : ℤ, mu A N i y * (rho A χ N BM a c y * V N y)
    have he₁ (y : ℤ) : e₁ y = fun _ : Fin 1 => y := by
      funext d
      simp [e₁]
    apply tsum_congr
    intro y
    rw [he₁ y]
    simp [mReference, g, BV, weightedPivotTupleMass, weightedPivotMass,
      rho, nu, colorFactor, mu, V, A, i, BM, calibrationMapBlock] <;> ring
  have hTVbound (N : ℕ) :
      |(∑' z, mActual N z * g N z) - ∑' z, mReference N z * g N z| ≤
        arithmeticL1 (mActual N) (mReference N) := by
    let D := OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1))
    let suppActual : Finset (Fin 1 → ℤ) := D.image pMaster
    let suppReference : Finset (Fin 1 → ℤ) :=
      (muSupport A N i).image (fun y : ℤ => fun _ : Fin 1 => y)
    let supp := suppActual ∪ suppReference
    letI : IsProbabilityMeasure (A.law N (hXA N)) :=
      OAI.SourceMenuAlignment.law_probability A N (hXA N)
    have hAE : ∀ᵐ t ∂A.law N (hXA N), t ∈ D := by
      simpa [D, OAI.SourceAdmissible.Parameters.law] using
        OAI.ProductExposureLaw.outside_ae_domain (A.X N) (primorial (N + 1))
          (primorial_pos _) (hXA N)
    have hDnull : (A.law N (hXA N)).real (Dᶜ : Set (Fin K → ℕ)) = 0 := by
      have hmeasure : A.law N (hXA N) {t : Fin K → ℕ | t ∉ D} = 0 :=
        (ae_iff.mp hAE)
      have hset : ({t : Fin K → ℕ | t ∉ D} : Set (Fin K → ℕ)) =
          (D : Set (Fin K → ℕ))ᶜ := by
        ext t
        simp
      rw [← hset]
      simp [MeasureTheory.measureReal_def, hmeasure]
    have hActualZero (z : Fin 1 → ℤ) (hz : z ∉ supp) : mActual N z = 0 := by
      have hzA : z ∉ suppActual := (Finset.notMem_union.mp hz).1
      have hpre : pMaster ⁻¹' {z} ⊆ (D : Set (Fin K → ℕ))ᶜ := by
        intro t ht htD
        apply hzA
        apply Finset.mem_image.mpr
        exact ⟨t, htD, by simpa using ht⟩
      have hmapzero : (Measure.map pMaster (A.law N (hXA N))).real {z} = 0 := by
        apply le_antisymm
        · calc
            _ ≤ (A.law N (hXA N)).real (Dᶜ : Set (Fin K → ℕ)) := by
              rw [MeasureTheory.map_measureReal_apply (measurable_of_countable _)
                MeasurableSet.of_discrete]
              exact MeasureTheory.measureReal_mono hpre
            _ = 0 := hDnull
        · exact MeasureTheory.measureReal_nonneg
      change parameterJointBlockProductMass A N BV (hXA N) z = 0
      rw [parameterJointBlockProductMass_eq_map_atom A N BV (hXA N) z]
      exact hmapzero
    have hReferenceZero (z : Fin 1 → ℤ) (hz : z ∉ supp) : mReference N z = 0 := by
      have hzR : z ∉ suppReference := (Finset.notMem_union.mp hz).2
      have hz0 : z 0 ∉ muSupport A N i := by
        intro hmem
        apply hzR
        apply Finset.mem_image.mpr
        refine ⟨z 0, hmem, ?_⟩
        funext d
        exact (congrArg z (Subsingleton.elim d (0 : Fin 1))).symm
      have hmu0 : mu A N i (z 0) = 0 := mu_zero_of_not_mem_support A N i (z 0) hz0
      have hharm : harmonicLaw (A.X N i) (primorial (N + 1)) (z 0) = 0 := by
        simpa [mu] using hmu0
      have hharm' : harmonicLaw (A.X N BM.1) (primorial (N + 1)) (z 0) = 0 := by
        simpa [i, BM, calibrationMapBlock] using hharm
      simp [mReference, weightedPivotTupleMass, BV,
        HindmanSumsProducts.weightedPivotMass, hharm']
    exact tsum_mass_expectation_diff_bound (mActual N) (mReference N) (g N) supp
      hActualZero hReferenceZero (hgAbs N)
  have hProbabilityLE (N : ℕ) :
      calibrationProbabilityUnder (μ N) S χ N B' a c τ ≤
        ∫ z, g N z ∂Measure.map pMaster (A.law N (hXA N)) := by
    rw [hProbabilityEq N]
    let push := Measure.map pMaster (A.law N (hXA N))
    letI : IsProbabilityMeasure (A.law N (hXA N)) :=
      OAI.SourceMenuAlignment.law_probability A N (hXA N)
    have hGint : Integrable (g N) push := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact hgAbs N z
    have hEint : Integrable ((E N).indicator (fun _ => (1 : ℝ))) push :=
      (integrable_const (1 : ℝ)).indicator MeasurableSet.of_discrete
    calc
      push.real (E N) = ∫ z, (E N).indicator (fun _ => (1 : ℝ)) z ∂push :=
        (MeasureTheory.integral_indicator_one MeasurableSet.of_discrete).symm
      _ ≤ ∫ z, g N z ∂push := integral_mono hEint hGint (hIndicatorLe N)
  have hAtom (N : ℕ) (z : Fin 1 → ℤ) :
      mActual N z = (Measure.map pMaster (A.law N (hXA N))).real {z} := by
    simpa [mActual, pMaster] using
      parameterJointBlockProductMass_eq_map_atom A N BV (hXA N) z
  have hIntegralSum (N : ℕ) :
      (∫ z, g N z ∂Measure.map pMaster (A.law N (hXA N))) =
        ∑' z, mActual N z * g N z := by
    let push := Measure.map pMaster (A.law N (hXA N))
    letI : IsProbabilityMeasure (A.law N (hXA N)) :=
      OAI.SourceMenuAlignment.law_probability A N (hXA N)
    have hGint : Integrable (g N) push := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact hgAbs N z
    calc
      (∫ z, g N z ∂push) = ∑' z, push.real {z} * g N z := by
        rw [MeasureTheory.integral_countable hGint]
        simp only [smul_eq_mul]
      _ = ∑' z, mActual N z * g N z := by
        apply tsum_congr
        intro z
        rw [← hAtom N z]
  let qTest : ℕ → ℝ := fun N => Emu A N i
    (fun y => (rho A χ N BM a c y - F N BM a c y) * V N y)
  have hReferenceDecomp (N : ℕ) :
      Emu A N i (fun y => rho A χ N BM a c y * V N y) = qDense N + qTest N := by
    calc
      Emu A N i (fun y => rho A χ N BM a c y * V N y) =
          Emu A N i (fun y => F N BM a c y * V N y +
            (rho A χ N BM a c y - F N BM a c y) * V N y) := by
        congr 1
        funext y
        ring
      _ = qDense N + qTest N := by
        simp only [qDense, qTest]
        exact Emu_add A N i _ _
  have hIntegralBound (N : ℕ) :
      (∫ z, g N z ∂Measure.map pMaster (A.law N (hXA N))) ≤
        qDense N + qTest N +
          arithmeticL1 (mActual N) (mReference N) := by
    rw [hIntegralSum N]
    have htv := hTVbound N
    have hdiff :
        (∑' z, mActual N z * g N z) - ∑' z, mReference N z * g N z ≤
          arithmeticL1 (mActual N) (mReference N) := (abs_le.mp htv).2
    calc
      ∑' z, mActual N z * g N z =
          (∑' z, mReference N z * g N z) +
            ((∑' z, mActual N z * g N z) - ∑' z, mReference N z * g N z) := by ring
      _ ≤ (∑' z, mReference N z * g N z) +
          arithmeticL1 (mActual N) (mReference N) := by linarith
      _ = Emu A N i (fun y => rho A χ N BM a c y * V N y) +
          arithmeticL1 (mActual N) (mReference N) := by rw [hReferenceEmu N]
      _ = qDense N + qTest N +
          arithmeticL1 (mActual N) (mReference N) := by rw [hReferenceDecomp N]
  have hErrorEvent' : ∀ᶠ N in (U : Filter ℕ),
      arithmeticL1 (mActual N) (mReference N) ≤ α := by
    simpa [mActual, mReference, A, BV] using hErrorEvent
  filter_upwards [hDenseEvent, hNilEvent, hErrorEvent'] with N hDense hNil hErr
  have hNilUpper : qTest N ≤ α := (abs_le.mp hNil).2
  calc
    calibrationProbabilityUnder (μ N) S χ N B' a c τ ≤
        ∫ z, g N z ∂Measure.map pMaster (A.law N (hXA N)) := hProbabilityLE N
    _ ≤ qDense N + qTest N + arithmeticL1 (mActual N) (mReference N) :=
      hIntegralBound N
    _ ≤ 3 * τ + ε + 3 * α := by nlinarith [hDense, hNilUpper, hErr]
    _ = 3 * τ + ε + δ := by dsimp [α]; ring

end

end HindmanSumsProducts.Prediction
