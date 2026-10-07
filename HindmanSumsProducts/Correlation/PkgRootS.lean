import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.PkgElim
import HindmanSumsProducts.Correlation.PkgMask
import HindmanSumsProducts.Correlation.PkgElim2

/-! Root translation in additive elimination. -/

namespace HindmanSumsProducts
open FromArithmetic Filter
open scoped BigOperators Topology
noncomputable section

variable {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

def sol_root_envelope (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N d B : ℕ) : ℕ :=
  (d + 1) * (S.core.parameters.H N C.gap + 1) *
    ((S.primeStage.pool N C.gap).upper + FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ B

def sol_root_error (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N d B : ℕ) : ℝ :=
  ∑ j : Fin m, FromArithmetic.harmonicTranslationUniformError
    (S.core.parameters.X N (C.block j).1) (primorial (N + 1))
    (sol_root_envelope S C N d B)

theorem sol_root_pivot_translation_bound
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N d B : ℕ) (h : Fin m → ℤ)
    (hdiv : ∀ j, ∃ v : ℤ, h j = (primorial (N + 1) : ℤ) * v)
    (hh : ∀ j, |(h j : ℝ)| ≤ (sol_root_envelope S C N d B : ℝ))
    (Ftest : (Fin m → ℤ) → ℝ) (Btest : ℝ) (hBtest : 0 ≤ Btest)
    (hFtest : ∀ z, |Ftest z| ≤ Btest) :
    |(∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
        Ftest (fun j => z j + h j)) -
      ∑' z, pivotMass S.core.parameters C N z * Ftest z| ≤
      Btest * (m : ℝ) * sol_root_error S C N d B := by
  classical
  let Henv := sol_root_envelope S C N d B
  let err : ℕ → ℝ := fun n => sol_root_error S C n d B
  have htranslationErrorNonneg (j : Fin m) :
      0 ≤ FromArithmetic.harmonicTranslationUniformError
        (S.core.parameters.X N (C.block j).1) (primorial (N + 1)) Henv := by
    have hcut := S.gapStage.valid_raw_cutoffs N (C.block j).1
    have hW : 0 < primorial (N + 1) := primorial_pos (N + 1)
    have hlog := c_elim2_harmonicCutoffLogCondition hW hcut
    have hXnat : 0 < S.core.parameters.X N (C.block j).1 := by omega
    have hX : (0 : ℝ) < S.core.parameters.X N (C.block j).1 := by exact_mod_cast hXnat
    unfold FromArithmetic.harmonicTranslationUniformError
    apply le_min
    · norm_num
    · apply div_nonneg
      · positivity
      · apply mul_nonneg hX.le
        exact (sub_pos.mpr hlog).le
  have htranslationL1 (j : Fin m) (h : ℤ)
      (hdiv : ∃ m : ℤ, h = (primorial (N + 1) : ℤ) * m)
      (hh : |(h : ℝ)| ≤ (Henv : ℝ)) :
      arithmeticL1
          (translatedLaw
            (harmonicLaw (S.core.parameters.X N (C.block j).1) (primorial (N + 1))) h)
          (harmonicLaw (S.core.parameters.X N (C.block j).1) (primorial (N + 1))) ≤ err N := by
    have hcut := S.gapStage.valid_raw_cutoffs N (C.block j).1
    have hW : 0 < primorial (N + 1) := primorial_pos (N + 1)
    have hXnat : 2 ≤ S.core.parameters.X N (C.block j).1 := by omega
    have hX : 2 ≤ S.core.parameters.X N (C.block j).1 := hXnat
    have hlog := c_elim2_harmonicCutoffLogCondition hW hcut
    have herror := c_elim2_arithmeticL1_translation_le_uniformError
      hW hX hlog hdiv hh
    have hterm : FromArithmetic.harmonicTranslationUniformError
        (S.core.parameters.X N (C.block j).1) (primorial (N + 1)) Henv ≤ err N := by
      dsimp [err, sol_root_error]
      exact Finset.single_le_sum
        (f := fun i : Fin m => FromArithmetic.harmonicTranslationUniformError
          (S.core.parameters.X N (C.block i).1) (primorial (N + 1)) Henv)
        (fun i hi => htranslationErrorNonneg i) (Finset.mem_univ j)
    exact le_trans herror hterm
  let lawSupport : Fin m → Finset ℤ := fun j =>
    Finset.Icc ((S.core.parameters.X N (C.block j).1 : ℤ) - (Henv : ℤ))
      (((S.core.parameters.X N (C.block j).1) ^ 2 : ℕ) + Henv : ℤ)
  let allLawSupport : Finset ℤ := Finset.biUnion Finset.univ lawSupport
  have hbaseLawSupport (j : Fin m) (z : ℤ)
      (hz : harmonicLaw (S.core.parameters.X N (C.block j).1)
        (primorial (N + 1)) z ≠ 0) : z ∈ lawSupport j := by
    unfold harmonicLaw at hz
    split_ifs at hz with h
    · have hcast : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr h.1
      have hlo : (S.core.parameters.X N (C.block j).1 : ℤ) ≤ z := by
        rw [← hcast]
        exact_mod_cast h.2.1
      have hhi : z ≤ ((S.core.parameters.X N (C.block j).1 ^ 2 : ℕ) : ℤ) := by
        rw [← hcast]
        exact_mod_cast h.2.2.1.le
      dsimp [lawSupport]
      apply Finset.mem_Icc.mpr
      constructor
      · linarith
      · exact le_trans hhi (by
          exact_mod_cast Nat.le_add_right
            (S.core.parameters.X N (C.block j).1 ^ 2) Henv)
    · simp at hz
  have hlawZero (j : Fin m) (z : ℤ) (hz : z ∉ allLawSupport) :
      harmonicLaw (S.core.parameters.X N (C.block j).1) (primorial (N + 1)) z = 0 := by
    by_contra hne
    apply hz
    unfold allLawSupport
    apply Finset.mem_biUnion.mpr
    exact ⟨j, Finset.mem_univ j, hbaseLawSupport j z hne⟩
  have htranslatedLawZero (j : Fin m) (h : ℤ)
      (hh : |(h : ℝ)| ≤ (Henv : ℝ)) (z : ℤ) (hz : z ∉ allLawSupport) :
      translatedLaw (harmonicLaw (S.core.parameters.X N (C.block j).1)
        (primorial (N + 1))) h z = 0 := by
    have hshift : -(Henv : ℤ) ≤ h ∧ h ≤ Henv := by
      rcases abs_le.mp hh with ⟨hlo, hhi⟩
      constructor
      · exact_mod_cast hlo
      · exact_mod_cast hhi
    have hbase : harmonicLaw (S.core.parameters.X N (C.block j).1)
        (primorial (N + 1)) (z - h) = 0 := by
      by_cases hcond : 0 ≤ z - h ∧
          S.core.parameters.X N (C.block j).1 ≤ (z - h).toNat ∧
          (z - h).toNat < (S.core.parameters.X N (C.block j).1) ^ 2 ∧
          Nat.Coprime (z - h).toNat (primorial (N + 1))
      · have hcast : (((z - h).toNat : ℤ)) = z - h :=
          Int.natCast_toNat_eq_self.mpr hcond.1
        have hlo : (S.core.parameters.X N (C.block j).1 : ℤ) ≤ z - h := by
          rw [← hcast]
          exact_mod_cast hcond.2.1
        have hhi : z - h ≤ ((S.core.parameters.X N (C.block j).1 ^ 2 : ℕ) : ℤ) := by
          rw [← hcast]
          exact_mod_cast hcond.2.2.1.le
        have hzlo : (S.core.parameters.X N (C.block j).1 : ℤ) - Henv ≤ z := by
          linarith [hshift.1]
        have hzhi : z ≤ ((S.core.parameters.X N (C.block j).1 ^ 2 : ℕ) : ℤ) + Henv := by
          linarith [hshift.2]
        have hmem : z ∈ allLawSupport := by
          unfold allLawSupport
          apply Finset.mem_biUnion.mpr
          refine ⟨j, Finset.mem_univ j, ?_⟩
          have hupper : z ≤
              (((S.core.parameters.X N (C.block j).1 ^ 2) + Henv : ℕ) : ℤ) := by
            exact_mod_cast hzhi
          exact Finset.mem_Icc.mpr ⟨hzlo, hupper⟩
        exact (hz hmem).elim
      · unfold harmonicLaw
        rw [if_neg hcond]
    simpa [translatedLaw] using hbase
  have hnormalizer (j : Fin m) :
      0 < harmonicNormalizer (S.core.parameters.X N (C.block j).1)
        (primorial (N + 1)) := by
    exact harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N (C.block j).1)
  have hcoordinateMass (j : Fin m) :
      ∑' z : ℤ, harmonicLaw (S.core.parameters.X N (C.block j).1)
        (primorial (N + 1)) z = 1 := by
    exact harmonicLaw_tsum_one_of_normalizer_pos _ _
      (S.core.parameters.Xpos N (C.block j).1) (hnormalizer j)
  have hcoordinateNonneg (j : Fin m) (z : ℤ) :
      0 ≤ harmonicLaw (S.core.parameters.X N (C.block j).1)
        (primorial (N + 1)) z :=
    harmonicLaw_nonneg_of_normalizer_pos _ _ (hnormalizer j) z
  have hPivotTranslationTest (h : Fin m → ℤ) (hdiv : ∀ j,
      ∃ v : ℤ, h j = (primorial (N + 1) : ℤ) * v)
      (hh : ∀ j, |(h j : ℝ)| ≤ (Henv : ℝ))
      (Ftest : (Fin m → ℤ) → ℝ) (Btest : ℝ) (hBtest : 0 ≤ Btest)
      (hFtest : ∀ z, |Ftest z| ≤ Btest) :
      |(∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
          Ftest (fun j => z j + h j)) -
        ∑' z, pivotMass S.core.parameters C N z * Ftest z| ≤
        Btest * (Fintype.card (Fin m) : ℝ) * err N := by
    let coordLaw : Fin m → ℤ → ℝ := fun j z =>
      harmonicLaw (S.core.parameters.X N (C.block j).1) (primorial (N + 1)) z
    have hzero (j : Fin m) (z : ℤ) (hz : z ∉ allLawSupport) : coordLaw j z = 0 :=
      hlawZero j z hz
    have hshiftZero (j : Fin m) (z : ℤ) : z ∉ allLawSupport →
        translatedLaw (coordLaw j) (h j) z = 0 := by
      intro hz
      exact htranslatedLawZero j (h j) (hh j) z hz
    have hcoordL1 (j : Fin m) :
        arithmeticL1 (translatedLaw (coordLaw j) (h j)) (coordLaw j) ≤ err N := by
      apply htranslationL1 j (h j) (hdiv j) (hh j)
    exact c_elim2_productTranslation_expectation_bound coordLaw h allLawSupport
      Ftest Btest (err N) hBtest hzero hshiftZero
      hcoordinateNonneg hcoordinateMass hcoordL1 hFtest
  simpa using hPivotTranslationTest h hdiv hh Ftest Btest hBtest hFtest

theorem sol_root_finite_mean_bound {α : Type*} [Fintype α]
    (w F : α → ℝ) (δ : ℝ) (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) (hF : ∀ x, |F x| ≤ δ) :
    |∑ x, w x * F x| ≤ δ := by
  calc
    _ ≤ ∑ x, |w x * F x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, w x * δ := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul, abs_of_nonneg (hw x)]
      exact mul_le_mul_of_nonneg_left (hF x) (hw x)
    _ = δ := by rw [← Finset.sum_mul, hsum, one_mul]

theorem sol_root_uniform_mean_bound {α : Type*} [Fintype α] [Nonempty α]
    (F : α → ℝ) (δ : ℝ) (hF : ∀ x, |F x| ≤ δ) :
    |c_elim2_uniformFintypeAverage F| ≤ δ := by
  unfold c_elim2_uniformFintypeAverage
  rw [Finset.mul_sum]
  apply sol_root_finite_mean_bound _ F δ (fun _ => by positivity) _ hF
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

theorem sol_root_finite_mean_commute {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (F : α → β → ℝ) :
    (∑ x, w x * c_elim2_uniformFintypeAverage (F x)) =
      c_elim2_uniformFintypeAverage (fun y => ∑ x, w x * F x y) := by
  unfold c_elim2_uniformFintypeAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem sol_root_uniform_mean_sub {α : Type*} [Fintype α] (F G : α → ℝ) :
    c_elim2_uniformFintypeAverage F - c_elim2_uniformFintypeAverage G =
      c_elim2_uniformFintypeAverage (fun x => F x - G x) := by
  simp [c_elim2_uniformFintypeAverage, Finset.sum_sub_distrib, mul_sub]

theorem sol_root_uniform_mean_const {α : Type*} [Fintype α] [Nonempty α] (x : ℝ) :
    c_elim2_uniformFintypeAverage (fun _ : α => x) = x :=
  c_elim2_uniformFintypeAverage_const x

theorem sol_root_atQ_weight_bounds
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N : ℕ) (I : Fin m) (x : ℚ) :
    0 ≤ atQ (chainWeight S.core.parameters C N I) x ∧
      atQ (chainWeight S.core.parameters C N I) x ≤
        (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) := by
  by_cases hx : x.den = 1
  · simpa [atQ, hx] using
      ⟨chainWeight_nonneg S C N I x.num,
        chainWeight_le_masterScaleV S C N I x.num⟩
  · simp [atQ, hx]

theorem sol_root_product_bound
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (p : Fin q → ℕ) (z : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ)
    (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1 +
      chainWeight S.core.parameters C N (Sh.row Sh.star).anchor y) :
    |(∏ ω : NonTarget Sh → Fin 2, atQ h
      (targetVertex (chainScale S.core.parameters C a N) Sh p
        (directionModulus S N dirs.poly p) z u ω)) *
      retainedWeights S C a N dirs p z u| ≤
      (1 + (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ)) ^
        (2 ^ Fintype.card (NonTarget Sh) +
          Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1)) := by
  classical
  let V : ℝ := FromArithmetic.masterScaleV S.core.parameters N C.gap
  let d := Fintype.card (NonTarget Sh)
  have hc : ∀ x : ℚ, |atQ h x| ≤ 1 + V := by
    intro x
    by_cases hx : x.den = 1
    · rw [atQ, if_pos hx]
      exact (hh x.num).trans (by
        dsimp [V]
        linarith [chainWeight_le_masterScaleV S C N (Sh.row Sh.star).anchor x.num])
    · simp [atQ, hx]
      dsimp [V]
      positivity
  have htarget : |∏ ω : NonTarget Sh → Fin 2, atQ h
      (targetVertex (chainScale S.core.parameters C a N) Sh p
        (directionModulus S N dirs.poly p) z u ω)| ≤ (1 + V) ^ (2 ^ d) := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _ω : NonTarget Sh → Fin 2, (1 + V) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => hc _)
      _ = _ := by simp [d]
  have hcard (I : NonTarget Sh) :
      Fintype.card {R : NonTarget Sh // R ≠ I} = d - 1 := by
    calc
      _ = Fintype.card {R : NonTarget Sh //
          R ∈ (Finset.univ : Finset (NonTarget Sh)).erase I} :=
        (Fintype.card_congr (c_elim2_univEraseSubtypeEquiv I)).symm
      _ = ((Finset.univ : Finset (NonTarget Sh)).erase I).card := by simp
      _ = d - 1 := by simp [d]
  have hretained : |retainedWeights S C a N dirs p z u| ≤
      (1 + V) ^ (d * 2 ^ (d - 1)) := by
    unfold retainedWeights
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ I : NonTarget Sh, ∏ _η : {R : NonTarget Sh // R ≠ I} → Fin 2,
          (1 + V) := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro I hI
        rw [Finset.abs_prod]
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro η hη
        have hb := sol_root_atQ_weight_bounds S C N (Sh.row I.1).anchor
          (rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
            (fun k => z k + ∑ R : {R : NonTarget Sh // R ≠ I},
              (u R.1 (η R) : ℚ) * dirs.translation
                (chainScale S.core.parameters C a N)
                (directionModulus S N dirs.poly p) p R.1.1 k))
        rw [abs_of_nonneg (by linarith [hb.1])]
        dsimp [V]
        linarith [hb.2]
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, hcard]
        rw [← pow_mul]
        simp [d, Nat.mul_comm]
  rw [abs_mul]
  calc
    _ ≤ (1 + V) ^ (2 ^ d) * (1 + V) ^ (d * 2 ^ (d - 1)) :=
      mul_le_mul htarget hretained (abs_nonneg _) (by dsimp [V]; positivity)
    _ = _ := by rw [← pow_add]

theorem sol_root_sampling_cost
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (d B e : ℕ) :
    Tendsto (fun N => (1 + (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ)) ^ e *
      (m : ℝ) * sol_root_error S C N d B) atTop (𝓝 0) := by
  classical
  let V : ℕ → ℕ := fun N => FromArithmetic.masterScaleV S.core.parameters N C.gap
  let err : ℕ → ℝ := fun N => sol_root_error S C N d B
  have hVtop : Tendsto (fun N => (V N : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (masterScaleV_tendsto_atTop S.core.parameters C.gap)
  have herrSmall : SuperPolynomialSmall err (fun N => (V N : ℝ)) := by
    apply superPolynomialSmall_fintype_sum
    intro j
    simpa [err, V, sol_root_error, sol_root_envelope] using
      (c_elim2_pivotTranslationError_superpolynomial S C j d B)
  have hVge2 (N : ℕ) : 2 ≤ V N := by
    dsimp [V, FromArithmetic.masterScaleV]
    omega
  have hErrNonneg : ∀ᶠ N in atTop, 0 ≤ err N := by
    have hden : ∀ᶠ N in atTop, ∀ j : Fin m,
        Real.log (S.core.parameters.X N (C.block j).1 : ℝ) >
          (primorial (N + 1) : ℝ) / S.core.parameters.X N (C.block j).1 := by
      filter_upwards [] with N
      intro j
      exact c_elim2_harmonicCutoffLogCondition (primorial_pos (N + 1))
        (S.gapStage.valid_raw_cutoffs N (C.block j).1)
    filter_upwards [hden] with N hN
    dsimp [err, sol_root_error]
    apply Finset.sum_nonneg
    intro j hj
    unfold FromArithmetic.harmonicTranslationUniformError
    have hX : 0 < (S.core.parameters.X N (C.block j).1 : ℝ) := by
      have hcut := S.gapStage.valid_raw_cutoffs N (C.block j).1
      have hW := primorial_pos (N + 1)
      have hXnat : 0 < S.core.parameters.X N (C.block j).1 := by omega
      exact_mod_cast hXnat
    have hdenom : 0 < (S.core.parameters.X N (C.block j).1 : ℝ) *
        (Real.log (S.core.parameters.X N (C.block j).1 : ℝ) -
          (primorial (N + 1) : ℝ) / S.core.parameters.X N (C.block j).1) :=
      mul_pos hX (sub_pos.mpr (hN j))
    exact le_min (by norm_num) (div_nonneg (by positivity) hdenom.le)
  have hSampleCost (q : ℕ) :
      Tendsto (fun N => (1 + (V N : ℝ)) ^ q * (Fintype.card (Fin m) : ℝ) * err N)
        atTop (𝓝 0) := by
    have hsmall := SuperPolynomialSmall.tendsto_mul_nat_pow herrSmall hVtop q
    have hconst : Tendsto
        (fun N => ((2 : ℝ) ^ q * (Fintype.card (Fin m) : ℝ)) *
          ((V N : ℝ) ^ q * err N)) atTop (𝓝 0) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        hsmall.const_mul ((2 : ℝ) ^ q * (Fintype.card (Fin m) : ℝ))
    have hle : ∀ᶠ N in atTop,
        (1 + (V N : ℝ)) ^ q * (Fintype.card (Fin m) : ℝ) * err N ≤
          ((2 : ℝ) ^ q * (Fintype.card (Fin m) : ℝ)) *
            ((V N : ℝ) ^ q * err N) := by
      filter_upwards [hErrNonneg] with N herr
      have hV : 1 ≤ (V N : ℝ) := by exact_mod_cast le_trans (by omega) (hVge2 N)
      have hpow : (1 + (V N : ℝ)) ^ q ≤ (2 * (V N : ℝ)) ^ q := by
        apply pow_le_pow_left₀ (by positivity) _ q
        nlinarith
      have hpowCard : (1 + (V N : ℝ)) ^ q * (Fintype.card (Fin m) : ℝ) ≤
          (2 * (V N : ℝ)) ^ q * (Fintype.card (Fin m) : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      have hmul := mul_le_mul_of_nonneg_right hpowCard herr
      simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hnonneg : ∀ᶠ N in atTop,
        0 ≤ (1 + (V N : ℝ)) ^ q * (Fintype.card (Fin m) : ℝ) * err N := by
      filter_upwards [hErrNonneg] with N hN
      positivity
    exact squeeze_zero' hnonneg hle hconst
  simpa [V, err] using hSampleCost e

theorem sol_root_pivot_finite_sum
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N : ℕ) (F : (Fin m → ℤ) → ℝ) :
    (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z * F z) =
      ∑ z : {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N},
        pivotMass S.core.parameters C N z.1 * F z.1 := by
  classical
  rw [tsum_eq_sum (L := SummationFilter.unconditional (Fin m → ℤ))
    (s := c_elim2_pivotSupport S.core.parameters C N)
    (f := fun z => pivotMass S.core.parameters C N z * F z)
    (by intro z hz; simp [c_elim2_pivotMass_zero_of_not_mem_support
      S.core.parameters C N z hz])]
  simpa only [Finset.attach_eq_univ] using
    (Finset.sum_attach (c_elim2_pivotSupport S.core.parameters C N)
      (fun z => pivotMass S.core.parameters C N z * F z)).symm

theorem sol_root_pivot_root_step
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N B : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (p : Fin q → ℕ)
    (hfacts : IntegerDirectionFacts S C a N dirs tests B p)
    (u : NonTarget Sh → Fin 2 → ℕ) (h : ℤ → ℝ)
    (hh : ∀ y, |h y| ≤ 1 + chainWeight S.core.parameters C N
      (Sh.row Sh.star).anchor y) :
    |(∑ z : {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N},
        pivotMass S.core.parameters C N z.1 *
          ((∏ ω : NonTarget Sh → Fin 2, atQ h
            (targetVertex (chainScale S.core.parameters C a N) Sh p
              (directionModulus S N dirs.poly p) (fun k => (z.1 k : ℚ)) u ω)) *
            averagedRetainedWeights S C a N dirs p (fun k => (z.1 k : ℚ)) u)) -
      ∑ z : {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N},
        pivotMass S.core.parameters C N z.1 *
          ((∏ ω : NonTarget Sh → Fin 2, atQ h
            (targetVertex (chainScale S.core.parameters C a N) Sh p
              (directionModulus S N dirs.poly p) (fun k => (z.1 k : ℚ)) u ω)) *
            retainedWeights S C a N dirs p (fun k => (z.1 k : ℚ)) u)| ≤
      (1 + (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ)) ^
        (2 ^ Fintype.card (NonTarget Sh) +
          Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1)) *
        (m : ℝ) * sol_root_error S C N (Fintype.card (NonTarget Sh)) B := by
  classical
  let cscale := chainScale S.core.parameters C a N
  let d := Fintype.card (NonTarget Sh)
  let H := S.core.parameters.H N C.gap
  let U0 := Fin H
  letI : Nonempty U0 := ⟨⟨0, S.core.parameters.Hpos N C.gap⟩⟩
  let Z := {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N}
  let G : (Fin m → ℤ) → ℝ := fun z => ∏ ω : NonTarget Sh → Fin 2, atQ h
    (targetVertex cscale Sh p (directionModulus S N dirs.poly p)
      (fun k => (z k : ℚ)) u ω)
  let F : (Fin m → ℤ) → ℝ := fun z =>
    G z * retainedWeights S C a N dirs p (fun k => (z k : ℚ)) u
  let T := (S.primeStage.pool N C.gap).upper + FromArithmetic.masterScaleV S.core.parameters N C.gap
  have hroot := hfacts.2.1
  let vi : Fin m → ℤ := fun k => Classical.choose (hroot k)
  have hvi (k : Fin m) : (vi k : ℚ) =
      dirs.rootTranslation cscale (S.core.parameters.M N) p k ∧
      (primorial (N + 1) : ℤ) ∣ vi k ∧ (vi k).natAbs ≤ T ^ B :=
    Classical.choose_spec (hroot k)
  let shift (v : U0) : Fin m → ℤ := fun k => (v.val : ℤ) * vi k
  have hshiftq (v : U0) (k : Fin m) : (shift v k : ℚ) =
      (v.val : ℚ) * dirs.rootTranslation cscale (S.core.parameters.M N) p k := by
    simp only [shift, Int.cast_mul, Int.cast_natCast, (hvi k).1]
  have hshiftCast (z : Fin m → ℤ) (v : U0) :
      (fun k => ((z k + shift v k : ℤ) : ℚ)) =
        fun k => (z k : ℚ) + (v.val : ℚ) *
          dirs.rootTranslation cscale (S.core.parameters.M N) p k := by
    funext k
    simp [hshiftq v k]
  have hGshift (z : Fin m → ℤ) (v : U0) :
      G (fun k => z k + shift v k) = G z := by
    have hresponse : rowForm cscale (Sh.row Sh.star) p
        (dirs.rootTranslation cscale (S.core.parameters.M N) p) = 0 :=
      hfacts.2.2.2.2.2.1
    have hform : rowForm cscale (Sh.row Sh.star) p
        (fun k => (z k : ℚ) + (v.val : ℚ) *
          dirs.rootTranslation cscale (S.core.parameters.M N) p k) =
        rowForm cscale (Sh.row Sh.star) p (fun k => (z k : ℚ)) := by
      rw [c_elim2_rowForm_add, hresponse]
      ring
    unfold G targetVertex
    rw [hshiftCast z v, hform]
  have hFshift (z : Fin m → ℤ) (v : U0) :
      F (fun k => z k + shift v k) = G z * retainedWeights S C a N dirs p
        (fun k => (z k : ℚ) + (v.val : ℚ) *
          dirs.rootTranslation cscale (S.core.parameters.M N) p k) u := by
    unfold F
    rw [hGshift, hshiftCast]
  have havg (z : Fin m → ℤ) :
      c_elim2_uniformFintypeAverage (fun v : U0 => F (fun k => z k + shift v k)) =
        G z * averagedRetainedWeights S C a N dirs p (fun k => (z k : ℚ)) u := by
    simp_rw [hFshift]
    unfold c_elim2_uniformFintypeAverage averagedRetainedWeights
    simp only [U0, Fintype.card_fin]
    rw [← Finset.mul_sum]
    have hsum : (∑ v : U0, retainedWeights S C a N dirs p
        (fun k => (z k : ℚ) + (v.val : ℚ) *
          dirs.rootTranslation cscale (S.core.parameters.M N) p k) u) =
        ∑ v ∈ Finset.range H, retainedWeights S C a N dirs p
          (fun k => (z k : ℚ) + (v : ℚ) *
            dirs.rootTranslation cscale (S.core.parameters.M N) p k) u := by
      exact Fin.sum_univ_eq_sum_range
        (fun v : ℕ => retainedWeights S C a N dirs p
          (fun k => (z k : ℚ) + (v : ℚ) *
            dirs.rootTranslation cscale (S.core.parameters.M N) p k) u) H
    rw [hsum]
    dsimp [H, cscale]
    ring
  have hshiftBound (v : U0) (k : Fin m) :
      |(shift v k : ℝ)| ≤ (sol_root_envelope S C N d B : ℝ) := by
    have hnat : (shift v k).natAbs ≤ H * T ^ B := by
      simp only [shift, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul v.isLt.le (hvi k).2.2
    have henv : H * T ^ B ≤ sol_root_envelope S C N d B := by
      unfold sol_root_envelope
      change H * T ^ B ≤ (d + 1) * (H + 1) * T ^ B
      apply Nat.mul_le_mul_right
      calc
        H = 1 * H := by simp
        _ ≤ (d + 1) * (H + 1) := Nat.mul_le_mul (by omega) (by omega)
    have hcast : |(shift v k : ℝ)| = ((shift v k).natAbs : ℝ) := by
      have hc := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (shift v k))
      simpa using hc.symm
    rw [hcast]
    exact_mod_cast hnat.trans henv
  have hFbound (z : Fin m → ℤ) : |F z| ≤
      (1 + (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ)) ^
        (2 ^ d + d * 2 ^ (d - 1)) :=
    sol_root_product_bound S C a N dirs p (fun k => (z k : ℚ)) u h hh
  have herror (v : U0) :
      |(∑ z : Z, pivotMass S.core.parameters C N z.1 *
          F (fun k => z.1 k + shift v k)) -
        ∑ z : Z, pivotMass S.core.parameters C N z.1 * F z.1| ≤
      (1 + (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ)) ^
        (2 ^ d + d * 2 ^ (d - 1)) * (m : ℝ) * sol_root_error S C N d B := by
    have hs := sol_root_pivot_translation_bound S C N d B (shift v)
      (by
        intro k
        have hd := dvd_mul_of_dvd_right (hvi k).2.1 (v.val : ℤ)
        obtain ⟨b, hb⟩ := hd
        exact ⟨b, hb⟩)
      (hshiftBound v) F _ (by positivity) hFbound
    rw [sol_root_pivot_finite_sum, sol_root_pivot_finite_sum] at hs
    exact hs
  change |(∑ z : Z, pivotMass S.core.parameters C N z.1 *
      (G z.1 * averagedRetainedWeights S C a N dirs p (fun k => (z.1 k : ℚ)) u)) -
    ∑ z : Z, pivotMass S.core.parameters C N z.1 * F z.1| ≤ _
  simp_rw [← havg]
  rw [sol_root_finite_mean_commute]
  rw [← sol_root_uniform_mean_const (α := U0)
    (∑ z : Z, pivotMass S.core.parameters C N z.1 * F z.1)]
  rw [sol_root_uniform_mean_sub]
  exact sol_root_uniform_mean_bound _ _ herror

theorem sol_root_good_prime_mass
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) :
    (∑ p : {p : Fin q → ℕ // p ∈ c_elim2_goodPrimeSupport S C N Sh dirs tests},
      gapSlotMass S C.gap N p.1) =
      gapSlotProbability S C.gap N (GoodTuple S C.gap N tests dirs.poly) := by
  classical
  let Good : (Fin q → ℕ) → Prop := GoodTuple S C.gap N tests dirs.poly
  let lo : Fin q → ℕ := fun _ => (S.primeStage.pool N C.gap).lower
  let hi : Fin q → ℕ := fun _ => (S.primeStage.pool N C.gap).upper
  let Psupport := c_elim2_independentPrimeSupport lo hi
  let PGood := {p : Fin q → ℕ // p ∈ c_elim2_goodPrimeSupport S C N Sh dirs tests}
  let prob := gapSlotProbability S C.gap N Good
  have hPzero (p : Fin q → ℕ) (hp : p ∉ Psupport) :
      gapSlotMass S C.gap N p = 0 := by
    simpa [gapSlotMass, Psupport, lo, hi] using
      c_elim2_independentPrimePoolMass_zero_of_not_mem_support lo hi p
        (by simpa [Psupport] using hp)
  have hmasszero (p : Fin q → ℕ) (hp : p ∉ Psupport) :
      independentPrimePoolMass lo hi p = 0 := by
    simpa [gapSlotMass, lo, hi] using hPzero p hp
  have hprobBase : prob =
      ∑ p ∈ Psupport, gapSlotMass S C.gap N p * (if Good p then 1 else 0) := by
    unfold prob gapSlotProbability independentPrimePoolProbability
    rw [tsum_eq_sum (L := SummationFilter.unconditional (Fin q → ℕ))
      (s := Psupport)
      (f := fun p => independentPrimePoolMass lo hi p * (if Good p then 1 else 0))
      (by intro p hp; simp [hmasszero p hp])]
    simp [gapSlotMass, lo, hi]
  have hprobFilter :
      (∑ p ∈ Psupport, gapSlotMass S C.gap N p * (if Good p then 1 else 0)) =
        ∑ p ∈ Psupport.filter Good, gapSlotMass S C.gap N p := by
    calc
      _ = ∑ p ∈ Psupport, if Good p then gapSlotMass S C.gap N p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hgood : Good p <;> simp [hgood]
      _ = _ := by rw [← Finset.sum_filter]
  have hprobAttach :
      (∑ p ∈ Psupport.filter Good, gapSlotMass S C.gap N p) =
        ∑ p : PGood, gapSlotMass S C.gap N p.1 := by
    change (∑ p ∈ Psupport.filter Good, gapSlotMass S C.gap N p) =
      ∑ p : {p : Fin q → ℕ // p ∈ Psupport.filter Good}, gapSlotMass S C.gap N p.1
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach (Psupport.filter Good) (fun p => gapSlotMass S C.gap N p)).symm
  have hgoodMass : ∑ p : PGood, gapSlotMass S C.gap N p.1 = prob := by
    calc
      _ = ∑ p ∈ Psupport.filter Good, gapSlotMass S C.gap N p := hprobAttach.symm
      _ = prob := hprobFilter.symm.trans hprobBase.symm
  exact hgoodMass

theorem sol_root_elimination_error_average
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 : ℕ)
    (hprob : 0 < gapSlotProbability S C.gap N (GoodTuple S C.gap N tests dirs.poly))
    (hL : ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      0 < shiftLength S C.gap J0 N dirs.poly p)
    (F G : (Fin q → ℕ) → (Fin m → ℚ) → (NonTarget Sh → Fin 2 → ℕ) → ℝ)
    (δ : ℝ)
    (herror : ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      ∀ u : NonTarget Sh → Fin 2 → ℕ,
        |(∑ z : {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N},
            pivotMass S.core.parameters C N z.1 * F p (fun k => (z.1 k : ℚ)) u) -
          ∑ z : {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N},
            pivotMass S.core.parameters C N z.1 * G p (fun k => (z.1 k : ℚ)) u| ≤ δ) :
    |eliminationAverage S C N dirs tests J0 F -
      eliminationAverage S C N dirs tests J0 G| ≤ δ := by
  classical
  let P := {p : Fin q → ℕ // p ∈ c_elim2_goodPrimeSupport S C N Sh dirs tests}
  let Z := {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N}
  let prob := gapSlotProbability S C.gap N (GoodTuple S C.gap N tests dirs.poly)
  let wP : P → ℝ := fun p => prob⁻¹ * gapSlotMass S C.gap N p.1
  let wZ : Z → ℝ := fun z => pivotMass S.core.parameters C N z.1
  let U (p : P) := NonTarget Sh → Fin 2 → Fin (shiftLength S C.gap J0 N dirs.poly p.1)
  have hpGood (p : P) : GoodTuple S C.gap N tests dirs.poly p.1 :=
    (Finset.mem_filter.mp p.2).2
  letI (p : P) : Nonempty (U p) := ⟨fun _ _ => ⟨0, hL p.1 (hpGood p)⟩⟩
  have hPnonneg (p : P) : 0 ≤ wP p := by
    apply mul_nonneg (inv_nonneg.mpr hprob.le)
    unfold gapSlotMass independentPrimePoolMass
    apply Finset.prod_nonneg
    intro i hi
    unfold primePoolLaw primePoolMass
    split_ifs <;> positivity
  have hPsum : ∑ p : P, wP p = 1 := by
    unfold wP
    rw [← Finset.mul_sum, sol_root_good_prime_mass]
    exact inv_mul_cancel₀ hprob.ne'
  have hfinite (A : (Fin q → ℕ) → (Fin m → ℚ) → (NonTarget Sh → Fin 2 → ℕ) → ℝ) :
      eliminationAverage S C N dirs tests J0 A =
        ∑ p : P, wP p * ∑ z : Z, wZ z *
          c_elim2_uniformFintypeAverage (fun u : U p =>
            A p.1 (fun k => (z.1 k : ℚ)) (fun R j => (u R j).val)) := by
    rw [c_elim2_eliminationAverage_eq_finiteGoodSupport]
    simp_rw [c_elim2_shiftAverage_eq_uniformFintypeAverage]
    dsimp only [wP, wZ]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hfinite F, hfinite G, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply sol_root_finite_mean_bound wP _ δ hPnonneg hPsum
  intro p
  rw [sol_root_finite_mean_commute, sol_root_finite_mean_commute,
    sol_root_uniform_mean_sub]
  exact sol_root_uniform_mean_bound _ δ
    (fun u : U p => herror p.1 (hpGood p) (fun R j => (u R j).val))

end
end HindmanSumsProducts
