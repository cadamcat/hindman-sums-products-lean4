import HindmanSumsProducts.OAIAlignment
import HindmanSumsProducts.ChainSelection

/-!
# Framework: two principles and their combinatorial deduction

Definitions in this file follow §2 of `02_framework.tex`. Its asymptotic index is `N`, so the
paper's `w` is `N + 1`, and OAI's admissible parameter and model objects are reused literally.
-/

namespace HindmanSumsProducts

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- A block is OAI's pivot together with its nonempty earlier tail. -/
abbrev FrameworkBlock (n : ℕ) := OAI.SourceBlocks.Block n

/-- The paper's added-block relation `𝓔_B` (equation `eq:adding-blocks`). -/
def E_B {n : ℕ} (B : FrameworkBlock n) : Set (Finset (Fin n)) :=
  {A | OAI.SourceBlocks.Added B.1 B.2.val A}

/-- An ordered list of OAI blocks is a chain precisely when its tails and pivots satisfy the
ordering condition `eq:block-chain`; this is the same predicate as `IsChain` in
`ChainSelection.lean`. -/
def IsBlockChain {n m : ℕ} (B : Fin m → FrameworkBlock n) : Prop :=
  IsChain (fun d => (B d).2.val) (fun d => (B d).1)

/-- Earlier blocks of a chain lie in the later block's added-block family; this is the
combinatorial reason for the tail-then-pivot ordering in `eq:block-chain`. -/
theorem earlier_chain_block_mem_E {n m : ℕ} (B : Fin m → FrameworkBlock n)
    (hB : IsBlockChain B) {k d : Fin m} (hkd : k < d) :
    OAI.SourceBlocks.Added (B d).1 (B d).2.val (B k).set := by
  rcases hB with ⟨htail, htails, htailPivot, hpivots⟩
  refine ⟨(B k).2.val, (B k).1, htail k, ?_, ?_, hpivots hkd, rfl⟩
  · intro p hp t ht
    exact htails k d hkd p hp t ht
  · intro t ht
    exact htailPivot d k t ht

/-- The rational scale vectors reused from OpenAI's word plan. -/
abbrev FrameworkScale (n : ℕ) := OAI.ConstructedWordPlan.GlobalWordPlan.Scale n

/-- The value of a scale vector on a block, using OpenAI's `blockProduct`. -/
def blockScale {n : ℕ} (b : FrameworkScale n) (B : FrameworkBlock n) : ℚ :=
  OAI.ConstructedWordPlan.AlignmentScales.blockProduct b B.set

/-- The paper's scale-list closure condition `eq:scale-list-closure`. -/
def ScaleListsClosed {n : ℕ} (bs : Finset (FrameworkScale n)) (vs : Finset ℚ) : Prop :=
  ∀ b ∈ bs, ∀ B : FrameworkBlock n, blockScale b B ∈ vs

/-- The total law sequence: where the paper's interval lower bound holds this is exactly
`A.law N hX`; before that (a finite initial segment) it is the zero measure. -/
def frameworkLaw {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) :
    Measure (Fin n → ℕ) :=
  if hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i then A.law N hX else 0

/-- On every index where OAI's interval hypothesis is available, the total law is exactly
`Parameters.law`; the proof argument is irrelevant by proof irrelevance. -/
theorem frameworkLaw_eq {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) :
    frameworkLaw A N = A.law N hX := by
  simp [frameworkLaw, hX]

/-- The raw tail product in a sampled vector. -/
def tailValue {n : ℕ} (B : FrameworkBlock n) (t : Fin n → ℕ) : ℕ :=
  ∏ j ∈ B.2.val, t j

/-- Divisor weight `ν_B(y) = E_{σ=t_T} σ 1_{σ|y}` (equation `eq:divisor-weight`). The integral
is against the raw tail marginal of OAI's product law; the integrand depends only on the tail. -/
def divisorWeight {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : FrameworkBlock n) (y : ℤ) : ℝ :=
  ∫ t, if (tailValue B t : ℤ) ∣ y then (tailValue B t : ℝ) else 0 ∂frameworkLaw A N

/-- A rational argument is a colour hit only when it is an actual positive-integer-domain
argument. This is the paper's extension-by-zero convention for colour indicators. -/
def rationalColorHit {r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (q : ℚ) : Prop :=
  ∃ x : ℕ, 0 < x ∧ (x : ℚ) = q ∧ χ x = c

/-- The real-valued indicator associated to `rationalColorHit`. -/
noncomputable def rationalColorIndicator {r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (q : ℚ) : ℝ := by
  classical
  exact if rationalColorHit χ c q then 1 else 0

/-- The sum form `L_J` from equation `eq:sum-forms`. The last index is the maximum of `J`. -/
def sumForm {m : ℕ} (c : Fin m → ℚ) (J : Finset (Fin m)) (hJ : J.Nonempty)
    (z : Fin m → ℕ) : ℚ :=
  ∑ k ∈ J, (c k / c (J.max' hJ)) * (z k : ℚ)

/-- All nonempty subset product colour indicators, the product mask `U` of
`eq:product-mask`. -/
abbrev NonemptySubsets (m : ℕ) := {J : Finset (Fin m) // J.Nonempty}

/-- Subsets indexing the nonsingleton sum factors in `eq:weighted-count`. -/
abbrev NonsingletonSubsets (m : ℕ) := {J : Finset (Fin m) // 2 ≤ J.val.card}

/-- All nonempty subset product colour indicators, the product mask `U` of
`eq:product-mask`. -/
def productMask {m r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (coeff : Fin m → ℚ)
    (z : Fin m → ℕ) : ℝ :=
  ∏ J : NonemptySubsets m,
    rationalColorIndicator χ c (∏ k ∈ J.val, coeff k * (z k : ℚ))

/-- A rational argument to a divisor weight is extended by zero off the integer lattice. -/
noncomputable def rationalDivisorWeight {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : FrameworkBlock n) (q : ℚ) : ℝ := by
  classical
  exact if hq : ∃ y : ℤ, (y : ℚ) = q then divisorWeight A N B (Classical.choose hq) else 0

/-- Evaluate a piecewise model at a rational argument, extending by zero away from integers. -/
noncomputable def rationalModelValue {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (N : ℕ) (B : FrameworkBlock n)
    (v : ℚ) (c : Fin r) (q : ℚ) : ℝ := by
  classical
  exact if hq : ∃ k : ℤ, (k : ℚ) = q then
    S.model N B v c (Classical.choose hq)
  else 0

/-- Marginal law of the pivot coordinate of a block. -/
def pivotLaw {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : Fin m → FrameworkBlock n) (d : Fin m) : Measure ℕ :=
  Measure.map (fun t : Fin n → ℕ => t (B d).1) (frameworkLaw A N)

/-- The weighted count `𝓘_{b,c,𝐁}` in equation `eq:weighted-count`. Independent divisor samples
are represented by separate factors of `divisorWeight`. The base variables have the pivot laws
from `A.law`; the paper's `μ_i` are their one-coordinate marginals. -/
def weightedCount {n m r : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (χ : ℕ → Fin r) (colour : Fin r) (b : FrameworkScale n)
    (B : Fin m → FrameworkBlock n) : ℝ := by
  let coeff : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  exact ∫ z, productMask χ colour coeff z *
      (∏ d, rationalDivisorWeight A N (B d) (z d : ℚ)) *
      (∏ J : NonsingletonSubsets m, by
        classical
        let hJ : J.val.Nonempty := by
          have hcard : 2 ≤ J.val.card := J.property
          exact Finset.card_pos.mp (by omega)
        let d := J.val.max' hJ
        exact rationalColorIndicator χ colour (coeff d * sumForm coeff J.val hJ z) *
          rationalDivisorWeight A N (B d) (sumForm coeff J.val hJ z)
      ) ∂ Measure.pi (pivotLaw A N B)

/-- The actual model integrand compared to the weighted count in
`eq:prediction-counting`, evaluated at `z(t)_d=t_{B_d}`. -/
def modelIntegrandMean {n m r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (N : ℕ) (χ : ℕ → Fin r)
    (colour : Fin r) (b : FrameworkScale n) (B : Fin m → FrameworkBlock n) : ℝ :=
  ∫ t, by
    classical
    let coeff : Fin m → ℚ := fun d =>
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A.ht N) (B d).set : ℚ) * blockScale b (B d)
    let z : Fin m → ℕ := fun d => tailValue (B d) t * t (B d).1
    exact productMask χ colour coeff z *
      ∏ J : NonsingletonSubsets m, by
        have hJ : J.val.Nonempty := by
          have hcard : 2 ≤ J.val.card := J.property
          exact Finset.card_pos.mp (by omega)
        let d := J.val.max' hJ
        exact rationalModelValue S N (B d) (blockScale b (B d)) colour
          (sumForm coeff J.val hJ z)
  ∂ frameworkLaw A N

/-- Calibration-failure event for one `(B,a,c)`: the centre colour is correct while the model is
at most `2τ`. -/
def calibrationFailureSet {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (B : FrameworkBlock n) (a : ℚ) (c : Fin r) (τ : ℝ) : Set (Fin n → ℕ) :=
  {t | rationalColorHit χ c
      ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A.ht N) B.set : ℚ) * a * (tailValue B t : ℚ)) ∧
    S.model N B a c
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (fun j => (t j : ℤ)) B.set) ≤ 2 * τ}

/-- Calibration-failure probability under `A.law N _` (with the finite initial segment convention
of `frameworkLaw`). -/
def calibrationProbability {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (B : FrameworkBlock n) (a : ℚ) (c : Fin r) (τ : ℝ) : ℝ :=
  (frameworkLaw A N).real (calibrationFailureSet S χ N B a c τ)

/-- Upper-bound notation for a limit along an ultrafilter. The sequences here are bounded
probabilities (or absolute differences of two `[0,1]` expectations), so this is equivalent to the
paper's `lim_U f ≤ bound`. -/
def UltrafilterLimLE (U : Ultrafilter ℕ) (f : ℕ → ℝ) (bound : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ N in (U : Filter ℕ), f N < bound + ε

/-- The Prediction Principle `pr:prediction`, in OAI's admissible-parameter and raw-menu
vocabulary. The quantifier order makes `s` depend only on `m`. `U` may be any nonprincipal
ultrafilter; lists and tolerances are fixed before the parameters and models are supplied. -/
def PredictionPrinciple : Prop :=
  ∀ m, 2 ≤ m → ∃ s, ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.cofinite →
  ∀ n r (χ : ℕ → Fin r) (bs : Finset (FrameworkScale n)) (vs : Finset ℚ),
    (∀ b ∈ bs, ∀ j, 0 < b j) → (∀ v ∈ vs, 0 < v) → ScaleListsClosed bs vs →
    ∀ τ η : ℝ, 0 < τ → τ < 1/4 → 0 < η →
    ∃ (A : OAI.SourceAdmissible.Parameters n) (F : OAI.SourceRawMenu.Menu s)
      (S : OAI.SourceRawMenu.ModelsSystem A vs r F),
      (∀ B : FrameworkBlock n, ∀ a ∈ vs, ∀ c : Fin r,
        UltrafilterLimLE U (fun N => calibrationProbability S χ N B a c τ) (3*τ+η)) ∧
      (∀ (B : Fin m → FrameworkBlock n), IsBlockChain B →
        ∀ b ∈ bs, ∀ c : Fin r,
          UltrafilterLimLE U
            (fun N => |weightedCount A N χ c b B - modelIntegrandMean S N χ c b B|) η)

/-- Alignment Principle `pr:alignment`; this is exactly OpenAI's proved statement and is not
restated in this file. -/
theorem alignment_principle : OAI.SourceRawMenu.Alignment := oai_alignment

/-- The rational shift written in the paper's alignment implication. -/
def paperAlignmentShift {n : ℕ} (ht : Fin n → ℤ) (b : FrameworkScale n)
    (u : Fin n → ℕ) (B : FrameworkBlock n) (D : Finset (Finset (Fin n))) : ℚ :=
  ∑ A ∈ D,
    (((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height ht A : ℚ) *
        OAI.ConstructedWordPlan.AlignmentScales.blockProduct b A) /
      ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height ht B.set : ℚ) *
        blockScale b B)) *
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (fun j => (u j : ℤ)) A : ℚ)

/-- Bridge between the paper's displayed shift and OAI's `SourceBlocks.offset`. -/
theorem oai_alignment_event_bridge {n : ℕ} (ht : Fin n → ℤ) (b : FrameworkScale n)
    (u : Fin n → ℕ) (B : FrameworkBlock n) (D : Finset (Finset (Fin n))) :
    paperAlignmentShift ht b u B D = OAI.SourceBlocks.offset ht b u B D := by
  rfl

/-- Finite calibration-error union bound in the ultrafilter-limit form used at lines 289–330. -/
theorem calibration_union_bound {ι : Type} [DecidableEq ι] (U : Ultrafilter ℕ)
    (I : Finset ι) (p : ι → ℕ → ℝ) (bound : ℝ)
    (hp : ∀ i ∈ I, UltrafilterLimLE U (p i) bound) :
    UltrafilterLimLE U (fun N => ∑ i ∈ I, p i N) ((I.card : ℝ) * bound) := by
  intro ε hε
  let ε' : ℝ := ε / ((I.card : ℝ) + 1)
  have hε' : 0 < ε' := by
    dsimp [ε']
    positivity
  have hall : ∀ᶠ N in (U : Filter ℕ), ∀ i ∈ I, p i N < bound + ε' := by
    apply (eventually_all_finset I).2
    intro i hi
    exact hp i hi ε' hε'
  filter_upwards [hall] with N hN
  have hsum : (∑ i ∈ I, p i N) ≤ ∑ i ∈ I, (bound + ε') := by
    apply Finset.sum_le_sum
    intro i hi
    exact le_of_lt (hN i hi)
  have hsumConst : (∑ i ∈ I, (bound + ε')) = (I.card : ℝ) * (bound + ε') := by
    simp
    ring
  have hcardPos : 0 < (I.card : ℝ) + 1 := by positivity
  have hsmall : (I.card : ℝ) * ε' < ε := by
    calc
      (I.card : ℝ) * ε' = ((I.card : ℝ) * ε) / ((I.card : ℝ) + 1) := by
        dsimp [ε']
        ring
      _ < ε := (div_lt_iff₀ hcardPos).2 (by nlinarith)
  calc
    (∑ i ∈ I, p i N) ≤ (I.card : ℝ) * (bound + ε') := hsum.trans_eq hsumConst
    _ = (I.card : ℝ) * bound + (I.card : ℝ) * ε' := by ring
    _ < (I.card : ℝ) * bound + ε := by linarith

/-- Combine an ordinary alignment lower limit and an ultrafilter calibration upper limit
(lines 320–345). The conclusion is the lower bound for their pointwise difference. -/
theorem ultrafilter_alignment_intersection (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite) (alignment calibration : ℕ → ℝ)
    (δ ε : ℝ) (hε : 0 < ε)
    (halign : ∀ ε' > 0, ∀ᶠ N in Filter.atTop, δ - ε' < alignment N)
    (hcal : UltrafilterLimLE U calibration (δ / 2)) :
    ∀ᶠ N in (U : Filter ℕ), δ / 2 - ε < alignment N - calibration N := by
  have hAlignTop : ∀ᶠ N in Filter.atTop, δ - ε / 2 < alignment N :=
    halign (ε / 2) (by linarith)
  have hUtop : (U : Filter ℕ) ≤ Filter.atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hU
  have hAlign : ∀ᶠ N in (U : Filter ℕ), δ - ε / 2 < alignment N :=
    Filter.Eventually.filter_mono hUtop hAlignTop
  have hCal : ∀ᶠ N in (U : Filter ℕ), calibration N < δ / 2 + ε / 2 :=
    hcal (ε / 2) (by linarith)
  filter_upwards [hAlign, hCal] with N ha hc
  linarith

/-- A lower bound for the model part of the aligned integrand (lines 330–355). The exponent
`2^m` safely dominates the number of nonsingleton subsets. -/
theorem aligned_model_integrand_positive (m : ℕ) (_hm : 2 ≤ m) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (f : NonsingletonSubsets m → ℝ)
    (hf : ∀ J, τ < f J) :
    τ ^ (2 ^ m) ≤ ∏ J : NonsingletonSubsets m, f J := by
  have hcard : Fintype.card (NonsingletonSubsets m) ≤ 2 ^ m := by
    calc
      Fintype.card (NonsingletonSubsets m) ≤ Fintype.card (Finset (Fin m)) :=
        Fintype.card_subtype_le _
      _ = 2 ^ Fintype.card (Fin m) := Fintype.card_finset
      _ = 2 ^ m := by simp
  have hprod : (∏ _J : NonsingletonSubsets m, τ) ≤ ∏ J : NonsingletonSubsets m, f J := by
    apply Finset.prod_le_prod₀
    · intro J hJ
      exact le_of_lt hτ0
    · intro J hJ
      exact le_of_lt (hf J)
  have hprod' : τ ^ Fintype.card (NonsingletonSubsets m) ≤
      ∏ J : NonsingletonSubsets m, f J := by
    convert hprod using 1
    all_goals simp [Finset.prod_const]
  exact (pow_le_pow_of_le_one (le_of_lt hτ0) hτ1 hcard).trans hprod'

/-- A finite sum of nonnegative weighted counts with positive value has a positive summand; this
is applied after choosing an index in the ultrafilter-positive set (lines 355–366). -/
theorem positive_total_count_has_positive_summand {ι : Type} [DecidableEq ι]
    (I : Finset ι) (f : ι → ℝ) (hpos : 0 < ∑ i ∈ I, f i) : ∃ i ∈ I, 0 < f i := by
  by_contra h
  push Not at h
  have hsum : (∑ i ∈ I, f i) ≤ 0 := Finset.sum_nonpos h
  linarith

/-- A positive weighted count yields an actual finite-sums/products configuration (lines
366–375). This includes divisor-support, integer-lattice, and distinctness extraction from the
admissible growth hierarchy. -/
theorem positive_weighted_count_configuration {n m r : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (χ : ℕ → Fin r) (colour : Fin r)
    (b : FrameworkScale n) (B : Fin m → FrameworkBlock n) (hB : IsBlockChain B)
    (hN : ∀ i, 4 * primorial (N + 1) ≤ A.X N i)
    (hpositive : 0 < weightedCount A N χ colour b B) :
    ∃ (C : Finset ℕ), C.card = m ∧ (∀ a ∈ C, 0 < a) ∧
      (∀ D ⊆ C, D.Nonempty → χ (∑ a ∈ D, a) = colour ∧
        χ (∏ a ∈ D, a) = colour) := by
  sorry

/-- Main deduction for `m≥2`, with its long proof packaged into the five claims above. -/
theorem main_of_principles_large (hP : PredictionPrinciple) (r : ℕ) (χ : ℕ → Fin r)
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  sorry

/-- Deduction of the frozen finite sums/products statement from Prediction and Alignment. The
separation parameters in Theorem `thm:main` are omitted because `Challenge.lean` asks only for the
monochromatic configuration. -/
theorem main_of_principles (hP : PredictionPrinciple) (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) :
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  classical
  by_cases hr : r = 0
  · subst r
    exact (Fin.elim0 (χ 0))
  by_cases hm0 : m = 0
  · subst m
    obtain ⟨c⟩ : Nonempty (Fin r) := ⟨χ 0⟩
    refine ⟨∅, c, by simp, by simp, ?_⟩
    intro B hB hne
    have : B = ∅ := Finset.subset_empty.mp hB
    subst B
    simp at hne
  by_cases hm1 : m = 1
  · subst m
    refine ⟨{1}, χ 1, by simp, by simp, ?_⟩
    intro B hB hne
    have hcard : B.card = 1 := by
      have hsubset : B ⊆ ({1} : Finset ℕ) := hB
      have hle : B.card ≤ 1 := Finset.card_le_card hsubset |>.trans (by simp)
      have hpos : 0 < B.card := Finset.card_pos.mpr hne
      omega
    obtain ⟨x, hxB⟩ := Finset.card_eq_one.mp hcard
    have hx : x = 1 := Finset.mem_singleton.mp (hB (by simp [hxB]))
    subst x
    simp [hxB]
  · have hm : 2 ≤ m := by omega
    exact main_of_principles_large hP r χ m hm

/-- The family of nonempty subsets used to define `FS(A)` and `FP(A)`. -/
def nonemptySubsetsOf (A : Finset ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter fun B => B.Nonempty

/-- Finite sums set `FS(A)` (the first set in Corollary `cor:distinct-expressions`). -/
def finiteSumsSet (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsetsOf A).image fun B => ∑ a ∈ B, a

/-- Finite products set `FP(A)` (the second set in Corollary `cor:distinct-expressions`). -/
def finiteProductsSet (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsetsOf A).image fun B => ∏ a ∈ B, a

/-- Sum plus product of the elements preceding an index in an increasing `Fin m` list. -/
def previousMagnitude {m : ℕ} (a : Fin m → ℕ) (d : Fin m) : ℕ :=
  (∑ k ∈ Finset.univ.filter (fun k : Fin m => k < d), a k) +
    ∏ k ∈ Finset.univ.filter (fun k : Fin m => k < d), a k

/-- Corollary `cor:distinct-expressions`: separation makes both subset-expression maps injective,
and their common values are exactly the singleton expressions. -/
theorem distinct_expressions_corollary (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      (∀ B ⊆ A, B.Nonempty → χ (∑ a ∈ B, a) = c ∧ χ (∏ a ∈ B, a) = c) ∧
      (finiteSumsSet A).card = 2 ^ m - 1 ∧
      (finiteProductsSet A).card = 2 ^ m - 1 ∧
      finiteSumsSet A ∩ finiteProductsSet A = A ∧
      (finiteSumsSet A ∪ finiteProductsSet A).card = 2 * (2 ^ m - 1) - m := by
  sorry

/-- Corollary `cor:finite-interval`: the finite interval theorem with prescribed divisibility,
growth separation, and all sums/products in the interval. -/
theorem finite_interval_form (r m q : ℕ) (R D : ℝ)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hq : 1 ≤ q) (hR : 2 ≤ R) (hD : 1 ≤ D) :
    ∃ N : ℕ, ∀ χ : ℕ → Fin r, ∃ (a : Fin m → ℕ) (c : Fin r),
      StrictMono a ∧ (∀ d, q ∣ a d) ∧
      (∀ d, a d ≤ N) ∧
      (∀ J : Finset (Fin m), J.Nonempty →
        (∑ d ∈ J, a d) ≤ N ∧ (∏ d ∈ J, a d) ≤ N ∧
        χ (∑ d ∈ J, a d) = c ∧ χ (∏ d ∈ J, a d) = c) ∧
      (a ⟨0, by omega⟩ : ℝ) > R ∧
      (∀ d : Fin m, 0 < d.val →
        (a d : ℝ) > R * ((previousMagnitude a d : ℝ) ^ D)) := by
  sorry

end
end HindmanSumsProducts
