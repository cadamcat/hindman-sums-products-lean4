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

/-- Finite type of OAI block chains of a fixed length and ambient dimension. -/
abbrev BlockChains (n m : ℕ) := {B : Fin m → FrameworkBlock n // IsBlockChain B}

/-- The block-chain subtype is finite because its ambient list type is finite. -/
noncomputable instance blockChainsFintype (n m : ℕ) : Fintype (BlockChains n m) :=
  Fintype.ofFinite _

/-- A finite rational scale list viewed as a finite subtype. -/
noncomputable instance scaleListSubtypeFintype (vs : Finset ℚ) :
    Fintype {a : ℚ // a ∈ vs} := Fintype.ofFinite _

/-- The calibration triples `(B,a,c)` for fixed finite data. -/
abbrev CalibrationIndex (n r : ℕ) (vs : Finset ℚ) :=
  FrameworkBlock n × {a : ℚ // a ∈ vs} × Fin r

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

/-- Repackage the tails and pivots returned by `chain_selection` as OAI blocks. -/
theorem blocksOfChainSelection {n m : ℕ} (T : Fin m → Finset (Fin n))
    (piv : Fin m → Fin n) (hT : IsChain T piv) :
    ∃ B : Fin m → FrameworkBlock n, IsBlockChain B ∧
      ∀ d, (B d).set = insert (piv d) (T d) := by
  refine ⟨fun d => ⟨piv d, ⟨T d, hT.1 d, ?_⟩⟩, ?_, fun d => rfl⟩
  · intro j hj
    exact hT.2.2.1 d d j hj
  · exact hT

/-- The rational scale vectors reused from OpenAI's word plan. -/
abbrev FrameworkScale (n : ℕ) := OAI.ConstructedWordPlan.GlobalWordPlan.Scale n

/-- The count triples `(b,𝐁,c)` for fixed finite data. -/
abbrev PredictionCountIndex (n m r : ℕ) (bs : Finset (FrameworkScale n)) :=
  {b : FrameworkScale n // b ∈ bs} × BlockChains n m × Fin r

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

/-- The total law is either OAI's probability law or the zero measure. -/
noncomputable instance frameworkLawIsZeroOrProbabilityMeasure {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) :
    MeasureTheory.IsZeroOrProbabilityMeasure (frameworkLaw A N) := by
  rw [MeasureTheory.isZeroOrProbabilityMeasure_iff]
  unfold frameworkLaw
  split_ifs with hX
  · haveI : MeasureTheory.IsProbabilityMeasure (A.law N hX) :=
      OAI.SourceMenuAlignment.law_probability A N hX
    exact Or.inr MeasureTheory.IsProbabilityMeasure.measure_univ
  · simp

/-- The total law is finite at the whole sample space. -/
theorem frameworkLaw_ne_top_univ {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) :
    frameworkLaw A N Set.univ ≠ ⊤ := by
  have hcases : frameworkLaw A N Set.univ = 0 ∨ frameworkLaw A N Set.univ = 1 :=
    (MeasureTheory.isZeroOrProbabilityMeasure_iff).mp inferInstance
  rcases hcases with hzero | hone
  · simpa [hzero]
  · simpa [hone]

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

/-- Calibration failure set at a finite triple `(B,a,c)`. -/
def calibrationFailureAt {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (τ : ℝ) (i : CalibrationIndex n r vs) : Set (Fin n → ℕ) :=
  calibrationFailureSet S χ N i.1 i.2.1 i.2.2 τ

/-- Union of the finitely many calibration-failure events. -/
def calibrationUnionSet {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (τ : ℝ) : Set (Fin n → ℕ) :=
  ⋃ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
    calibrationFailureAt S χ N τ i

/-- Probability that at least one calibration failure occurs. The index type is finite. -/
def calibrationUnionProbability {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (τ : ℝ) : ℝ :=
  (frameworkLaw A N).real (calibrationUnionSet S χ N τ)

/-- Probability form of the union bound for the finite calibration family. -/
theorem calibration_failure_union_probability_le {n r s : ℕ}
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceRawMenu.Menu s} (S : OAI.SourceRawMenu.ModelsSystem A vs r F)
    (χ : ℕ → Fin r) (N : ℕ) (τ : ℝ) :
    calibrationUnionProbability S χ N τ ≤
      ∑ i : CalibrationIndex n r vs,
        calibrationProbability S χ N i.1 i.2.1 i.2.2 τ := by
  classical
  unfold calibrationUnionProbability calibrationUnionSet
  calc
    (frameworkLaw A N).real (calibrationUnionSet S χ N τ) ≤
      ∑ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
        (frameworkLaw A N).real (calibrationFailureAt S χ N τ i) :=
      MeasureTheory.measureReal_biUnion_finset_le _ _
    _ = _ := by simp [calibrationFailureAt, calibrationProbability]

/-- The alignment event from OpenAI's model event predicate. -/
def alignmentEventSet {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (bs : Finset (FrameworkScale n))
    (N : ℕ) (τ : ℝ) : Set (Fin n → ℕ) :=
  OAI.SourceMenuAlignment.event bs (S.model N) (A.ht N) τ

/-- OAI alignment-event probability, evaluated using the total law sequence. -/
def alignmentProbability {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (bs : Finset (FrameworkScale n))
    (N : ℕ) (τ : ℝ) : ℝ :=
  (frameworkLaw A N).real (alignmentEventSet S bs N τ)

/-- Mass of samples that align and avoid every calibration failure. -/
def goodAlignmentProbability {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceRawMenu.Menu s}
    (S : OAI.SourceRawMenu.ModelsSystem A vs r F) (χ : ℕ → Fin r)
    (bs : Finset (FrameworkScale n)) (N : ℕ) (τ : ℝ) : ℝ :=
  (frameworkLaw A N).real
    (alignmentEventSet S bs N τ ∩ (calibrationUnionSet S χ N τ)ᶜ)

/-- Upper-bound notation for a limit along an ultrafilter. The sequences here are bounded
probabilities (or absolute differences of two `[0,1]` expectations), so this is equivalent to the
paper's `lim_U f ≤ bound`. -/
def UltrafilterLimLE (U : Ultrafilter ℕ) (f : ℕ → ℝ) (bound : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ N in (U : Filter ℕ), f N < bound + ε

/-- A pointwise smaller sequence has the same ultrafilter upper bound. -/
theorem UltrafilterLimLE.mono {U : Ultrafilter ℕ} {f g : ℕ → ℝ} {bound : ℝ}
    (hfg : ∀ N, f N ≤ g N) (hg : UltrafilterLimLE U g bound) :
    UltrafilterLimLE U f bound := by
  intro ε hε
  filter_upwards [hg ε hε] with N hN
  exact lt_of_le_of_lt (hfg N) hN

/-- Increasing the comparison bound preserves `UltrafilterLimLE`. -/
theorem UltrafilterLimLE.bound_mono {U : Ultrafilter ℕ} {f : ℕ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : UltrafilterLimLE U f a) : UltrafilterLimLE U f b := by
  intro ε hε
  filter_upwards [hf ε hε] with N hN
  exact lt_of_lt_of_le hN (by linarith)

/-- Extract eventual lower bounds from an ordinary lower limit for a sequence in `[0,1]`. -/
theorem liminf_bound_eventually {f : ℕ → ℝ} {δ : ℝ}
    (hf0 : ∀ N, 0 ≤ f N) (hf1 : ∀ N, f N ≤ 1)
    (hδ : δ ≤ Filter.liminf f Filter.atTop) :
    ∀ ε, 0 < ε → ∀ᶠ N in Filter.atTop, δ - ε < f N := by
  have hCob : Filter.IsCoboundedUnder (fun x y : ℝ => y ≤ x) Filter.atTop f :=
    Filter.IsCoboundedUnder.of_frequently_le
      (Filter.Frequently.of_forall fun N => hf1 N)
  have hBdd : Filter.IsBoundedUnder (fun x y : ℝ => y ≤ x) Filter.atTop f :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hf0)
  intro ε hε
  exact (Filter.le_liminf_iff (h₁ := hCob) (h₂ := hBdd)).mp hδ
    (δ - ε) (by linarith)

/-- For a finite measure, removing a bad event reduces event mass by at most the bad-event mass. -/
theorem measureReal_inter_compl_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≠ ⊤) (s t : Set α) :
    μ.real (s ∩ tᶜ) ≥ μ.real s - μ.real t := by
  have hsub : s ⊆ (s ∩ tᶜ) ∪ t := by
    intro x hx
    by_cases hxt : x ∈ t
    · exact Or.inr hxt
    · exact Or.inl ⟨hx, hxt⟩
  have hnot : μ ((s ∩ tᶜ) ∪ t) ≠ ⊤ := by
    intro hs
    have hle : μ ((s ∩ tᶜ) ∪ t) ≤ μ Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ ((s ∩ tᶜ) ∪ t))
    rw [hs] at hle
    exact hμ (top_unique hle)
  have hmono := MeasureTheory.measureReal_mono hsub hnot
  have hunion := MeasureTheory.measureReal_union_le (μ := μ) (s ∩ tᶜ) t
  linarith [hmono, hunion]

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

/-- The calibration union and the alignment event leave positive mass along the ultrafilter. -/
theorem goodAlignmentMass_eventually {n r s : ℕ}
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceRawMenu.Menu s} (S : OAI.SourceRawMenu.ModelsSystem A vs r F)
    (χ : ℕ → Fin r) (bs : Finset (FrameworkScale n)) (τ δ : ℝ)
    (hAlign : δ ≤ Filter.liminf (fun N => alignmentProbability S bs N τ) Filter.atTop)
    (hBad : UltrafilterLimLE U (fun N => calibrationUnionProbability S χ N τ) (δ/2)) :
    ∀ ε, 0 < ε → ∀ᶠ N in (U : Filter ℕ),
      δ/2 - ε < goodAlignmentProbability S χ bs N τ := by
  have hA0 : ∀ N, 0 ≤ alignmentProbability S bs N τ := by
    intro N
    exact MeasureTheory.measureReal_nonneg
  have hA1 : ∀ N, alignmentProbability S bs N τ ≤ 1 := by
    intro N
    exact MeasureTheory.measureReal_le_one
  have hAlignEventually := liminf_bound_eventually hA0 hA1 hAlign
  intro ε hε
  have hDiff := ultrafilter_alignment_intersection U hU
    (fun N => alignmentProbability S bs N τ)
    (fun N => calibrationUnionProbability S χ N τ) δ ε hε hAlignEventually hBad
  have hPoint : ∀ N,
      alignmentProbability S bs N τ - calibrationUnionProbability S χ N τ ≤
        goodAlignmentProbability S χ bs N τ := by
    intro N
    have hmass := measureReal_inter_compl_ge (frameworkLaw A N)
      (frameworkLaw_ne_top_univ A N)
      (alignmentEventSet S bs N τ) (calibrationUnionSet S χ N τ)
    exact hmass
  filter_upwards [hDiff] with N hN
  exact lt_of_lt_of_le hN (hPoint N)

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

/-- The outer tolerances can be chosen after the alignment mass and the two finite index counts
are fixed, as in `eq:outer-tolerances`. -/
theorem existsFrameworkTolerances {C K δ : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hδ : 0 < δ) (m : ℕ) :
    ∃ τ η : ℝ, 0 < τ ∧ τ < 1/4 ∧ 3*C*τ < δ/4 ∧ 0 < η ∧
      C*η < δ/4 ∧ K*η < δ*τ^(2^m)/4 := by
  let τ : ℝ := min (1/8) (δ / (100 * (C + 1)))
  have hdenC : 0 < C + 1 := by linarith
  have hratioC : C / (C + 1) ≤ 1 := (div_le_iff₀ hdenC).2 (by linarith)
  have hτpos : 0 < τ := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hτlt : τ < 1/4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hτsmall : τ ≤ δ / (100 * (C + 1)) := min_le_right _ _
  have hCτ : C * τ ≤ δ / 100 := by
    calc
      C * τ ≤ C * (δ / (100 * (C + 1))) := mul_le_mul_of_nonneg_left hτsmall hC
      _ = δ / 100 * (C / (C + 1)) := by field_simp
      _ ≤ δ / 100 := by
        simpa using mul_le_mul_of_nonneg_left (a := δ / 100) hratioC (by positivity)
  have hCτ' : 3 * C * τ < δ / 4 := by nlinarith
  let η : ℝ := min (δ / (100 * (C + 1)))
    (δ * τ ^ (2 ^ m) / (100 * (K + 1)))
  have hdenK : 0 < K + 1 := by linarith
  have hratioK : K / (K + 1) ≤ 1 := (div_le_iff₀ hdenK).2 (by linarith)
  have hηpos : 0 < η := lt_min (div_pos hδ (by positivity))
    (div_pos (mul_pos hδ (pow_pos hτpos _)) (by positivity))
  have hηCsmall : η ≤ δ / (100 * (C + 1)) := min_le_left _ _
  have hCη : C * η ≤ δ / 100 := by
    calc
      C * η ≤ C * (δ / (100 * (C + 1))) := mul_le_mul_of_nonneg_left hηCsmall hC
      _ = δ / 100 * (C / (C + 1)) := by field_simp
      _ ≤ δ / 100 := by
        simpa using mul_le_mul_of_nonneg_left (a := δ / 100) hratioC (by positivity)
  have hηKsmall : η ≤ δ * τ ^ (2 ^ m) / (100 * (K + 1)) := min_le_right _ _
  have hKη : K * η ≤ δ * τ ^ (2 ^ m) / 100 := by
    calc
      K * η ≤ K * (δ * τ ^ (2 ^ m) / (100 * (K + 1))) :=
        mul_le_mul_of_nonneg_left hηKsmall hK
      _ = δ * τ ^ (2 ^ m) / 100 * (K / (K + 1)) := by field_simp
      _ ≤ δ * τ ^ (2 ^ m) / 100 :=
        by
          simpa using mul_le_mul_of_nonneg_left (a := δ * τ ^ (2 ^ m) / 100)
            hratioK (by positivity)
  have hδτpos : 0 < δ * τ ^ (2 ^ m) := mul_pos hδ (pow_pos hτpos _)
  refine ⟨τ, η, hτpos, hτlt, hCτ', hηpos, ?_, ?_⟩
  · nlinarith
  · nlinarith

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
  classical
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ Filter.cofinite := by
    exact Filter.hyperfilter_le_cofinite
  obtain ⟨s, hPstep⟩ := hP m hm
  obtain ⟨n, hchainSelection⟩ := chain_selection m r
  obtain ⟨bs, vs, δ, hδ, hbs, hvs, hclosed, hAlign⟩ :=
    alignment_principle n r s
  let C : ℝ := Fintype.card (CalibrationIndex n r vs)
  let K : ℝ := Fintype.card (PredictionCountIndex n m r bs)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨τ, η, hτ, hτlt, hτC, hη, hηC, hηK⟩ :=
    existsFrameworkTolerances hC hK hδ m
  obtain ⟨A, F, S, hcalibration, hcount⟩ :=
    hPstep U hU n r χ bs vs hbs hvs hclosed τ η hτ hτlt hη
  have hAlignMass : δ ≤ Filter.liminf (fun N => alignmentProbability S bs N τ) Filter.atTop := by
    apply hAlign A F S (fun N => frameworkLaw A N)
    · intro N hX
      exact frameworkLaw_eq A N hX
    · exact hτ
  have hCalibrationSum : UltrafilterLimLE U
      (fun N => ∑ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
        calibrationProbability S χ N i.1 i.2.1 i.2.2 τ)
      ((Fintype.card (CalibrationIndex n r vs) : ℝ) * (3*τ+η)) := by
    apply calibration_union_bound U Finset.univ
    · intro i hi
      exact hcalibration i.1 i.2.1.val i.2.1.property i.2.2
  have hCalibrationUnion : UltrafilterLimLE U
      (fun N => calibrationUnionProbability S χ N τ) (C * (3*τ+η)) := by
    apply UltrafilterLimLE.mono (f := fun N => calibrationUnionProbability S χ N τ)
      (g := fun N => ∑ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
        calibrationProbability S χ N i.1 i.2.1 i.2.2 τ)
    · intro N
      simpa using calibration_failure_union_probability_le S χ N τ
    · simpa [C] using hCalibrationSum
  have hCalibrationUnionSmall : C * (3*τ+η) < δ/2 := by
    calc
      C * (3*τ+η) = 3*C*τ + C*η := by ring
      _ < δ/4 + δ/4 := add_lt_add hτC hηC
      _ = δ/2 := by ring
  have hCalibrationBound : UltrafilterLimLE U
      (fun N => calibrationUnionProbability S χ N τ) (δ/2) :=
    UltrafilterLimLE.bound_mono (le_of_lt hCalibrationUnionSmall) hCalibrationUnion
  have hGoodMass := goodAlignmentMass_eventually U hU S χ bs τ δ hAlignMass hCalibrationBound
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
