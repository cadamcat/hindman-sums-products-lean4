import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for the §4 proof package `Elim` (owned by its proof lane). -/

namespace HindmanSumsProducts
open Filter
open FromArithmetic
open scoped Topology

/-- Encode a chain tail as the finite-coordinate divisor template used by §3. -/
noncomputable def tailDivisorTemplate {n : ℕ} (T : Finset (Fin n)) :
    DivisorTemplate n n where
  arity := T.card
  arity_le := by simpa using Finset.card_le_univ T
  cutoff i := ((T.equivFinOfCardEq rfl).symm i).val

/-- An arity-zero divisor template contributes the constant weight one. -/
theorem nuB_divisorTemplate_arity_zero {n b : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (D : DivisorTemplate n b) (hD : D.arity = 0) (y : ℤ) :
    nuB (divisorTemplateLaw A N D) y = 1 := by
  cases D with
  | mk arity arity_le cutoff =>
    have hzero : arity = 0 := hD
    subst arity
    simp [nuB, divisorTemplateLaw, harmonicProductLaw]
    rw [tsum_eq_single 1]
    · simp
    · intro σ hσ
      simp [hσ]

theorem weighted_variance_identity (b h c : ℝ) :
    b * h ^ 2 - (2 * c) * (b * h) + c ^ 2 * b = b * (h - c) ^ 2 := by
  ring

/-- Expand a finite product of `1 + f` into its subset moments. -/
theorem prod_one_add_eq_powerset_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) :
    ∏ i ∈ s, (1 + f i) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
  exact Finset.prod_one_add s

/-- Limits commute with a fixed finite sum. -/
theorem tendsto_finset_sum_of_pointwise {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ → ℝ) (g : α → ℝ)
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (g i))) :
    Tendsto (fun n => ∑ i ∈ s, f i n) atTop (𝓝 (∑ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- If every subset term has limit one, their sum has the expected power-of-two limit. -/
theorem tendsto_powerset_sum_of_tendsto_one {α : Type*} [DecidableEq α]
    (s : Finset α) (E : ℕ → Finset α → ℝ)
    (hE : ∀ t ∈ s.powerset, Tendsto (fun n => E n t) atTop (𝓝 1)) :
    Tendsto (fun n => ∑ t ∈ s.powerset, E n t) atTop (𝓝 ((2 : ℝ) ^ s.card)) := by
  have hsum := tendsto_finset_sum_of_pointwise s.powerset
    (fun t n => E n t) (fun _ => (1 : ℝ)) hE
  simpa [Finset.card_powerset] using hsum

/-- The three auxiliary moments force the weighted square error to tend to zero. -/
theorem tendsto_weighted_variance_from_moments
    (E0 E1 E2 : ℕ → ℝ) (a c : ℝ)
    (h0 : Tendsto E0 atTop (𝓝 a))
    (h1 : Tendsto E1 atTop (𝓝 (a * c)))
    (h2 : Tendsto E2 atTop (𝓝 (a * c ^ 2))) :
    Tendsto (fun n => E2 n - (2 * c) * E1 n + c ^ 2 * E0 n) atTop (𝓝 0) := by
  have hlin : Tendsto
      (fun n => E2 n - (2 * c) * E1 n + c ^ 2 * E0 n) atTop
      (𝓝 (a * c ^ 2 - (2 * c) * (a * c) + c ^ 2 * a)) := by
    exact (h2.sub (h1.const_mul (2 * c))).add (h0.const_mul (c ^ 2))
  convert hlin using 1 <;> ring_nf

/-- The pointwise target-cube product is dominated by its product of weight bounds. -/
theorem target_cube_product_abs_le_targetBound
    {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (p : Fin q → ℕ) (z : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ)
    (g : ℤ → ℝ)
    (hg : ∀ y, |g y| ≤ 1 + chainWeight S.core.parameters C N
      (Sh.row Sh.star).anchor y) :
    |∏ ω : NonTarget Sh → Fin 2,
        atQ g (targetVertex (chainScale S.core.parameters C a N) Sh p
          (directionModulus S N dirs.poly p) z u ω)| ≤
      targetBound S C a N dirs p z u := by
  classical
  have hfactor (ω : NonTarget Sh → Fin 2) :
      |atQ g (targetVertex (chainScale S.core.parameters C a N) Sh p
        (directionModulus S N dirs.poly p) z u ω)| ≤
      1 + atQ (chainWeight S.core.parameters C N (Sh.row Sh.star).anchor)
        (targetVertex (chainScale S.core.parameters C a N) Sh p
          (directionModulus S N dirs.poly p) z u ω) := by
    let x := targetVertex (chainScale S.core.parameters C a N) Sh p
      (directionModulus S N dirs.poly p) z u ω
    by_cases hx : x.den = 1
    · simpa [atQ, x, hx] using hg x.num
    · simp [atQ, x, hx]
  rw [Finset.abs_prod]
  unfold targetBound
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    (fun ω _ => hfactor ω)

end HindmanSumsProducts
