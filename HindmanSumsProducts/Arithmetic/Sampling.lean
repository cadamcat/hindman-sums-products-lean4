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

/-- Pointwise harmonic estimates underlying Lemma `lem:sampling`. -/
theorem sampling_pointwise_claim (X W : ℕ) (hX : 2 ≤ X)
    (hlog : Real.log X > (W : ℝ) / X) : SamplingPointwiseBounds X W := by
  sorry

/-- Uniform sampling on an integer interval: residue total-mass error and translation error
from §3 lines 132–143. -/
theorem uniform_interval_sampling_bounds (a T k : ℕ) (hT : 0 < T) (hk : 0 < k) :
    finiteL1
        (fun r : Fin k =>
          ∑ n ∈ (Finset.Ico a (a + T)), if n % k = r.val then 1 / (T : ℝ) else 0)
        (uniformResidueLaw k) ≤ 2 * k / T := by
  sorry

/-- Translating a uniform integer interval by u changes its probability law in total-mass
norm by at most `2 min(1,|u|/T)` (§3 lines 137–140). -/
def uniformIntegerIntervalLaw (a : ℤ) (T : ℕ) (z : ℤ) : ℝ :=
  if a ≤ z ∧ z < a + T then 1 / (T : ℝ) else 0

theorem uniform_interval_translation_bound (a u : ℤ) (T : ℕ) (hT : 0 < T) :
    arithmeticL1 (translatedLaw (uniformIntegerIntervalLaw a T) u)
      (uniformIntegerIntervalLaw a T) ≤
      2 * min 1 (|u| / (T : ℝ)) := by
  sorry

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
theorem lem_sampling (X W : ℕ) (hX : 2 ≤ X)
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
  refine ⟨sampling_pointwise_claim X W hX hlog, ?_⟩
  intro Wseq K H V Xseq hK hH hV hW hXseq hden hDomX hDomLogX
  exact sampling_asymptotics Wseq K H V Xseq hK hH hV hW hXseq hden hDomX hDomLogX

end
end HindmanSumsProducts
