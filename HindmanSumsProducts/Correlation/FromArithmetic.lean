import HindmanSumsProducts.Correlation.Defs

/-!
The arithmetic results cited by §4 are declared here while the arithmetic
lane develops §3. These declarations are copied interfaces, not proofs of
new arithmetic facts; the coordinator will unify them with that lane.
-/

namespace HindmanSumsProducts

attribute [local instance] Classical.propDecidable

noncomputable section

open MeasureTheory
open Filter
open scoped Topology
open scoped BigOperators ENNReal

/-- Ordinary convergence to zero, used to state every paper `o(1)` claim. -/
def tendsToZero (f : ℕ → ℝ) : Prop := Tendsto f atTop (𝓝 0)

/-- OpenAI's domination predicate, with the §2 name used in this lane. -/
abbrev dominatesPowers := OAI.MicrocellScale.Dominates

/-- The harmonic normalizer `Z_X` in Lemma `lem:sampling`. -/
def harmonicNormalizer (X W : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico X (X ^ 2), if W.Coprime n then (n : ℝ)⁻¹ else 0

/-- OpenAI's harmonic `W`-unit probability law, which is the paper's `μ_X`. -/
def harmonicLaw (X W : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X) : Measure ℕ :=
  (OAI.RawHarmonicProbability.law X W hW hX : Measure ℕ)

/-- The explicit error `E_X(k)` in equation `eq:harmonic-residue-error`. -/
def harmonicResidueError (X W k : ℕ) : ℝ :=
  (W : ℝ) * (k + 1) / ((X : ℝ) *
    (Real.log X - (W : ℝ) / X))

/-- Total variation error of the reciprocal prime law modulo `Q` from the
uniform law on the unit residue classes. -/
noncomputable def primePoolResidueTV (P : Finset ℕ) (Q : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ Finset.range Q,
    |primeAverage P (fun p => if p % Q = a then 1 else 0) -
      (if Nat.Coprime a Q then 1 / (Nat.totient Q : ℝ) else 0)|

/-- Probability under the independent reciprocal prime law that a fixed
nonzero integer polynomial vanishes. -/
noncomputable def polynomialZeroProbability {q : ℕ} (pool : Finset ℕ)
    (P : MvPolynomial (Fin q) ℤ) : ℝ := by
  classical
  exact primeTupleAverage pool fun u =>
    if P.eval (fun i => (u i : ℤ)) = 0 then 1 else 0

/-- Probability under independent pool slots of a repeated prime entry. -/
noncomputable def repeatedPrimeProbability {q : ℕ} (pool : Finset ℕ) : ℝ := by
  classical
  exact primeTupleAverage pool fun u =>
    if ∃ i j : Fin q, i ≠ j ∧ u i = u j then 1 else 0

/-- Countable `L¹` distance between finite measures; all laws here have finite
support. -/
noncomputable def measureL1 {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (μ ν : Measure α) : ℝ :=
  ∑' x, |μ.real {x} - ν.real {x}|

/-- Translation of the natural harmonic law, viewed as a measure on `ℤ`. -/
def translatedHarmonicLaw (X W : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X)
    (h : ℤ) : Measure ℤ :=
  Measure.map (fun y : ℕ => (y : ℤ) + h) (harmonicLaw X W hW hX)

/-- The law of `kY`, and the unnormalized weighted divisibility law `η_k`. -/
def dilatedHarmonicLaw (X W k : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X) : Measure ℕ :=
  Measure.map (fun y : ℕ => k * y) (harmonicLaw X W hW hX)

def weightedDivisibilityLaw (X W k : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X) : Measure ℕ :=
  (harmonicLaw X W hW hX).withDensity fun y =>
    if k ∣ y then (k : ℝ≥0∞) else 0

/-- The weighted progression law `k 1_{y≡h (mod k)} μ_X` used for the cube root. -/
def harmonicProgressionLaw (X W k h : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X) :
    Measure ℕ :=
  (harmonicLaw X W hW hX).withDensity fun y =>
    if y % k = h % k then (k : ℝ≥0∞) else 0

/-- Law of `kY+h` for `Y∼μ_X`. -/
def harmonicAffineLaw (X W k h : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X) :
    Measure ℕ :=
  Measure.map (fun y : ℕ => k * y + h) (harmonicLaw X W hW hX)

/-- Right-hand side of the explicit total-variation estimate in
equation `eq:correlation-root-tv-bound`. -/
def harmonicRootTVScale (X W k H : ℕ) : ℝ :=
  Real.log (2 * k) / Real.log X + (H : ℝ) / X +
    (W : ℝ) * k ^ 2 /
      (((Nat.totient W : ℝ) / W) * X * Real.log X)

/-- Dilation and translation estimate for the root law, used in
`eq:correlation-root-progression`. -/
theorem harmonic_root_progression_bound
    (X W k h H : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X)
    (hlog : (W : ℝ) / X < Real.log X)
    (hk : 0 < k) (hkX : k ≤ X) (hcop : Nat.Coprime k W)
    (hdiv : W ∣ h) (hh : h ≤ H) (hHX : 2 * H < X) :
    ∃ C : ℝ, 0 < C ∧
      measureL1 (harmonicAffineLaw X W k h hW hX)
        (harmonicProgressionLaw X W k h hW hX) ≤
        C * harmonicRootTVScale X W k H := by
  sorry

/-- All finite and asymptotic conclusions of §3 Lemma `lem:sampling`, including
the exact endpoint errors and their fixed-power consequences. -/
structure SamplingConclusion (X W : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X) where
  logarithmic_cutoff : (W : ℝ) / X < Real.log X
  /-- Endpoints are natural cutoffs, matching every use in §§3–4. -/
  periodic_harmonic : ∀ (A B k a : ℕ), 0 < A → A < B → 0 < k →
    Nat.Coprime k W → a < k →
      |(∑ n ∈ Finset.Ico A B,
          if W.Coprime n ∧ n % k = a then (n : ℝ)⁻¹ else 0) -
        (Nat.totient W : ℝ) / k *
          Real.log ((B : ℝ) / A)| ≤ (Nat.totient W : ℝ) / A
  normalizer : |harmonicNormalizer X W -
      (Nat.totient W : ℝ) / W * Real.log X| ≤ (Nat.totient W : ℝ) / X
  residue_pointwise : ∀ (k a : ℕ), 0 < k → Nat.Coprime k W → a < k →
    |k * (harmonicLaw X W hW hX).real {y | y % k = a} - 1| ≤
      harmonicResidueError X W k
  residue_total_variation : ∀ k, 0 < k → Nat.Coprime k W →
    (∑ a ∈ Finset.range k,
      |k * (harmonicLaw X W hW hX).real {y | y % k = a} - 1|) / (2 * k) ≤
        harmonicResidueError X W k
  translation : ∀ h : ℤ, (W : ℤ) ∣ h →
    measureL1 (translatedHarmonicLaw X W hW hX h)
      (Measure.map (fun y : ℕ => (y : ℤ)) (harmonicLaw X W hW hX)) ≤
        min 2 (2 * |h| / ((X : ℝ) *
          (Real.log X - (W : ℝ) / X)))
  dilation : ∀ k, 0 < k → k ≤ X → Nat.Coprime k W →
    measureL1 (dilatedHarmonicLaw X W k hW hX)
      (weightedDivisibilityLaw X W k hW hX) ≤
        (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) /
          (Real.log X - (W : ℝ) / X)
  dilation_mass : ∀ k, 0 < k → Nat.Coprime k W →
    |(weightedDivisibilityLaw X W k hW hX).real Set.univ - 1| ≤
      harmonicResidueError X W k

/-- Lemma `lem:sampling`, §3, lines 34–84. Its fields state the paper's
periodic harmonic estimate, residue law, translation and dilation laws. -/
theorem sampling_changes (X W : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X)
    (hlog : (W : ℝ) / X < Real.log X) : SamplingConclusion X W hW hX := by
  sorry

/-- Fixed-power uniform consequence from the final paragraph of
Lemma `lem:sampling`. -/
theorem sampling_fixed_power_errors
    (X W K H V : ℕ → ℕ)
    (hResidueTranslation : dominatesPowers (fun n => X n)
      (fun n => 2 + W n + K n + H n + V n))
    (hDilation : dominatesPowers (fun n => Real.log (X n : ℝ))
      (fun n => 2 + W n + K n + V n))
    (C : ℝ) (hC : 0 < C) :
    tendsToZero (fun n => (V n : ℝ) ^ C *
      (harmonicResidueError (X n) (W n) (K n) +
       (H n : ℝ) / ((X n : ℝ) *
         (Real.log (X n) - (W n : ℝ) / X n)) +
       (2 * Real.log (K n) + (W n : ℝ) * K n / X n *
         (1 + 1 / X n)) /
           (Real.log (X n) - (W n : ℝ) / X n))) := by
  sorry

/-- Prime slots uniform on the unit residues modulo `W^e`. -/
def unitResidueTuples (q w e : ℕ) : Finset (Fin q → ZMod (primorial w ^ e)) := by
  classical
  have hQ : 0 < primorial w ^ e := Nat.pow_pos (primorial_pos w)
  letI : NeZero (primorial w ^ e) := ⟨Nat.ne_of_gt hQ⟩
  exact Finset.univ.filter fun u => ∀ i, IsUnit (u i)

/-- Probability of the small-prime exceptional event from Lemma
`lem:master-scales`, computed on independent uniform unit slots modulo `W^e`.
Because `p^e ∣ W^e` for every prime `p ≤ w`, divisibility of the canonical
residue is the required congruence. -/
def smallPrimeExceptionProbability {q : ℕ} (w e : ℕ)
    (P : MvPolynomial (Fin q) ℤ) : ℝ := by
  classical
  let Q := primorial w ^ e
  have hQ : 0 < Q := Nat.pow_pos (primorial_pos w)
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  let U := unitResidueTuples q w e
  let bad := U.filter fun u =>
    ∃ p ∈ Finset.range (w + 1), p.Prime ∧
      p ^ e ∣ (MvPolynomial.eval₂ (Int.castRingHom (ZMod Q)) u P).val
  exact if U.card = 0 then 0 else (bad.card : ℝ) / U.card

/-- Master-scale choices and the facts carried between §§3 and 4. The paper's
`w` is the sequence index, `W=primorial w`, and all scales in this interface
are indexed by `w`. The named fields record the four enumerated clauses of
Lemma `lem:master-scales`; polynomial and prime-tuple estimates are explicit
inputs to the downstream correlation statements. -/
def masterBlockScaleRat {N : ℕ} (h : Fin N → ℕ) (B : PaperBlock N) : ℚ :=
  OAI.ConstructedWordPlan.AlignmentScales.blockProduct
    (fun j => (h j : ℚ)) (OAI.SourceBlocks.Block.set B)

/-- The CRT modulus `Q_l=W^{e₀}∏_{w<p≤V_l}p` from the master-scale lemma. -/
def masterPrimeModulus (w e V : ℕ) : ℕ :=
  primorial w ^ e * ∏ p ∈ (Finset.range (V + 1)).filter
    (fun p => p.Prime ∧ w < p), p

structure MasterScalePackage (N b : ℕ) (A : Finset ℚ) (q : ℕ)
    (D : Finset (MvPolynomial (Fin q) ℤ)) where
  h : ℕ → Fin N → ℕ
  M : ℕ → ℕ
  X : ℕ → Fin N → ℕ
  R : ℕ → Fin N → ℕ
  Pminus : ℕ → Fin N → ℕ
  Pplus : ℕ → Fin N → ℕ
  V : ℕ → Fin N → ℕ
  pool : ℕ → Fin N → Finset ℕ
  smallPrimeExponent : ℕ → ℕ
  h_exact : ∀ w j, h w j = primorial w ^ (w * 2 ^ (N - (j.val + 1)))
  h_smooth : ∀ w j, OAI.RoughScales.Smooth w (h w j : ℤ)
  M_is_W_power : ∀ w, ∃ e, M w = primorial w ^ e
  M_smooth : ∀ w, OAI.RoughScales.Smooth w (M w : ℤ)
  Ww_divides_M : ∀ w, primorial w ^ w ∣ M w
  h_below_M : ∀ w j, h w j ≤ M w
  block_size_bound : ∀ B : PaperBlock N, (OAI.SourceBlocks.Block.set B).card ≤ b
  block_scale_bound : ∀ w (B : PaperBlock N),
    masterBlockScaleRat (h w) B ≤ (M w : ℚ)
  adding_pair_ratio : ∀ w (B E : PaperBlock N),
    OAI.SourceBlocks.Added B.1 B.2.val (OAI.SourceBlocks.Block.set E) →
    ∃ d : ℕ, masterBlockScaleRat (h w) E = masterBlockScaleRat (h w) B *
      (primorial w ^ w : ℚ) * d
  rational_scale_integrality : ∀ᶠ w in atTop, ∀ (B : PaperBlock N) a,
    a ∈ A → ∃ c : ℕ, masterBlockScaleRat (h w) B * a = c
  rational_scale_ratio : ∀ᶠ w in atTop, ∀ (B E : PaperBlock N) a a',
    OAI.SourceBlocks.Added B.1 B.2.val (OAI.SourceBlocks.Block.set E) →
    a ∈ A → a' ∈ A →
    ∃ d : ℕ, masterBlockScaleRat (h w) E * a =
      masterBlockScaleRat (h w) B * a' * (primorial w ^ w : ℚ) * d
  smooth_scale_divides_M : ∀ᶠ w in atTop, ∀ (B : PaperBlock N) a,
    a ∈ A → ∃ c : ℕ,
      masterBlockScaleRat (h w) B * a = c ∧
      primorial w ^ (smallPrimeExponent w + 1) * c ∣ M w
  M_divides_R : ∀ w l, M w ∣ R w l
  previous_R_divides : ∀ w l, ∀ j, j < l → R w j ∣ R w l
  R_dominates_prime_scale : ∀ l, dominatesPowers
    (fun w => (R w l : ℝ)) (fun w => (Pplus w l + V w l : ℝ))
  log_X_dominates_R : ∀ l, dominatesPowers
    (fun w => Real.log (X w l : ℝ)) (fun w => (R w l : ℝ))
  X_is_power_two : ∀ w l, ∃ e, X w l = 2 ^ e
  pool_primes : ∀ w l p, p ∈ pool w l → p.Prime
  V_formula : ∀ w l, V w l = 2 + M w +
    ∏ j ∈ Finset.univ.filter (fun j : Fin N => j < l), X w j ^ 2
  pool_above_V : ∀ w l p, p ∈ pool w l → V w l < p
  pool_in_dyadic_range : ∀ w l p, p ∈ pool w l → Pminus w l ≤ p ∧ p < Pplus w l
  pool_mass_lower : ∀ w l, w * V w l ^ w ≤ primeHarmonicMass (pool w l)
  Pminus_lower : ∀ w l, w * V w l ^ w ≤ Pminus w l
  Pminus_dominates : ∀ l, dominatesPowers
    (fun w => (Pminus w l : ℝ)) (fun w => (V w l : ℝ))
  pool_mass_dominates : ∀ l, dominatesPowers
    (fun w => primeHarmonicMass (pool w l)) (fun w => (V w l : ℝ))
  pool_complete_dyadic_union : ∀ w l, ∃ a b,
    Pminus w l = 2 ^ a ∧ Pplus w l = 2 ^ b ∧
      pool w l = (Finset.Ico (2 ^ a) (2 ^ b)).filter Nat.Prime
  pool_residue_uniform : ∀ l (C₀ : ℝ), 0 < C₀ → tendsToZero fun w =>
    (V w l : ℝ) ^ C₀ * primePoolResidueTV (pool w l)
      (masterPrimeModulus w (smallPrimeExponent w) (V w l))
  polynomial_zero_superpolynomial : ∀ l P, P ∈ D → P ≠ 0 →
    ∀ C₀ : ℝ, 0 < C₀ → tendsToZero fun w =>
      (V w l : ℝ) ^ C₀ * polynomialZeroProbability (pool w l) P
  repeated_slots_superpolynomial : ∀ l (C₀ : ℝ), 0 < C₀ → tendsToZero fun w =>
    (V w l : ℝ) ^ C₀ * repeatedPrimeProbability (q := q) (pool w l)
  polynomial_values_divide_R : ∀ w l (P : MvPolynomial (Fin q) ℤ)
    (u : Fin q → ℕ), P ∈ D → (∀ i, u i ∈ pool w l) →
      P.eval (fun i => (u i : ℤ)) ≠ 0 →
        M w * (Int.natAbs (P.eval fun i => (u i : ℤ))) ∣ R w l
  small_prime_exception_probability : ∀ P, P ∈ D → P ≠ 0 → ∀ᶠ w in atTop,
      smallPrimeExceptionProbability w (smallPrimeExponent w) P ≤ 1 / w
  residue_error : ∀ l, ∀ᶠ w in atTop,
    primeHarmonicMass (pool w l) > 0

/-- Lemma `lem:master-scales`, §3, lines 197–274. -/
theorem master_scales (N b q : ℕ) (A : Finset ℚ)
    (D : Finset (MvPolynomial (Fin q) ℤ))
    (hA : ∀ a ∈ A, 0 < a) (hD : ∀ P ∈ D, P ≠ 0) :
    Nonempty (MasterScalePackage N b A q D) := by
  sorry

/-- Hypotheses for Proposition `prop:linear-forms`. The base residue law,
row-minor tests, and CRT law are stated separately so restricted
prime-only domains retain the absolute error of the paper. -/
noncomputable def primeTupleCRTTV {s : ℕ} (P : Finset ℕ) (Q : ℕ) : ℝ := by
  classical
  let units := (Finset.range Q).filter (fun a => Nat.Coprime a Q)
  let residues := Fintype.piFinset (fun _ : Fin s => units)
  exact (1 / 2) * ∑ a ∈ residues,
    |primeTupleAverage P (fun p =>
      if ∀ i, p i % Q = a i then 1 else 0) -
        1 / (Nat.totient Q : ℝ) ^ s|

/-- Total-variation error of the joint residue law of a base vector modulo
`K` from uniform measure on `(ℤ/Kℤ)^d`. -/
noncomputable def linearBaseResidueTV {d : ℕ} (μ : Measure (Fin d → ℤ))
    (K : ℕ) (_hK : 0 < K) : ℝ := by
  classical
  let residues := Fintype.piFinset (fun _ : Fin d => Finset.range K)
  exact (1 / 2) * ∑ a ∈ residues,
    |μ.real {x | ∀ i, x i % (K : ℤ) = (a i : ℤ)} - 1 / (K : ℝ) ^ d|

/-- One input for the one-gap specialization of Proposition
`prop:linear-forms`. The finite prime slots use the independent reciprocal
law `λ(p)=1/(pS)`; every divisor occurrence is the product of at most `b`
independent harmonic `W`-unit variables. -/
structure LinearFormsTemplate (q d s b : ℕ) where
  coefficient : Fin q → (Fin s → ℕ) → Fin d → ℤ
  polynomialTests : Finset (MvPolynomial (Fin s) ℤ)
  factorCount : Fin q → ℕ
  factorCount_le : ∀ u, factorCount u ≤ b

/-- One scale and sampling instance for fixed linear and divisor templates. -/
structure WeightedLinearFormsInput {q d s b : ℕ}
    (T : LinearFormsTemplate q d s b) where
  V : ℕ
  M : ℕ
  w : ℕ
  smallPrimeExponent : ℕ
  epsilonBase : ℝ
  epsilonCRT : ℝ
  primePool : Finset ℕ
  primePoolPrime : ∀ p ∈ primePool, p.Prime
  primePoolAboveV : ∀ p ∈ primePool, V < p
  primePoolMass_pos : 0 < primeHarmonicMass primePool
  baseLaw : (Fin s → ℕ) → Measure (Fin d → ℤ)
  good : (Fin s → ℕ) → Prop
  rawCutoff : ∀ u, Fin (T.factorCount u) → ℕ
  rawCutoff_large : ∀ u j, 4 * primorial w ≤ rawCutoff u j
  rawFactorLaw : ∀ u, Measure (Fin (T.factorCount u) → ℕ)
  rawFactorLaw_product : ∀ u, rawFactorLaw u = Measure.pi (fun j =>
    harmonicLaw (rawCutoff u j) (primorial w) (primorial_pos w)
      (rawCutoff_large u j))

/-- Law of the divisor `σ_u`, a product of independent raw factors. -/
noncomputable def WeightedLinearFormsInput.divisorLaw {q d s b : ℕ}
    {T : LinearFormsTemplate q d s b} (I : WeightedLinearFormsInput T)
    (u : Fin q) : Measure ℕ :=
  Measure.map (fun x => ∏ j, x j) (I.rawFactorLaw u)

/-- Divisor weight `ν_u(y)=E σ_u 1_{σ_u|y}` for one occurrence. -/
noncomputable def WeightedLinearFormsInput.weight {q d s b : ℕ}
    {T : LinearFormsTemplate q d s b} (I : WeightedLinearFormsInput T)
    (u : Fin q) (y : ℤ) : ℝ :=
  ∫ σ, (σ : ℝ) * (if (σ : ℤ) ∣ y then 1 else 0) ∂ I.divisorLaw u

/-- Linear form `ℓ_u(x;p)` with its integer coefficient vector. -/
def WeightedLinearFormsInput.row {q d s b : ℕ}
    {T : LinearFormsTemplate q d s b} (_I : WeightedLinearFormsInput T) (u : Fin q)
    (p : Fin s → ℕ) (x : Fin d → ℤ) : ℤ :=
  ∑ j, T.coefficient u p j * x j

/-- A tuple of divisor values that can occur under the independent divisor
laws; every expanded weight occurrence receives its own draw. -/
def WeightedLinearFormsInput.PossibleDivisors {q d s b : ℕ}
    {T : LinearFormsTemplate q d s b} (I : WeightedLinearFormsInput T)
    (σ : Fin q → ℕ) : Prop :=
  ∀ u, 0 < (I.divisorLaw u).real {σ u}

/-- Exact base-residue hypothesis (1) of Proposition `prop:linear-forms`. -/
def WeightedLinearFormsInput.BaseResidueUniformity {q d s b : ℕ}
    {T : LinearFormsTemplate q d s b} (I : WeightedLinearFormsInput T) : Prop :=
  ∀ p, I.good p → ∀ σ, I.PossibleDivisors σ →
    ∀ _hK : 0 < ∏ u, σ u,
      linearBaseResidueTV (I.baseLaw p) (∏ u, σ u) _hK ≤ I.epsilonBase

/-- Exact row hypotheses (2) of Proposition `prop:linear-forms`: every row
is primitive, and all pairs are independent whenever the fixed polynomial
tests avoid `π`. -/
def WeightedLinearFormsInput.RowHypotheses {q d s b : ℕ}
    {T : LinearFormsTemplate q d s b} (I : WeightedLinearFormsInput T) : Prop :=
  ∀ p, I.good p → ∀ π, π.Prime → I.w < π → π ≤ I.V →
    (∀ u, ∃ j, ¬ ((π : ℤ) ∣ T.coefficient u p j)) ∧
    ∀ u v, u ≠ v →
      (∀ Q ∈ T.polynomialTests,
        ¬ ((π : ℤ) ∣ Q.eval fun i => (p i : ℤ))) →
      ∃ j k, ¬ ((π : ℤ) ∣
        T.coefficient u p j * T.coefficient v p k -
          T.coefficient u p k * T.coefficient v p j)

/-- Exact CRT-law hypothesis of Proposition `prop:linear-forms`. -/
def WeightedLinearFormsInput.PrimeSlotsCRTUniformity {q d s b : ℕ}
    {T : LinearFormsTemplate q d s b} (I : WeightedLinearFormsInput T) : Prop :=
  primeTupleCRTTV (s := s) I.primePool
    (masterPrimeModulus I.w I.smallPrimeExponent I.V) ≤ I.epsilonCRT

/-- Expectation in Proposition `prop:linear-forms`, restricted to a
prime-only event. -/
noncomputable def weightedLinearFormsAverage {q d s b : ℕ}
    {T : LinearFormsTemplate q d s b} (I : WeightedLinearFormsInput T)
    (E : (Fin s → ℕ) → Prop) : ℝ := by
  classical
  exact primeTupleAverage I.primePool (fun p =>
    if I.good p ∧ E p then
      ∫ x, ∏ u, I.weight u (I.row u p x) ∂ I.baseLaw p else 0)

/-- Proposition `prop:linear-forms`, §3, lines 463–519. The constant is
chosen from the fixed row, divisor, and polynomial templates before the
prime pools and sampling laws are supplied. -/
theorem weighted_linear_forms {q d s b : ℕ}
    (T : LinearFormsTemplate q d s b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (I : WeightedLinearFormsInput T)
      (hw : 2 ≤ I.w)
      (hV : I.V ≥ 1) (hM : I.V ≥ I.M)
      (hdraw : ∀ u, ∀ᵐ σ ∂ I.divisorLaw u, σ ≤ I.V)
      (hbase : I.BaseResidueUniformity)
      (hrows : I.RowHypotheses)
      (hcrt : I.PrimeSlotsCRTUniformity)
      (E : (Fin s → ℕ) → Prop)
      (hE : ∀ p, E p → I.good p),
      |weightedLinearFormsAverage I E -
        primeTupleAverage I.primePool (fun p => if E p then 1 else 0)| ≤
        C * (1 / I.w + (I.V : ℝ) ^ q *
          (I.epsilonBase + I.epsilonCRT)) := by
  sorry

end

end HindmanSumsProducts
