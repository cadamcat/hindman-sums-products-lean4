import HindmanSumsProducts.Prediction.Tests

open scoped BigOperators
open scoped NNReal
open MeasureTheory Filter
open Classical

namespace HindmanSumsProducts.Prediction

/-- Pushforward law of the product `t_B`; local to §5 because the Framework lane owns the
canonical §2 version of this definition. -/
noncomputable def blockProductLaw {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) : Measure ℤ :=
  Measure.map (fun t : Fin n → ℕ => rawBlockProductInt B t) (rawLaw A N)

/-- §3, Lemma `lem:sampling` (lines 34–79): the uniform polynomially-bounded translation
consequence used by §5. This is stated for the exact OAI pivot law and allows shifts in `Wℤ`. -/
theorem sampling_translation_at_scales {n : ℕ} (A : Parameters n) (i : Fin n)
    (V H : ℕ → ℝ) (hV : ∀ N, 1 ≤ V N)
    (hsmall : ∀ C > 0, tendsToZeroAtTop
      (fun N => V N ^ C * H N / (A.X N i : ℝ)))
    (shift : ℕ → ℤ)
    (hWdiv : ∀ N, (primorial (N + 1) : ℤ) ∣ shift N)
    (hshift : ∀ N, |(shift N : ℝ)| ≤ H N)
    (C : ℝ) (hC : 0 ≤ C) (f : ℕ → ℤ → ℝ)
    (hf : ∀ N y, |f N y| ≤ V N ^ C) :
    tendsToZeroAtTop (fun N =>
      |(∫ y, f N (y + shift N) ∂pivotLaw A N i) -
        ∫ y, f N y ∂pivotLaw A N i|) := by
  sorry

/-- §3, Lemma `lem:sampling` (lines 34–79): residue classes modulo a rough divisor have
asymptotically uniform harmonic mass, uniformly when the modulus is polynomially bounded by a
scale dominated by `X_i`. -/
theorem sampling_residue_uniform_at_scales {n : ℕ} (A : Parameters n) (i : Fin n)
    (V : ℕ → ℝ) (hV : ∀ N, 1 ≤ V N)
    (k : ℕ → ℕ) (hk : ∀ N, 0 < k N)
    (hrough : ∀ N, Nat.Coprime (k N) (primorial (N + 1)))
    (hsize : ∃ C : ℝ, 0 ≤ C ∧ ∀ N, (k N : ℝ) ≤ V N ^ C)
    (a : ℕ → ℤ) (ha : ∀ N, 0 ≤ a N ∧ a N < (k N : ℤ)) :
    tendsToZeroAtTop (fun N =>
      |(k N : ℝ) * (pivotLaw A N i).real
          {y | Int.emod y (k N : ℤ) = a N} - 1|) := by
  sorry

/-- §3, Corollary `cor:product-law` (lines 152–183): product-law replacement in the form used
by §5. For every fixed polynomial bound on the integrand, the raw block-product law and
`ν_B μ_i` have the same limit. -/
theorem product_law_integral_replacement {n : ℕ} (A : Parameters n) (B : Block n)
    (V : ℕ → ℝ) (hV : ∀ N, 1 ≤ V N)
    (hgrowth : dominatesPowers (fun N => Real.log (A.X N B.1 : ℝ)) V)
    (C : ℝ) (hC : 0 ≤ C) (f : ℕ → ℤ → ℝ)
    (hf : ∀ N y, |f N y| ≤ V N ^ C) :
    tendsToZeroAtTop (fun N =>
      |(∫ y, f N y ∂blockProductLaw A N B) -
        ∫ y, f N y * divisorWeight A N B y ∂pivotLaw A N B.1|) := by
  sorry

/-- Joint product-law replacement for any fixed list of disjoint OAI blocks, the second clause
of `cor:product-law` and the form used at the end of §5.4. -/
theorem product_law_joint_replacement {n m : ℕ} (A : Parameters n)
    (C : BlockChain n m) (hdisj : ∀ i j, i ≠ j →
      Disjoint (C.block i).set (C.block j).set)
    (V : ℕ → ℝ) (hV : ∀ N, 1 ≤ V N)
    (hgrowth : ∀ d : Fin m,
      dominatesPowers (fun N => Real.log (A.X N (C.block d).1 : ℝ)) V)
    (Cexp : ℝ) (hC : 0 ≤ Cexp) (f : ℕ → (Fin m → ℤ) → ℝ)
    (hf : ∀ N z, |f N z| ≤ V N ^ Cexp) :
    tendsToZeroAtTop (fun N =>
      |(∫ t, f N (fun d => rawBlockProductInt (C.block d) t) ∂rawLaw A N) -
        ∫ z, f N z * (∏ d, divisorWeight A N (C.block d) (z d))
          ∂Measure.pi (fun d : Fin m => pivotLaw A N (C.block d).1)|) := by
  sorry

/-- Witness returned by §3, Lemma `lem:master-scales` (lines 197–252). The finite master count
is kept separate from the asymptotic Lean index `N`; its paper value is `w=N+1`. -/
def masterComplexityScale {K : ℕ} (M : ℕ → ℕ) (X : ℕ → Fin K → ℕ)
    (N : ℕ) (l : Fin K) : ℝ :=
  2 + (M N : ℝ) +
    ∏ j ∈ (Finset.univ.filter fun j : Fin K => j < l), (X N j : ℝ) ^ 2

structure MasterScaleWitness (K : ℕ) where
  M : ℕ → ℕ
  h : ℕ → Fin K → ℤ
  X : ℕ → Fin K → ℕ
  R : ℕ → Fin K → ℕ
  primeLower : ℕ → Fin K → ℕ
  primeUpper : ℕ → Fin K → ℕ
  primePool : ℕ → Fin K → Finset ℕ
  primeWeight : ℕ → Fin K → ℕ → ℝ
  harmonicPrimeMass : ℕ → Fin K → ℝ
  h_formula : ∀ N j,
    h N j = (primorial (N + 1) : ℤ) ^ ((N + 1) * 2 ^ (K - j.val - 1))
  M_power : ∀ N, ∃ e : ℕ, M N = primorial (N + 1) ^ e
  Ww_dvd_M : ∀ N, primorial (N + 1) ^ (N + 1) ∣ M N
  block_height_bound : ∀ (N : ℕ) (B : Block K),
    (integerHeight (h N) B.set).natAbs ≤ M N
  h_div_M : ∀ N j, (h N j).natAbs ≤ M N
  added_block_ratio : ∀ N (B : Block K) (A : Finset (Fin K)),
    OAI.SourceBlocks.Added B.1 B.2.val A →
    ∃ d : ℤ, integerHeight (h N) A = integerHeight (h N) B.set *
      ((primorial (N + 1) : ℤ) ^ (N + 1) * d)
  -- The shared source currently defines `RoughScales` directly under `OAI`.
  h_smooth : ∀ N j, OAI.RoughScales.Smooth
    (N + 1) (h N j)
  X_power_two : ∀ N j, ∃ e : ℕ, X N j = 2 ^ e
  pool_prime : ∀ N j p, p ∈ primePool N j → Nat.Prime p
  pool_range : ∀ N j p, p ∈ primePool N j →
    primeLower N j ≤ p ∧ p < primeUpper N j
  pool_weight_formula : ∀ N j p, primeWeight N j p =
    if p ∈ primePool N j then (p : ℝ)⁻¹ / harmonicPrimeMass N j else 0
  pool_weight_sum : ∀ N j,
    ∑ p ∈ primePool N j, primeWeight N j p = 1
  pool_dyadic_structure : Prop
  pool_lower_endpoint_dominates : ∀ j,
    dominatesPowers (fun N => (primeLower N j : ℝ))
      (fun N => masterComplexityScale M X N j)
  pool_harmonic_mass_dominates : ∀ j,
    dominatesPowers (fun N => harmonicPrimeMass N j)
      (fun N => masterComplexityScale M X N j)
  pool_is_complete_dyadic_union : Prop
  gap_multiple_M : ∀ N j, M N ∣ R N j
  gap_nested : ∀ N i j, i ≤ j → R N i ∣ R N j
  cutoff_growth : ∀ j,
    dominatesPowers (fun N => Real.log (X N j : ℝ))
      (fun N => R N j)
  gap_growth : ∀ j,
    dominatesPowers (fun N => R N j)
      (fun N => (primeUpper N j : ℝ) + masterComplexityScale M X N j)
  -- GAP: expand these three predicates as the exact polynomial-divisibility, small-prime
  -- exception-probability, and CRT-residue formulas from §3 before freezing this package.
  templateDivisibility : Prop
  smallPrimeExceptionalProbability : Prop
  residueUniformity : Prop
  -- GAP: expand the eventual rational-scale integrality and adding-ratio clauses from §3.
  smoothAddedBlockRatios : Prop

/-- §3, Lemma `lem:master-scales` (lines 197–252): choose the scales, cutoffs, prime pools, and
gap lengths for any fixed template list before sending `w=N+1` to infinity. -/
theorem master_scales_exists (K maxBlock slots : ℕ) (A : Finset ℚ)
    (D : Finset (MvPolynomial (Fin slots) ℤ)) :
    Nonempty (MasterScaleWitness K) := by
  sorry

/-- The rough part `|z|_{>w}` from §3. -/
noncomputable def roughPart (w : ℕ) (z : ℤ) : ℕ :=
  ∏ p ∈ z.natAbs.factorization.support.filter (fun p => w < p),
    p ^ z.natAbs.factorization p

/-- A finite harmonic prime-tuple law as in `lem:rough-coprimality`. -/
structure HarmonicPrimeTupleLaw (k : ℕ) where
  Tuple : Type
  [tupleFintype : Fintype Tuple]
  [tupleDecidableEq : DecidableEq Tuple]
  lower : Fin k → ℕ
  value : Tuple → Fin k → ℕ
  weight : Tuple → ℝ
  weight_nonneg : ∀ p, 0 ≤ weight p
  weight_sum_one : ∑ p, weight p = 1
  support_primes : ∀ p, weight p ≠ 0 → ∀ j, Nat.Prime (value p j) ∧
    lower j ≤ value p j ∧ value p j < 2 * lower j
  maximum_atom : ∃ C : ℝ, 0 < C ∧ ∀ p,
    weight p ≤ C * ∏ j, (Real.log (lower j : ℝ) / lower j)

attribute [instance] HarmonicPrimeTupleLaw.tupleFintype
  HarmonicPrimeTupleLaw.tupleDecidableEq

/-- §3, Lemma `lem:rough-coprimality` (lines 353–370): two independent, disjoint harmonic
prime tuples give coprime rough polynomial values with probability `1-o(1)`, also after
conditioning on prime-only good events of probability `1-o(1)`. -/
theorem rough_coprimality_polynomial_values {k k' : ℕ}
    (P : HarmonicPrimeTupleLaw k) (P' : HarmonicPrimeTupleLaw k')
    (F : MvPolynomial (Fin k) ℤ) (G : MvPolynomial (Fin k') ℤ)
    (hF : F ≠ 0) (hG : G ≠ 0)
    (goodF : ℕ → P.Tuple → Prop) (goodG : ℕ → P'.Tuple → Prop)
    (hgoodF : tendsToZeroAtTop (fun N =>
      |1 - ∑ p, P.weight p * (if goodF N p then 1 else 0)|))
    (hgoodG : tendsToZeroAtTop (fun N =>
      |1 - ∑ p, P'.weight p * (if goodG N p then 1 else 0)|)) :
    tendsToZeroAtTop (fun N => ∑ p, P.weight p * ∑ q, P'.weight q *
      if goodF N p ∧ goodG N q ∧
        (F.eval (fun j => (P.value p j : ℤ)) = 0 ∨
          G.eval (fun j => (P'.value q j : ℤ)) = 0 ∨
          ¬ Nat.Coprime
            (roughPart (N + 1) (F.eval (fun j => (P.value p j : ℤ))))
            (roughPart (N + 1) (G.eval (fun j => (P'.value q j : ℤ)))))
      then 1 else 0) := by
  sorry

/-- A row system for the restricted weighted linear-forms estimate, §3, Proposition
`prop:linear-forms` (lines 463–519). `form` is integral on the base support; the two row
hypotheses encode nonvanishing and pairwise linear independence modulo every rough prime. -/
structure WeightedLinearFormsSystem (q d : ℕ) where
  Base : Type
  [baseFintype : Fintype Base]
  [baseDecidableEq : DecidableEq Base]
  baseWeight : Base → ℝ
  baseWeight_nonneg : ∀ x, 0 ≤ baseWeight x
  baseWeight_sum_one : ∑ x, baseWeight x = 1
  Prime : Type
  [primeFintype : Fintype Prime]
  [primeDecidableEq : DecidableEq Prime]
  primeWeight : Prime → ℝ
  primeWeight_nonneg : ∀ p, 0 ≤ primeWeight p
  primeWeight_sum_one : ∑ p, primeWeight p = 1
  event : Prime → Prop
  row : Fin q → Prime → Base → ℤ
  divisor : Fin q → ℤ → ℝ
  V : ℝ
  w : ℕ
  epsilonBase : ℝ
  epsilonCRT : ℝ
  impliedErrorConstant : ℝ
  impliedErrorConstant_nonneg : 0 ≤ impliedErrorConstant
  -- GAP: expand the total-variation residue hypothesis (1), row-minor hypothesis (2), and CRT
  -- law in Proposition `prop:linear-forms`; these markers are not the final statement.
  uniformBaseResidues : Prop
  independentRowsAtRoughPrimes : Prop
  crtResidualPrimeLaw : Prop

attribute [instance] WeightedLinearFormsSystem.baseFintype
  WeightedLinearFormsSystem.baseDecidableEq WeightedLinearFormsSystem.primeFintype
  WeightedLinearFormsSystem.primeDecidableEq

/-- §3, Proposition `prop:linear-forms` (lines 463–519), including its restricted-domain form:
the absolute error is `O(1/w + V^q (ε_base+ε_CRT))`, even for prime-only events of small mass. -/
theorem weighted_linear_forms_restricted {q d : ℕ}
    (S : WeightedLinearFormsSystem q d)
    (hV : 1 ≤ S.V) (hbase : S.uniformBaseResidues)
    (hrows : S.independentRowsAtRoughPrimes) (hcrt : S.crtResidualPrimeLaw) :
    |∑ p, S.primeWeight p *
      (if S.event p then ∑ x, S.baseWeight x *
        ∏ u : Fin q, S.divisor u (S.row u p x) else 0) -
      ∑ p, S.primeWeight p * (if S.event p then 1 else 0)| ≤
      S.impliedErrorConstant *
        (1 / (S.w : ℝ) + S.V ^ q * (S.epsilonBase + S.epsilonCRT)) := by
  sorry

/-- Input/output package for the weighted Cauchy–Schwarz elimination in §4. -/
structure AdditiveEliminationInstance (d : ℕ) where
  initialAverage : ℕ → ℝ
  targetCubeAverage : ℕ → ℝ
  -- GAP: replace these markers by the actual row forms, translation directions, and sampling
  -- bounds in the paper's weighted Cauchy–Schwarz hypothesis.
  rowBounds : Prop
  rowDirections : Prop
  samplingErrors : Prop

/-- §4, Lemma `lem:additive-elimination` (lines 420–441): after `d` weighted
Cauchy–Schwarz steps the retained root has its `2^d`-cube bound, with fixed-`J₀` error `o(1)`. -/
theorem weighted_additive_elimination (d m : ℕ)
    (I : AdditiveEliminationInstance d)
    (hrows : I.rowBounds) (hdirections : I.rowDirections) (hsampling : I.samplingErrors)
    (C_m : ℝ) (hC : 0 ≤ C_m) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      |I.initialAverage N| ^ (2 ^ d) ≤ C_m * |I.targetCubeAverage N| + ε := by
  sorry

/-- The one-variable correlation estimate's fixed master-chain data. -/
structure CorrelationTestInstance (m : ℕ) where
  correlation : ℕ → ℝ
  targetCube : ℕ → ℝ
  K_m : ℕ
  d : ℕ
  C : ℝ
  theta : ℝ
  d_pos : 1 ≤ d
  d_bound : d < K_m
  maskCSCount : ℕ
  theta_eq : theta = ((2 : ℝ) ^ (maskCSCount + d))⁻¹
  C_nonneg : 0 ≤ C
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  -- GAP: expand the fixed polynomial template, normalized good-prime-tuple law, and shift
  -- distribution from Lemma `lem:row-directions` and Proposition `prop:correlation-test`.
  fixedTemplate : Prop
  goodPrimeTupleLaw : Prop
  shiftsHaveLawOfDualTest : Prop

/-- The finitely many correlation-test templates supplied for a fixed chain length. `orderBound`
is the paper's `K_m`; every cube dimension satisfies `d < K_m`. -/
structure CorrelationTemplateFamily (m : ℕ) where
  Template : Type
  [templateFintype : Fintype Template]
  [templateDecidableEq : DecidableEq Template]
  orderBound : ℕ
  instanceFor : Template → CorrelationTestInstance m
  dimension_lt : ∀ t, (instanceFor t).d < orderBound
  finiteTemplates : Prop

attribute [instance] CorrelationTemplateFamily.templateFintype
  CorrelationTemplateFamily.templateDecidableEq

/-- The correlation-test proposition supplies a finite fixed template family with order bound
`K_m`, independent of all later master-count choices. -/
theorem correlation_templates_exist (m : ℕ) (hm : 2 ≤ m) :
    Nonempty (CorrelationTemplateFamily m) := by
  sorry

/-- §4, Proposition `prop:correlation-test`, equation `eq:correlation-test` (lines 576–611):
`|𝒞| ≤ o(1)+C_m |cube|^θ`, uniformly in bounded masks/functions and fixed `J₀`, with all
analytic constants independent of the master count. -/
theorem uniform_correlation_test {m : ℕ} (I : CorrelationTestInstance m)
    (htemplate : I.fixedTemplate) (hprime : I.goodPrimeTupleLaw)
    (hshift : I.shiftsHaveLawOfDualTest) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      |I.correlation N| ≤ ε + I.C * |I.targetCube N| ^ I.theta := by
  sorry

/-- §7, Lemma `lem:cube-corner` (lines 117–138): one missing vertex in a dimension-`s+1`
nilmanifold cube is continuously reconstructed from the other vertices, with a uniform finite
coordinate-product approximation for a bounded-complexity family. The recipe form is used in
`nilsequence_testing`. -/
theorem cube_corner_recipe {s : ℕ} {F : Menu s} {K : ℝ≥0}
    (P : CosetPiece F K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : ℕ, ∃ coeff : Fin q → ℝ,
      ∃ φ : Fin q → (ω : Finset (Fin (s + 1))) →
        ω.Nonempty → (F.G P.index ⧸ F.Γ P.index) → ℝ,
      (∀ t ω hω x, |φ t ω hω x| ≤ 1) ∧
      (∀ (k : ℤ) (v : Fin (s + 1) → ℤ),
        |P.obs (P.g ^ k • P.x) -
          ∑ t, coeff t * ∏ ω : Finset (Fin (s + 1)),
            if hω : ω.Nonempty then
              φ t ω hω (P.g ^ (k + ∑ j ∈ ω, v j) • P.x)
            else 1| ≤ δ) := by
  sorry

end HindmanSumsProducts.Prediction
