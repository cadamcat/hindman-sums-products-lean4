import HindmanSumsProducts.Arithmetic.RoughCoprimality

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A homogeneous linear row whose coefficients are rational polynomials in prime slots. -/
structure RationalLinearRow (d m : ℕ) where
  coefficient : Fin d → MvPolynomial (Fin m) ℚ

/-- Rational coefficient of a row after evaluating its prime parameters. -/
def rationalRowCoefficient {d m : ℕ} (L : RationalLinearRow d m)
    (p : Fin m → ℕ) (j : Fin d) : ℚ :=
  MvPolynomial.eval (fun i => (p i : ℚ)) (L.coefficient j)

/-- Rational value of a homogeneous row on integer base variables and prime parameters. -/
def rationalRowValue {d m : ℕ} (L : RationalLinearRow d m)
    (x : Fin d → ℤ) (p : Fin m → ℕ) : ℚ :=
  ∑ j, rationalRowCoefficient L p j * (x j : ℚ)

/-- Integer represented by a rational row value when its denominator is one. -/
def rationalRowIntegerValue {d m : ℕ} (L : RationalLinearRow d m)
    (x : Fin d → ℤ) (p : Fin m → ℕ) : ℤ :=
  (rationalRowValue L x p).num

/-- Reduction of a rational coefficient modulo a prime where its denominator is a unit. -/
noncomputable def rationalResidue (p : ℕ) (hp : p.Prime) (r : ℚ) : ZMod p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact (r.num : ZMod p) / (r.den : ZMod p)

/-- A row coefficient reduced modulo p. -/
noncomputable def rationalRowCoefficientResidue {d m : ℕ}
    (L : RationalLinearRow d m) (p : ℕ) (hp : p.Prime)
    (slots : Fin m → ℕ) (j : Fin d) : ZMod p :=
  rationalResidue p hp (rationalRowCoefficient L slots j)

/-- A row is primitive modulo p when its coefficient vector is nonzero. -/
def rowPrimitiveModulo {d m : ℕ} (L : RationalLinearRow d m)
    (p : ℕ) (hp : p.Prime) (slots : Fin m → ℕ) : Prop :=
  ∃ j, rationalRowCoefficientResidue L p hp slots j ≠ 0

/-- Two rows are linearly independent modulo p, expressed by a nonzero two-column minor. -/
def rowsIndependentModulo {d m : ℕ} (L₁ L₂ : RationalLinearRow d m)
    (p : ℕ) (hp : p.Prime) (slots : Fin m → ℕ) : Prop :=
  ∃ i j,
    rationalRowCoefficientResidue L₁ p hp slots i *
        rationalRowCoefficientResidue L₂ p hp slots j ≠
      rationalRowCoefficientResidue L₁ p hp slots j *
        rationalRowCoefficientResidue L₂ p hp slots i

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

/-- Complete data and hypotheses for the weighted linear-forms proposition. The divisor
templates are fresh independent raw harmonic draws for each row occurrence. -/
structure WeightedLinearFormsData {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    (S : MasterScales n Aset m tests) where
  gap : Fin m → Fin n
  row : Fin q → RationalLinearRow d m
  divisor : Fin q → DivisorTemplate n b
  V : ℕ → ℕ
  epsilonBase : ℕ → ℝ
  epsilonCRT : ℕ → ℝ
  baseMass : ℕ → (Fin m → ℕ) → (Fin d → ℤ) → ℝ
  goodDomain : ℕ → (Fin m → ℕ) → Prop
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
    ∀ u, (rationalRowValue (row u) x p).den = 1
  row_denominators_are_units : ∀ N p, goodDomain N p → ∀ r (_hr : r.Prime),
    N + 1 < r → r ≤ V N → ∀ u j,
      Nat.Coprime (rationalRowCoefficient (row u) p j).den r
  row_primitive : ∀ N p, goodDomain N p → ∀ r (hr : r.Prime),
    N + 1 < r → r ≤ V N → ∀ u,
      rowPrimitiveModulo (row u) r hr p
  pairwise_row_tests : ∀ N p, goodDomain N p → ∀ r (hr : r.Prime),
    N + 1 < r → r ≤ V N →
      (∀ Q ∈ tests, ¬ ((r : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
      ∀ u v, u ≠ v → rowsIndependentModulo (row u) (row v) r hr p
  crt_error_bound : ∀ N,
    finiteL1
      (primeTupleCRTLaw
        (fun i => (S.primeStage.pool N (gap i)).lower)
        (fun i => (S.primeStage.pool N (gap i)).upper) (N + 1) (V N))
      (uniformPrimeTupleCRTLaw (N + 1) (V N)) ≤ epsilonCRT N
  epsilonBase_superpolynomial : SuperPolynomialSmall epsilonBase (fun N => (V N : ℝ))
  epsilonCRT_superpolynomial : SuperPolynomialSmall epsilonCRT (fun N => (V N : ℝ))

/-- `O(V^q)`-bounded divisor-weight product average over a prime-only event. -/
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
            (rationalRowIntegerValue (D.row u) x p))

/-- Probability of a prime-only event under the independent harmonic pool slots. -/
def weightedLinearFormsEventProbability {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (E : (Fin m → ℕ) → Prop) : ℝ :=
  independentPrimePoolProbability
    (fun i => (S.primeStage.pool N (D.gap i)).lower)
    (fun i => (S.primeStage.pool N (D.gap i)).upper) E

/-- Kernel probability of a homomorphism between finite groups, under uniform input. -/
def localKernelProbability {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) : ℝ :=
  (Fintype.card f.ker : ℝ) / Fintype.card G

/-- Normalized divisibility kernel count `|H|·P(f(x)=1)`, the local factor αₚ. -/
def normalizedKernelCount {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) : ℝ :=
  (Fintype.card H : ℝ) * localKernelProbability f

/-- A homomorphism's kernel and image cardinalities multiply to the domain size. -/
theorem finite_group_kernel_cardinality {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) :
    Fintype.card G = Fintype.card f.ker * Fintype.card f.range := by
  sorry

/-- The normalized local divisibility count is at least one; if the local map is surjective,
it is exactly one. These are the homomorphism steps used in the local kernel calculation. -/
theorem local_linear_kernel_count_excess {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) :
    1 ≤ normalizedKernelCount f ∧ (Function.Surjective f → normalizedKernelCount f = 1) := by
  sorry

/-- Prime-p valuation mass of a divisor law. -/
def primeValuationMass (law : TailProductLaw) (p a : ℕ) : ℝ :=
  ∑' σ : ℕ, law σ * if Nat.factorization σ p = a then 1 else 0

/-- Joint Euler-product domination for the q fresh divisor draws: each row has at most b raw
factors and contributes valuation mass bounded by a polynomial times p⁻ᵃ; a single global
constant raised to bq dominates the whole product (§3 lines 581–618). -/
theorem harmonic_divisor_valuation_domination {n q b : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (D : Fin q → DivisorTemplate n b)
    (p : ℕ) (hp : p.Prime) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ N in atTop, ∀ a : Fin q → ℕ,
      (∏ u, primeValuationMass
        (divisorTemplateLaw A N (D u)) p (a u)) ≤
      C₀ ^ (b * q) * ∏ u,
        ((a u + 1 : ℕ) : ℝ) ^ b / (p : ℝ) ^ (a u) := by
  sorry

/-- The two geometric valuation series from regular and exceptional local tests. -/
def regularDivisorExcessSeries (p q b : ℕ) : ℝ :=
  ∑' A : ℕ, ∑' B : ℕ,
    if 1 ≤ B ∧ B ≤ A then
      (((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ (b * q) /
        (p : ℝ) ^ (A + B)
    else 0

/-- The valuation series when a polynomial test is exceptional modulo p. -/
def exceptionalDivisorExcessSeries (p q b : ℕ) : ℝ :=
  ∑' A : ℕ, if 1 ≤ A then
    (((A + 1 : ℕ) : ℝ) ^ (b * q)) / (p : ℝ) ^ A else 0

/-- Both local valuation series are `O(p⁻²)`: the exceptional series gains its extra
`1/p` from the polynomial-root test (§3 lines 620–648). -/
theorem local_divisor_excess_prime_square_bound (q b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      regularDivisorExcessSeries p q b ≤ C / (p : ℝ) ^ 2 ∧
      exceptionalDivisorExcessSeries p q b / p ≤ C / (p : ℝ) ^ 2 := by
  sorry

/-- Proposition `prop:linear-forms`: the weighted product of divisor weights has mean
`P(E)` up to the absolute error `O(1/w + V^q(ε_base+ε_CRT))`, uniformly over every
prime-only event `E⊆G`. The formulation permits rational rows with denominators that are
units modulo every possible divisor (§3 lines 463–519). -/
theorem prop_linear_forms {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) :
    ∃ C : ℝ, 0 < C ∧ ∀ N (E : (Fin m → ℕ) → Prop),
      (∀ p, E p → D.goodDomain N p) →
      |weightedLinearFormsAverage D N E - weightedLinearFormsEventProbability D N E| ≤
        C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ q *
          (D.epsilonBase N + D.epsilonCRT N)) := by
  sorry

/-- With master-scale CRT accuracy and base residue errors smaller than every fixed inverse
power of V, the linear-forms error tends to zero at each fixed row count. -/
theorem weighted_linear_forms_error_tends_zero {n q d b m : ℕ}
    {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) :
    Tendsto
      (fun N : ℕ => 1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ q *
        (D.epsilonBase N + D.epsilonCRT N)) atTop (𝓝 0) := by
  sorry

/-- Expansion consequences: products of `1+ν_u` have main term `2^q P(E)`; any nonempty
product with a factor `ν_u−1` cancels to `o(1)` when each expanded subsystem has the same
row hypotheses (§3 lines 666–678). -/
theorem divisor_weight_expansion_cancellation {q : ℕ}
    (P : ℝ) (moment : Finset (Fin q) → ℝ)
    (hmain : ∀ S, moment S = P)
    (fixed minus plus : Finset (Fin q))
    (hdisj₁ : Disjoint fixed minus) (hdisj₂ : Disjoint fixed plus)
    (hdisj₃ : Disjoint minus plus) (hminus : minus.Nonempty) :
    (∑ S : Finset (Fin q), moment S = (2 ^ q : ℕ) * P) ∧
    (∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
      (-1 : ℝ) ^ (minus.card - U.card) * moment (fixed ∪ S ∪ U) = 0) := by
  sorry

end
end HindmanSumsProducts
