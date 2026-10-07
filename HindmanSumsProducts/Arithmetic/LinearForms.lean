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
  rw [← Nat.card_eq_fintype_card, Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  simp only [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- The normalized local divisibility count is at least one; if the local map is surjective,
it is exactly one. These are the homomorphism steps used in the local kernel calculation. -/
theorem local_linear_kernel_count_excess {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) :
    1 ≤ normalizedKernelCount f ∧ (Function.Surjective f → normalizedKernelCount f = 1) := by
  have hcard := finite_group_kernel_cardinality f
  have hcardR : (Fintype.card G : ℝ) =
      (Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ) := by
    exact_mod_cast hcard
  have hK : (0 : ℝ) < (Fintype.card f.ker : ℝ) := by positivity
  have hR : (0 : ℝ) < (Fintype.card f.range : ℝ) := by positivity
  have hle : Fintype.card f.range ≤ Fintype.card H :=
    Fintype.card_le_of_injective (fun x : f.range => (x : H)) Subtype.val_injective
  have hleR : (Fintype.card f.range : ℝ) ≤ (Fintype.card H : ℝ) := by
    exact_mod_cast hle
  constructor
  · change 1 ≤ (Fintype.card H : ℝ) *
      ((Fintype.card f.ker : ℝ) / (Fintype.card G : ℝ))
    rw [hcardR]
    have hfrac : (Fintype.card H : ℝ) *
        ((Fintype.card f.ker : ℝ) /
          ((Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ))) =
        (Fintype.card H : ℝ) / (Fintype.card f.range : ℝ) := by
      field_simp
    rw [hfrac]
    exact (one_le_div hR).2 hleR
  · intro hsurj
    have hbij : Function.Bijective (fun x : f.range => (x : H)) :=
      ⟨Subtype.val_injective, fun y => ⟨⟨y, hsurj y⟩, rfl⟩⟩
    have hR_eq : (Fintype.card f.range : ℝ) = (Fintype.card H : ℝ) := by
      exact_mod_cast Fintype.card_congr (Equiv.ofBijective _ hbij)
    change (Fintype.card H : ℝ) *
      ((Fintype.card f.ker : ℝ) / (Fintype.card G : ℝ)) = 1
    rw [hcardR]
    have hfrac : (Fintype.card H : ℝ) *
        ((Fintype.card f.ker : ℝ) /
          ((Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ))) =
        (Fintype.card H : ℝ) / (Fintype.card f.range : ℝ) := by
      field_simp
    rw [hfrac, hR_eq]
    field_simp

/-- Prime-p valuation mass of a divisor law. -/
def primeValuationMass (law : TailProductLaw) (p a : ℕ) : ℝ :=
  ∑' σ : ℕ, law σ * if Nat.factorization σ p = a then 1 else 0

private def harmonicNatSupport (X W : ℕ) : Finset ℕ :=
  (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)

private theorem harmonicNatLaw_zero_of_not_mem (X W n : ℕ)
    (hn : n ∉ harmonicNatSupport X W) : harmonicNatLaw X W n = 0 := by
  have hnot : ¬ (X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W) := by
    intro h
    apply hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
  simp [harmonicNatLaw, hnot]

private theorem harmonicNatLaw_tsum_eq_one (X W : ℕ) (hX : 0 < X)
    (hH : 0 < harmonicNormalizer X W) :
    ∑' n : ℕ, harmonicNatLaw X W n = 1 := by
  let S := harmonicNatSupport X W
  have hzero : ∀ n ∉ S, harmonicNatLaw X W n = 0 := by
    intro n hn
    exact harmonicNatLaw_zero_of_not_mem X W n (by simpa [S] using hn)
  rw [tsum_eq_sum (s := S) hzero]
  calc
    (∑ n ∈ S, harmonicNatLaw X W n) =
        ∑ n ∈ S, (1 / (n : ℝ)) / harmonicNormalizer X W := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnIco : n ∈ Finset.Ico X (X ^ 2) := (Finset.mem_filter.mp hn).1
      have hnrange : X ≤ n ∧ n < X ^ 2 := Finset.mem_Ico.mp hnIco
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hX hnrange.1
      have hnvalid : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W :=
        ⟨hnrange.1, hnrange.2, (Finset.mem_filter.mp hn).2⟩
      have hpoint : harmonicNatLaw X W n =
          1 / ((n : ℝ) * harmonicNormalizer X W) := by
        simp [harmonicNatLaw, hnvalid.1, hnvalid.2.1, hnvalid.2.2]
      rw [hpoint]
      field_simp [ne_of_gt hnpos, ne_of_gt hH]
    _ = (∑ n ∈ S, 1 / (n : ℝ)) / harmonicNormalizer X W := by
      rw [Finset.sum_div]
    _ = 1 := by
      rw [show (∑ n ∈ S, 1 / (n : ℝ)) = harmonicNormalizer X W by
        simp [harmonicNormalizer, S, harmonicNatSupport]]
      exact div_self (ne_of_gt hH)

private theorem harmonicNatTupleLaw_tsum_eq_one {k : ℕ} (W : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W) :
    ∑' t : Fin k → ℕ, ∏ i, harmonicNatLaw (X i) W (t i) = 1 := by
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  have hzero (t : Fin k → ℕ) (ht : t ∉ T) :
      ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 := by
      exact harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  rw [tsum_eq_sum (s := T) hzero]
  have hsum (i : Fin k) :
      ∑ n ∈ S i, harmonicNatLaw (X i) W n = 1 := by
    have htotal := harmonicNatLaw_tsum_eq_one (X i) W (hX i) (hH i)
    rw [tsum_eq_sum (s := S i) (fun n hn =>
      harmonicNatLaw_zero_of_not_mem (X i) W n hn)] at htotal
    exact htotal
  calc
    (∑ t ∈ T, ∏ i, harmonicNatLaw (X i) W (t i)) =
        ∏ i, ∑ n ∈ S i, harmonicNatLaw (X i) W n := by
      simpa [T] using (Finset.prod_univ_sum S
        (fun i n => harmonicNatLaw (X i) W n)).symm
    _ = 1 := by simp [hsum]

private theorem harmonicProductLaw_tsum_eq_one {k : ℕ} (W : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W) :
    (∑' σ : ℕ, harmonicProductLaw W X σ = 1) ∧
      (∀ σ, harmonicProductLaw W X σ ≠ 0 → Nat.Coprime σ W) := by
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  let weight : (Fin k → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (X i) W (t i)
  let product : (Fin k → ℕ) → ℕ := fun t => ∏ i, t i
  have hweight_zero (t : Fin k → ℕ) (ht : t ∉ T) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 := by
      exact harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hterm_zero_out (σ : ℕ) (t : Fin k → ℕ) (ht : t ∉ T) :
      (if product t = σ then 1 else 0) * weight t = 0 := by
    simp [hweight_zero t ht]
  have hLawZero (σ : ℕ) (hσ : σ ∉ T.image product) :
      harmonicProductLaw W X σ = 0 := by
    unfold harmonicProductLaw
    rw [tsum_eq_sum (s := T) (hterm_zero_out σ)]
    apply Finset.sum_eq_zero
    intro t ht
    have hp : product t ≠ σ := by
      intro heq
      apply hσ
      exact Finset.mem_image.mpr ⟨t, ht, heq⟩
    simp [hp]
  have hLawEq (σ : ℕ) : harmonicProductLaw W X σ =
      ∑ t ∈ T, (if product t = σ then 1 else 0) * weight t := by
    unfold harmonicProductLaw
    rw [tsum_eq_sum (s := T) (hterm_zero_out σ)]
  have hcop_product (t : Fin k → ℕ) (ht : t ∈ T) : Nat.Coprime (product t) W := by
    apply Nat.coprime_fintype_prod_left_iff.mpr
    intro i
    have hi : t i ∈ harmonicNatSupport (X i) W := by
      simpa [S] using (Fintype.mem_piFinset.mp ht i)
    exact (Finset.mem_filter.mp hi).2
  have htuple : ∑ t ∈ T, weight t = 1 := by
    have h := harmonicNatTupleLaw_tsum_eq_one W X hX hH
    have hzero : ∀ t ∉ T, weight t = 0 := hweight_zero
    simpa [weight, T] using (tsum_eq_sum (s := T) hzero).symm.trans h
  constructor
  · rw [tsum_eq_sum (s := T.image product) hLawZero]
    calc
      (∑ σ ∈ T.image product, harmonicProductLaw W X σ) =
          ∑ σ ∈ T.image product, ∑ t ∈ T,
            (if product t = σ then 1 else 0) * weight t := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact hLawEq σ
      _ = ∑ t ∈ T, weight t := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro t ht
            have hin : product t ∈ T.image product :=
              Finset.mem_image.mpr ⟨t, ht, rfl⟩
            simp [Finset.sum_ite_eq', hin]
      _ = 1 := htuple
  · intro σ hσ
    have himage : σ ∈ T.image product := by
      by_contra hnot
      exact hσ (hLawZero σ hnot)
    obtain ⟨t, ht, hprod⟩ := Finset.mem_image.mp himage
    rw [← hprod]
    exact hcop_product t ht

private theorem harmonicProductLaw_primeValuationMass {k : ℕ} (W p : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (X : Fin k → ℕ)
    (hX : ∀ i, 0 < X i) (hH : ∀ i, 0 < harmonicNormalizer (X i) W) (a : ℕ) :
    primeValuationMass (harmonicProductLaw W X) p a = if a = 0 then 1 else 0 := by
  obtain ⟨htotal, hsupport⟩ := harmonicProductLaw_tsum_eq_one W X hX hH
  by_cases ha : a = 0
  · subst a
    have hterm (σ : ℕ) :
        harmonicProductLaw W X σ *
            (if Nat.factorization σ p = 0 then 1 else 0) = harmonicProductLaw W X σ := by
      by_cases hmass : harmonicProductLaw W X σ = 0
      · simp [hmass]
      · have hcopW := hsupport σ hmass
        have hcopP : Nat.Coprime σ p := hcopW.coprime_dvd_right hpW
        have hnot : ¬ p ∣ σ := by
          intro hdiv
          have hgcd : Nat.gcd σ p = 1 := Nat.coprime_iff_gcd_eq_one.mp hcopP
          have hdvd : p ∣ Nat.gcd σ p := Nat.dvd_gcd hdiv (dvd_rfl)
          rw [hgcd] at hdvd
          exact hp.not_dvd_one hdvd
        rw [Nat.factorization_eq_zero_of_not_dvd hnot]
        simp
    unfold primeValuationMass
    calc
      (∑' σ : ℕ, harmonicProductLaw W X σ *
          (if Nat.factorization σ p = 0 then 1 else 0)) =
        ∑' σ : ℕ, harmonicProductLaw W X σ := tsum_congr hterm
      _ = 1 := htotal
  · have hterm (σ : ℕ) :
        harmonicProductLaw W X σ *
            (if Nat.factorization σ p = a then 1 else 0) = 0 := by
      by_cases hmass : harmonicProductLaw W X σ = 0
      · simp [hmass]
      · have hcopW := hsupport σ hmass
        have hcopP : Nat.Coprime σ p := hcopW.coprime_dvd_right hpW
        have hnot : ¬ p ∣ σ := by
          intro hdiv
          have hgcd : Nat.gcd σ p = 1 := Nat.coprime_iff_gcd_eq_one.mp hcopP
          have hdvd : p ∣ Nat.gcd σ p := Nat.dvd_gcd hdiv (dvd_rfl)
          rw [hgcd] at hdvd
          exact hp.not_dvd_one hdvd
        have hval : Nat.factorization σ p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd hnot
        simp [hmass, hval, ha, eq_comm]
    unfold primeValuationMass
    have hfun : (fun σ : ℕ => harmonicProductLaw W X σ *
        (if Nat.factorization σ p = a then 1 else 0)) = fun _ => 0 := by
      funext σ
      exact hterm σ
    rw [hfun]
    simp [ha]

private theorem harmonicNormalizer_pos_of_cutoff (X W : ℕ) (hW : 0 < W)
    (hX : 4 * W ≤ X) : 0 < harmonicNormalizer X W := by
  have h := OAI.RawHarmonicProbability.mass_pos X W hW hX
  simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
    Finset.sum_filter, one_div, Nat.coprime_comm] using h

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
  refine ⟨1, by norm_num, ?_⟩
  have hXall : ∀ᶠ N in atTop, ∀ i : Fin n,
      4 * primorial (N + 1) ≤ A.X N i := by
    simp only [Filter.eventually_all]
    exact fun i => A.eventual_X i
  have hpN : ∀ᶠ N in atTop, p ≤ N + 1 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨p, fun N hN => hN⟩] with N hN
    exact hN.trans (Nat.le_succ N)
  filter_upwards [hXall, hpN] with N hNX hNp
  intro a
  have hWpos : 0 < primorial (N + 1) := primorial_pos _
  have hpW : p ∣ primorial (N + 1) := hp.dvd_primorial_iff.mpr hNp
  have hlocal (u : Fin q) :
      primeValuationMass (divisorTemplateLaw A N (D u)) p (a u) =
        if a u = 0 then 1 else 0 := by
    let Xraw : Fin (D u).arity → ℕ := fun i => A.X N ((D u).cutoff i)
    have hXraw (i : Fin (D u).arity) : 0 < Xraw i := by
      exact A.Xpos N ((D u).cutoff i)
    have hXcut (i : Fin (D u).arity) : 4 * primorial (N + 1) ≤ Xraw i :=
      hNX ((D u).cutoff i)
    have hHraw (i : Fin (D u).arity) : 0 < harmonicNormalizer (Xraw i) (primorial (N + 1)) :=
      harmonicNormalizer_pos_of_cutoff _ _ hWpos (hXcut i)
    change primeValuationMass (harmonicProductLaw (primorial (N + 1)) Xraw) p (a u) = _
    exact harmonicProductLaw_primeValuationMass (primorial (N + 1)) p hp hpW
      Xraw hXraw hHraw (a u)
  by_cases ha0 : ∀ u, a u = 0
  · simp_rw [hlocal]
    simp [ha0]
  · obtain ⟨u, hu⟩ := not_forall.mp ha0
    have huval : primeValuationMass (divisorTemplateLaw A N (D u)) p (a u) = 0 := by
      rw [hlocal u]
      simp [hu]
    rw [Finset.prod_eq_zero (Finset.mem_univ u) huval]
    positivity

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

private def expPolyWeight (k n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ n

private theorem expPolyWeight_summable (k : ℕ) :
    Summable (fun n : ℕ => expPolyWeight k n) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ k * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  have htail : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  have hmul := htail.mul_left (2 : ℝ)
  exact hmul.congr fun n => by
    simp only [expPolyWeight]
    rw [pow_succ]
    field_simp

private theorem regularExpTerm_bound (p k A B : ℕ) (hp : p.Prime) :
    (if 1 ≤ B ∧ B ≤ A then
      (((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ k / (p : ℝ) ^ (A + B) else 0) ≤
    (4 / (p : ℝ) ^ 2) * expPolyWeight k A * expPolyWeight k B := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases hAB : 1 ≤ B ∧ B ≤ A
  · have hsum0 : 2 ≤ A + B := by omega
    let t := A + B - 2
    have hsum : 2 + t = A + B := by dsimp [t]; omega
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hden : (p : ℝ) ^ 2 * (2 : ℝ) ^ t ≤ (p : ℝ) ^ (A + B) := by
      rw [← hsum, pow_add]
      gcongr
    have hrecip : 1 / (p : ℝ) ^ (A + B) ≤
        1 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ t) :=
      one_div_le_one_div_of_le (by positivity) hden
    have htwo : (2 : ℝ) ^ (A + B) = 4 * (2 : ℝ) ^ t := by
      rw [← hsum, pow_add]
      norm_num
    have hfactor :
        (4 / (p : ℝ) ^ 2) * expPolyWeight k A * expPolyWeight k B =
          ((((A + 1 : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ)) ^ k) /
            ((p : ℝ) ^ 2 * (2 : ℝ) ^ t) := by
      unfold expPolyWeight
      calc
        _ = (4 / (p : ℝ) ^ 2) *
            ((((A + 1 : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ)) ^ k *
              (1 / 2 : ℝ) ^ (A + B)) := by
                calc
                  _ = (4 / (p : ℝ) ^ 2) *
                      ((((A + 1 : ℕ) : ℝ) ^ k * ((B + 1 : ℕ) : ℝ) ^ k) *
                        ((1 / 2 : ℝ) ^ A * (1 / 2 : ℝ) ^ B)) := by ring
                  _ = _ := by rw [← mul_pow, ← pow_add]
        _ = _ := by rw [one_div_pow, htwo]; field_simp [ne_of_gt hp0]
    simp only [if_pos hAB]
    calc
      ((((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ k) / (p : ℝ) ^ (A + B) =
          ((((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ k) *
            (1 / (p : ℝ) ^ (A + B)) := by ring
      _ ≤ ((((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ k) *
            (1 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ t)) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = (4 / (p : ℝ) ^ 2) * expPolyWeight k A * expPolyWeight k B := by
        simpa only [div_eq_mul_inv, one_mul, Nat.cast_add, Nat.cast_one] using hfactor.symm
  · simp [hAB]
    unfold expPolyWeight
    positivity

private theorem exceptionalExpTerm_bound (p k A : ℕ) (hp : p.Prime) :
    (if 1 ≤ A then (((A + 1 : ℕ) : ℝ) ^ k) / (p : ℝ) ^ A else 0) ≤
      (2 / (p : ℝ)) * expPolyWeight k A := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases hA : 1 ≤ A
  · let t := A - 1
    have hsum : 1 + t = A := by dsimp [t]; omega
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hden : (p : ℝ) * (2 : ℝ) ^ t ≤ (p : ℝ) ^ A := by
      rw [← hsum, pow_add, pow_one]
      gcongr
    have hrecip : 1 / (p : ℝ) ^ A ≤ 1 / ((p : ℝ) * (2 : ℝ) ^ t) :=
      one_div_le_one_div_of_le (by positivity) hden
    have htwo : (2 : ℝ) ^ A = 2 * (2 : ℝ) ^ t := by
      rw [← hsum, pow_add]
      norm_num
    have hfactor :
        (2 / (p : ℝ)) * expPolyWeight k A =
          (((A + 1 : ℕ) : ℝ) ^ k) / ((p : ℝ) * (2 : ℝ) ^ t) := by
      unfold expPolyWeight
      rw [one_div_pow, htwo]
      field_simp [ne_of_gt hp0]
    simp only [if_pos hA]
    calc
      (((A + 1 : ℕ) : ℝ) ^ k) / (p : ℝ) ^ A =
          (((A + 1 : ℕ) : ℝ) ^ k) * (1 / (p : ℝ) ^ A) := by ring
      _ ≤ (((A + 1 : ℕ) : ℝ) ^ k) * (1 / ((p : ℝ) * (2 : ℝ) ^ t)) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = (2 / (p : ℝ)) * expPolyWeight k A := by
        simpa only [div_eq_mul_inv, one_mul] using hfactor.symm
  · simp [hA]
    unfold expPolyWeight
    positivity

/-- Both local valuation series are `O(p⁻²)`: the exceptional series gains its extra
`1/p` from the polynomial-root test (§3 lines 620–648). -/
theorem local_divisor_excess_prime_square_bound (q b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      regularDivisorExcessSeries p q b ≤ C / (p : ℝ) ^ 2 ∧
      exceptionalDivisorExcessSeries p q b / p ≤ C / (p : ℝ) ^ 2 := by
  let k := b * q
  let F : ℝ := ∑' A : ℕ, expPolyWeight k A
  let G : ℝ := ∑' x : ℕ × ℕ, expPolyWeight k x.1 * expPolyWeight k x.2
  let C : ℝ := 4 * G + 2 * F + 1
  have hFsum : Summable (fun A : ℕ => expPolyWeight k A) := expPolyWeight_summable k
  have hFterm : ∀ A, 0 ≤ expPolyWeight k A := by
    intro A
    unfold expPolyWeight
    positivity
  have hFnonneg : 0 ≤ F := by
    dsimp [F]
    exact tsum_nonneg hFterm
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact tsum_nonneg fun x => mul_nonneg (hFterm x.1) (hFterm x.2)
  have hpair : Summable (fun x : ℕ × ℕ => expPolyWeight k x.1 * expPolyWeight k x.2) :=
    hFsum.mul_of_nonneg hFsum hFterm hFterm
  have hCpos : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpDen : 0 < (p : ℝ) ^ 2 := by positivity
  let rterm : ℕ × ℕ → ℝ := fun x =>
    if 1 ≤ x.2 ∧ x.2 ≤ x.1 then
      (((x.1 + 1 : ℕ) : ℝ) * (x.2 + 1 : ℝ)) ^ k / (p : ℝ) ^ (x.1 + x.2)
    else 0
  let rcomp : ℕ × ℕ → ℝ := fun x =>
    (4 / (p : ℝ) ^ 2) * expPolyWeight k x.1 * expPolyWeight k x.2
  have hrterm_nonneg : ∀ x, 0 ≤ rterm x := by
    intro x
    dsimp [rterm]
    split_ifs <;> positivity
  have hrcomp_sum : Summable rcomp := by
    simpa [rcomp, mul_assoc] using hpair.mul_left (4 / (p : ℝ) ^ 2)
  have hrterm_le : ∀ x, rterm x ≤ rcomp x := by
    intro x
    dsimp [rterm, rcomp]
    exact regularExpTerm_bound p k x.1 x.2 hp
  have hrterm_sum : Summable rterm := hrcomp_sum.of_nonneg_of_le hrterm_nonneg hrterm_le
  have hrseries : regularDivisorExcessSeries p q b = ∑' x : ℕ × ℕ, rterm x := by
    simpa [regularDivisorExcessSeries, rterm, k] using hrterm_sum.tsum_prod.symm
  have hrbound : regularDivisorExcessSeries p q b ≤ (4 / (p : ℝ) ^ 2) * G := by
    calc
      regularDivisorExcessSeries p q b = ∑' x : ℕ × ℕ, rterm x := hrseries
      _ ≤ ∑' x : ℕ × ℕ, rcomp x :=
        Summable.tsum_le_tsum hrterm_le hrterm_sum hrcomp_sum
      _ = (4 / (p : ℝ) ^ 2) * G := by
        simpa [rcomp, G, mul_assoc] using hpair.tsum_mul_left (4 / (p : ℝ) ^ 2)
  have hCreg : 4 * G ≤ C := by
    dsimp [C]
    linarith [hFnonneg]
  have hRfinal : regularDivisorExcessSeries p q b ≤ C / (p : ℝ) ^ 2 := by
    calc
      regularDivisorExcessSeries p q b ≤ (4 / (p : ℝ) ^ 2) * G := hrbound
      _ = (4 * G) / (p : ℝ) ^ 2 := by ring
      _ ≤ C / (p : ℝ) ^ 2 := div_le_div_of_nonneg_right hCreg hpDen.le
  let eterm : ℕ → ℝ := fun A =>
    if 1 ≤ A then (((A + 1 : ℕ) : ℝ) ^ k) / (p : ℝ) ^ A else 0
  let ecomp : ℕ → ℝ := fun A => (2 / (p : ℝ)) * expPolyWeight k A
  have heterm_nonneg : ∀ A, 0 ≤ eterm A := by
    intro A
    dsimp [eterm]
    split_ifs <;> positivity
  have hecomp_sum : Summable ecomp := by
    simpa [ecomp] using hFsum.mul_left (2 / (p : ℝ))
  have heterm_le : ∀ A, eterm A ≤ ecomp A := by
    intro A
    dsimp [eterm, ecomp]
    exact exceptionalExpTerm_bound p k A hp
  have heterm_sum : Summable eterm := hecomp_sum.of_nonneg_of_le heterm_nonneg heterm_le
  have heseries : exceptionalDivisorExcessSeries p q b = ∑' A : ℕ, eterm A := by
    simp [exceptionalDivisorExcessSeries, eterm, k, Nat.cast_add]
  have hebound : exceptionalDivisorExcessSeries p q b ≤ (2 / (p : ℝ)) * F := by
    calc
      exceptionalDivisorExcessSeries p q b = ∑' A : ℕ, eterm A := heseries
      _ ≤ ∑' A : ℕ, ecomp A := Summable.tsum_le_tsum heterm_le heterm_sum hecomp_sum
      _ = (2 / (p : ℝ)) * F := by
        simpa [ecomp, F] using hFsum.tsum_mul_left (2 / (p : ℝ))
  have hCexc : 2 * F ≤ C := by
    dsimp [C]
    linarith [hGnonneg]
  have hEfinal : exceptionalDivisorExcessSeries p q b / p ≤ C / (p : ℝ) ^ 2 := by
    calc
      exceptionalDivisorExcessSeries p q b / p ≤ ((2 / (p : ℝ)) * F) / p :=
        div_le_div_of_nonneg_right hebound hp0.le
      _ = (2 * F) / (p : ℝ) ^ 2 := by field_simp [ne_of_gt hp0]
      _ ≤ C / (p : ℝ) ^ 2 := div_le_div_of_nonneg_right hCexc hpDen.le
  exact ⟨hRfinal, hEfinal⟩

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

/-- The error bound in `prop_linear_forms` needs a nonnegativity hypothesis for
`epsilonBase`: on an empty good domain its total-variation condition is vacuous, while
superpolynomial smallness is unchanged by altering finitely many values. -/
theorem prop_linear_forms_counterexample_when_base_error_negative
    {n : ℕ} {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial 0)}
    (S : MasterScales n Aset 0 tests) :
    ∃ D : WeightedLinearFormsData (q := 0) (d := 0) (b := 0) S,
      ¬ (∃ C : ℝ, 0 < C ∧ ∀ N (E : (Fin 0 → ℕ) → Prop),
        (∀ p, E p → D.goodDomain N p) →
        |weightedLinearFormsAverage D N E - weightedLinearFormsEventProbability D N E| ≤
          C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ 0 *
            (D.epsilonBase N + D.epsilonCRT N))) := by
  classical
  let D : WeightedLinearFormsData (q := 0) (d := 0) (b := 0) S := {
    gap := Fin.elim0
    row := Fin.elim0
    divisor := Fin.elim0
    V := fun N => max (S.core.parameters.M N) N
    epsilonBase := fun N => if N = 0 then -2 else 0
    epsilonCRT := fun _ => 0
    baseMass := fun _ _ _ => 1
    goodDomain := fun _ _ => False
    V_lower := by intro N; exact Nat.le_max_left _ _
    V_tendsto := by
      apply Filter.tendsto_atTop.2
      intro k
      filter_upwards [Filter.eventually_atTop.2 ⟨k, fun N hN => hN⟩] with N hN
      exact hN.trans (Nat.le_max_right _ _)
    slot_gap_bound := by intro N i; exact Fin.elim0 i
    base_nonnegative := by intro N p x; norm_num
    base_normalized := by intro N p; simp
    divisor_positive := by intro N u; exact Fin.elim0 u
    divisor_bounded := by intro N u; exact Fin.elim0 u
    base_residue_uniform := by
      intro N p σ hgood
      exact False.elim hgood
    row_integer_on_support := by
      intro N p x hgood hx u
      exact Fin.elim0 u
    row_denominators_are_units := by
      intro N p hgood r hr hN hrV u
      exact Fin.elim0 u
    row_primitive := by
      intro N p hgood r hr hN hrV u
      exact Fin.elim0 u
    pairwise_row_tests := by
      intro N p hgood r hr hN hrV htests u
      exact Fin.elim0 u
    crt_error_bound := by
      intro N
      have hActual (r : Fin 0 → CRTResidues (N + 1) (max (S.core.parameters.M N) N)) :
          primeTupleCRTLaw
            (fun i : Fin 0 => (S.primeStage.pool N (Fin.elim0 i)).lower)
            (fun i : Fin 0 => (S.primeStage.pool N (Fin.elim0 i)).upper) (N + 1)
            (max (S.core.parameters.M N) N) r = 1 := by
        have hres (p : Fin 0 → ℕ) :
            (fun i => integerCRTResidues (N + 1) (max (S.core.parameters.M N) N) (p i)) = r :=
          Subsingleton.elim _ _
        simp [primeTupleCRTLaw, independentPrimePoolMass, hres]
      have hUniform (r : Fin 0 → CRTResidues (N + 1) (max (S.core.parameters.M N) N)) :
          uniformPrimeTupleCRTLaw (N + 1) (max (S.core.parameters.M N) N) r = 1 := by
        simp [uniformPrimeTupleCRTLaw]
      have hzero : finiteL1
          (primeTupleCRTLaw
            (fun i : Fin 0 => (S.primeStage.pool N (Fin.elim0 i)).lower)
            (fun i : Fin 0 => (S.primeStage.pool N (Fin.elim0 i)).upper) (N + 1)
            (max (S.core.parameters.M N) N))
          (uniformPrimeTupleCRTLaw (N + 1) (max (S.core.parameters.M N) N)) = 0 := by
        simp [finiteL1, hActual, hUniform]
      rw [hzero]
    epsilonBase_superpolynomial := by
      intro C hC
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
      have hN0 : N ≠ 0 := by omega
      simp [hN0]
    epsilonCRT_superpolynomial := by
      intro C hC
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  }
  refine ⟨D, ?_⟩
  intro hprop
  let E : (Fin 0 → ℕ) → Prop := fun _ => False
  have hgood : ∀ p, E p → D.goodDomain 0 p := by
    intro p hp
    exact False.elim hp
  have havg : weightedLinearFormsAverage D 0 E = 0 := by
    simp [weightedLinearFormsAverage, D, E, independentPrimePoolMass]
  have hprob : weightedLinearFormsEventProbability D 0 E = 0 := by
    simp [weightedLinearFormsEventProbability, E, independentPrimePoolProbability,
      independentPrimePoolMass]
  obtain ⟨C, hC, hbound⟩ := hprop
  have h := hbound 0 E hgood
  rw [havg, hprob] at h
  simp [D] at h
  norm_num at h
  nlinarith

/-- With master-scale CRT accuracy and base residue errors smaller than every fixed inverse
power of V, the linear-forms error tends to zero at each fixed row count. -/
theorem weighted_linear_forms_error_tends_zero {n q d b m : ℕ}
    {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) :
    Tendsto
      (fun N : ℕ => 1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ q *
        (D.epsilonBase N + D.epsilonCRT N)) atTop (𝓝 0) := by
  have hVreal : Tendsto (fun N : ℕ => (D.V N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp D.V_tendsto
  have hinvV : Tendsto (fun N : ℕ => (D.V N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hVreal
  have hVpos : ∀ᶠ N : ℕ in atTop, 0 < (D.V N : ℝ) :=
    hVreal.eventually (eventually_gt_atTop 0)
  have hweighted (e : ℕ → ℝ) (he : SuperPolynomialSmall e (fun N => (D.V N : ℝ))) :
      Tendsto (fun N => (D.V N : ℝ) ^ q * e N) atTop (𝓝 0) := by
    have hs := he ((q : ℝ) + 1) (by positivity)
    have hpow (N : ℕ) : (D.V N : ℝ) ^ ((q : ℝ) + 1) =
        (D.V N : ℝ) ^ q * (D.V N : ℝ) := by
      have hexp : (q : ℝ) + 1 = ((q + 1 : ℕ) : ℝ) := by norm_num
      rw [hexp, Real.rpow_natCast]
      simp [pow_succ]
    have hbase : Tendsto
        (fun N => e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ))) atTop (𝓝 0) := by
      exact hs.congr fun N => by rw [hpow]
    have heq : (fun N =>
        e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ)) * (D.V N : ℝ)⁻¹) =ᶠ[atTop]
        (fun N => (D.V N : ℝ) ^ q * e N) := by
      filter_upwards [hVpos] with N hN
      field_simp [ne_of_gt hN]
    have hprod : Tendsto
        (fun N => e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ)) * (D.V N : ℝ)⁻¹)
        atTop (𝓝 0) := by
      simpa using hbase.mul hinvV
    exact hprod.congr' heq
  have hbase := hweighted D.epsilonBase D.epsilonBase_superpolynomial
  have hcrt := hweighted D.epsilonCRT D.epsilonCRT_superpolynomial
  have hweightedSum : Tendsto
      (fun N => (D.V N : ℝ) ^ q * (D.epsilonBase N + D.epsilonCRT N))
      atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun N => (D.V N : ℝ) ^ q * D.epsilonBase N +
          (D.V N : ℝ) ^ q * D.epsilonCRT N) atTop (𝓝 0) := by
      simpa using hbase.add hcrt
    apply hsum.congr'
    filter_upwards with N
    ring
  have hNplus : Tendsto (fun N : ℕ => (N + 1 : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro a
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop a)] with N hN
    exact le_trans hN (by norm_num)
  have hinvN : Tendsto (fun N : ℕ => (N + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hNplus
  simpa [one_div] using hinvN.add hweightedSum

private theorem alternating_powerset_card_sub_zero {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) :
    ∑ U ∈ s.powerset, (-1 : ℝ) ^ (s.card - U.card) = 0 := by
  have hsumZ : (∑ U ∈ s.powerset, (-1 : ℤ) ^ U.card) = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hs
  have hsum : (∑ U ∈ s.powerset, (-1 : ℝ) ^ U.card) = 0 := by
    exact_mod_cast hsumZ
  have hterm (U : Finset α) (hU : U ∈ s.powerset) :
      (-1 : ℝ) ^ (s.card - U.card) = (-1 : ℝ) ^ s.card * (-1 : ℝ) ^ U.card := by
    have hle : U.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hU)
    have hexp : s.card - U.card + U.card = s.card := Nat.sub_add_cancel hle
    rcases neg_one_pow_eq_or ℝ U.card with hpow | hpow
    · rw [hpow, ← hexp, pow_add, hpow]
      simp
    · rw [hpow, ← hexp, pow_add, hpow]
      simp
  calc
    (∑ U ∈ s.powerset, (-1 : ℝ) ^ (s.card - U.card)) =
        ∑ U ∈ s.powerset, (-1 : ℝ) ^ s.card * (-1 : ℝ) ^ U.card := by
          apply Finset.sum_congr rfl
          intro U hU
          exact hterm U hU
    _ = (-1 : ℝ) ^ s.card * ∑ U ∈ s.powerset, (-1 : ℝ) ^ U.card := by
          rw [Finset.mul_sum]
    _ = 0 := by rw [hsum, mul_zero]

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
  constructor
  · simp_rw [hmain]
    simp
  · simp_rw [hmain]
    have hzero := alternating_powerset_card_sub_zero minus hminus
    have hweighted :
        ∑ U ∈ minus.powerset,
          (-1 : ℝ) ^ (minus.card - U.card) * P = 0 := by
      rw [← Finset.sum_mul, hzero]
      simp
    simp_rw [hweighted]
    simp

end
end HindmanSumsProducts
