import OAI.Combinatorics.SumProduct.Alignment.RawMenu
import OAI.Combinatorics.SumProduct.Alignment.ConstantCoefficient01

/-!
Local vocabulary for §4.  The admissible family, its product harmonic law,
and blocks are OpenAI's objects.  The divisor weight and correlation
integrands are local copies of the paper's §2 definitions and are marked for
unification with Framework.
-/

namespace HindmanSumsProducts

noncomputable section

open MeasureTheory
open scoped BigOperators

abbrev AdmissibleParameters := OAI.SourceAdmissible.Parameters
abbrev PaperBlock := OAI.SourceBlocks.Block

/-- The paper's asymptotic index is `N`; its `w` is always `N + 1`. -/
abbrev AsymptoticIndex := ℕ

/-- The harmonic product law from OpenAI's admissible parameters. -/
def admissibleLaw {n : ℕ} (A : AdmissibleParameters n) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) : Measure (Fin n → ℕ) :=
  A.law N hX

/-- A master chain with its §2 order conditions and integer scales at each
asymptotic index. The chain uses OpenAI's `Block` and `Tail` verbatim. -/
structure MasterChain (n m : ℕ) where
  parameters : AdmissibleParameters n
  blocks : Fin m → PaperBlock n
  gap : Fin n
  tail_before_gap : ∀ d j, j ∈ (blocks d).2.val → j < gap
  gap_before_pivots : ∀ d, gap < (blocks d).1
  tails_ordered : ∀ d e, d < e → ∀ j ∈ (blocks d).2.val,
    ∀ k ∈ (blocks e).2.val, j < k
  pivots_ordered : StrictMono fun d => (blocks d).1
  /-- Rational scale family reused from OpenAI's `GlobalWordPlan.Scale`. -/
  scale : ℕ → OAI.ConstructedWordPlan.GlobalWordPlan.Scale m
  scaleFactor : Fin m → ℚ
  scaleFactor_pos : ∀ d, 0 < scaleFactor d
  /-- Integer representative of `c_d=h_{B_d}a_d` for the arithmetic formulas. -/
  integerScale : ℕ → Fin m → ℕ
  scale_cast : ∀ N d, scale N d = (integerScale N d : ℚ)
  scale_blockProduct : ∀ N d,
    scale N d =
      OAI.ConstructedWordPlan.AlignmentScales.blockProduct
        (fun j => (parameters.ht N j : ℚ)) (OAI.SourceBlocks.Block.set (blocks d)) *
        scaleFactor d
  scale_pos : ∀ N d, 0 < integerScale N d
  scale_anchor_dvd : ∀ N d e, d ≤ e → integerScale N e ∣ integerScale N d
  scale_smooth : ∀ N d, OAI.RoughScales.Smooth
    (N + 1) (integerScale N d : ℤ)
  law_cutoff : ∀ N i, 4 * primorial (N + 1) ≤ parameters.X N i

/-- Product of the raw variables in a block tail. -/
def tailProduct {n : ℕ} (B : PaperBlock n) (x : Fin n → ℕ) : ℕ :=
  ∏ j ∈ B.2.val, x j

/-- OpenAI's integer height of a block, retained as a named component of the
local correlation vocabulary. -/
def blockHeight {n m : ℕ} (C : MasterChain n m) (N : ℕ) (d : Fin m) : ℤ :=
  OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
    (C.parameters.ht N) (OAI.SourceBlocks.Block.set (C.blocks d))

/-- Divisor weight `ν_B(y) = E_{σ=t_T} σ 1_{σ|y}` from §2, Definition
`def:divisor-weight`. Each integral is with respect to OpenAI's raw product
harmonic law, so distinct occurrences are independent when expanded. -/
noncomputable def divisorWeight {n : ℕ} (A : AdmissibleParameters n)
    (N : ℕ) (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i)
    (B : PaperBlock n) (y : ℤ) : ℝ :=
  ∫ x, (tailProduct B x : ℝ) *
    (if (tailProduct B x : ℤ) ∣ y then 1 else 0) ∂ A.law N hX

/-- A nonempty subset of a finite index set, retaining its nonemptiness proof. -/
abbrev NonemptySubset (m : ℕ) := {U : Finset (Fin m) // U.Nonempty}

/-- The finite family of all nonempty subsets of a finite index set. -/
def nonemptySubsets (m : ℕ) : Finset (NonemptySubset m) := Finset.univ

/-- The paper's anchor `a(J) = max J`. -/
noncomputable def anchor {m : ℕ} (J : Finset (Fin m)) (hJ : J.Nonempty) : Fin m :=
  J.max' hJ

/-- The integer-valued form `L_J(z)`; the divisibility condition on the scales
is recorded in `MasterChain.scale_anchor_dvd`. -/
def linearForm {m : ℕ} (c : Fin m → ℕ) (J : Finset (Fin m))
    (hJ : J.Nonempty) (z : Fin m → ℕ) : ℤ :=
  ∑ k ∈ J, ((c k / c (anchor J hJ)) * z k : ℕ)

/-- The product variable `z_U` used by the multiplicative masks. -/
def subsetProduct {m : ℕ} (U : Finset (Fin m)) (z : Fin m → ℕ) : ℕ :=
  ∏ k ∈ U, z k

/-- The initial correlation integrand in equation `eq:correlation-initial`.
`b` is indexed by nonempty product masks and `g` by nonempty linear forms. -/
def correlationIntegrand {m : ℕ} (c : Fin m → ℕ)
    (b : Finset (Fin m) → ℕ → ℝ) (g : Finset (Fin m) → ℤ → ℝ)
    (z : Fin m → ℕ) : ℝ :=
  (∏ U ∈ nonemptySubsets m, b U.val (subsetProduct U.val z)) *
    ∏ J ∈ nonemptySubsets m, g J.val (linearForm c J.val J.property z)

/-- Average over the pivot variables in the master chain. This is the
pushforward of `Parameters.law` under the pivot-coordinate map; using the
source law directly avoids introducing a second copy of its product measure. -/
noncomputable def chainAverage {n m : ℕ} (C : MasterChain n m) (N : ℕ)
    (F : (Fin m → ℕ) → ℝ) : ℝ :=
  ∫ x, F (fun d => x (C.blocks d).1) ∂ C.parameters.law N (C.law_cutoff N)

/-- Correlation `𝒞` in equation `eq:correlation-initial`. -/
noncomputable def correlation {n m : ℕ} (C : MasterChain n m) (N : ℕ)
    (b : Finset (Fin m) → ℕ → ℝ) (g : Finset (Fin m) → ℤ → ℝ) : ℝ :=
  chainAverage C N (fun z => correlationIntegrand (C.integerScale N) b g z)

/-- Supremum-norm and divisor-majorant hypotheses from the opening setup of
§4. The target support is required to be nonsingleton. -/
def CorrelationFunctionsValid {n m : ℕ} (C : MasterChain n m) (N : ℕ)
    (Jstar : Finset (Fin m)) (b : Finset (Fin m) → ℕ → ℝ)
    (g : Finset (Fin m) → ℤ → ℝ) : Prop :=
  Jstar.Nonempty ∧ 2 ≤ Jstar.card ∧
    (∀ U ∈ nonemptySubsets m, ∀ y, |b U.val y| ≤ 1) ∧
    (∀ J ∈ nonemptySubsets m, ∀ y,
      |g J.val y| ≤ 1 + divisorWeight C.parameters N (C.law_cutoff N)
        (C.blocks (anchor J.val J.property)) y)

/-- A finite harmonic prime pool with its reciprocal mass. -/
def primeHarmonicMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (p : ℝ)⁻¹

/-- Expectation under the law `λ(p) = 1/(p S)` on a finite prime pool. -/
noncomputable def primeAverage (P : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  (primeHarmonicMass P)⁻¹ * ∑ p ∈ P, (p : ℝ)⁻¹ * f p

/-- Product of independent reciprocal prime laws on the same finite pool.
Separate gaps use separate instances of this average in the arithmetic lane. -/
noncomputable def primeTupleAverage {q : ℕ} (P : Finset ℕ)
    (f : (Fin q → ℕ) → ℝ) : ℝ := by
  classical
  exact ((primeHarmonicMass P) ^ q)⁻¹ *
    ∑ p ∈ Fintype.piFinset (fun _ : Fin q => P),
      (∏ i, (p i : ℝ)⁻¹) * f p

/-- Reciprocal prime-tuple law conditioned on a prime-only good event and
renormalized to probability one. -/
noncomputable def goodPrimeTupleAverage {q : ℕ} (P : Finset ℕ)
    (good : (Fin q → ℕ) → Prop) (f : (Fin q → ℕ) → ℝ) : ℝ := by
  classical
  let mass := primeTupleAverage P (fun p => if good p then 1 else 0)
  exact mass⁻¹ * primeTupleAverage P (fun p => if good p then f p else 0)

/-- A formal prime-dependent row template. An exponent in `ℤ` records a
Laurent monomial in the formal prime slots, so substitutions by reciprocal
prime powers remain literal and parallelity is symbolic. -/
structure RowTemplate (m q : ℕ) where
  exponent : Fin m → Option (Fin q → ℤ)
  support : Finset (Fin m)
  support_spec : ∀ k, k ∈ support ↔ (exponent k).isSome
  anchor : Fin m
  anchor_mem : anchor ∈ support
  anchor_max : ∀ k ∈ support, k ≤ anchor
  slotColumns : Fin m → Finset (Fin q)
  slotColumns_spec : ∀ k, slotColumns k =
    Finset.univ.filter fun i => ∃ e, exponent k = some e ∧ e i ≠ 0
  prime_slots_disjoint : ∀ k k', k ≠ k' → Disjoint (slotColumns k) (slotColumns k')

/-- Rational evaluation of a formal Laurent prime monomial. -/
def monomialValue {q : ℕ} (e : Fin q → ℤ) (p : Fin q → ℕ) : ℚ :=
  ∏ i, (p i : ℚ) ^ (e i)

/-- The same Laurent monomial represented in the fraction field of the
multivariable polynomial ring. -/
noncomputable def monomialFraction {q : ℕ} (e : Fin q → ℤ) :
    FractionRing (MvPolynomial (Fin q) ℚ) :=
  algebraMap _ _ (MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm fun i => Int.toNat (max 0 (e i))) (1 : ℚ)) /
    algebraMap _ _ (MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm fun i => Int.toNat (max 0 (-e i))) (1 : ℚ))

/-- Rational-function coefficient represented by a row-template entry. -/
noncomputable def RowTemplate.coeff {m q : ℕ} (A : RowTemplate m q) (k : Fin m) :
    FractionRing (MvPolynomial (Fin q) ℚ) :=
  (A.exponent k).elim 0 monomialFraction

/-- Parallelity over the rational-function field, as required by §4. -/
def ParallelRows {m q : ℕ} (A B : RowTemplate m q) : Prop :=
  A.support = B.support ∧ ∃ e : Fin q → ℤ, ∀ k ∈ A.support,
    ∃ a b, A.exponent k = some a ∧ B.exponent k = some b ∧
      ∀ i, b i = a i + e i

/-- Integer polynomial direction vectors used in Lemma `lem:row-directions`. -/
abbrev PolynomialVector (m q : ℕ) := Fin m → MvPolynomial (Fin q) ℤ

/-- Coefficient map used to view an integer polynomial as a rational function. -/
def rationalPolynomial {q : ℕ} (p : MvPolynomial (Fin q) ℤ) :
    MvPolynomial (Fin q) ℚ := MvPolynomial.map (Int.castRingHom ℚ) p

/-- Response of a formal row to a polynomial direction. -/
noncomputable def rowResponse {m q : ℕ} (A : RowTemplate m q)
    (v : PolynomialVector m q) : FractionRing (MvPolynomial (Fin q) ℚ) :=
  ∑ k, A.coeff k * algebraMap (MvPolynomial (Fin q) ℚ)
    (FractionRing (MvPolynomial (Fin q) ℚ)) (rationalPolynomial (v k))

end

end HindmanSumsProducts
