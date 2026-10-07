import HindmanSumsProducts.Correlation.FromArithmetic
import HindmanSumsProducts.Correlation.Outside

/-!
# Removing multiplicative masks and detecting a shifted error

Skeleton of §4. The asymptotic parameter is `N` and the paper's `w` is
`N + 1`. All `o(1)` assertions below are expressed as explicit convergence or
eventual inequalities. -/

namespace HindmanSumsProducts

attribute [local instance] Classical.propDecidable

open MeasureTheory
open Filter
open scoped Topology BigOperators

/-- `f ≤ g + o(1)` along the asymptotic index. -/
def asymptoticLe (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, f N ≤ g N + ε

/-- Number of nonempty product masks in a chain of length `m`. -/
def maskCount (m : ℕ) : ℕ := 2 ^ m - 1

/-- The row bound `K_m=q_mask 2^{q_mask}` from Lemma `lem:mask-removal`. -/
def maskRowBound (m : ℕ) : ℕ := maskCount m * 2 ^ maskCount m

/-- Uniform prefactor for the iterated additive Cauchy–Schwarz steps. -/
def additiveEliminationConstant (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * maskRowBound m * 2 ^ maskRowBound m)

/-- The harmonic law of one pivot coordinate, as the marginal of
`Parameters.law`. -/
noncomputable def pivotAverage {n m : ℕ} (C : MasterChain n m) (N : ℕ)
    (i : Fin n) (F : ℕ → ℝ) : ℝ :=
  ∫ x, F (x i) ∂ C.parameters.law N (C.law_cutoff N)

/-- Expectation of a function of all independent raw harmonic variables. -/
noncomputable def rawAverage {n m : ℕ} (C : MasterChain n m) (N : ℕ)
    (F : (Fin n → ℕ) → ℝ) : ℝ :=
  ∫ x, F x ∂ C.parameters.law N (C.law_cutoff N)

/-- Correlation formed from a family of prime-dependent formal row templates.
The integer coefficient field is the evaluation of
`(c_k/c_{a(R)}) A_{R,k}`; `coefficient_formula` records that identity. -/
structure CorrelationRows {n m q r : ℕ} (C : MasterChain n m) where
  templates : Fin r → RowTemplate m q
  star : Fin r
  coefficient : ℕ → (Fin q → ℕ) → Fin r → Fin m → ℤ
  coefficient_formula : ∀ N p R k,
    (coefficient N p R k : ℚ) =
      ((C.integerScale N k / C.integerScale N (templates R).anchor : ℕ) : ℚ) *
        ((templates R).exponent k).elim 0 (fun e => monomialValue e p)
  functions : ℕ → Fin r → (Fin q → ℕ) → ℤ → ℝ

/-- Integer form attached to a row after substituting its prime slots. -/
def CorrelationRows.form {n m q r : ℕ} {C : MasterChain n m}
    (S : CorrelationRows (q := q) (r := r) C) (N : ℕ) (p : Fin q → ℕ) (R : Fin r)
    (z : Fin m → ℕ) : ℤ :=
  ∑ k, S.coefficient N p R k * (z k : ℤ)

/-- Linear response of a row to an integer translation vector. -/
def CorrelationRows.response {n m q r : ℕ} {C : MasterChain n m}
    (S : CorrelationRows (q := q) (r := r) C) (N : ℕ) (p : Fin q → ℕ) (R : Fin r)
    (v : Fin m → ℤ) : ℤ :=
  ∑ k, S.coefficient N p R k * v k

/-- Pairwise rational-function nonparallelity of a row family. -/
def CorrelationRows.PairwiseNonparallel {n m q r : ℕ} {C : MasterChain n m}
    (S : CorrelationRows (q := q) (r := r) C) : Prop :=
  ∀ R I, R ≠ I → ¬ ParallelRows (S.templates R) (S.templates I)

/-- Exact retention of the distinguished target function. -/
def CorrelationRows.TargetIs {n m q r : ℕ} {C : MasterChain n m}
    (S : CorrelationRows (q := q) (r := r) C) (Jstar : Finset (Fin m))
    (g : ℕ → Finset (Fin m) → ℤ → ℝ) : Prop :=
  ∀ N p y, S.functions N S.star p y = g N Jstar y

/-- Divisor-weight majorants for every row function. -/
def CorrelationRows.HasWeightBounds {n m q r : ℕ} {C : MasterChain n m}
    (S : CorrelationRows (q := q) (r := r) C) : Prop :=
  ∀ N R p y, |S.functions N R p y| ≤
    1 + divisorWeight C.parameters N (C.law_cutoff N)
      (C.blocks (S.templates R).anchor) y

/-- Product expectation over the independent prime slots and pivot samples. -/
noncomputable def rowCorrelation {n m q r : ℕ} (C : MasterChain n m)
    (S : CorrelationRows (q := q) (r := r) C) (P : ℕ → Finset ℕ) (N : ℕ) : ℝ :=
  primeTupleAverage (P N) fun p =>
    ∫ x, ∏ R, S.functions N R p
      (S.form N p R (fun d => x (C.blocks d).1))
      ∂ C.parameters.law N (C.law_cutoff N)

/-- Row correlation after restricting prime tuples to the normalized good
law produced by Lemma `lem:row-directions`. -/
noncomputable def goodRowCorrelation {n m q r : ℕ} (C : MasterChain n m)
    (S : CorrelationRows (q := q) (r := r) C) (P : ℕ → Finset ℕ)
    (good : ℕ → (Fin q → ℕ) → Prop) (N : ℕ) : ℝ :=
  goodPrimeTupleAverage (P N) (good N) fun p =>
    ∫ x, ∏ R, S.functions N R p
      (S.form N p R (fun d => x (C.blocks d).1))
      ∂ C.parameters.law N (C.law_cutoff N)

/-- Error of replacing a pivot sample by a fresh independent prime dilation.
The error bound is uniform over the auxiliary parameter `a` and all bounded
function families. -/
theorem prime_insertion_average
    {n m : ℕ} (C : MasterChain n m) (i : Fin n) (hi : C.gap < i)
    (P : ℕ → Finset ℕ) (V : ℕ → ℕ)
    (hV : Tendsto (fun N => V N) atTop atTop)
    (hP : ∀ N p, p ∈ P N → p.Prime ∧ V N < p)
    (hMass : ∀ A : ℝ, 0 < A → Tendsto
      (fun N => primeHarmonicMass (P N) / (V N : ℝ) ^ A) atTop atTop)
    (A : ℝ) (hA : 0 < A) :
    ∃ err : ℕ → ℝ, tendsToZero err ∧
      ∀ (α : Type) (F : ℕ → α → ℕ → ℝ),
        (∀ N a y, |F N a y| ≤ (V N : ℝ) ^ A) →
        ∀ a, ∀ᶠ N in atTop,
          |pivotAverage C N i (F N a) -
            primeAverage (P N) (fun p =>
              pivotAverage C N i (fun y => F N a (p * y)))| ≤ err N := by
  sorry

/-- Fixed-dilation substitution and its superpolynomial total-mass error,
equation `eq:prime-fixed-dilation`. Division is used only under the displayed
divisibility indicator. -/
theorem prime_insertion_fixed_dilation
    {n m : ℕ} (C : MasterChain n m) (i : Fin n) (hi : C.gap < i)
    (Pplus V k : ℕ → ℕ) (hV : Tendsto (fun N => V N) atTop atTop)
    (A : ℝ) (hA : 0 < A) (B C₀ : ℕ)
    (hkBound : ∀ N, k N ≤ C₀ * (Pplus N + V N) ^ B)
    (hkCoprime : ∀ᶠ N in atTop, Nat.Coprime (k N) (primorial (N + 1))) :
    (∀ C₀ : ℝ, 0 < C₀ → tendsToZero fun N =>
      (V N : ℝ) ^ C₀ * |pivotAverage C N i (fun y =>
        if k N ∣ y then (k N : ℝ) else 0) - 1|) ∧
    ∃ err : ℕ → ℝ, tendsToZero err ∧
      ∀ (α : Type) (F : ℕ → α → ℕ → ℝ),
        (∀ N a y, |F N a y| ≤ (V N : ℝ) ^ A) →
        ∀ a, ∀ᶠ N in atTop,
          |pivotAverage C N i (fun y => F N a (k N * y)) -
            pivotAverage C N i (fun y =>
              if k N ∣ y then (k N : ℝ) * F N a y else 0)| ≤ err N := by
  sorry

/-- Lemma `lem:prime-insertion`, §4, lines 61–119. -/
theorem prime_insertion
    {n m : ℕ} (C : MasterChain n m) (i : Fin n) (hi : C.gap < i)
    (P : ℕ → Finset ℕ) (Pplus V : ℕ → ℕ)
    (hV : Tendsto (fun N => V N) atTop atTop)
    (hP : ∀ N p, p ∈ P N → p.Prime ∧ V N < p)
    (hMass : ∀ A : ℝ, 0 < A → Tendsto
      (fun N => primeHarmonicMass (P N) / (V N : ℝ) ^ A) atTop atTop) :
    (∀ A : ℝ, 0 < A →
      ∃ err : ℕ → ℝ, tendsToZero err ∧
        ∀ (α : Type) (F : ℕ → α → ℕ → ℝ),
          (∀ N a y, |F N a y| ≤ (V N : ℝ) ^ A) →
          ∀ a, ∀ᶠ N in atTop,
            |pivotAverage C N i (F N a) -
              primeAverage (P N) (fun p =>
                pivotAverage C N i (fun y => F N a (p * y)))| ≤ err N) ∧
    (∀ (k : ℕ → ℕ) (A : ℝ), 0 < A → ∀ B C₀ : ℕ,
      (∀ N, k N ≤ C₀ * (Pplus N + V N) ^ B) →
        (∀ᶠ N in atTop, Nat.Coprime (k N) (primorial (N + 1))) →
        (∀ C₁ : ℝ, 0 < C₁ → tendsToZero fun N =>
          (V N : ℝ) ^ C₁ * |pivotAverage C N i (fun y =>
            if k N ∣ y then (k N : ℝ) else 0) - 1|) ∧
        ∃ err : ℕ → ℝ, tendsToZero err ∧
          ∀ (α : Type) (F : ℕ → α → ℕ → ℝ),
            (∀ N a y, |F N a y| ≤ (V N : ℝ) ^ A) →
            ∀ a, ∀ᶠ N in atTop,
              |pivotAverage C N i (fun y => F N a (k N * y)) -
                pivotAverage C N i (fun y =>
                  if k N ∣ y then (k N : ℝ) * F N a y else 0)| ≤ err N) := by
  refine ⟨?_, ?_⟩
  · intro A hA
    exact prime_insertion_average C i hi P V hV hP hMass A hA
  · intro k A hA B C₀ hkBound hkCoprime
    exact prime_insertion_fixed_dilation C i hi Pplus V k hV A hA B C₀
      hkBound hkCoprime

/-- At one mask-removal step, weighted Cauchy–Schwarz leaves one copy of
each invariant row weight. -/
theorem mask_removal_weighted_cauchy_schwarz
    {α : Type} [MeasurableSpace α] (μ : Measure α) (Ω H₀ H₁ : α → ℝ)
    (hΩ : ∀ x, 0 ≤ Ω x) (h0 : ∀ x, |H₀ x| ≤ Ω x)
    (hΩint : Integrable Ω μ)
    (hH1int : Integrable (fun x => Ω x * H₁ x ^ 2) μ) :
    |∫ x, H₀ x * H₁ x ∂ μ| ^ 2 ≤
      (∫ x, Ω x ∂ μ) * (∫ x, Ω x * H₁ x ^ 2 ∂ μ) := by
  sorry

/-- Row templates and their prime-dependent integer forms arising after the
mask substitutions. The row templates are chosen before scales and functions;
the form coefficients are the integer realizations in equation
`eq:correlation-row-template`. -/
structure MaskRemovalRows (m q r : ℕ) where
  templates : Fin r → RowTemplate m q
  star : Fin r
  pairwise_nonparallel : ∀ R I, R ≠ I →
    ¬ ParallelRows (templates R) (templates I)

/-- Index type for rows other than the distinguished target. -/
abbrev NonTargetIndex (r : ℕ) (star : Fin r) := {R : Fin r // R ≠ star}

/-- Lemma `lem:mask-removal`, §4, lines 135–307. The row count, prime-slot
count, and prefactor are chosen before the chain, scales, and functions. -/
theorem weighted_mask_removal (m : ℕ) (Jstar : Finset (Fin m))
    (hJ : Jstar.Nonempty) (hJcard : 2 ≤ Jstar.card) :
    ∃ C_m : ℝ, 0 < C_m ∧ ∃ q r : ℕ, r ≤ maskRowBound m ∧
      q ≤ 2 * maskCount m ∧ ∃ Shape : MaskRemovalRows m q r,
        ∀ {n : ℕ} (C : MasterChain n m) (P : ℕ → Finset ℕ)
          (V : ℕ → ℕ),
          (∀ N p, p ∈ P N → p.Prime ∧ V N < p) →
          (∀ A : ℝ, 0 < A → Tendsto
            (fun N => primeHarmonicMass (P N) / (V N : ℝ) ^ A) atTop atTop) →
          (∀ (b : ℕ → Finset (Fin m) → ℕ → ℝ)
            (g : ℕ → Finset (Fin m) → ℤ → ℝ),
            (∀ N, CorrelationFunctionsValid C N Jstar
            (b N) (g N)) →
            ∃ Rows : CorrelationRows (q := q) (r := r) C,
              Rows.templates = Shape.templates ∧ Rows.star = Shape.star ∧
              CorrelationRows.PairwiseNonparallel Rows ∧
              CorrelationRows.TargetIs Rows Jstar g ∧
              CorrelationRows.HasWeightBounds Rows ∧
              asymptoticLe
                (fun N => |correlation C N (b N) (g N)| ^ (2 ^ (2 ^ m - 1)))
                (fun N => C_m * |rowCorrelation C Rows P N|)) := by
  sorry

/-- Algebraic kernel directions from Lemma `lem:row-directions`: each
nontarget row has a polynomial vector in its kernel that moves every other
row, and a second vector kills only the target response. -/
structure PolynomialDirections {m q r : ℕ}
    (templates : Fin r → RowTemplate m q) (star : Fin r) where
  direction : Fin r → PolynomialVector m q
  targetDirection : PolynomialVector m q
  kernel : ∀ R, R ≠ star → rowResponse (templates R) (direction R) = 0
  separates : ∀ R I, R ≠ star → I ≠ R →
    rowResponse (templates I) (direction R) ≠ 0
  target_kernel : rowResponse (templates star) targetDirection = 0
  target_separates : ∀ I, I ≠ star →
    rowResponse (templates I) targetDirection ≠ 0
  responseNumerator : Fin r → MvPolynomial (Fin q) ℤ
  responseDenominator : Fin r → MvPolynomial (Fin q) ℤ
  response_denominator_nonzero : ∀ R, R ≠ star → responseDenominator R ≠ 0
  response_fraction : ∀ R, R ≠ star →
    rowResponse (templates star) (direction R) =
      algebraMap _ _ (rationalPolynomial (responseNumerator R)) /
        algebraMap _ _ (rationalPolynomial (responseDenominator R))

/-- Integer translations with modulus `M(p)=M|D(p)|_{>w}`. All translations
are in `Wℤ^m`, have responses `M` at the target and zero at their assigned
row, and have size bounded by a fixed power of `P_l^+ + V_l`. The final field
encodes the finite polynomial exception list for unit responses. -/
def roughPart (w : ℕ) (z : ℤ) : ℕ :=
  ∏ p ∈ (Int.natAbs z).factorization.support.filter (fun p => w < p),
    p ^ (Int.natAbs z).factorization p

/-- Evaluate an integer polynomial at the natural prime slots in `ℚ`. -/
def integerPolynomialEval {q : ℕ} (P : MvPolynomial (Fin q) ℤ)
    (p : Fin q → ℕ) : ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (p i : ℚ)) P

/-- Integer translations constructed from the polynomial directions. -/
structure IntegerDirectionData {n m q r : ℕ} {C : MasterChain n m}
    (Rows : CorrelationRows (q := q) (r := r) C)
    (polynomialDirections : PolynomialDirections Rows.templates Rows.star) where
  baseModulus : ℕ → ℕ
  Pplus : ℕ → ℕ
  V : ℕ → ℕ
  polynomial : MvPolynomial (Fin q) ℤ
  polynomial_nonzero : polynomial ≠ 0
  polynomial_is_product_of_target_responses : polynomial =
    ∏ R : NonTargetIndex r Rows.star,
      polynomialDirections.responseNumerator R.val
  exceptionalPolynomials : Finset (MvPolynomial (Fin q) ℤ)
  modulus : ℕ → (Fin q → ℕ) → ℕ
  good : ℕ → (Fin q → ℕ) → Prop
  vector : ℕ → (Fin q → ℕ) → Fin r → Fin m → ℤ
  polynomial_eval_nonzero : ∀ N p, good N p →
    polynomial.eval (fun i => (p i : ℤ)) ≠ 0
  response_denominator_eval_nonzero : ∀ N p R, good N p → R ≠ Rows.star →
    integerPolynomialEval (polynomialDirections.responseDenominator R) p ≠ 0
  modulus_formula : ∀ N p, good N p → modulus N p =
    baseModulus N * roughPart (N + 1) (polynomial.eval fun i => (p i : ℤ))
  vector_formula : ∀ N p R k, good N p →
    (vector N p R k : ℚ) =
      if hR : R = Rows.star then
        (baseModulus N : ℚ) *
          (C.integerScale N (Rows.templates Rows.star).anchor : ℚ) /
            C.integerScale N k *
          integerPolynomialEval (polynomialDirections.targetDirection k) p
      else
        (modulus N p : ℚ) *
          (C.integerScale N (Rows.templates Rows.star).anchor : ℚ) /
            C.integerScale N k *
          integerPolynomialEval (polynomialDirections.direction R k) p *
          integerPolynomialEval (polynomialDirections.responseDenominator R) p /
            integerPolynomialEval (polynomialDirections.responseNumerator R) p
  target_response : ∀ N p, good N p →
    Rows.response N p Rows.star (vector N p Rows.star) = 0
  row_kernel_response : ∀ N p R, good N p → R ≠ Rows.star →
    Rows.response N p R (vector N p R) = 0
  target_moved_response : ∀ N p R, good N p → R ≠ Rows.star →
    Rows.response N p Rows.star (vector N p R) = (modulus N p : ℤ)
  other_responses_nonzero : ∀ N p R I, good N p → R ≠ Rows.star →
    I ≠ R → Rows.response N p I (vector N p R) ≠ 0
  W_divides_coordinates : ∀ N p R k, good N p →
    (primorial (N + 1) : ℤ) ∣ vector N p R k
  size_bound : ∃ A : ℕ, ∀ᶠ N in atTop, ∀ p R k, good N p →
    Int.natAbs (vector N p R k) ≤ (Pplus N + V N) ^ A
  response_unit_off_exceptional_polynomials : ∀ N p R I π,
    good N p → R ≠ Rows.star → I ≠ R → π.Prime → N + 1 < π →
    π ≤ V N →
    (∀ Q ∈ exceptionalPolynomials,
      ¬ ((π : ℤ) ∣ Q.eval fun j => (p j : ℤ))) →
      ¬ ((π : ℤ) ∣ Rows.response N p I (vector N p R))
  target_direction_unit_off_exceptional_polynomials : ∀ N p I π,
    good N p → I ≠ Rows.star → π.Prime → N + 1 < π → π ≤ V N →
    (∀ Q ∈ exceptionalPolynomials,
      ¬ ((π : ℤ) ∣ Q.eval fun j => (p j : ℤ))) →
      ¬ ((π : ℤ) ∣ Rows.response N p I (vector N p Rows.star))

/-- Polynomial-vector construction (the first part of `lem:row-directions`). -/
theorem row_directions_polynomial
    {m q r : ℕ} (Rows : MaskRemovalRows m q r)
    (hm : 2 ≤ m) (hr : 2 ≤ r) :
    Nonempty (PolynomialDirections Rows.templates Rows.star) := by
  sorry

/-- Integer clearing of smooth denominators and rough factors, with
scale-separation size and unit-residue bounds (the second part of
`lem:row-directions`). -/
theorem row_directions_integer
    {n m q r : ℕ} {C : MasterChain n m}
    (Rows : CorrelationRows (q := q) (r := r) C)
    (D : PolynomialDirections Rows.templates Rows.star) :
    Nonempty (IntegerDirectionData Rows D) := by
  sorry

/-- Lemma `lem:row-directions`, §4, lines 322–418. -/
theorem row_directions
    {n m q r : ℕ} (C : MasterChain n m)
    (Rows : CorrelationRows (q := q) (r := r) C)
    (hm : 2 ≤ m) (hr : 2 ≤ r) :
    ∃ D : PolynomialDirections Rows.templates Rows.star,
      Nonempty (IntegerDirectionData Rows D) := by
  sorry

/-- Two copies of the shift for each nontarget row. -/
abbrev ShiftArray (r : ℕ) (star : Fin r) :=
  NonTargetIndex r star → Fin 2 → ℕ

/-- Uniform average over two independent shifts in `[0,L)` for each
nontarget row. -/
noncomputable def intervalShiftAverage {r : ℕ} (star : Fin r) (L : ℕ)
    (F : ShiftArray r star → ℝ) : ℝ := by
  classical
  let ι := NonTargetIndex r star × Fin 2
  exact ((L : ℝ) ^ (2 * Fintype.card (NonTargetIndex r star)))⁻¹ *
    ∑ s ∈ Fintype.piFinset (fun _ : ι => Finset.range L),
      F (fun R b => s (R, b))

/-- The target cube after additive elimination, before the final change of
root law; the vertices are `ℓ_*(z)+M∑_R u_R^{ω_R}`. -/
noncomputable def additiveCubeAverage {n m q r : ℕ} (C : MasterChain n m)
    (Rows : CorrelationRows (q := q) (r := r) C) (P : ℕ → Finset ℕ) (N : ℕ)
    (good : ℕ → (Fin q → ℕ) → Prop)
    (M L : ℕ → (Fin q → ℕ) → ℕ) : ℝ := by
  classical
  exact goodPrimeTupleAverage (P N) (good N) fun p => intervalShiftAverage Rows.star (L N p)
    (fun u => ∫ x,
      ∏ ω : NonTargetIndex r Rows.star → Fin 2,
        Rows.functions N Rows.star p
          (Rows.form N p Rows.star (fun d => x (C.blocks d).1) +
            (M N p : ℤ) * ∑ R : NonTargetIndex r Rows.star,
              (u R (ω R) : ℤ))
      ∂ C.parameters.law N (C.law_cutoff N))

/-- Weighted Cauchy–Schwarz elimination of one nontarget row, retaining its
divisor weights once. -/
theorem additive_elimination_weighted_cauchy_schwarz
    {α : Type} [MeasurableSpace α] (μ : Measure α) (Ω Hout Hin : α → ℝ)
    (hΩ : ∀ x, 0 ≤ Ω x) (hH : ∀ x, |Hout x| ≤ Ω x)
    (hΩint : Integrable Ω μ)
    (hHin : Integrable (fun x => Ω x * Hin x ^ 2) μ) :
    |∫ x, Hout x * Hin x ∂ μ| ^ 2 ≤
      (∫ x, Ω x ∂ μ) * (∫ x, Ω x * Hin x ^ 2 ∂ μ) := by
  sorry

/-- The retained-weight moment identities in equation
`eq:auxiliary-weight-moments`. -/
structure AuxiliaryMomentSystem (d t : ℕ) where
  sampleType : Type
  [measurableSpace : MeasurableSpace sampleType]
  law : ℕ → Measure sampleType
  targetBound : ℕ → sampleType → ℝ
  retainedWeightAverage : ℕ → sampleType → ℝ
  expandedFormsDistinct : Prop
  freshDivisorDraws : Prop

noncomputable def auxiliaryMomentB {d t : ℕ} (S : AuxiliaryMomentSystem d t)
    (N : ℕ) : ℝ := ∫ x, S.targetBound N x ∂ S.law N

noncomputable def auxiliaryMomentBH {d t : ℕ} (S : AuxiliaryMomentSystem d t)
    (N : ℕ) : ℝ := ∫ x, S.targetBound N x * S.retainedWeightAverage N x ∂ S.law N

noncomputable def auxiliaryMomentBH2 {d t : ℕ} (S : AuxiliaryMomentSystem d t)
    (N : ℕ) : ℝ := ∫ x, S.targetBound N x * (S.retainedWeightAverage N x) ^ 2 ∂ S.law N

theorem additive_elimination_auxiliary_moments
    {d t : ℕ} (S : AuxiliaryMomentSystem d t)
    (hDistinct : S.expandedFormsDistinct) (hFresh : S.freshDivisorDraws) :
    tendsToZero (fun N => |auxiliaryMomentB S N - 2 ^ (2 ^ d)|) ∧
    tendsToZero (fun N => |auxiliaryMomentBH S N - 2 ^ (2 ^ d + t)|) ∧
    tendsToZero (fun N => |auxiliaryMomentBH2 S N - 2 ^ (2 ^ d + 2 * t)|) := by
  sorry

/-- Weighted additive elimination, Lemma `lem:additive-elimination`,
§4, lines 420–573. -/
theorem weighted_additive_elimination
    {n m q r : ℕ} (C : MasterChain n m)
    (Rows : CorrelationRows (q := q) (r := r) C)
    (P : ℕ → Finset ℕ) (V : ℕ → ℕ)
    (good : ℕ → (Fin q → ℕ) → Prop)
    (Rgap : ℕ → ℕ) (M L : ℕ → (Fin q → ℕ) → ℕ)
    (Directions : PolynomialDirections Rows.templates Rows.star)
    (Dirs : IntegerDirectionData Rows Directions)
    (hGood : ∀ N p, good N p ↔ Dirs.good N p)
    (hM : ∀ N p, M N p = Dirs.modulus N p)
    (hGoodMass : tendsToZero fun N =>
      primeTupleAverage (P N) (fun p => if good N p then 0 else 1))
    (Jstar : Finset (Fin m)) (b : ℕ → Finset (Fin m) → ℕ → ℝ)
    (g : ℕ → Finset (Fin m) → ℤ → ℝ)
    (hValid : ∀ N, CorrelationFunctionsValid C N Jstar (b N) (g N))
    (hRows : CorrelationRows.PairwiseNonparallel Rows ∧
      CorrelationRows.HasWeightBounds Rows ∧ CorrelationRows.TargetIs Rows Jstar g)
    (J0 : ℕ) (hJ0 : 0 < J0)
    (hL : ∀ N p, L N p = Rgap N / (J0 * M N p))
    (hrBound : r ≤ maskRowBound m)
    (hd : 1 ≤ Fintype.card (NonTargetIndex r Rows.star)) :
    asymptoticLe
      (fun N => |goodRowCorrelation C Rows P good N| ^
        (2 ^ Fintype.card (NonTargetIndex r Rows.star)))
      (fun N => additiveEliminationConstant m *
        |additiveCubeAverage C Rows P N good M L|) := by
  sorry

/-- The one-variable cube expectation in equation `eq:correlation-test`.
Its base point is sampled at the target pivot and the shifts are
`u_R^1-u_R^0`. -/
noncomputable def oneVariableCubeTest {n m q r : ℕ} (C : MasterChain n m)
    (Rows : CorrelationRows (q := q) (r := r) C) (P : ℕ → Finset ℕ)
    (good : ℕ → (Fin q → ℕ) → Prop)
    (M L : ℕ → (Fin q → ℕ) → ℕ)
    (Jstar : Finset (Fin m)) (hJ : Jstar.Nonempty)
    (g : ℕ → Finset (Fin m) → ℤ → ℝ) (N : ℕ) : ℝ := by
  classical
  exact goodPrimeTupleAverage (P N) (good N) fun p =>
    intervalShiftAverage Rows.star (L N p) (fun u =>
      ∫ x, ∏ ω : NonTargetIndex r Rows.star → Fin 2,
        g N Jstar ((x (C.blocks (anchor Jstar hJ)).1 : ℤ) +
          (M N p : ℤ) * ∑ R : NonTargetIndex r Rows.star,
            if ω R = 1 then (u R 1 : ℤ) - u R 0 else 0)
      ∂ C.parameters.law N (C.law_cutoff N))

/-- The root-law calculation: after averaging the independent earlier
coordinate, the cube root has law `μ_{i_{a_*}}` with superpolynomial total
mass error. -/
theorem correlation_cube_root_sampling
    {n m : ℕ} (C : MasterChain n m) (a j : Fin m) (hja : j < a)
    (k b H V : ℕ → ℕ) (hK : ∀ᶠ N in atTop, 0 < k N)
    (hB : ∀ᶠ N in atTop, 0 < b N)
    (hKX : ∀ᶠ N in atTop, k N ≤ C.parameters.X N (C.blocks a).1)
    (hKCoprime : ∀ᶠ N in atTop, Nat.Coprime (k N) (primorial (N + 1)))
    (hBCoprime : ∀ᶠ N in atTop, Nat.Coprime (b N) (k N))
    (hTargetGrowth : dominatesPowers
      (fun N => Real.log (C.parameters.X N (C.blocks a).1 : ℝ))
      (fun N => (2 + primorial (N + 1) + k N + H N + V N : ℕ)) )
    (hEarlierGrowth : dominatesPowers
      (fun N => Real.log (C.parameters.X N (C.blocks j).1 : ℝ))
      (fun N => (2 + primorial (N + 1) + k N + H N + V N : ℕ)) )
    (A : ℝ) (hA : 0 < A) :
    ∃ err : ℕ → ℝ,
      (∀ C₀ : ℝ, 0 < C₀ → tendsToZero fun N => (V N : ℝ) ^ C₀ * err N) ∧
      ∀ (α : Type) (h : ℕ → α → ℕ),
        (∀ N ξ, h N ξ ≤ H N) →
        (∀ N ξ, primorial (N + 1) ∣ h N ξ) →
        ∀ (F : ℕ → α → ℕ → ℝ),
        (∀ N ξ y, |F N ξ y| ≤ (V N : ℝ) ^ A) →
        ∀ ξ, ∀ᶠ N in atTop,
          |rawAverage C N (fun x => F N ξ
                (k N * x (C.blocks a).1 + b N * x (C.blocks j).1 + h N ξ)) -
            pivotAverage C N (C.blocks a).1 (F N ξ)| ≤ err N := by
  sorry

/-- The cube-root translation and progression comparison, including the
total-variation bound in equation `eq:correlation-root-tv-bound`. -/
theorem correlation_cube_root_tv_bound
    (X W k H : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X)
    (hlog : (W : ℝ) / X < Real.log X)
    (hk : 0 < k) (hkX : k ≤ X) (hcop : Nat.Coprime k W)
    (hdiv : W ∣ H) (hHX : 2 * H < X) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      measureL1 (harmonicAffineLaw X W k H hW hX)
        (harmonicProgressionLaw X W k H hW hX) ≤
          C₀ * harmonicRootTVScale X W k H := by
  exact harmonic_root_progression_bound X W k H H hW hX hlog hk hkX hcop hdiv
    le_rfl hHX

/-- Proposition `prop:correlation-test`, §4, lines 576–707. -/
theorem uniform_correlation_test
    (m : ℕ) (hm : 2 ≤ m) (Jstar : Finset (Fin m))
    (hJ : Jstar.Nonempty) (hJcard : 2 ≤ Jstar.card) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ maskRowBound m - 1 ∧
    ∃ C_m : ℝ, 0 < C_m ∧
    ∃ q r : ℕ, q ≤ 2 * (2 ^ m - 1) ∧
      2 ≤ r ∧ r ≤ maskRowBound m ∧
      ∃ Shape : MaskRemovalRows m q r,
        ∃ hcard : Fintype.card (NonTargetIndex r Shape.star) = d,
        ∀ {n : ℕ} (C : MasterChain n m)
          (P : ℕ → Finset ℕ) (Pplus V Rgap : ℕ → ℕ)
          (good : ℕ → (Fin q → ℕ) → Prop)
          (M L : ℕ → (Fin q → ℕ) → ℕ)
          (hV : Tendsto (fun N => V N) atTop atTop)
          (hP : ∀ N (p : Fin q → ℕ), (∀ i, p i ∈ P N) →
            ∀ i, (p i).Prime ∧ V N < p i)
          (hMass : ∀ A : ℝ, 0 < A → Tendsto
            (fun N => primeHarmonicMass (P N) / (V N : ℝ) ^ A) atTop atTop)
          (hGoodSubset : ∀ N (p : Fin q → ℕ),
            (∀ i, p i ∈ P N) → good N p)
          (hGoodMass : tendsToZero fun N =>
            primeTupleAverage (P N) (fun p => if good N p then 0 else 1))
          (hGapDiv : ∀ N (p : Fin q → ℕ), good N p → M N p ∣ Rgap N)
          (J0 : ℕ) (hJ0 : 0 < J0)
          (hL : ∀ N (p : Fin q → ℕ), L N p = Rgap N / (J0 * M N p))
          (hLong : ∀ A : ℝ, 0 < A → ∀ᶠ N in atTop,
            ∀ (p : Fin q → ℕ),
            (∀ i, p i ∈ P N) → (V N : ℝ) ^ A < L N p)
          (b : ℕ → Finset (Fin m) → ℕ → ℝ)
          (g : ℕ → Finset (Fin m) → ℤ → ℝ)
          (hValid : ∀ N, CorrelationFunctionsValid C N Jstar (b N) (g N)),
          ∃ Rows : CorrelationRows (q := q) (r := r) C,
            Rows.templates = Shape.templates ∧ Rows.star = Shape.star ∧
            CorrelationRows.PairwiseNonparallel Rows ∧
            CorrelationRows.TargetIs Rows Jstar g ∧
            CorrelationRows.HasWeightBounds Rows ∧
            ∃ Directions : PolynomialDirections Rows.templates Rows.star,
              ∃ Dirs : IntegerDirectionData Rows Directions,
                (∀ N p, good N p ↔ Dirs.good N p) ∧
                (∀ N p, M N p = Dirs.modulus N p) ∧
                asymptoticLe
                  (fun N => |correlation C N (b N) (g N)|)
                  (fun N => C_m * |oneVariableCubeTest C Rows P good M L
                    Jstar hJ g N| ^
                      ((2 : ℝ) ^ (-(2 ^ m - 1 + d : ℤ)))) := by
  sorry

end HindmanSumsProducts
