import HindmanSumsProducts.Prediction.Defs

open scoped BigOperators
open MeasureTheory
open Classical

namespace HindmanSumsProducts.Prediction

/-- Uniform average on a finite type. -/
noncomputable def finiteAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

/-- The finite prime-and-shift law in (eq:prediction-dual-test), §5, lines 40–61. The prime
weights are independent harmonic prime-slot weights conditioned on a prime-only good event; the
conditional shifts are independent and uniform on `[0, shiftLength p)`. -/
structure DualTest {n : ℕ} (B : Block n) (ν : ℤ → ℝ) where
  PrimeTuple : Type
  [primeTupleFintype : Fintype PrimeTuple]
  [primeTupleDecidableEq : DecidableEq PrimeTuple]
  dimension : ℕ
  primeSlots : ℕ
  gap : Fin n
  gap_after_tail : ∀ j ∈ B.2.val, j < gap
  gap_before_pivot : gap < B.1
  J0 : ℕ
  J0_pos : 0 < J0
  gapLength : ℕ
  baseModulus : ℕ
  baseModulus_pos : 0 < baseModulus
  primeValue : PrimeTuple → Fin primeSlots → ℕ
  primePool : Fin primeSlots → Finset ℕ
  primePoolStructure : Prop
  poolMass : Fin primeSlots → ℝ
  poolMass_eq : ∀ j, poolMass j = ∑ p ∈ primePool j, (p : ℝ)⁻¹
  goodTuple : PrimeTuple → Prop
  primePool_support : ∀ p j, primeValue p j ∈ primePool j ∧ Nat.Prime (primeValue p j)
  primeTuple_distinct : ∀ p i j, i ≠ j → primeValue p i ≠ primeValue p j
  primeTuple_value_injective : ∀ p p',
    (∀ j, primeValue p j = primeValue p' j) → p = p'
  polynomial : MvPolynomial (Fin primeSlots) ℤ
  goodTuple_polynomial_ne_zero : ∀ p, goodTuple p →
    polynomial.eval (fun j => (primeValue p j : ℤ)) ≠ 0
  normalizer : ℝ
  normalizer_pos : 0 < normalizer
  normalizer_eq : normalizer = ∑ p, if goodTuple p then
    ∏ j, (primeValue p j : ℝ)⁻¹ else 0
  goodTupleMass : ℝ
  goodTupleMass_nonneg : 0 ≤ goodTupleMass
  goodTupleMass_le_one : goodTupleMass ≤ 1
  goodTupleMass_eq : goodTupleMass = normalizer / ∏ j, poolMass j
  primeWeight : PrimeTuple → ℝ
  primeWeight_nonneg : ∀ p, 0 ≤ primeWeight p
  primeWeight_sum_one : ∑ p, primeWeight p = 1
  primeWeight_eq : ∀ p, primeWeight p = if goodTuple p then
    (∏ j, (primeValue p j : ℝ)⁻¹) / normalizer else 0
  modulus : PrimeTuple → ℕ
  modulus_pos : ∀ p, 0 < modulus p
  baseModulus_dvd : ∀ p, baseModulus ∣ modulus p
  modulus_eq : ∀ p, modulus p = baseModulus *
    (polynomial.eval (fun j => (primeValue p j : ℤ))).natAbs
  shiftLength : PrimeTuple → ℕ
  shiftLength_pos : ∀ p, 0 < shiftLength p
  shiftLength_eq : ∀ p, shiftLength p = gapLength / (J0 * modulus p)
  primeFactor : PrimeTuple → ℝ
  primeFactor_bound : ∀ p, |primeFactor p| ≤ 1
  input : PrimeTuple → (ω : Finset (Fin dimension)) → ω.Nonempty → ℤ → ℝ
  input_bound : ∀ (p : PrimeTuple) (ω : Finset (Fin dimension))
    (hω : ω.Nonempty) (y : ℤ), |input p ω hω y| ≤ 1 + ν y

attribute [instance] DualTest.primeTupleFintype DualTest.primeTupleDecidableEq

/-- Along a family of tests the good-tuple restriction has unconditioned probability `1-o(1)`,
as supplied by the master scales and polynomial exceptional-set deletion. -/
def DualTestFamilyGood {n : ℕ} {B : Block n} (A : Parameters n)
    (D : ∀ N, DualTest B (divisorWeight A N B)) : Prop :=
  tendsToZeroAtTop (fun N => 1 - (D N).goodTupleMass)

/-- The displacement of a nonroot vertex under a shift tuple. -/
def DualTest.shift {n : ℕ} {B : Block n} {ν : ℤ → ℝ}
  (D : DualTest B ν) (p : D.PrimeTuple)
  (u : Fin D.dimension → Fin 2 → Fin (D.shiftLength p))
  (ω : Finset (Fin D.dimension)) : ℤ :=
  (D.modulus p : ℤ) *
    ∑ j ∈ ω, (((u j 1).val : ℤ) - ((u j 0).val : ℤ))

/-- Value of the dual test at the root, including the bounded prime factor and every nonroot
vertex. This is exactly the cube test displayed in (eq:prediction-dual-test). -/
noncomputable def DualTest.value {n : ℕ} {B : Block n} {ν : ℤ → ℝ}
    (D : DualTest B ν) (y : ℤ) : ℝ := by
  classical
  exact ∑ p, D.primeWeight p * D.primeFactor p *
    finiteAverage (fun u : Fin D.dimension → Fin 2 → Fin (D.shiftLength p) =>
      ∏ ω : Finset (Fin D.dimension),
        if hω : ω.Nonempty then
          D.input p ω hω (y + D.shift p u ω)
        else 1)

/-- Fixed weighted pairing against the pivot measure. -/
noncomputable def dualPairing {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) (f : ℤ → ℝ) (D : DualTest B (divisorWeight A N B)) : ℝ :=
  ∫ y, f y * D.value y ∂pivotLaw A N B.1

/-- Rooted cube expectation for the dual-test sampling law, with all vertices carrying the same
target function and no prime factor `e`; this is the quantity in (eq:prediction-subgroup-conclusion).
-/
noncomputable def DualTest.cubeAverage {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) (D : DualTest B (divisorWeight A N B)) (h : ℤ → ℝ) : ℝ := by
  classical
  exact ∑ p, D.primeWeight p * finiteAverage
    (fun u : Fin D.dimension → Fin 2 → Fin (D.shiftLength p) =>
      ∫ y, (∏ ω : Finset (Fin D.dimension), h (y + D.shift p u ω))
        ∂pivotLaw A N B.1)

/-- The moment appearing in (eq:prediction-dual-moments). -/
noncomputable def dualWeightedMoment {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) (D : DualTest B (divisorWeight A N B)) (b : ℕ) : ℝ :=
  ∫ y, (1 + divisorWeight A N B y) * |D.value y| ^ b ∂pivotLaw A N B.1

/-- Clipping a real test to `[-K,K]`. -/
def clipTest (K x : ℝ) : ℝ := max (-K) (min K x)

/-- The weighted `L^p` clipping error in the dual-test lemma. -/
noncomputable def dualClippingMoment {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) (D : DualTest B (divisorWeight A N B)) (K : ℝ) (p : ℕ) : ℝ :=
  ∫ y, (1 + divisorWeight A N B y) *
    |D.value y - clipTest K (D.value y)| ^ p ∂pivotLaw A N B.1

end HindmanSumsProducts.Prediction
