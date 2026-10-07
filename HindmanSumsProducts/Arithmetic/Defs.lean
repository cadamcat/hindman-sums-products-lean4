import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.Admissible01
import OAI.Combinatorics.SumProduct.Alignment.Blocks01
import OAI.Combinatorics.SumProduct.Alignment.RawMenu
import OAI.Combinatorics.SumProduct.Alignment.WordPlan01
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays14
import OAI.Combinatorics.SumProduct.Alignment.ConstantCoefficient01
import OAI.Combinatorics.SumProduct.Alignment.MicrocellScale01
import OAI.Combinatorics.SumProduct.Alignment.RawHarmonic01

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Total-mass (ℓ¹) distance used for the arithmetic sampling laws. -/
def arithmeticL1 {α : Type*} (μ ν : α → ℝ) : ℝ := ∑' x, |μ x - ν x|

/-- Super-polynomial smallness: the stated error is `o(V^{-C})` for every fixed positive C. -/
def SuperPolynomialSmall (e V : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → Tendsto (fun n => e n * V n ^ C) atTop (𝓝 0)

/-- Harmonic normalization on the W-units in `[X,X²)`. -/
def harmonicNormalizer (X W : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W), 1 / (n : ℝ)

/-- The harmonic W-unit probability mass, extended by zero to signed integers. -/
def harmonicLaw (X W : ℕ) (z : ℤ) : ℝ :=
  if 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W then
    1 / ((z.toNat : ℝ) * harmonicNormalizer X W)
  else 0

/-- Translation of a signed-integer law by an integer. -/
def translatedLaw {α : Type*} [AddGroup α] (μ : α → ℝ) (h : α) (z : α) : ℝ := μ (z - h)

/-- Pushforward of a signed-integer law by multiplication by `k`, for `0 < k` (the only case used;
at `k = 0` the formula is not the pushforward). -/
def dilatedLaw (μ : ℤ → ℝ) (k : ℕ) (z : ℤ) : ℝ :=
  if z % (k : ℤ) = 0 then μ (z / (k : ℤ)) else 0

/-- Unnormalized comparison measure `k 1_{k|n} μ(n)` from the sampling lemma. -/
def dilationReference (μ : ℤ → ℝ) (k : ℕ) (z : ℤ) : ℝ :=
  if (k : ℤ) ∣ z then (k : ℝ) * μ z else 0

/-- Residue law modulo k for a law supported on nonnegative integers. -/
def harmonicResidueLaw (μ : ℤ → ℝ) (k : ℕ) (a : Fin k) : ℝ :=
  ∑' z : ℤ, if 0 ≤ z ∧ z.toNat % k = a.val then μ z else 0

/-- Uniform law on all k residue classes. -/
def uniformResidueLaw (k : ℕ) (_a : Fin k) : ℝ := 1 / (k : ℝ)

/-- Harmonic mass of primes in a finite interval. -/
def primePoolMass (lo hi : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime, 1 / (p : ℝ)

/-- Probability law proportional to `1/p` on primes in `[lo,hi)`. -/
def primePoolLaw (lo hi p : ℕ) : ℝ :=
  if lo ≤ p ∧ p < hi ∧ p.Prime then (1 / (p : ℝ)) / primePoolMass lo hi else 0

/-- Residue law of the harmonic prime pool, represented by `Fin Q`. -/
def primePoolResidueLaw (lo hi Q : ℕ) (a : Fin Q) : ℝ :=
  (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
    if p % Q = a.val then 1 / (p : ℝ) else 0) / primePoolMass lo hi

/-- Uniform law on the unit residue classes modulo Q. -/
def uniformUnitResidueLaw (Q : ℕ) (a : Fin Q) : ℝ :=
  if Nat.Coprime a.val Q then 1 / (Nat.totient Q : ℝ) else 0

/-- Total-mass distance for laws on a finite type. -/
def finiteL1 {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  ∑ x, |μ x - ν x|

/-- A dyadic pool is a finite union of consecutive complete intervals `[2^j,2^(j+1))`. -/
structure PrimePool where
  lower : ℕ
  upper : ℕ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  lower_pow_two : ∃ k, lower = 2 ^ k
  upper_pow_two : ∃ k, upper = 2 ^ k
  consecutive_complete_intervals : ∃ k, upper = lower * 2 ^ k

/-- Independent harmonic prime slots from the indicated pools. -/
def independentPrimePoolMass {m : ℕ} (lo hi : Fin m → ℕ) (p : Fin m → ℕ) : ℝ :=
  ∏ i, primePoolLaw (lo i) (hi i) (p i)

/-- Probability of an event under independent harmonic prime slots. -/
def independentPrimePoolProbability {m : ℕ} (lo hi : Fin m → ℕ)
    (E : (Fin m → ℕ) → Prop) : ℝ :=
  ∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p * if E p then 1 else 0

/-- Probability of an event on two independent prime tuples from disjoint slot sets. -/
def independentPrimePairProbability {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) : ℝ :=
  ∑' x : Fin kF → ℕ,
    independentPrimePoolMass loF hiF x *
      (∑' y : Fin kG → ℕ,
        independentPrimePoolMass loG hiG y * if E x y then 1 else 0)

/-- Integer polynomial in a fixed finite set of prime-parameter slots. -/
abbrev IntegerPolynomial (m : ℕ) := MvPolynomial (Fin m) ℤ

/-- A polynomial together with the number of prime slots on which it depends. -/
abbrev PolynomialTemplate := Σ m : ℕ, IntegerPolynomial m

/-- Evaluation of an integer polynomial at integer slots. -/
def evalIntegerPolynomial {m : ℕ} (P : IntegerPolynomial m) (x : Fin m → ℤ) : ℤ :=
  MvPolynomial.eval x P

/-- Probability mass of a uniform unit tuple modulo Q. -/
def uniformUnitTupleMass (Q m : ℕ) (x : Fin m → Fin Q) : ℝ :=
  if ∀ i, Nat.Coprime (x i).val Q then 1 / (Nat.totient Q : ℝ) ^ m else 0

/-- Probability of a predicate for independent uniform unit residues modulo Q. -/
def uniformUnitTupleProbability (Q m : ℕ) (E : (Fin m → Fin Q) → Prop) : ℝ :=
  ∑ x, uniformUnitTupleMass Q m x * if E x then 1 else 0

/-- Local representation of a tail-product divisor draw by its probability mass. -/
abbrev TailProductLaw := ℕ → ℝ

-- to be unified with Framework
/-- The divisor weight `ν_B(y)=E[σ 1_{σ|y}]` associated with a tail-product law. -/
def nuB (tailLaw : TailProductLaw) (y : ℤ) : ℝ :=
  ∑' σ : ℕ, tailLaw σ * (σ : ℝ) * if (σ : ℤ) ∣ y then 1 else 0

/-- Harmonic W-unit law on positive integers, before embedding into `ℤ`. -/
def harmonicNatLaw (X W n : ℕ) : ℝ :=
  if X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W then
    1 / ((n : ℝ) * harmonicNormalizer X W)
  else 0

/-- Law of a product of independent raw harmonic variables at their specified cutoffs. -/
def harmonicProductLaw {k : ℕ} (W : ℕ) (X : Fin k → ℕ) (σ : ℕ) : ℝ :=
  ∑' t : Fin k → ℕ,
    (if (∏ i, t i) = σ then 1 else 0) * ∏ i, harmonicNatLaw (X i) W (t i)

/-- The rough part `|a|_{>w}` as defined in §3 for nonzero integers; the formula gives `1` at `a = 0`. -/
def roughPart (w : ℕ) (a : ℤ) : ℕ :=
  ∏ p ∈ (Finset.range (a.natAbs + 1)).filter (fun p => p.Prime ∧ w < p),
    p ^ (Nat.factorization a.natAbs p)

/-- A master chain in the convention used by the correlation consumer: all tails lie before
one gap and are ordered there, while the block pivots lie after the gap and are ordered. -/
structure MasterChain (n r : ℕ) where
  gap : Fin n
  block : Fin r → OAI.SourceBlocks.Block n
  tails_before_gap : ∀ d j, j ∈ (block d).2.val → j < gap
  tails_ordered : ∀ u d, u < d → ∀ a ∈ (block u).2.val, ∀ b ∈ (block d).2.val, a < b
  pivots_after_gap : ∀ d, gap < (block d).1
  pivots_ordered : ∀ u d, u < d → (block u).1 < (block d).1

end
end HindmanSumsProducts
