import HindmanSumsProducts.Arithmetic.MasterScales

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section

/-- Smallest lower endpoint in one finite tuple of dyadic prime intervals. -/
noncomputable def smallestPrimeEndpoint {k : ℕ} (Y : Fin k → ℕ) : ℕ :=
  if h : (Finset.univ.image Y).Nonempty then (Finset.univ.image Y).min' h else 1

/-- Finite set of all dyadic lower endpoints in two independent prime tuples. -/
def roughEndpointSet {kF kG : ℕ} (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) : Finset ℕ :=
  Finset.univ.image YF ∪ Finset.univ.image YG

/-- The smallest lower endpoint in two independent prime tuples (1 if both are constant). -/
noncomputable def roughSmallestEndpoint {kF kG : ℕ}
    (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) : ℕ :=
  if h : (roughEndpointSet YF YG).Nonempty then
    (roughEndpointSet YF YG).min' h
  else 1

/-- Probability of a polynomial zero under independent harmonic prime samples in dyadic
intervals; this is the first estimate in `lem:rough-coprimality`. -/
theorem polynomial_zero_dyadic_prime_bound {k : ℕ}
    (F : IntegerPolynomial k) (hF : F ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : Fin k → ℕ, (∀ i, 2 ≤ Y i) →
      independentPrimePoolProbability Y (fun i => 2 * Y i)
        (fun p => evalIntegerPolynomial F (fun i => (p i : ℤ)) = 0) ≤
        C * Real.log (smallestPrimeEndpoint Y : ℝ) /
          smallestPrimeEndpoint Y := by
  sorry

/-- Small common rough prime divisors, `w<p≤√L`, are controlled by two independent
root-class tests and contribute `O(1/w)` (§3 lines 391–411). -/
theorem rough_coprimality_small_prime_divisors {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (w L : ℕ),
      (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) → w < L →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun i => (y i : ℤ)) ≠ 0 ∧
          ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧
            (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial G (fun i => (y i : ℤ))) ≤ C / w := by
  sorry

/-- Large common rough prime divisors, `p>√L`, contribute `O(log L/√L)` by testing
the finitely many large prime factors of the polynomial with the smaller main endpoint
(§3 lines 413–432). -/
theorem rough_coprimality_large_prime_divisors {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (L : ℕ),
      (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun i => (y i : ℤ)) ≠ 0 ∧
          ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
            (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial G (fun i => (y i : ℤ))) ≤
        C * Real.log L / Real.sqrt L := by
  sorry

/-- Lemma `lem:rough-coprimality`: for fixed nonzero integer polynomials in disjoint
independent prime tuples sampled harmonically from dyadic intervals, the polynomial-zero
probability is `O(log L/L)` and the probability of a common rough prime factor is
`O(1/w+log L/√L)`, uniformly in endpoint ratios (§3 lines 353–370). -/
theorem lem_rough_coprimality {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ N₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (w : ℕ),
      N₀ ≤ w → N₀ ≤ roughSmallestEndpoint YF YG →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y => evalIntegerPolynomial F (fun i => (x i : ℤ)) = 0 ∨
          evalIntegerPolynomial G (fun i => (y i : ℤ)) = 0) ≤
          C * Real.log (roughSmallestEndpoint YF YG) /
            roughSmallestEndpoint YF YG ∧
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun i => (y i : ℤ)) ≠ 0 ∧
          Nat.gcd
            (roughPart w (evalIntegerPolynomial F (fun i => (x i : ℤ))))
            (roughPart w (evalIntegerPolynomial G (fun i => (y i : ℤ)))) > 1) ≤
          C * (1 / w + Real.log (roughSmallestEndpoint YF YG) /
            Real.sqrt (roughSmallestEndpoint YF YG)) := by
  sorry

/-- Restricting independent tuples to prime-only events of probability tending to one
preserves the rough-coprimality conclusion; this is the constructed-pool consequence at
§3 lines 434–438. -/
theorem rough_coprimality_survives_high_probability_restrictions
    {kF kG : ℕ} (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0)
    (poolF : ℕ → Fin kF → PrimePool) (poolG : ℕ → Fin kG → PrimePool)
    (EF : ℕ → (Fin kF → ℕ) → Prop) (EG : ℕ → (Fin kG → ℕ) → Prop)
    (hEF : Tendsto (fun N : ℕ => independentPrimePoolProbability
      (fun i => (poolF N i).lower) (fun i => (poolF N i).upper) (EF N))
      atTop (𝓝 1))
    (hEG : Tendsto (fun N : ℕ => independentPrimePoolProbability
      (fun i => (poolG N i).lower) (fun i => (poolG N i).upper) (EG N))
      atTop (𝓝 1))
    (hloF : ∀ i, Tendsto (fun N : ℕ => (poolF N i).lower) atTop atTop)
    (hloG : ∀ i, Tendsto (fun N : ℕ => (poolG N i).lower) atTop atTop) :
    Tendsto (fun N : ℕ => independentPrimePairProbability
      (fun i => (poolF N i).lower) (fun i => (poolF N i).upper)
      (fun i => (poolG N i).lower) (fun i => (poolG N i).upper)
      (fun x y => EF N x ∧ EG N y ∧
        Nat.gcd (roughPart (N + 1) (evalIntegerPolynomial F (fun i => (x i : ℤ))))
          (roughPart (N + 1) (evalIntegerPolynomial G (fun i => (y i : ℤ)))) = 1))
      atTop (𝓝 1) := by
  sorry

end
end HindmanSumsProducts
