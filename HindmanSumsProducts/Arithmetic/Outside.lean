import HindmanSumsProducts.Arithmetic.Defs

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts.Arithmetic.Outside
noncomputable section

/-- Prime number theorem in dyadic intervals, in the exact harmonic form used for
the maximum atom and positive pool mass in `lem:master-scales` and
`lem:rough-coprimality` (§3 lines 284–294, 373–377). -/
theorem dyadic_harmonic_prime_mass_and_atom_bound :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ Y : ℕ in atTop,
      c / Real.log Y ≤ primePoolMass Y (2 * Y) ∧
      primePoolMass Y (2 * Y) ≤ C / Real.log Y ∧
      ∀ p, Y ≤ p → p < 2 * Y → p.Prime →
        primePoolLaw Y (2 * Y) p ≤ C * Real.log Y / Y := by
  sorry

/-- Selberg's prime number theorem in arithmetic progressions, equation (1.1),
followed by partial summation: the harmonic prime law on `[Y,2Y)` approaches
uniform measure on unit classes modulo every fixed Q. Used in `lem:master-scales`
(§3 lines 283–294). -/
theorem harmonic_prime_residue_equidistribution (Q : ℕ) (hQ : 0 < Q) :
    Tendsto (fun Y : ℕ => finiteL1
      (primePoolResidueLaw Y (2 * Y) Q)
      (uniformUnitResidueLaw Q)) atTop (𝓝 0) := by
  sorry

/-- Interval Brun–Titchmarsh bound for the harmonic prime law on `[Y,2Y)`.
For a prime p with p²≤Y, every nonzero residue class has probability O(1/p).
This is Theorem 2 of Yamada, used in `lem:rough-coprimality` (§3 lines 379–389). -/
theorem harmonic_prime_brun_titchmarsh :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℕ in atTop,
      ∀ p, p.Prime → p ^ 2 ≤ Y → ∀ a : Fin p, 0 < a.val →
        (∑ q ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
          if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) ≤ C / p := by
  sorry

/-- Divergence of the reciprocal-prime series, used to make the union of complete
dyadic intervals in each pool have arbitrary prescribed harmonic mass
(`lem:master-scales`, §3 line 291). -/
theorem reciprocalPrimeSeries_tendsto_atTop :
    Tendsto (fun Y : ℕ => ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, 1 / (p : ℝ))
      atTop atTop := by
  sorry

end
end HindmanSumsProducts.Arithmetic.Outside
