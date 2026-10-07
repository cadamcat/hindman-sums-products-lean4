import HindmanSumsProducts.Arithmetic.Sampling

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section

/-- Tail-product law induced by independent harmonic raw variables at the OAI cutoffs. -/
def parameterTailProductLaw {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n)) (σ : ℕ) : ℝ :=
  ∑' t : Fin n → ℕ,
    (if (∏ j ∈ T, t j) = σ then 1 else 0) *
      ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)

/-- The actual block-product mass obtained by pushing forward OpenAI's `Parameters.law`. -/
def parameterBlockProductMass {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : ℤ) : ℝ :=
  if 0 ≤ z then
    (A.law N hX).real {t : Fin n → ℕ | (∏ j ∈ B.set, t j : ℕ) = z.toNat}
  else 0

/-- The weighted pivot law `ν_B μ_i`, with `ν_B` defined locally in `Defs.lean`. -/
def weightedPivotMass {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : OAI.SourceBlocks.Block n) (z : ℤ) : ℝ :=
  nuB (parameterTailProductLaw A N B.2.val) z *
    harmonicLaw (A.X N B.1) (primorial (N + 1)) z

/-- Joint block-product mass under the OAI law, for a fixed family of blocks. -/
def parameterJointBlockProductMass {n r : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : Fin r → OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : Fin r → ℤ) : ℝ :=
  (A.law N hX).real {t : Fin n → ℕ |
    ∀ d, 0 ≤ z d ∧ (∏ j ∈ (B d).set, t j) = (z d).toNat}

/-- Product of the individual weighted pivot masses for a fixed block family. -/
def weightedPivotTupleMass {n r : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : Fin r → OAI.SourceBlocks.Block n)
    (z : Fin r → ℤ) : ℝ := ∏ d, weightedPivotMass A N (B d) (z d)

/-- The block product law, including its joint version for fixed pairwise disjoint blocks.
This is Corollary `cor:product-law` (§3 lines 152–166). -/
theorem cor_product_law {n r : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (hX : ∀ N j, 4 * primorial (N + 1) ≤ A.X N j)
    (V : ℕ → ℕ) (hV : ∀ N, 1 ≤ V N)
    (hDom : ∀ d, OAI.MicrocellScale.Dominates
      (fun N => Real.log (A.X N (B d).1 : ℝ))
      (fun N => 2 + primorial (N + 1) +
        (∏ j ∈ (B d).2.val, (A.X N j)^2) + V N)) :
    SuperPolynomialSmall
      (fun N => arithmeticL1
        (parameterJointBlockProductMass A N B (hX N))
        (weightedPivotTupleMass A N B))
      (fun N => (V N : ℝ)) := by
  sorry

/-- Conditioning on `t_T=σ` expresses the block-product law as the mixture of the pivot
dilation laws (§3 lines 168–172). -/
theorem block_product_mass_conditioning_formula {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) :
    ∀ z : ℤ, parameterBlockProductMass A N B hX z =
      ∑' σ : ℕ, parameterTailProductLaw A N B.2.val σ *
        dilatedLaw (harmonicLaw (A.X N B.1) (primorial (N + 1))) σ z := by
  sorry

/-- Averaging the unnormalized dilation reference measures gives the divisor-weighted pivot
law `ν_B μ_i` exactly (§3 lines 172–182). -/
theorem block_product_weight_average_is_nu {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n) (z : ℤ) :
    (∑' σ : ℕ, parameterTailProductLaw A N B.2.val σ *
      dilationReference (harmonicLaw (A.X N B.1) (primorial (N + 1))) σ z) =
      weightedPivotMass A N B z := by
  classical
  unfold weightedPivotMass nuB dilationReference
  rw [← tsum_mul_right]
  apply tsum_congr
  intro σ
  by_cases hdiv : (σ : ℤ) ∣ z <;> simp [hdiv] <;> ring

end
end HindmanSumsProducts
