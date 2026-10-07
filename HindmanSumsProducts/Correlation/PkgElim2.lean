import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for weighted additive elimination (04:418–572). -/

namespace HindmanSumsProducts
open FromArithmetic
open Filter
open scoped Topology

theorem c_elim2_weighted_variance_identity (b h c : ℝ) :
    b * h ^ 2 - (2 * c) * (b * h) + c ^ 2 * b = b * (h - c) ^ 2 := by
  ring

theorem c_elim2_weighted_variance_tendsto {B c : ℝ} (b h : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 B))
    (hbh : Tendsto (fun n => b n * h n) atTop (𝓝 (B * c)))
    (hbh2 : Tendsto (fun n => b n * h n ^ 2) atTop (𝓝 (B * c ^ 2))) :
    Tendsto (fun n => b n * (h n - c) ^ 2) atTop (𝓝 0) := by
  have hlinear : Tendsto
      (fun n => b n * h n ^ 2 - (2 * c) * (b n * h n) + c ^ 2 * b n)
      atTop (𝓝 (B * c ^ 2 - (2 * c) * (B * c) + c ^ 2 * B)) := by
    exact (hbh2.sub (hbh.const_mul (2 * c))).add (hb.const_mul (c ^ 2))
  have hzero : B * c ^ 2 - (2 * c) * (B * c) + c ^ 2 * B = 0 := by ring
  have heq : (fun n => b n * (h n - c) ^ 2) =ᶠ[atTop]
      fun n => b n * h n ^ 2 - (2 * c) * (b n * h n) + c ^ 2 * b n := by
    filter_upwards [] with n
    exact (c_elim2_weighted_variance_identity (b n) (h n) c).symm
  rw [hzero] at hlinear
  exact (tendsto_congr' heq).2 hlinear

/-- The pointwise target-cube product is bounded by its product of divisor weights. -/
theorem c_elim2_target_cube_product_abs_le_targetBound
    {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (p : Fin q → ℕ) (z : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ)
    (g : ℤ → ℝ)
    (hg : ∀ y, |g y| ≤ 1 + chainWeight S.core.parameters C N
      (Sh.row Sh.star).anchor y) :
    |∏ ω : NonTarget Sh → Fin 2,
        atQ g (targetVertex (chainScale S.core.parameters C a N) Sh p
          (directionModulus S N dirs.poly p) z u ω)| ≤
      targetBound S C a N dirs p z u := by
  classical
  have hfactor (ω : NonTarget Sh → Fin 2) :
      |atQ g (targetVertex (chainScale S.core.parameters C a N) Sh p
        (directionModulus S N dirs.poly p) z u ω)| ≤
      1 + atQ (chainWeight S.core.parameters C N (Sh.row Sh.star).anchor)
        (targetVertex (chainScale S.core.parameters C a N) Sh p
          (directionModulus S N dirs.poly p) z u ω) := by
    let x := targetVertex (chainScale S.core.parameters C a N) Sh p
      (directionModulus S N dirs.poly p) z u ω
    by_cases hx : x.den = 1
    · simpa [atQ, x, hx] using hg x.num
    · simp [atQ, x, hx]
  rw [Finset.abs_prod]
  unfold targetBound
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    (fun ω _ => hfactor ω)

end HindmanSumsProducts
