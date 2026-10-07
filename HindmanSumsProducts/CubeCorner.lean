import OAI.Combinatorics.SumProduct.Alignment.RawMenu

/-!
# Missing-corner reconstruction (paper Lemma `lem:cube-corner`), in the form used by §5

Paper: `07_cube_limits.tex` lines 117–208 (statement 117–138, proof 140–168); use site
`05_prediction.tex` lines 288–301 (Lemma `lem:nilsequence-testing`).

On each nilmanifold of a finite menu, the value of a bounded Lipschitz observable at the root
`x_∅ = g^k x` of a linear orbit cube `x_ω = g^(k + ∑_{j∈ω} v j) x` (`ω ⊆ Fin (s+1)`) is
approximated within `ε` by a finite "recipe" `∑_t λ_t ∏_{ω ≠ ∅} φ_{t,ω}(x_ω)` in the other
vertices, with `|φ| ≤ 1` Lipschitz. Finitely many recipes serve all observables with given sup
and Lipschitz bounds, uniformly in `g`, `x`, `k`, `v`.
-/

namespace HindmanSumsProducts

open OAI OAI.SourceRawMenu
open scoped NNReal BoundedContinuousFunction

variable {s : ℕ} (F : Menu s)

/-- The menu metric with its topology made definitionally the quotient topology. -/
abbrev menuMetric (i : Fin F.size) : MetricSpace (F.G i ⧸ F.Γ i) :=
  (F.metric i).replaceTopology (F.compatible i)

/-- One missing-corner recipe on menu entry `i`. -/
structure CornerRecipe (i : Fin F.size) where
  terms : ℕ
  coeff : Fin terms → ℝ
  factor : Fin terms → Finset (Fin (s+1)) → (F.G i ⧸ F.Γ i) →ᵇ ℝ
  bound : ∀ t ω y, |factor t ω y| ≤ 1
  lip : ∃ L : ℝ≥0, ∀ t ω, letI := menuMetric F i; LipschitzWith L (factor t ω)

/-- Evaluation of a recipe on the non-root vertices of a cube `x`. -/
def CornerRecipe.eval {i : Fin F.size} (R : CornerRecipe F i)
    (x : Finset (Fin (s+1)) → F.G i ⧸ F.Γ i) : ℝ :=
  ∑ t, R.coeff t * ∏ ω ∈ (Finset.univ.erase ∅), R.factor t ω (x ω)

/-- Paper Lemma `lem:cube-corner` (07:117–138), in the form used by Lemma
`lem:nilsequence-testing` (05:288–301). -/
theorem cube_corner_recipes (B : ℝ) (K : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : Fin F.size → ℕ) (R : ∀ i, Fin (m i) → CornerRecipe F i),
      ∀ i (obs : (F.G i ⧸ F.Γ i) →ᵇ ℝ), ‖obs‖ ≤ B →
        (letI := menuMetric F i; LipschitzWith K obs) →
        ∃ ρ, ∀ (g : F.G i) (x : F.G i ⧸ F.Γ i) (k : ℤ) (v : Fin (s+1) → ℤ),
          |obs (g ^ k • x) - (R i ρ).eval F (fun ω => g ^ (k + ∑ j ∈ ω, v j) • x)| ≤ ε := by
  sorry

end HindmanSumsProducts
