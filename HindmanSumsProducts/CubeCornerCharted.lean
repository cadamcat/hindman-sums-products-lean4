import HindmanSumsProducts.CubeCorner

/-!
# Missing-corner reconstruction for charted menus

The same statement as `HindmanSumsProducts.cube_corner_recipes`, for OpenAI's charted menus
`OAI.SourceChartedMenu.Menu` (a Mal'cev chart and any metric compatible with the quotient
topology), which is the menu type the Prediction half produces and OpenAI's charted Alignment
theorem consumes. Paper Lemma `lem:cube-corner` (`07_cube_limits.tex` 117–208), used at
`05_prediction.tex` 288–301.
-/

namespace HindmanSumsProducts.Charted

open OAI OAI.SourceChartedMenu
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

/-- Paper Lemma `lem:cube-corner` (07:117–138) for charted menus, in the form used by Lemma
`lem:nilsequence-testing` (05:288–301). -/
theorem cube_corner_recipes (B : ℝ) (K : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : Fin F.size → ℕ) (R : ∀ i, Fin (m i) → CornerRecipe F i),
      ∀ i (obs : (F.G i ⧸ F.Γ i) →ᵇ ℝ), ‖obs‖ ≤ B →
        (letI := menuMetric F i; LipschitzWith K obs) →
        ∃ ρ, ∀ (g : F.G i) (x : F.G i ⧸ F.Γ i) (k : ℤ) (v : Fin (s+1) → ℤ),
          |obs (g ^ k • x) - (R i ρ).eval F (fun ω => g ^ (k + ∑ j ∈ ω, v j) • x)| ≤ ε := by
  sorry

end HindmanSumsProducts.Charted
