import HindmanSumsProducts.InverseBridge.Linear

/-!
The compactly supported interpolation observable and its menu metric (IB.a9--a10).
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3
open Filter
open scoped BigOperators BoundedContinuousFunction NNReal Topology

/-- A triangular bump supported in the interval `(-1/3, 1/3)`. -/
noncomputable def bump (x : ℝ) : ℝ := max 0 (1 - 3 * |x|)

theorem bump_nonneg (x : ℝ) : 0 ≤ bump x := le_max_left _ _

theorem bump_le_one (x : ℝ) : bump x ≤ 1 := by
  unfold bump
  exact max_le (by norm_num) (by nlinarith [abs_nonneg x])

/-- Interpolate a function on a quotient along the integer translation coordinate. -/
noncomputable def liftObs {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (x : X) : ℝ :=
  ∑ᶠ m : ℤ, bump (r x - m) * H (point x m)

/-- At an integral translation coordinate only the matching translate contributes. -/
theorem liftObs_at_integer {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (x : X) (n : ℤ) (hr : r x = n)
    (hzero : ∀ m : ℤ, m ≠ n → bump (r x - m) = 0) :
    liftObs r point H x = H (point x n) := by
  unfold liftObs
  calc
    (∑ᶠ m : ℤ, bump (r x - m) * H (point x m)) =
        bump (r x - n) * H (point x n) :=
      finsum_eq_single _ n (by
        intro m hm
        rw [hzero m hm]
        simp)
    _ = H (point x n) := by simp [hr, bump]

/-- An observable lift together with the lattice invariance needed to descend it. -/
structure ObservableDescent (G : Type*) [Group G] (Γ : Subgroup G) (Y : Type*) where
  lift : (Y → ℝ) → G → ℝ
  desc : (Y → ℝ) → G ⧸ Γ → ℝ
  desc_mk : ∀ H g, desc H (QuotientGroup.mk g) = lift H g
  invariant : ∀ H g γ, γ ∈ Γ → lift H (g * γ) = lift H g
  scale : ∀ (c : ℝ) H x, desc (fun y => c * H y) x = c * desc H x
  unit_bound : ∀ H, (∀ y, |H y| ≤ 1) → ∀ x, |desc H x| ≤ 1

/-- The normalized, one-Lipschitz observables used to define the custom metric. -/
def LipOne (Y : Type*) [MetricSpace Y] :=
  {H : Y → ℝ // (∀ y, |H y| ≤ 1) ∧ LipschitzWith 1 H}

/-- The compactness/equicontinuity construction equips the quotient with a
compatible metric for which every descended Lipschitz observable has a uniform
Lipschitz constant.  This is IB.a10. -/
theorem exists_observable_menuMetric {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Γ : Subgroup G} [MetricSpace (G ⧸ Γ)]
    [CompactSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)] {Y : Type*} [MetricSpace Y]
    (O : ObservableDescent G Γ Y)
    (heq : ∀ x ε, 0 < ε →
      ∃ U : Set (G ⧸ Γ), U ∈ 𝓝 x ∧
        ∀ y ∈ U, ∀ H : LipOne Y,
          |O.desc H.1 y - O.desc H.1 x| < ε) :
    ∃ d : MetricSpace (G ⧸ Γ),
      QuotientGroup.instTopologicalSpace Γ = d.toUniformSpace.toTopologicalSpace ∧
      ∀ (H : Y → ℝ), (∀ y, |H y| ≤ 1) → ∀ (K₁ : ℝ≥0),
        LipschitzWith K₁ H →
          letI := d
          LipschitzWith (max 1 K₁) (O.desc H) := by
  /-
  The hypotheses do not require the supplied metric on `G ⧸ Γ` to induce
  `QuotientGroup.instTopologicalSpace Γ`.  The requested conclusion implies
  that this topology is metrizable, which fails for compact nonmetrizable
  quotient groups (for example an uncountable product of two-element groups)
  with the trivial observable descent.  The missing compatibility hypothesis
  is `QuotientGroup.instTopologicalSpace Γ =
    (inferInstance : PseudoMetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace`.
  -/
  sorry

end HindmanSumsProducts.InverseBridge
