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
    (hcompat : QuotientGroup.instTopologicalSpace Γ =
      (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace)
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
  classical
  letI : TopologicalSpace (LipOne Y) := ⊥
  letI : DiscreteTopology (LipOne Y) := ⟨rfl⟩
  let obsFam (x : G ⧸ Γ) : LipOne Y →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfDiscrete
      (fun H => O.desc H.1 x) 2 (by
        intro H H'
        rw [Real.dist_eq]
        have hH := O.unit_bound H.1 H.2.1 x
        have hH' := O.unit_bound H'.1 H'.2.1 x
        calc
          |O.desc H.1 x - O.desc H'.1 x| ≤
              |O.desc H.1 x| + |O.desc H'.1 x| := by
                calc
                  |O.desc H.1 x - O.desc H'.1 x| =
                      |O.desc H.1 x + -(O.desc H'.1 x)| := by congr 1 <;> ring
                  _ ≤ |O.desc H.1 x| + |-(O.desc H'.1 x)| := abs_add_le _ _
                  _ = |O.desc H.1 x| + |O.desc H'.1 x| := by simp
          _ ≤ 2 := by linarith)
  have hobs_cont : Continuous obsFam := by
    rw [Metric.continuous_iff']
    intro x ε hε
    obtain ⟨U, hU, hclose⟩ := heq x (ε / 2) (by linarith)
    filter_upwards [hU] with y hy
    have hdist : dist (obsFam y) (obsFam x) ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (C := ε / 2) (by linarith)).2 ?_
      intro H
      change dist (O.desc H.1 y) (O.desc H.1 x) ≤ ε / 2
      rw [Real.dist_eq]
      exact (hclose y hy H).le
    linarith
  let Φ : (G ⧸ Γ) → (G ⧸ Γ) × (LipOne Y →ᵇ ℝ) := fun x => (x, obsFam x)
  have hΦemb : Topology.IsEmbedding Φ := by
    simpa [Φ] using isEmbedding_graph (f := obsFam) hobs_cont
  let baseMetric : MetricSpace (G ⧸ Γ) := inferInstance
  let prodMetric : MetricSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ)) := inferInstance
  let dRaw : MetricSpace (G ⧸ Γ) :=
    MetricSpace.induced Φ hΦemb.injective prodMetric
  have hprodTopo :
      (inferInstance : TopologicalSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ))) =
        prodMetric.toUniformSpace.toTopologicalSpace := by
    rw [hcompat]
    with_reducible_and_instances rfl
  have htopRaw : QuotientGroup.instTopologicalSpace Γ =
      dRaw.toUniformSpace.toTopologicalSpace := by
    -- The first coordinate of `Φ` recovers the original topology, and
    -- `hcompat` identifies that topology with the supplied metric topology.
    calc
      QuotientGroup.instTopologicalSpace Γ =
          (inferInstance : TopologicalSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ))).induced Φ :=
        hΦemb.eq_induced
      _ = prodMetric.toUniformSpace.toTopologicalSpace.induced Φ := by rw [hprodTopo]
      _ = dRaw.toUniformSpace.toTopologicalSpace := rfl
  refine ⟨dRaw, htopRaw, ?_⟩
  intro H hH K₁ hK₁
  letI := dRaw
  letI : Dist (G ⧸ Γ) := dRaw.toPseudoMetricSpace.toDist
  let C : ℝ≥0 := max 1 K₁
  have hCpos : 0 < (C : ℝ) := by
    have : (1 : ℝ≥0) ≤ C := le_max_left _ _
    exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
  let H' : LipOne Y := ⟨fun y => H y / (C : ℝ), by
    constructor
    · intro y
      rw [abs_div, abs_of_pos hCpos]
      rw [div_le_iff₀ hCpos]
      have hCy : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast (le_max_left 1 K₁)
      nlinarith [hH y]
    · apply LipschitzWith.of_dist_le_mul
      intro y z
      rw [Real.dist_eq, show H y / (C : ℝ) - H z / (C : ℝ) =
        (H y - H z) / (C : ℝ) by ring, abs_div, abs_of_pos hCpos]
      rw [div_le_iff₀ hCpos]
      have hdist := hK₁.dist_le_mul y z
      rw [Real.dist_eq] at hdist
      have hKC : (K₁ : ℝ) ≤ (C : ℝ) := by exact_mod_cast (le_max_right 1 K₁)
      calc
        |H y - H z| ≤ (K₁ : ℝ) * dist y z := hdist
        _ ≤ (C : ℝ) * dist y z := mul_le_mul_of_nonneg_right hKC dist_nonneg
        _ = 1 * dist y z * (C : ℝ) := by ring⟩
  have hscale (x : G ⧸ Γ) : O.desc H x = (C : ℝ) * O.desc H'.1 x := by
    have hfun : (fun y => (C : ℝ) * H'.1 y) = H := by
      funext y
      dsimp [H']
      field_simp [ne_of_gt hCpos]
    rw [← hfun]
    exact O.scale (C : ℝ) H'.1 x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, hscale x, hscale y, ← mul_sub, abs_mul]
  have hobs : |O.desc H'.1 x - O.desc H'.1 y| ≤
      @dist _ (dRaw.toPseudoMetricSpace.toDist) x y := by
    letI : MetricSpace (G ⧸ Γ) := baseMetric
    letI : Dist (G ⧸ Γ) := baseMetric.toPseudoMetricSpace.toDist
    letI : PseudoMetricSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ)) :=
      prodMetric.toPseudoMetricSpace
    letI : Dist ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ)) :=
      prodMetric.toPseudoMetricSpace.toDist
    calc
      |O.desc H'.1 x - O.desc H'.1 y| =
          dist (obsFam x H') (obsFam y H') := rfl
      _ ≤ dist (obsFam x) (obsFam y) := BoundedContinuousFunction.dist_coe_le_dist H'
      _ ≤ dist (Φ x) (Φ y) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      _ = @dist _ (dRaw.toPseudoMetricSpace.toDist) x y := by
        change @dist _ (prodMetric.toPseudoMetricSpace.toDist) (Φ x) (Φ y) =
          @dist _ (prodMetric.toPseudoMetricSpace.toDist) (Φ x) (Φ y)
        rfl
  have hCnonneg : 0 ≤ (C : ℝ) := by positivity
  rw [abs_of_nonneg hCnonneg]
  change (C : ℝ) * |O.desc H'.1 x - O.desc H'.1 y| ≤
    (C : ℝ) * dist x y
  exact mul_le_mul_of_nonneg_left hobs hCnonneg

end HindmanSumsProducts.InverseBridge
