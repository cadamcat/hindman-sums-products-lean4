import HindmanSumsProducts.Prediction.Imported

open scoped BigOperators
open scoped NNReal
open MeasureTheory Filter
open Classical

namespace HindmanSumsProducts.Prediction

/-- Real-valued nilsequence correlator used for the inverse theorem. OAI's `CosetPiece` is
`[0,1]`-valued; this local variant is `[-1,1]`-valued, matching the GTZ correlator before the
paper takes real parts and clips it to produce an OAI model. -/
structure RealCosetPiece {s : ℕ} (F : Menu s) (K : ℝ≥0) where
  index : Fin F.size
  g : F.G index
  x : F.G index ⧸ F.Γ index
  obs : (F.G index ⧸ F.Γ index) → ℝ
  lip : letI : MetricSpace (F.G index ⧸ F.Γ index) :=
    (F.metric index).replaceTopology (F.compatible index)
    LipschitzWith K obs
  bound : ∀ z, |obs z| ≤ 1

def RealCosetPiece.eval {s : ℕ} {F : Menu s} {K : ℝ≥0}
    (P : RealCosetPiece F K) (k : ℤ) : ℝ := P.obs (P.g ^ k • P.x)

/-- A finite parameterization of all integer cubes whose vertices lie in `[0,L)`. The
increment range `[-L,L]` contains every possible edge of such a cube. -/
def signedIncrement (L : ℕ) (a : Fin (2 * L + 1)) : ℤ :=
  (a.val : ℤ) - (L : ℤ)

def intervalVertex {t L : ℕ} (x : Fin (L + 1))
    (a : Fin t → Fin (2 * L + 1)) (ω : Finset (Fin t)) : ℤ :=
  (x.val : ℤ) + ∑ j ∈ ω, signedIncrement L (a j)

def intervalCubeValid {t L : ℕ} (x : Fin (L + 1))
    (a : Fin t → Fin (2 * L + 1)) : Prop :=
  ∀ ω : Finset (Fin t), 0 ≤ intervalVertex x a ω ∧ intervalVertex x a ω < L

noncomputable def intervalCubeDomain (t L : ℕ) : Finset (Fin (L + 1) × (Fin t → Fin (2 * L + 1))) :=
  Finset.univ.filter fun z => intervalCubeValid z.1 z.2

/-- Normalized all-vertices-in-interval cube mean; its `2^t`-th power is the interval `U^t`
quantity in the Green–Tao–Ziegler inverse theorem. -/
noncomputable def intervalCubeMean (t L : ℕ) (f : ℤ → ℝ) : ℝ :=
  let D := intervalCubeDomain t L
  (D.card : ℝ)⁻¹ * ∑ z ∈ D,
    ∏ ω : Finset (Fin t), f (intervalVertex z.1 z.2 ω)

/-- Normalized correlation over the fixed representatives `[0,L)`. -/
noncomputable def intervalCorrelation {s : ℕ} {F : Menu s} {K : ℝ≥0}
    (L : ℕ) (f : ℤ → ℝ) (P : RealCosetPiece F K) : ℝ :=
  (L : ℝ)⁻¹ * ∑ x : Fin L, f (x.val : ℤ) * P.eval (x.val : ℤ)

/-- Green–Tao–Ziegler inverse theorem, Theorem 1.3 with the lower-order cases and Erratum,
in precisely the finite-list linear-nilsequence form used in §5, lines 472–489 and 631–674.
The menu depends only on `(t,δ)`; no bound on the translating element `g` is imposed. -/
theorem green_tao_ziegler_inverse_interval
    (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (F : Menu (t - 1)) (K : ℝ≥0) (c : ℝ), 0 < c ∧
      ∀ L : ℕ, 0 < L → ∀ f : ℤ → ℝ,
        (∀ x, |f x| ≤ 1) →
        δ ^ (2 ^ t) ≤ intervalCubeMean t L f →
        ∃ P : RealCosetPiece F K,
          c ≤ |intervalCorrelation L f P| := by
  sorry

/-- Reusable coordinate-product recipe with a fixed total coefficient bound. -/
structure CubeCornerRecipe {s : ℕ} (F : Menu s) where
  terms : ℕ
  coefficient : Fin terms → ℝ
  factor : ∀ (t : Fin terms) (i : Fin F.size),
    (ω : Finset (Fin (s + 1))) → ω.Nonempty →
      (F.G i ⧸ F.Γ i) → ℝ
  factor_bound : ∀ t i ω hω x, |factor t i ω hω x| ≤ 1
  coefficientL1 : ℝ
  coefficientL1_nonneg : 0 ≤ coefficientL1
  coefficientL1_bound : ∑ t, |coefficient t| ≤ coefficientL1

/-- Uniform finite-menu clause of `lem:cube-corner` (lines 130–137): fixed nilmanifold menu
and observable/Lipschitz bounds admit recipes with a common total coefficient bound. -/
theorem cube_corner_finite_menu_recipe {s : ℕ} (F : Menu s) (K : ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : CubeCornerRecipe F, ∀ P : CosetPiece F K,
      ∀ (k : ℤ) (v : Fin (s + 1) → ℤ),
        |P.obs (P.g ^ k • P.x) -
          ∑ t, R.coefficient t * ∏ ω : Finset (Fin (s + 1)),
            if hω : ω.Nonempty then
              R.factor t P.index ω hω
                (P.g ^ (k + ∑ j ∈ ω, v j) • P.x)
            else 1| ≤ δ := by
  sorry

/-- Finite-family form of Tao–Ziegler's concatenation / qualitative Bessel inequality
(`TaoZiegler`, Theorem 1.23), specialized to finite subgroups as used in (eq:prediction-bessel),
§5, lines 450–470. The fields `highNorm` and `lowNorm` are respectively the actual subgroup
`U^(2k-1)` and `U^k` norms of one `1`-bounded function on one probability system. -/
structure FiniteBesselSystem (k : ℕ) where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  weight : Index → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_one : ∑ i, weight i = 1
  highNorm : Index → Index → ℝ
  lowNorm : Index → ℝ
  highNorm_nonneg : ∀ i j, 0 ≤ highNorm i j
  lowNorm_nonneg : ∀ i, 0 ≤ lowNorm i
  functionBounded : Prop
  subgroupNormInterpretation : Prop

attribute [instance] FiniteBesselSystem.indexFintype
  FiniteBesselSystem.indexDecidableEq

def FiniteBesselSystem.highMean {k : ℕ} (S : FiniteBesselSystem k) : ℝ :=
  ∑ i, ∑ j, S.weight i * S.weight j * S.highNorm i j

def FiniteBesselSystem.lowMean {k : ℕ} (S : FiniteBesselSystem k) : ℝ :=
  ∑ i, S.weight i * S.lowNorm i

/-- Tao–Ziegler concatenation modulus `b_k(δ)→0` as `δ↓0`, independent of the finite family,
the group, and the probability system. -/
theorem tao_ziegler_concatenation_bessel (k : ℕ) :
    ∃ b : ℝ → ℝ, Monotone b ∧ (∀ δ ≥ 0, 0 ≤ b δ) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ x, 0 ≤ x → x < δ → b x < ε) ∧
      ∀ (S : FiniteBesselSystem k) (δ : ℝ),
        S.functionBounded → S.subgroupNormInterpretation →
        S.highMean ≤ δ → S.lowMean ≤ b δ := by
  sorry

end HindmanSumsProducts.Prediction
