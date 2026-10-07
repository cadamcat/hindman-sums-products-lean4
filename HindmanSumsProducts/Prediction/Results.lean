import HindmanSumsProducts.Prediction.Outside
import HindmanSumsProducts.CubeCornerCharted

/-!
# Dual-test pseudorandomness, bounded dense models, nilsequence testing (§5.1–§5.2)

`05_prediction.tex` 63–353.  Throughout, `MS : MasterScales K As sl Dm` are §3's master scales and
`A = MS.core.parameters`.  "`o(1)` uniformly over the inputs" is `∀ ε > 0, ∀ᶠ N in atTop, ∀ inputs`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace HindmanSumsProducts.Prediction

noncomputable section

variable {K sl r : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

/-! ### Lemma `lem:dual-pseudorandomness` (05:68–190) -/

/-- `A_* = 2^{2^{d_*} − 1}` (05:76). -/
def dualMomentConstant (dStar : ℕ) : ℝ := (2 : ℝ) ^ (2 ^ dStar - 1)

/-- Integer direction coefficients (05:92–101): for a nonempty `ω ⊆ [d]` there are integers
`a_0, …, a_d` with `a_0 ≠ 0`, `a_0 + ∑_{j∈ω} a_j = 0` and `a_0 + ∑_{j∈ω'} a_j ≠ 0` for `ω' ≠ ω`. -/
theorem direction_integers (d : ℕ) (ω : Finset (Fin d)) (hω : ω.Nonempty) :
    ∃ a : Fin (d + 1) → ℤ, a 0 ≠ 0 ∧ a 0 + ∑ j ∈ ω, a j.succ = 0 ∧
      ∀ ω' : Finset (Fin d), ω' ≠ ω → a 0 + ∑ j ∈ ω', a j.succ ≠ 0 := by
  sorry

/-- (eq:prediction-dual-products), 05:68–74 and 129–164: for every fixed `b` and fixed tests at
the same block (possibly different valid gaps, allowed types and `J₀`),
`E_{μ_i}(ν − 1) ∏_{k<b} 𝒟_k = o(1)` uniformly over their inputs. -/
theorem dual_products_orthogonal (MS : MasterScales K As sl Dm) (B : Block K) (b : ℕ)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y)| ≤ ε := by
  sorry

/-- (eq:prediction-dual-moments), 05:74–79 and 166–175: for every fixed `b ≥ 1` and a type of
dimension `≤ d_*`, `E_{μ_i}(1 + ν)|𝒟|^b ≤ 2 A_*^b + o(1)` uniformly over the inputs. -/
theorem dual_moment_bound (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) (hgap : ValidGap B l) (hT : Allowed Dm T) (hJ0 : 0 < J0)
    (dStar : ℕ) (hd : T.d ≤ dStar) (b : ℕ) (hb : 0 < b) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
      Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
        |dualTest MS B T l J0 N I y| ^ b) ≤ 2 * dualMomentConstant dStar ^ b + ε := by
  sorry

/-- Clipping, 05:80–82 and 177–184: for fixed `K > A_*` and fixed `p ≥ 1`,
`E_{μ_i}(1 + ν)|𝒟 − 𝒟^{[K]}|^p = o(1)` uniformly over the inputs. -/
theorem dual_clipping_error (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) (hgap : ValidGap B l) (hT : Allowed Dm T) (hJ0 : 0 < J0)
    (dStar : ℕ) (hd : T.d ≤ dStar) (Kc : ℝ) (hK : dualMomentConstant dStar < Kc)
    (p : ℕ) (hp : 0 < p) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
      Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
        |dualTest MS B T l J0 N I y - clip Kc (dualTest MS B T l J0 N I y)| ^ p) ≤ ε := by
  sorry

/-- 05:80–82 and 184–189: (eq:prediction-dual-products) remains true for clipped tests, for a
common clipping bound `K > A_*`. -/
theorem dual_products_orthogonal_clipped (MS : MasterScales K As sl Dm) (B : Block K) (b : ℕ)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (dStar : ℕ) (hd : ∀ k, (T k).d ≤ dStar) (Kc : ℝ) (hK : dualMomentConstant dStar < Kc) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, clip Kc (dualTest MS B (T k) (gap k) (J0 k) N (I k) y))| ≤ ε := by
  sorry

/-- Lemma `lem:dual-pseudorandomness` (05:68–83), assembled from its three parts. -/
theorem dual_pseudorandomness (MS : MasterScales K As sl Dm) (B : Block K) (dStar : ℕ) :
    (∀ (b : ℕ) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ),
      (∀ k, ValidGap B (gap k)) → (∀ k, Allowed Dm (T k)) → (∀ k, 0 < J0 k) →
      ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
        |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
          ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y)| ≤ ε) ∧
    (∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ), ValidGap B l → Allowed Dm T → 0 < J0 →
      T.d ≤ dStar → ∀ b : ℕ, 0 < b →
      ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          |dualTest MS B T l J0 N I y| ^ b) ≤ 2 * dualMomentConstant dStar ^ b + ε) ∧
    (∀ Kc : ℝ, dualMomentConstant dStar < Kc →
      (∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ), ValidGap B l → Allowed Dm T → 0 < J0 →
        T.d ≤ dStar → ∀ p : ℕ, 0 < p →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
          Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
            |dualTest MS B T l J0 N I y - clip Kc (dualTest MS B T l J0 N I y)| ^ p) ≤ ε) ∧
      (∀ (b : ℕ) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ),
        (∀ k, ValidGap B (gap k)) → (∀ k, Allowed Dm (T k)) → (∀ k, 0 < J0 k) →
        (∀ k, (T k).d ≤ dStar) →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
          |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (T k) (gap k) (J0 k) N (I k) y))| ≤ ε)) := by
  refine ⟨fun b gap T J0 hgap hT hJ0 => dual_products_orthogonal MS B b gap T J0 hgap hT hJ0,
    fun l T J0 hgap hT hJ0 hd b hb => dual_moment_bound MS B l T J0 hgap hT hJ0 dStar hd b hb,
    fun Kc hK => ⟨fun l T J0 hgap hT hJ0 hd p hp =>
      dual_clipping_error MS B l T J0 hgap hT hJ0 dStar hd Kc hK p hp,
      fun b gap T J0 hgap hT hJ0 hd =>
        dual_products_orthogonal_clipped MS B b gap T J0 hgap hT hJ0 dStar hd Kc hK⟩⟩

/-! ### Proposition `prop:dense-model` (05:199–248) -/

/-- The bounded dense-model property (eq:prediction-dense-approximation): `F` is `[0,1]`-valued
and, for every master block, scale label `a ∈ 𝒜`, colour, valid gap, allowed cube type (any
dimension) and fixed `J₀`, `E_{μ_i}(ρ − F)𝒟 = o(1)` uniformly over the inputs of `𝒟`. -/
def IsDenseModel (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) (F : BlockFamily K r) : Prop :=
  UnitValued F ∧
    ∀ (B : Block K), ∀ a ∈ As, ∀ c : Fin r, ∀ l : Fin K, ValidGap B l →
      ∀ T : CubeTemplate, Allowed Dm T → ∀ J0 : ℕ, 0 < J0 →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
          |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              dualTest MS B T l J0 N I y)| ≤ ε

/-- Finite-dimensional minimax (05:213–226), existence form: on a finite support with weights
`μ ≥ 0`, if `0 ≤ ρ ≤ ν` and `𝒞` is compact convex nonempty, some `F ∈ [0,1]^X` satisfies
`⟨ρ − F, G⟩_μ ≤ sup_{G' ∈ 𝒞} ⟨ν − 1, G'_+⟩_μ` for every `G ∈ 𝒞`. -/
theorem dense_model_minimax {X : Type} [Fintype X] (μ ρ ν : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ ν x) (C : Set (X → ℝ)) (hC : Convex ℝ C) (hCc : IsCompact C)
    (hne : C.Nonempty) :
    ∃ F : X → ℝ, (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ G ∈ C,
      ∑ x, μ x * (ρ x - F x) * G x ≤
        sSup ((fun G' : X → ℝ => ∑ x, μ x * (ν x - 1) * max (G' x) 0) '' C) := by
  sorry

/-- The stage-`Q` test class at a block: valid gap, allowed type of dimension `≤ Q`,
`0 < J₀ ≤ Q`. -/
def StageTest (Dm : Finset (IntegerPolynomial sl)) (B : Block K) (Q : ℕ) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) : Prop :=
  ValidGap B l ∧ Allowed Dm T ∧ T.d ≤ Q ∧ 0 < J0 ∧ J0 ≤ Q

/-- The signed clipped tests of stage `Q` at index `N` (05:213–215). -/
def stageClippedTests (MS : MasterScales K As sl Dm) (B : Block K) (Q : ℕ) (Kc : ℝ) (N : ℕ) :
    Set (ℤ → ℝ) :=
  {G | ∃ (l : Fin K) (T : CubeTemplate) (J0 : ℕ) (I : DualInput MS B T N),
    StageTest Dm B Q l T J0 ∧
      (G = (fun y => clip Kc (dualTest MS B T l J0 N I y)) ∨
        G = (fun y => -clip Kc (dualTest MS B T l J0 N I y)))}

/-- Positive-part bound (05:228–235): for fixed stage `Q`, `K > A_*` (with `d_* = Q`) and
`δ > 0`, `E_{μ_i}(ν − 1) G_+ ≤ 2δ + o(1)` uniformly over the closed convex hull of the signed
clipped stage tests. -/
theorem dense_model_positive_part (MS : MasterScales K As sl Dm) (B : Block K) (Q : ℕ)
    (Kc : ℝ) (hK : dualMomentConstant Q < Kc) (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ G ∈ closure (convexHull ℝ (stageClippedTests MS B Q Kc N)),
      Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) * max (G y) 0) ≤
        2 * δ + ε := by
  sorry

/-- One stage of Proposition `prop:dense-model` (05:209–240): for a fixed stage `Q` there are
`[0,1]`-valued models with error at most `1/(Q+1)` against every stage test, for all large `N`,
uniformly over the finitely many master blocks, scale labels, colours and inputs. -/
theorem dense_model_stage (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) (Q : ℕ) :
    ∃ F : BlockFamily K r, UnitValued F ∧ ∀ᶠ N in atTop,
      ∀ (B : Block K), ∀ a ∈ As, ∀ c : Fin r, ∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ),
        StageTest Dm B Q l T J0 → ∀ I : DualInput MS B T N,
          |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              dualTest MS B T l J0 N I y)| ≤ 1 / ((Q : ℝ) + 1) := by
  sorry

/-- Proposition `prop:dense-model` (05:199–207): bounded dense models exist.  Proof: the stages
`dense_model_stage Q`, diagonalized with `Q = Q(N)` increasing slowly (05:240–247). -/
theorem bounded_dense_models (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) :
    ∃ F : BlockFamily K r, IsDenseModel MS χ F := by
  sorry

/-! ### Lemma `lem:nilsequence-testing` (05:275–353) -/

/-- `y` lies within `width` of an endpoint of its `R`-interval `[kR, (k+1)R)`. -/
def InBoundaryStrip (R width : ℕ) (y : ℤ) : Prop :=
  y % (R : ℤ) ≤ (width : ℤ) ∨ (R : ℤ) ≤ y % (R : ℤ) + (width : ℤ)

/-- Indicator of `InBoundaryStrip`. -/
def boundaryIndicator (R width : ℕ) (y : ℤ) : ℝ := by
  classical
  exact if InBoundaryStrip R width y then 1 else 0

/-- Recipes realized as dual tests (05:287–323): for a fixed menu of step `≤ s`, Lipschitz bound
and accuracy `δ`, there are finitely many scalars `λ_t` (independent of `J₀`, `N` and the
family) such that, for every fixed `J₀` and all large `N`, every representing family at gap `l`
is reconstructed within `δ`, at every root farther than `(s+1)R_l/J₀` from the ends of its
`R_l`-interval, by `∑_t λ_t 𝒟_t` with dual tests of the extra type (dimension `s+1`, modulus `M`),
`e = 1` and inputs bounded by `1`.  Rests on `Charted.cube_corner_recipes`. -/
theorem nilsequence_recipe_tests (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hl : ValidGap B l) {s : ℕ} (Fm : Menu s) (Km : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n₀ : ℕ) (coeff : Fin n₀ → ℝ), ∀ J0 : ℕ, 0 < J0 → ∀ᶠ N in atTop,
      ∀ Φ : RepFamily MS.core.parameters l Fm Km,
        ∃ I : Fin n₀ → DualInput MS B (extraTemplate s) N,
          (∀ t p, (I t).e p = 1) ∧ (∀ t ω p y, |(I t).g ω p y| ≤ 1) ∧
          ∀ y : ℤ,
            ¬ InBoundaryStrip (MS.core.parameters.H N l)
              ((s + 1) * MS.core.parameters.H N l / J0) y →
            |Φ.eval N y - ∑ t, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y| ≤ δ := by
  sorry

/-- (eq:prediction-weighted-boundary), 05:325–342: the boundary strips of relative length
`(s+1)/J₀` carry `(1 + ν_B)μ_i`-mass `O_s(J₀^{-1}) + o(1)`.  The constant depends on `s` only. -/
theorem weighted_boundary (s : ℕ) :
    ∃ C : ℝ, ∀ {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
      (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K), ValidGap B l →
      ∀ J0 : ℕ, 0 < J0 → ∀ ε > 0, ∀ᶠ N in atTop,
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          boundaryIndicator (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J0) y) ≤ C / J0 + ε := by
  sorry

/-- Lemma `lem:nilsequence-testing` (eq:prediction-nilsequence-testing), 05:275–285, 344–353:
for a dense model `F`, a block `B`, a valid gap `l`, and a fixed menu of step `≤ s` with a fixed
Lipschitz bound, `E_{μ_i}(ρ − F) S' = o(1)` uniformly over the representing families `S'` at gap
`l` (bounded real families follow by affine combination with the constant family).  `1 ∈ Dm`
makes the extra type `extraTemplate s` allowed, so that `IsDenseModel` covers it. -/
theorem nilsequence_testing (MS : MasterScales K As sl Dm) (h1 : (1 : IntegerPolynomial sl) ∈ Dm)
    (χ : ℕ → Fin r) (F : BlockFamily K r) (hF : IsDenseModel MS χ F) (B : Block K) (a : ℚ) (ha : a ∈ As) (c : Fin r) (l : Fin K)
    (hl : ValidGap B l) {s : ℕ} (Fm : Menu s) (Km : ℝ≥0) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ Φ : RepFamily MS.core.parameters l Fm Km,
      |Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * Φ.eval N y)| ≤ ε := by
  sorry

end

end HindmanSumsProducts.Prediction
