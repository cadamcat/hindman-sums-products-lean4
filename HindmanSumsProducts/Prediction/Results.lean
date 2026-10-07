import HindmanSumsProducts.Prediction.Outside
import HindmanSumsProducts.CubeCornerCharted
import HindmanSumsProducts.Prediction.PkgB
import HindmanSumsProducts.Prediction.PkgC
import HindmanSumsProducts.Prediction.PkgD

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
  classical
  obtain ⟨m, Recipes, hRecipes⟩ :=
    HindmanSumsProducts.Charted.cube_corner_recipes Fm (1 : ℝ) Km δ hδ
  have hobsBound (P : CosetPiece Fm Km) : ‖P.obs‖ ≤ 1 := by
    rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro z
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(P.range z).1], (P.range z).2⟩
  have hselectExists (P : CosetPiece Fm Km) :
      ∃ ρ : Fin (m P.index), ∀ (g : Fm.G P.index)
        (x : Fm.G P.index ⧸ Fm.Γ P.index) (k : ℤ) (v : Fin (s + 1) → ℤ),
          |P.obs (g ^ k • x) - (Recipes P.index ρ).eval Fm
            (fun ω => g ^ (k + ∑ j ∈ ω, v j) • x)| ≤ δ := by
    exact hRecipes P.index P.obs (hobsBound P) P.lip
  let selected (P : CosetPiece Fm Km) : Fin (m P.index) :=
    Classical.choose (hselectExists P)
  have hselected (P : CosetPiece Fm Km) := Classical.choose_spec (hselectExists P)
  let nTerms : ℕ := ∑ i : Fin Fm.size, ∑ j : Fin (m i), (Recipes i j).terms
  let RecipeIndex : Type :=
    Σ i : Fin Fm.size, Σ j : Fin (m i), Fin nTerms
  let n₀ : ℕ := Fintype.card RecipeIndex
  let enum : Fin n₀ ≃ RecipeIndex := (Fintype.equivFin RecipeIndex).symm
  let coeffMass (i : Fin Fm.size) (n : ℕ) : ℝ :=
    ∑ j : Fin (m i),
      if h : n < (Recipes i j).terms then
        |(Recipes i j).coeff ⟨n, h⟩|
      else 0
  let coeffQ (q : RecipeIndex) : ℝ :=
    if h : q.2.2.val < (Recipes q.1 q.2.1).terms then
      |(Recipes q.1 q.2.1).coeff ⟨q.2.2.val, h⟩|
    else 0
  let coeff : Fin n₀ → ℝ := fun t => coeffQ (enum t)
  refine ⟨n₀, coeff, ?_⟩
  intro J0 hJ0
  let A := MS.core.parameters
  let p0 : Fin (extraTemplate s).q → ℕ := extraTemplateEmptyTuple s
  have hmodulus (N : ℕ) : (extraTemplate s).modulus (corrScales MS) N p0 = A.M N := by
    have heval : evalIntegerPolynomial (extraTemplate s).D (fun i => (p0 i : ℤ)) = 1 := by
      change (MvPolynomial.eval (fun i => (p0 i : ℤ))) (extraTemplate s).D = 1
      rw [show (extraTemplate s).D = 1 by rfl]
      exact map_one _
    change A.M N * roughPart (N + 1)
      (evalIntegerPolynomial (extraTemplate s).D (fun i => (p0 i : ℤ))) = A.M N
    rw [heval]
    simp [roughPart]
  have hlengthEventually : ∀ᶠ N in atTop,
      0 < (extraTemplate s).length (corrScales MS) l J0 N p0 := by
    have hscale := gapScale_multiple_le_eventually A l J0
    filter_upwards [hscale] with N hscale
    have hden : 0 < J0 * A.M N := Nat.mul_pos hJ0 (A.Mpos N)
    have hdiv : 0 < A.H N l / (J0 * A.M N) := Nat.div_pos hscale hden
    have hlength : (extraTemplate s).length (corrScales MS) l J0 N p0 =
        A.H N l / (J0 * A.M N) := by
      change A.H N l / (J0 * (extraTemplate s).modulus (corrScales MS) N p0) = _
      rw [hmodulus N]
    rw [hlength]
    exact hdiv
  filter_upwards [hlengthEventually] with N hlength
  intro Φ
  let Pof (z : ℤ) : CosetPiece Fm Km :=
    Φ.piece N (z / (A.H N l : ℤ)) (z % (A.M N : ℤ))
  let root0 : Fin (s + 1) := ⟨0, by omega⟩
  let rootFace : Finset (Fin (s + 1)) := {root0}
  have hrootFace : rootFace ∈
      (Finset.univ : Finset (Finset (Fin (s + 1)))).erase ∅ := by
    simp [rootFace, root0]
  have hcoeffMassNonneg (i : Fin Fm.size) (n : ℕ) : 0 ≤ coeffMass i n := by
    dsimp [coeffMass]
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  have hcoeffLeMass (P : CosetPiece Fm Km) (n : ℕ)
      (hn : n < (Recipes P.index (selected P)).terms) :
      |(Recipes P.index (selected P)).coeff ⟨n, hn⟩| ≤ coeffMass P.index n := by
    have hsum := Finset.single_le_sum
      (f := fun j : Fin (m P.index) =>
        if h : n < (Recipes P.index j).terms then
          |(Recipes P.index j).coeff ⟨n, h⟩| else 0)
      (fun j hj => by split_ifs <;> positivity)
      (Finset.mem_univ (selected P))
    simpa [coeffMass, hn] using hsum
  let scaleFor (P : CosetPiece Fm Km) (n : ℕ)
      (hn : n < (Recipes P.index (selected P)).terms) : ℝ :=
    if h : coeffMass P.index n = 0 then 0 else
      (Recipes P.index (selected P)).coeff ⟨n, hn⟩ / coeffMass P.index n
  have hscaleFor (P : CosetPiece Fm Km) (n : ℕ)
      (hn : n < (Recipes P.index (selected P)).terms) : |scaleFor P n hn| ≤ 1 := by
    by_cases hzero : coeffMass P.index n = 0
    · have hcoeffZero : (Recipes P.index (selected P)).coeff ⟨n, hn⟩ = 0 := by
        have hle := hcoeffLeMass P n hn
        have habs : |(Recipes P.index (selected P)).coeff ⟨n, hn⟩| = 0 := by
          apply le_antisymm
          · simpa [hzero] using hle
          · exact abs_nonneg _
        exact abs_eq_zero.mp habs
      simp [scaleFor, hzero, hcoeffZero]
    · have hpos : 0 < coeffMass P.index n := lt_of_le_of_ne
        (hcoeffMassNonneg P.index n) (Ne.symm hzero)
      have hscaleEq : scaleFor P n hn =
          (Recipes P.index (selected P)).coeff ⟨n, hn⟩ / coeffMass P.index n := by
        simp [scaleFor, hzero]
      rw [hscaleEq, abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).2 (hcoeffLeMass P n hn)
  let inputAt (q : RecipeIndex) (ω : Finset (Fin (s + 1)))
      (p : Fin 0 → ℕ) (z : ℤ) : ℝ := by
    classical
    let P := Pof z
    by_cases hi : q.1 = P.index
    · by_cases hn : q.2.2.val < (Recipes P.index (selected P)).terms
      · let t : Fin (Recipes P.index (selected P)).terms := ⟨q.2.2.val, hn⟩
        let f := (Recipes P.index (selected P)).factor t ω
          (P.g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • P.x)
        by_cases hω : ω = rootFace
        · exact f * scaleFor P q.2.2.val hn
        · exact f
      · exact 0
    · exact 0
  have hinputBound (q : RecipeIndex) (ω : Finset (Fin (s + 1)))
      (p : Fin 0 → ℕ) (z : ℤ) : |inputAt q ω p z| ≤ 1 := by
    classical
    unfold inputAt
    dsimp [extraTemplate] at *
    split_ifs with hindex hterm hface
    · rw [abs_mul]
      have hfac : |(Recipes (Pof z).index (selected (Pof z))).factor
          ⟨q.2.2.val, hterm⟩ ω
          ((Pof z).g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • (Pof z).x)| ≤ 1 :=
        (Recipes (Pof z).index (selected (Pof z))).bound ⟨q.2.2.val, hterm⟩ ω
          ((Pof z).g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • (Pof z).x)
      calc
        _ ≤ |(Recipes (Pof z).index (selected (Pof z))).factor
            ⟨q.2.2.val, hterm⟩ ω
            ((Pof z).g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • (Pof z).x)| :=
          mul_le_of_le_one_right (abs_nonneg _) (hscaleFor (Pof z) q.2.2.val hterm)
        _ ≤ 1 := hfac
    · simpa [extraTemplate] using
        (Recipes (Pof z).index (selected (Pof z))).bound
          ⟨q.2.2.val, hterm⟩ ω
          ((Pof z).g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • (Pof z).x)
    · simp
    · simp
  let I : Fin n₀ → DualInput MS B (extraTemplate s) N := fun t =>
    let q := enum t
    { e := fun _ => 1
      g := fun ω p z => by
        change Finset (Fin (s + 1)) at ω
        change Fin 0 → ℕ at p
        exact inputAt q ω p z
      e_bound := by intro p; norm_num
      g_bound := by
        intro ω p z
        change Finset (Fin (s + 1)) at ω
        change Fin 0 → ℕ at p
        have hν : 0 ≤ nu A N B z := nu_nonneg A N B
          (fun i => harmonicNormalizer_pos (A.X N i) (primorial (N + 1))
            (primorial_pos _) (MS.gapStage.valid_raw_cutoffs N i)) z
        exact (hinputBound q ω p z).trans (by linarith) }
  have hIone (t : Fin n₀) (p : Fin (extraTemplate s).q → ℕ) : (I t).e p = 1 := rfl
  have hIbound (t : Fin n₀) (ω : Finset (Fin (extraTemplate s).d))
      (p : Fin (extraTemplate s).q → ℕ) (z : ℤ) : |(I t).g ω p z| ≤ 1 := by
    change Finset (Fin (s + 1)) at ω
    change Fin 0 → ℕ at p
    exact hinputBound (enum t) ω p z
  let L := (extraTemplate s).length (corrScales MS) l J0 N p0
  let U : Finset (Fin (s + 1) → Fin 2 → ℕ) :=
    Fintype.piFinset (fun _ : Fin (s + 1) =>
      Fintype.piFinset (fun _ : Fin 2 => Finset.range L))
  have hUmem (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
      (j : Fin (s + 1)) (b : Fin 2) : u j b < L := by
    have hu' : u ∈ Fintype.piFinset (fun _ : Fin (s + 1) =>
        Fintype.piFinset (fun _ : Fin 2 => Finset.range L)) := by simpa [U] using hu
    have huOuter := Fintype.mem_piFinset.mp hu'
    have huInner := Fintype.mem_piFinset.mp (huOuter j)
    exact Finset.mem_range.mp (huInner b)
  have hRecipeApprox : ∀ y : ℤ,
      ¬ InBoundaryStrip (A.H N l) ((s + 1) * A.H N l / J0) y →
      |Φ.eval N y - ∑ t, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y| ≤ δ := by
    intro y hy
    let width : ℕ := (s + 1) * A.H N l / J0
    let P := Pof y
    let k : ℤ := (y - y % (A.M N : ℤ)) / (A.M N : ℤ)
    let R := Recipes P.index (selected P)
    have hmargin : (width : ℤ) < y % (A.H N l : ℤ) ∧
        y % (A.H N l : ℤ) + (width : ℤ) < (A.H N l : ℤ) := by
      have h := hy
      simp only [InBoundaryStrip, not_or, not_le] at h
      exact h
    have hLformula : L = A.H N l / (J0 * A.M N) := by
      dsimp [L]
      change A.H N l / (J0 * directionModulus (corrScales MS) N
        (extraTemplate s).D p0) = _
      have hdir : directionModulus (corrScales MS) N (extraTemplate s).D p0 = A.M N := by
        simpa [CubeTemplate.modulus] using hmodulus N
      rw [hdir]
    have hdivBound : J0 * A.M N * L ≤ A.H N l := by
      rw [hLformula]
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Nat.div_mul_le_self (A.H N l) (J0 * A.M N))
    have hRadius : (s + 1) * A.M N * L ≤ (s + 1) * A.H N l / J0 := by
      apply (Nat.le_div_iff_mul_le hJ0).2
      calc
        ((s + 1) * A.M N * L) * J0 = (s + 1) * (J0 * A.M N * L) := by ring
        _ ≤ (s + 1) * A.H N l := Nat.mul_le_mul_left (s + 1) hdivBound
    let v (u : Fin (s + 1) → Fin 2 → ℕ) : Fin (s + 1) → ℤ := fun j =>
      (u j 1 : ℤ) - u j 0
    have hshiftBound (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
        (ω : Finset (Fin (s + 1))) :
        |(A.M N : ℤ) * ∑ j ∈ ω, v u j| ≤ (width : ℤ) := by
      have hvUpper (j : Fin (s + 1)) : v u j ≤ (L : ℤ) := by
        have h0 := hUmem u hu j 0
        have h1 := hUmem u hu j 1
        dsimp [v]
        omega
      have hvLower (j : Fin (s + 1)) : -(L : ℤ) ≤ v u j := by
        have h0 := hUmem u hu j 0
        have h1 := hUmem u hu j 1
        dsimp [v]
        omega
      have hcard : ω.card ≤ s + 1 := by
        calc
          ω.card ≤ (Finset.univ : Finset (Fin (s + 1))).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = s + 1 := by simp
      have hcardZ : (ω.card : ℤ) ≤ (s + 1 : ℤ) := by exact_mod_cast hcard
      have hLnonneg : 0 ≤ (L : ℤ) := by positivity
      have hsumUpper : ∑ j ∈ ω, v u j ≤ (s + 1 : ℤ) * (L : ℤ) := by
        calc
          ∑ j ∈ ω, v u j ≤ ∑ j ∈ ω, (L : ℤ) :=
            Finset.sum_le_sum fun j hj => hvUpper j
          _ = (ω.card : ℤ) * (L : ℤ) := by simp
          _ ≤ (s + 1 : ℤ) * (L : ℤ) :=
            mul_le_mul_of_nonneg_right hcardZ hLnonneg
      have hsumLower : -(s + 1 : ℤ) * (L : ℤ) ≤ ∑ j ∈ ω, v u j := by
        have hlow : (∑ j ∈ ω, -(L : ℤ)) ≤ ∑ j ∈ ω, v u j :=
          Finset.sum_le_sum (s := ω) (fun j hj => hvLower j)
        have hconst : ∑ j ∈ ω, -(L : ℤ) = -((ω.card : ℤ) * (L : ℤ)) := by simp
        have hlow' : -((ω.card : ℤ) * (L : ℤ)) ≤ ∑ j ∈ ω, v u j := by
          simpa [hconst] using hlow
        have hcardMul := mul_le_mul_of_nonneg_right hcardZ hLnonneg
        exact (neg_le_neg hcardMul).trans hlow'
      have hRadiusZ : (A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ) ≤ (width : ℤ) := by
        have hNat' : A.M N * (s + 1) * L ≤ width := by
          calc
            A.M N * (s + 1) * L = (s + 1) * A.M N * L := by ring
            _ ≤ width := hRadius
        exact_mod_cast hNat'
      have hMnonneg : 0 ≤ (A.M N : ℤ) := by positivity
      have hmulLower : -((A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ)) ≤
          (A.M N : ℤ) * ∑ j ∈ ω, v u j := by
        calc
          -((A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ)) =
              (A.M N : ℤ) * (-( (s + 1 : ℤ) * (L : ℤ))) := by ring
          _ ≤ (A.M N : ℤ) * ∑ j ∈ ω, v u j :=
            mul_le_mul_of_nonneg_left hsumLower hMnonneg
      have hmulUpper : (A.M N : ℤ) * ∑ j ∈ ω, v u j ≤
          (A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ) := by
        calc
          (A.M N : ℤ) * ∑ j ∈ ω, v u j ≤
              (A.M N : ℤ) * ((s + 1 : ℤ) * (L : ℤ)) :=
            mul_le_mul_of_nonneg_left hsumUpper hMnonneg
          _ = (A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ) := by ring
      apply abs_le.mpr
      exact ⟨(neg_le_neg hRadiusZ).trans hmulLower, hmulUpper.trans hRadiusZ⟩
    have hPshift (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
        (ω : Finset (Fin (s + 1))) :
        Pof (y + (A.M N : ℤ) * ∑ j ∈ ω, v u j) = P := by
      have hquot := ediv_stable_of_interior (A.H N l) width (A.Hpos N l) y
        ((A.M N : ℤ) * ∑ j ∈ ω, v u j) (hshiftBound u hu ω) hmargin.1 hmargin.2
      have hres := residue_and_progression_shift (A.M N) (A.Mpos N) y
        (∑ j ∈ ω, v u j)
      dsimp [P, Pof]
      rw [hquot, hres.1]
    have hcoord (u : Fin (s + 1) → Fin 2 → ℕ) (ω : Finset (Fin (s + 1))) :
        ((y + (A.M N : ℤ) * ∑ j ∈ ω, v u j) -
          (y + (A.M N : ℤ) * ∑ j ∈ ω, v u j) % (A.M N : ℤ)) / (A.M N : ℤ) =
          k + ∑ j ∈ ω, v u j :=
      (residue_and_progression_shift (A.M N) (A.Mpos N) y
        (∑ j ∈ ω, v u j)).2
    let cube (u : Fin (s + 1) → Fin 2 → ℕ)
        (ω : Finset (Fin (s + 1))) : Fm.G P.index ⧸ Fm.Γ P.index :=
      P.g ^ (k + ∑ j ∈ ω, v u j) • P.x
    have hchart (u : Fin (s + 1) → Fin 2 → ℕ) :
        |R.eval Fm (cube u) - P.obs (P.g ^ k • P.x)| ≤ δ := by
      have h := hselected P P.g P.x k (v u)
      rw [abs_sub_comm] at h
      simpa only [R, cube, v] using h
    have hPhiRoot : Φ.eval N y = P.obs (P.g ^ k • P.x) := by
      simp [RepFamily.eval, OAI.SourceMenuLiteral.CosetPiece.eval, P, Pof, k, A]
    let faces : Finset (Finset (Fin (s + 1))) :=
      (Finset.univ : Finset (Finset (Fin (s + 1)))).erase ∅
    let shiftSum (u : Fin (s + 1) → Fin 2 → ℕ)
        (ω : Finset (Fin (s + 1))) : ℤ :=
      (∑ j ∈ ω, (u j 1 : ℤ)) - ∑ j ∈ ω, (u j 0 : ℤ)
    have hshiftSum (u : Fin (s + 1) → Fin 2 → ℕ) (ω : Finset (Fin (s + 1))) :
        shiftSum u ω = ∑ j ∈ ω, v u j := by
      dsimp [shiftSum, v]
      rw [← Finset.sum_sub_distrib]
    let zShift (u : Fin (s + 1) → Fin 2 → ℕ) (ω : Finset (Fin (s + 1))) : ℤ :=
      y + (A.M N : ℤ) * shiftSum u ω
    let shiftTerm (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ) : ℝ :=
      ∏ ω ∈ faces, (I (enum.symm q)).g ω p0
        (zShift u ω)
    have hmodEmpty :
        (extraTemplate s).modulus (corrScales MS) N (extraTemplateEmptyTuple s) = A.M N := by
      simpa [p0] using hmodulus N
    have hdual (q : RecipeIndex) :
      dualTest MS B (extraTemplate s) l J0 N (I (enum.symm q)) y =
          shiftAverage (Fin (s + 1)) L (shiftTerm q) := by
      rw [extraTemplate_dualTest_eq]
      rw [hmodEmpty]
      rw [show (extraTemplate s).length (corrScales MS) l J0 N
          (extraTemplateEmptyTuple s) = L by rfl]
      rw [(show (I (enum.symm q)).e (extraTemplateEmptyTuple s) = 1 by rfl), one_mul]
      change shiftAverage (Fin (s + 1)) L
          (fun u => ∏ ω ∈ faces,
            (I (enum.symm q)).g ω (extraTemplateEmptyTuple s)
              (y + (A.M N : ℤ) *
                ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))) =
        shiftAverage (Fin (s + 1)) L (shiftTerm q)
      congr 1
      funext u
      simp [shiftTerm, faces, shiftSum, zShift, p0, extraTemplateEmptyTuple,
        emptyNatTuple, Finset.sum_sub_distrib]
    have hreindex :
        (∑ t : Fin n₀, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y) =
          ∑ q : RecipeIndex, coeffQ q * dualTest MS B (extraTemplate s) l J0 N
            (I (enum.symm q)) y := by
      apply Fintype.sum_equiv enum
      intro t
      simp [coeff, coeffQ, I, enum.apply_symm_apply]
    have hsumAverage :
        (∑ q : RecipeIndex, coeffQ q * shiftAverage (Fin (s + 1)) L (shiftTerm q)) =
          shiftAverage (Fin (s + 1)) L
            (fun u => ∑ q : RecipeIndex, coeffQ q * shiftTerm q u) := by
      classical
      unfold shiftAverage
      let D : ℝ := ((L : ℝ) ^ (2 * Fintype.card (Fin (s + 1))))⁻¹
      calc
        _ = ∑ q : RecipeIndex, D *
              (coeffQ q * ∑ u ∈ U, shiftTerm q u) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = D * ∑ q : RecipeIndex, coeffQ q * ∑ u ∈ U, shiftTerm q u := by
          rw [← Finset.mul_sum]
        _ = D * ∑ u ∈ U, ∑ q : RecipeIndex, coeffQ q * shiftTerm q u := by
          congr 1
          change (∑ q ∈ (Finset.univ : Finset RecipeIndex),
              coeffQ q * ∑ u ∈ U, shiftTerm q u) =
            ∑ u ∈ U, ∑ q ∈ (Finset.univ : Finset RecipeIndex), coeffQ q * shiftTerm q u
          calc
            _ = ∑ q ∈ (Finset.univ : Finset RecipeIndex),
                  ∑ u ∈ U, coeffQ q * shiftTerm q u := by
                apply Finset.sum_congr rfl
                intro q hq
                rw [Finset.mul_sum]
            _ = _ := Finset.sum_comm
        _ = _ := by rfl
    have hPofShift (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
        (ω : Finset (Fin (s + 1))) : Pof (zShift u ω) = P := by
      have heq : zShift u ω = y + (A.M N : ℤ) * ∑ j ∈ ω, v u j := by
        simp [zShift, hshiftSum]
      rw [heq]
      exact hPshift u hu ω
    have hcoordShift (u : Fin (s + 1) → Fin 2 → ℕ)
        (ω : Finset (Fin (s + 1))) :
        (zShift u ω - zShift u ω % (A.M N : ℤ)) / (A.M N : ℤ) =
          k + shiftSum u ω := by
      have h := hcoord u ω
      simpa [zShift, hshiftSum] using h
    have hinputShift (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ)
        (hu : u ∈ U) (ω : Finset (Fin (s + 1))) :
        inputAt q ω p0 (zShift u ω) =
          if hi : q.1 = P.index then
            if hn : q.2.2.val < R.terms then
              if hω : ω = rootFace then
                R.factor ⟨q.2.2.val, hn⟩ ω (cube u ω) * scaleFor P q.2.2.val hn
              else R.factor ⟨q.2.2.val, hn⟩ ω (cube u ω)
            else 0
          else 0 := by
      dsimp [inputAt]
      rw [hPofShift u hu ω, hcoordShift u ω]
      simp [R, cube, hshiftSum u ω]
    have hIinput (q : RecipeIndex) (ω : Finset (Fin (s + 1))) (z : ℤ) :
        (I (enum.symm q)).g ω p0 z = inputAt q ω p0 z := by
      change inputAt (enum (enum.symm q)) ω p0 z = inputAt q ω p0 z
      rw [enum.apply_symm_apply]
    have hprodActive (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ)
        (hu : u ∈ U) (hi : q.1 = P.index)
        (hn : q.2.2.val < R.terms) :
        shiftTerm q u = scaleFor P q.2.2.val hn *
          ∏ ω ∈ faces, R.factor ⟨q.2.2.val, hn⟩ ω (cube u ω) := by
      let f : Finset (Fin (s + 1)) → ℝ := fun ω =>
        R.factor ⟨q.2.2.val, hn⟩ ω (cube u ω)
      let g : Finset (Fin (s + 1)) → ℝ := fun ω =>
        if ω = rootFace then f ω * scaleFor P q.2.2.val hn else f ω
      have hfactor (ω : Finset (Fin (s + 1))) (hω : ω ∈ faces) :
          inputAt q ω p0 (zShift u ω) = g ω := by
        have h := hinputShift q u hu ω
        simpa [hi, hn, R, cube, f, g] using h
      calc
        shiftTerm q u = ∏ ω ∈ faces, g ω := by
          dsimp [shiftTerm]
          apply Finset.prod_congr rfl
          intro ω hω
          rw [hIinput q ω (zShift u ω)]
          exact hfactor ω hω
        _ = scaleFor P q.2.2.val hn * ∏ ω ∈ faces, f ω := by
          calc
            ∏ ω ∈ faces, g ω =
                (∏ ω ∈ faces.erase rootFace, g ω) * g rootFace :=
              (Finset.prod_erase_mul faces g hrootFace).symm
            _ = (∏ ω ∈ faces.erase rootFace, f ω) *
                  (f rootFace * scaleFor P q.2.2.val hn) := by
              congr 1
              · apply Finset.prod_congr rfl
                intro ω hω
                have hne : ω ≠ rootFace := (Finset.mem_erase.mp hω).1
                simp [g, hne]
              all_goals simp [g]
            _ = scaleFor P q.2.2.val hn *
                  ((∏ ω ∈ faces.erase rootFace, f ω) * f rootFace) := by ring
            _ = scaleFor P q.2.2.val hn * ∏ ω ∈ faces, f ω := by
              rw [Finset.prod_erase_mul faces f hrootFace]
    have hprodZeroIndex (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ)
        (hu : u ∈ U) (hi : q.1 ≠ P.index) : shiftTerm q u = 0 := by
      have hz : inputAt q rootFace p0 (zShift u rootFace) = 0 := by
        have h := hinputShift q u hu rootFace
        simpa [hi] using h
      change (∏ ω ∈ faces, (I (enum.symm q)).g ω p0 (zShift u ω)) = 0
      apply Finset.prod_eq_zero hrootFace
      rw [hIinput q rootFace (zShift u rootFace)]
      exact hz
    have hprodZeroTerm (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ)
        (hu : u ∈ U) (hi : q.1 = P.index)
        (hn : ¬ q.2.2.val < R.terms) : shiftTerm q u = 0 := by
      have hz : inputAt q rootFace p0 (zShift u rootFace) = 0 := by
        have h := hinputShift q u hu rootFace
        simpa [hi, hn, R] using h
      change (∏ ω ∈ faces, (I (enum.symm q)).g ω p0 (zShift u ω)) = 0
      apply Finset.prod_eq_zero hrootFace
      rw [hIinput q rootFace (zShift u rootFace)]
      exact hz
    have htermSummand (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
        (i : Fin Fm.size) (j : Fin (m i)) (n : Fin nTerms) :
        coeffQ ⟨i, ⟨j, n⟩⟩ * shiftTerm ⟨i, ⟨j, n⟩⟩ u =
          if hi : i = P.index then
            if hn : n.val < R.terms then
              coeffQ ⟨i, ⟨j, n⟩⟩ *
                (scaleFor P n.val hn *
                  ∏ ω ∈ faces, R.factor ⟨n.val, hn⟩ ω (cube u ω))
            else 0
          else 0 := by
      by_cases hi : i = P.index
      · subst i
        by_cases hn : n.val < R.terms
        · have h := hprodActive ⟨P.index, ⟨j, n⟩⟩ u hu rfl hn
          simp [h, hn]
        · have h := hprodZeroTerm ⟨P.index, ⟨j, n⟩⟩ u hu rfl hn
          simp [h, hn]
      · have h := hprodZeroIndex ⟨i, ⟨j, n⟩⟩ u hu hi
        simp [h, hi]
    have hinner (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U) :
        (∑ q : RecipeIndex, coeffQ q * shiftTerm q u) = R.eval Fm (cube u) := by
      classical
      change (∑ q : (Σ i : Fin Fm.size, Σ j : Fin (m i), Fin nTerms),
        coeffQ q * shiftTerm q u) = R.eval Fm (cube u)
      simp only [Fintype.sum_sigma]
      change (∑ i : Fin Fm.size, ∑ j : Fin (m i), ∑ n : Fin nTerms,
        coeffQ ⟨i, ⟨j, n⟩⟩ * shiftTerm ⟨i, ⟨j, n⟩⟩ u) = R.eval Fm (cube u)
      simp_rw [htermSummand u hu]
      simp [Finset.sum_ite_eq']
      have hmassSum (n : Fin nTerms) :
          (∑ j : Fin (m P.index), coeffQ ⟨P.index, ⟨j, n⟩⟩) =
            coeffMass P.index n.val := by
        simp [coeffQ, coeffMass]
      have hscaled (n : Fin nTerms) (hn : n.val < R.terms) :
          coeffMass P.index n.val * scaleFor P n.val hn = R.coeff ⟨n.val, hn⟩ := by
        by_cases hz : coeffMass P.index n.val = 0
        · have hcoef : R.coeff ⟨n.val, hn⟩ = 0 := by
            have hle := hcoeffLeMass P n.val (by simpa [R] using hn)
            have habs : |R.coeff ⟨n.val, hn⟩| = 0 := by
              apply le_antisymm
              · have hle' : |R.coeff ⟨n.val, hn⟩| ≤ coeffMass P.index n.val := by
                  simpa [R] using hle
                simpa [hz] using hle'
              · exact abs_nonneg _
            exact abs_eq_zero.mp habs
          simp [scaleFor, hz, hcoef]
        · have hscale : scaleFor P n.val hn =
              R.coeff ⟨n.val, hn⟩ / coeffMass P.index n.val := by
            simp [scaleFor, hz, R]
          rw [hscale]
          field_simp [hz]
      have htermsBound : R.terms ≤ nTerms := by
        have hj : (Recipes P.index (selected P)).terms ≤
            ∑ j : Fin (m P.index), (Recipes P.index j).terms := by
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun j : Fin (m P.index) => (Recipes P.index j).terms)
            (fun j hj => Nat.zero_le _)
            (Finset.mem_univ (selected P))
        have hi : (∑ j : Fin (m P.index), (Recipes P.index j).terms) ≤
            ∑ i : Fin Fm.size, ∑ j : Fin (m i), (Recipes i j).terms := by
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun i : Fin Fm.size => ∑ j : Fin (m i), (Recipes i j).terms)
            (fun i hi => Finset.sum_nonneg fun j hj => Nat.zero_le _)
            (Finset.mem_univ P.index)
        simpa [R, nTerms] using hj.trans hi
      let paddedTerm (n : ℕ) : ℝ :=
        if hn : n < R.terms then
          R.coeff ⟨n, hn⟩ * ∏ ω ∈ faces, R.factor ⟨n, hn⟩ ω (cube u ω)
        else 0
      have hpad : (∑ n : Fin nTerms, paddedTerm n.val) =
          (∑ n : Fin R.terms, paddedTerm n.val) := by
        rw [Fin.sum_univ_eq_sum_range paddedTerm nTerms,
          Fin.sum_univ_eq_sum_range paddedTerm R.terms]
        apply (Finset.sum_subset (Finset.range_mono htermsBound) ?_).symm
        intro n hn hnot
        have hnot' : ¬ n < R.terms := by
          intro hlt
          exact hnot (Finset.mem_range.mpr hlt)
        simp [paddedTerm, hnot']
      rw [Finset.sum_comm]
      calc
        _ = ∑ n : Fin nTerms,
              if hn : n.val < R.terms then
                coeffMass P.index n.val *
                  (scaleFor P n.val hn *
                    ∏ ω ∈ faces, R.factor ⟨n.val, hn⟩ ω (cube u ω))
              else 0 := by
          apply Finset.sum_congr rfl
          intro n hnmem
          by_cases hn : n.val < R.terms
          · simp [hn]
            rw [← Finset.sum_mul, hmassSum n]
          · simp [hn]
        _ = ∑ n : Fin nTerms,
              if hn : n.val < R.terms then
                R.coeff ⟨n.val, hn⟩ *
                  ∏ ω ∈ faces, R.factor ⟨n.val, hn⟩ ω (cube u ω)
              else 0 := by
          apply Finset.sum_congr rfl
          intro n hnmem
          by_cases hn : n.val < R.terms
          · simp [hn]
            rw [← mul_assoc, hscaled n hn]
          · simp [hn]
        _ = R.eval Fm (cube u) := by
          simpa [paddedTerm, Charted.CornerRecipe.eval, faces] using hpad
    have hSumReconstruct :
        (∑ t : Fin n₀, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y) =
          shiftAverage (Fin (s + 1)) L (fun u => R.eval Fm (cube u)) := by
      calc
        _ = ∑ q : RecipeIndex, coeffQ q * dualTest MS B (extraTemplate s) l J0 N
              (I (enum.symm q)) y := hreindex
        _ = ∑ q : RecipeIndex, coeffQ q * shiftAverage (Fin (s + 1)) L (shiftTerm q) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [hdual q]
        _ = shiftAverage (Fin (s + 1)) L
              (fun u => ∑ q : RecipeIndex, coeffQ q * shiftTerm q u) := hsumAverage
        _ = shiftAverage (Fin (s + 1)) L (fun u => R.eval Fm (cube u)) := by
          unfold shiftAverage
          congr 1
          apply Finset.sum_congr rfl
          intro u hu
          exact hinner u hu
    have hAvg : |shiftAverage (Fin (s + 1)) L (fun u => R.eval Fm (cube u)) -
        P.obs (P.g ^ k • P.x)| ≤ δ := by
      exact shiftAverage_sub_const_abs_le (d := s + 1) (L := L)
        (by omega) (by simpa [L] using hlength)
        (fun u => R.eval Fm (cube u)) (P.obs (P.g ^ k • P.x)) δ hchart
    rw [hPhiRoot, hSumReconstruct]
    simpa [abs_sub_comm] using hAvg
  refine ⟨I, ?_, ?_, hRecipeApprox⟩
  · intro t p
    exact hIone t p
  · intro t ω p z
    exact hIbound t ω p z

/-- (eq:prediction-weighted-boundary), 05:325–342: the boundary strips of relative length
`(s+1)/J₀` carry `(1 + ν_B)μ_i`-mass `O_s(J₀^{-1}) + o(1)`.  The constant depends on `s` only. -/
theorem weighted_boundary (s : ℕ) :
    ∃ C : ℝ, ∀ {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
      (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K), ValidGap B l →
      ∀ J0 : ℕ, 0 < J0 → ∀ ε > 0, ∀ᶠ N in atTop,
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          boundaryIndicator (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J0) y) ≤ C / J0 + ε := by
  obtain ⟨C, hC⟩ := weighted_boundary_aux s
  refine ⟨C, ?_⟩
  intro K sl As Dm MS B l hl J0 hJ0 ε hε
  have h := hC MS B l hl J0 hJ0 ε hε
  filter_upwards [h] with N hN
  simpa [boundaryIndicator, InBoundaryStrip, pkgDBoundaryIndicator,
    pkgDBoundaryStrip] using hN

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
  intro ε hε
  let δ : ℝ := ε / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n₀, coeff, hrecipes⟩ :=
    nilsequence_recipe_tests MS B l hl Fm Km δ hδ
  let C₀ : ℝ := ∑ t : Fin n₀, |coeff t|
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact Finset.sum_nonneg fun t _ => abs_nonneg _
  obtain ⟨Cbd, hboundary⟩ := weighted_boundary s
  let CbdPlus : ℝ := max Cbd 0
  let ηb : ℝ := ε / (16 * (1 + C₀))
  let ηm : ℝ := ε / (8 * (1 + C₀))
  have hηb : 0 < ηb := by dsimp [ηb]; positivity
  have hηm : 0 < ηm := by dsimp [ηm]; positivity
  have hthreshold : 0 ≤ 16 * (1 + C₀) * CbdPlus / ε := by positivity
  obtain ⟨J₀, hJ₀gt⟩ := exists_nat_gt (16 * (1 + C₀) * CbdPlus / ε)
  have hJ₀ : 0 < J₀ := by
    have hJ₀real : 0 < (J₀ : ℝ) := lt_of_le_of_lt hthreshold hJ₀gt
    exact_mod_cast hJ₀real
  have hCbdPlus : Cbd ≤ CbdPlus := le_max_left _ _
  have hCbdDiv : Cbd / (J₀ : ℝ) ≤ ε / (16 * (1 + C₀)) := by
    have hprod : 16 * (1 + C₀) * CbdPlus < ε * (J₀ : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hJ₀gt
    have hprod' : Cbd * (16 * (1 + C₀)) ≤ ε * (J₀ : ℝ) := by
      calc
        Cbd * (16 * (1 + C₀)) ≤ CbdPlus * (16 * (1 + C₀)) :=
          mul_le_mul_of_nonneg_right hCbdPlus (by positivity)
        _ = 16 * (1 + C₀) * CbdPlus := by ring
        _ ≤ ε * (J₀ : ℝ) := le_of_lt hprod
    rw [div_le_div_iff₀ (by positivity : 0 < (J₀ : ℝ)) (by positivity)]
    exact hprod'
  have hboundaryN := hboundary MS B l hl J₀ hJ₀ ηb hηb
  have hboundarySmall : Cbd / (J₀ : ℝ) + ηb ≤ ε / (8 * (1 + C₀)) := by
    rw [show ηb = ε / (16 * (1 + C₀)) by rfl]
    calc
      Cbd / (J₀ : ℝ) + ε / (16 * (1 + C₀)) ≤
          ε / (16 * (1 + C₀)) + ε / (16 * (1 + C₀)) :=
        add_le_add_left hCbdDiv _
      _ = ε / (8 * (1 + C₀)) := by field_simp; norm_num
  have hrecipesN := hrecipes J₀ hJ₀
  have hmeanN := pivotEmu_one_plus_nu_le_three MS B l hl
  have hnuN := pivotNu_nonneg_eventually MS B
  have hAllowed : Allowed Dm (extraTemplate s) :=
    extraTemplate_allowed (K := K) (sl := sl) (s := s) (As := As) (Dm := Dm) h1
  have hDenseN := hF.2 B a ha c l hl (extraTemplate s) hAllowed J₀ hJ₀ ηm hηm
  filter_upwards [hrecipesN, hboundaryN, hmeanN, hnuN, hDenseN]
    with N hrecipesN hboundaryN hmeanN hnuN hDenseN
  intro Φ
  obtain ⟨I, hIone, hIbound, happrox⟩ := hrecipesN Φ
  have hD : ∀ t y, |dualTest MS B (extraTemplate s) l J₀ N (I t) y| ≤ 1 := by
    intro t y
    exact extraDualTest_abs_le_one (MS := MS) (B := B) (s := s) (l := l)
      (J0 := J₀) (N := N) (I := I t)
      (fun p => hIone t p) (fun ω p z => hIbound t ω p z) y
  let Q : ℤ → ℝ := fun y =>
    ∑ t : Fin n₀, coeff t * dualTest MS B (extraTemplate s) l J₀ N (I t) y
  have hQ : ∀ y, |Q y| ≤ C₀ := by
    intro y
    dsimp [Q, C₀]
    calc
      |∑ t : Fin n₀, coeff t * dualTest MS B (extraTemplate s) l J₀ N (I t) y|
          ≤ ∑ t : Fin n₀, |coeff t * dualTest MS B (extraTemplate s) l J₀ N (I t) y| :=
            by
              simpa [Real.norm_eq_abs] using
                (norm_sum_le (Finset.univ : Finset (Fin n₀))
                  (fun t => coeff t * dualTest MS B (extraTemplate s) l J₀ N (I t) y))
      _ ≤ ∑ t : Fin n₀, |coeff t| := by
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hD t y)
  have hPhi : ∀ y, Φ.eval N y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    dsimp [RepFamily.eval, OAI.SourceMenuLiteral.CosetPiece.eval]
    exact (Φ.piece N (y / (MS.core.parameters.H N l : ℤ))
      (y % (MS.core.parameters.M N : ℤ))).range _
  have hdiff : ∀ y,
      |Φ.eval N y - Q y| ≤ δ + (1 + C₀) *
        boundaryIndicator (MS.core.parameters.H N l)
          ((s + 1) * MS.core.parameters.H N l / J₀) y := by
    intro y
    by_cases hs : InBoundaryStrip (MS.core.parameters.H N l)
        ((s + 1) * MS.core.parameters.H N l / J₀) y
    · have hb : boundaryIndicator (MS.core.parameters.H N l)
          ((s + 1) * MS.core.parameters.H N l / J₀) y = 1 := by
        simp [boundaryIndicator, hs]
      rw [hb]
      have hphi0 := (hPhi y).1
      have hphi1 := (hPhi y).2
      calc
        |Φ.eval N y - Q y| ≤ |Φ.eval N y| + |Q y| := by
          calc
            |Φ.eval N y - Q y| = |Φ.eval N y + -Q y| := by congr 1 <;> ring
            _ ≤ |Φ.eval N y| + |-Q y| := abs_add_le _ _
            _ = |Φ.eval N y| + |Q y| := by rw [abs_neg]
        _ ≤ 1 + C₀ := by
          have hpa : |Φ.eval N y| ≤ 1 := abs_le.mpr ⟨by linarith, hphi1⟩
          exact add_le_add hpa (hQ y)
        _ ≤ δ + (1 + C₀) := by
          calc
            1 + C₀ = 0 + (1 + C₀) := by simp
            _ ≤ δ + (1 + C₀) := add_le_add_left hδ.le _
        _ = δ + (1 + C₀) * 1 := by simp
    · have hb : boundaryIndicator (MS.core.parameters.H N l)
          ((s + 1) * MS.core.parameters.H N l / J₀) y = 0 := by
        simp [boundaryIndicator, hs]
      rw [hb]
      simpa [Q] using happrox y hs
  have hcolor0 (y : ℤ) : 0 ≤ colorFactor MS.core.parameters χ N B a c y :=
    rationalColorIndicator_nonneg χ c _
  have hcolor1 (y : ℤ) : colorFactor MS.core.parameters χ N B a c y ≤ 1 := by
    classical
    unfold colorFactor rationalColorIndicator
    split_ifs <;> norm_num
  have hrhoF : ∀ y, |rho MS.core.parameters χ N B a c y - F N B a c y| ≤
      1 + nu MS.core.parameters N B y := by
    intro y
    have hν := hnuN y
    have hFval := hF.1 N B a c y
    have hρ0 : 0 ≤ rho MS.core.parameters χ N B a c y := by
      simp [rho]
      exact mul_nonneg hν (hcolor0 y)
    have hρν : rho MS.core.parameters χ N B a c y ≤ nu MS.core.parameters N B y := by
      simp [rho]
      exact mul_le_of_le_one_right hν (hcolor1 y)
    rcases hFval with ⟨hF0, hF1⟩
    apply abs_le.mpr
    constructor <;> simp only [rho] at * <;> nlinarith
  have herrorPoint (y : ℤ) :
      |(rho MS.core.parameters χ N B a c y - F N B a c y) *
          (Φ.eval N y - Q y)| ≤
        (1 + nu MS.core.parameters N B y) *
          (δ + (1 + C₀) * boundaryIndicator
            (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J₀) y) := by
    have hweight : 0 ≤ 1 + nu MS.core.parameters N B y := by linarith [hnuN y]
    have hsmall : 0 ≤ δ + (1 + C₀) * boundaryIndicator
        (MS.core.parameters.H N l) ((s + 1) * MS.core.parameters.H N l / J₀) y := by
      by_cases hs : InBoundaryStrip (MS.core.parameters.H N l)
          ((s + 1) * MS.core.parameters.H N l / J₀) y
      · simp [boundaryIndicator, hs]
        positivity
      · simp [boundaryIndicator, hs]
        positivity
    rw [abs_mul]
    exact mul_le_mul (hrhoF y) (hdiff y) (abs_nonneg _) hweight
  have herror := Emu_abs_bound_by_weight MS.core.parameters N B.1
    (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) *
      (Φ.eval N y - Q y))
    (fun y => (1 + nu MS.core.parameters N B y) *
      (δ + (1 + C₀) * boundaryIndicator (MS.core.parameters.H N l)
        ((s + 1) * MS.core.parameters.H N l / J₀) y))
    (fun y => harmonicLaw_nonneg_of_Xpos
      (MS.core.parameters.X N B.1) (primorial (N + 1))
      (MS.core.parameters.Xpos N B.1) y)
    herrorPoint
  have herrorValue : |Emu MS.core.parameters N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * (Φ.eval N y - Q y))| ≤
      δ * Emu MS.core.parameters N B.1 (fun y => 1 + nu MS.core.parameters N B y) +
        (1 + C₀) * Emu MS.core.parameters N B.1 (fun y =>
          (1 + nu MS.core.parameters N B y) * boundaryIndicator
            (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J₀) y) := by
    have hlin := Emu_const_add_mul MS.core.parameters N B.1
      (fun y => 1 + nu MS.core.parameters N B y)
      (fun y => boundaryIndicator (MS.core.parameters.H N l)
        ((s + 1) * MS.core.parameters.H N l / J₀) y) δ (1 + C₀)
    calc
      _ ≤ Emu MS.core.parameters N B.1 (fun y =>
          (1 + nu MS.core.parameters N B y) *
            (δ + (1 + C₀) * boundaryIndicator (MS.core.parameters.H N l)
              ((s + 1) * MS.core.parameters.H N l / J₀) y)) := herror
      _ = _ := hlin
  have hpairing : |Emu MS.core.parameters N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * Q y)| ≤ C₀ * ηm := by
    rw [Emu_sum_pairing MS.core.parameters N B.1
      (fun y => rho MS.core.parameters χ N B a c y - F N B a c y) coeff
      (fun t y => dualTest MS B (extraTemplate s) l J₀ N (I t) y)]
    have hdense (t : Fin n₀) := hDenseN (I t)
    calc
      |∑ t : Fin n₀, coeff t * Emu MS.core.parameters N B.1 (fun y =>
          (rho MS.core.parameters χ N B a c y - F N B a c y) *
            dualTest MS B (extraTemplate s) l J₀ N (I t) y)|
          ≤ ∑ t : Fin n₀, |coeff t * Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              dualTest MS B (extraTemplate s) l J₀ N (I t) y)| := by
            simpa [Real.norm_eq_abs] using
              (norm_sum_le (Finset.univ : Finset (Fin n₀))
                (fun t => coeff t * Emu MS.core.parameters N B.1 (fun y =>
                  (rho MS.core.parameters χ N B a c y - F N B a c y) *
                    dualTest MS B (extraTemplate s) l J₀ N (I t) y)))
      _ ≤ ∑ t : Fin n₀, |coeff t| * ηm := by
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hdense t) (abs_nonneg _)
      _ = C₀ * ηm := by rw [← Finset.sum_mul]
  have hsplit : Emu MS.core.parameters N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * Φ.eval N y) =
      Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * Q y) +
      Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) *
          (Φ.eval N y - Q y)) := by
    calc
      _ = Emu MS.core.parameters N B.1 (fun y =>
          (rho MS.core.parameters χ N B a c y - F N B a c y) * Q y +
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              (Φ.eval N y - Q y)) := by
        congr 1
        funext y
        ring
      _ = _ := Emu_add MS.core.parameters N B.1 _ _
  have hbdSmall : (1 + C₀) * (Cbd / (J₀ : ℝ) + ηb) ≤ ε / 8 := by
    rw [show ηb = ε / (16 * (1 + C₀)) by rfl]
    have h := mul_le_mul_of_nonneg_left hboundarySmall (by positivity : (0 : ℝ) ≤ 1 + C₀)
    calc
      _ ≤ (1 + C₀) * (ε / (8 * (1 + C₀))) := h
      _ = ε / 8 := by field_simp
  have hpairSmall : C₀ * ηm ≤ ε / 8 := by
    rw [show ηm = ε / (8 * (1 + C₀)) by rfl]
    have hC0bound : C₀ ≤ 1 + C₀ := by linarith [hC₀]
    have hmul := mul_le_mul_of_nonneg_right hC0bound (by positivity : (0 : ℝ) ≤ ε / (8 * (1 + C₀)))
    have hden : (1 + C₀) * (ε / (8 * (1 + C₀))) = ε / 8 := by field_simp
    nlinarith
  have herrorSmall : δ * Emu MS.core.parameters N B.1 (fun y =>
      1 + nu MS.core.parameters N B y) + (1 + C₀) *
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          boundaryIndicator (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J₀) y) ≤ 7 * ε / 16 := by
    have hbd := hboundaryN
    have hmean := hmeanN
    have hmean' := mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤ δ)
    have hbd' := mul_le_mul_of_nonneg_left hbd (by positivity : (0 : ℝ) ≤ 1 + C₀)
    have hmeanBound : δ * Emu MS.core.parameters N B.1
        (fun y => 1 + nu MS.core.parameters N B y) ≤ 3 * ε / 16 := by
      calc
        δ * Emu MS.core.parameters N B.1 (fun y => 1 + nu MS.core.parameters N B y) ≤ δ * 3 := hmean'
        _ = 3 * ε / 16 := by rw [show δ = ε / 16 by rfl]; ring
    calc
      _ ≤ 3 * ε / 16 + ε / 8 :=
        add_le_add hmeanBound (hbd'.trans hbdSmall)
      _ ≤ 7 * ε / 16 := by nlinarith [hε]
  calc
    |Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * Φ.eval N y)|
        ≤ |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) * Q y)| +
          |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              (Φ.eval N y - Q y))| := by rw [hsplit]; exact abs_add_le _ _
    _ ≤ C₀ * ηm + (δ * Emu MS.core.parameters N B.1 (fun y =>
          1 + nu MS.core.parameters N B y) + (1 + C₀) *
            Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
              boundaryIndicator (MS.core.parameters.H N l)
                ((s + 1) * MS.core.parameters.H N l / J₀) y)) := by
      exact add_le_add hpairing herrorValue
    _ ≤ ε / 8 + 7 * ε / 16 := add_le_add hpairSmall herrorSmall
    _ ≤ ε := by nlinarith [hε]

end

end HindmanSumsProducts.Prediction
