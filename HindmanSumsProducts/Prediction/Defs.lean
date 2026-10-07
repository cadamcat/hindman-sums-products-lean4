import HindmanSumsProducts.Arithmetic
import HindmanSumsProducts.Correlation
import HindmanSumsProducts.Framework
import OAI.Combinatorics.SumProduct.Alignment.MenuLiteral01

/-!
# §5 vocabulary (`05_prediction.tex`)

Conventions (PREDICTION.md §3): the asymptotic index is `N`, the paper's `w = N + 1` and
`W = primorial (N + 1)`.  Inside §5 every law is a finitely supported weight function, exactly as
in §3 and §4: the pivot law `μ_i` is `harmonicLaw (X_i) W` and the divisor weight `ν_B` is
`nuB (parameterTailProductLaw A N T)` (both `HindmanSumsProducts.Arithmetic`; the same objects as
§4's `pivotMass`, `chainWeight`).  The measure form of the Prediction Principle
(`HindmanSumsProducts.PredictionPrinciple`, `Framework.lean`) appears only in `Completion.lean`.

Menus and models are OpenAI's *charted* objects (`OAI.SourceChartedMenu.Menu`,
`OAI.SourceMenuLiteral.CosetPiece`, `OAI.SourceMenuLiteral.ModelsSystem`), as in
`PredictionPrinciple`.  Master scales are §3's `HindmanSumsProducts.MasterScales`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace HindmanSumsProducts.Prediction

noncomputable section

/-! ### OpenAI objects -/

abbrev Parameters (n : ℕ) := OAI.SourceAdmissible.Parameters n
abbrev Block (n : ℕ) := OAI.SourceBlocks.Block n
/-- Charted menu of step at most `s` (a finite list of nilmanifolds). -/
abbrev Menu (s : ℕ) := OAI.SourceChartedMenu.Menu s
/-- One nilsequence piece `k ↦ obs (g ^ k • x)` with a `[0,1]`-valued `K`-Lipschitz observable. -/
abbrev CosetPiece {s : ℕ} (F : Menu s) (K : ℝ≥0) := OAI.SourceMenuLiteral.CosetPiece F K
/-- Piecewise models (Definition `def:piecewise-model`), charted form. -/
abbrev ModelsSystem {n s : ℕ} (A : Parameters n) (vs : Finset ℚ) (r : ℕ) (F : Menu s) :=
  OAI.SourceMenuLiteral.ModelsSystem A vs r F

/-- `h_S = ∏_{j ∈ S} h_j` (OpenAI's `height`). -/
abbrev height {n : ℕ} (h : Fin n → ℤ) (S : Finset (Fin n)) : ℤ :=
  OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height h S

/-! ### Laws, weights, colour factors (finitely supported, §3 vocabulary) -/

/-- The pivot law `μ_i` of (eq:harmonic-law): harmonic `W`-units of `[X_i, X_i²)`. -/
def mu {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n) : ℤ → ℝ :=
  harmonicLaw (A.X N i) (primorial (N + 1))

/-- `E_{y ∼ μ_i} f(y)`; a finite sum, since `μ_i` has finite support. -/
def Emu {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n) (f : ℤ → ℝ) : ℝ :=
  ∑' y, mu A N i y * f y

/-- The divisor weight `ν_B(y) = E_{σ = t_T} σ 1_{σ ∣ y}` of (eq:divisor-weight). -/
def nu {n : ℕ} (A : Parameters n) (N : ℕ) (B : Block n) : ℤ → ℝ :=
  nuB (parameterTailProductLaw A N B.2.val)

/-- The colour factor `f(y) = 1_{χ(h_B a y) = c}` of 05:27, zero unless `h_B a y` is a positive
integer (Framework's `rationalColorIndicator`). -/
def colorFactor {n r : ℕ} (A : Parameters n) (χ : ℕ → Fin r) (N : ℕ) (B : Block n) (a : ℚ)
    (c : Fin r) (y : ℤ) : ℝ :=
  rationalColorIndicator χ c ((height (A.ht N) B.set : ℚ) * a * (y : ℚ))

/-- `ρ = ν_B f` of 05:27. -/
def rho {n r : ℕ} (A : Parameters n) (χ : ℕ → Fin r) (N : ℕ) (B : Block n) (a : ℚ)
    (c : Fin r) (y : ℤ) : ℝ :=
  nu A N B y * colorFactor A χ N B a c y

/-- Families of functions indexed by master block, scale label and colour (dense models `F`,
coarse models `S`), one function per asymptotic index `N`. -/
abbrev BlockFamily (n r : ℕ) := ℕ → Block n → ℚ → Fin r → ℤ → ℝ

/-- `[0,1]`-valued families. -/
def UnitValued {n r : ℕ} (F : BlockFamily n r) : Prop :=
  ∀ N B a c y, F N B a c y ∈ Set.Icc (0 : ℝ) 1

/-- A gap `l` is valid for the block `B = T ∪ {i}`: `max T < l < i` (05:42, 05:276). -/
def ValidGap {n : ℕ} (B : Block n) (l : Fin n) : Prop :=
  (∀ j ∈ B.2.val, j < l) ∧ l < B.1

/-! ### Limits -/

/-- `lim_L f ≤ C` in the form `∀ ε > 0, ∀ᶠ N in L, f N ≤ C + ε` (equivalent for bounded `f`; the
form of `PredictionPrinciple`). -/
def FilterUpperBound (L : Filter ℕ) (f : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ N in L, f N ≤ C + ε

/-- `lim_𝒰 f ≤ C` along an ultrafilter. -/
abbrev UltrafilterUpperBound (U : Ultrafilter ℕ) (f : ℕ → ℝ) (C : ℝ) : Prop :=
  FilterUpperBound (U : Filter ℕ) f C

/-- `lim_𝒰` of a sequence (meaningful for bounded sequences, the only ones used). -/
def ulim (U : Ultrafilter ℕ) (f : ℕ → ℝ) : ℝ := limUnder (U : Filter ℕ) f

/-! ### Representing families (Definition `def:piecewise-model` at a gap, 05:276–279, 355–364)

A representing family at gap `l` consists of nilsequence pieces on the `R_l`-intervals
`[k R_l, (k+1) R_l)` and residues modulo `M`, in the global progression index — OpenAI's
`ModelsSystem.represents` shape with `H := R_l = A.H N l`.  The menu (finite nilmanifold list) and
the Lipschitz bound are fixed within a family; pieces, translating elements and base points are
arbitrary.  Bounded real families are affine combinations of these `[0,1]`-valued ones and the
constant family, so their real span is the paper's span. -/
structure RepFamily {n : ℕ} (A : Parameters n) (l : Fin n) {s : ℕ} (Fm : Menu s) (Km : ℝ≥0) where
  piece : ℕ → ℤ → ℤ → CosetPiece Fm Km

/-- Value of a representing family at `(N, y)`. -/
def RepFamily.eval {n : ℕ} {A : Parameters n} {l : Fin n} {s : ℕ} {Fm : Menu s} {Km : ℝ≥0}
    (Φ : RepFamily A l Fm Km) (N : ℕ) (y : ℤ) : ℝ :=
  (Φ.piece N (y / (A.H N l : ℤ)) (y % (A.M N : ℤ))).eval ((y - y % (A.M N : ℤ)) / (A.M N : ℤ))

end

end HindmanSumsProducts.Prediction
