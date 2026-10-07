import HindmanSumsProducts.ChainSelection
import OAI.Combinatorics.SumProduct.Alignment.RawMenu

open scoped BigOperators
open scoped NNReal
open scoped Topology
open MeasureTheory
open Filter

namespace HindmanSumsProducts.Prediction

/-! Local §2 notation used by §5.  At final assembly these interfaces should be unified with
`HindmanSumsProducts.Framework`; the analytic objects at the boundaries are the OAI objects. -/

abbrev Parameters (n : ℕ) := OAI.SourceAdmissible.Parameters n
abbrev Block (n : ℕ) := OAI.SourceBlocks.Block n
abbrev Tail (n : ℕ) (i : Fin n) := OAI.SourceBlocks.Tail i
abbrev Scale (n : ℕ) := OAI.ConstructedWordPlan.GlobalWordPlan.Scale n
abbrev Menu (s : ℕ) := OAI.SourceRawMenu.Menu s
abbrev CosetPiece {s : ℕ} (F : Menu s) (K : ℝ≥0) :=
  OAI.SourceRawMenu.CosetPiece F K
abbrev ModelsSystem {n s : ℕ} (A : Parameters n) (vs : Finset ℚ) (r : ℕ)
    (F : Menu s) := OAI.SourceRawMenu.ModelsSystem A vs r F
abbrev Models (n r : ℕ) := OAI.SourceBlocks.Models n r
abbrev blockProduct {n : ℕ} (b : Fin n → ℚ) (S : Finset (Fin n)) : ℚ :=
  OAI.ConstructedWordPlan.AlignmentScales.blockProduct b S

/-- The paper's asymptotic index convention: this Lean index is `N`, and `w = N + 1`. -/
def paperW (N : ℕ) : ℕ := N + 1

/-- Paper label `def:admissible`, §2, lines 58–78. The objects are OpenAI's parameters. -/
abbrev AdmissibleParameters (n : ℕ) := OAI.SourceAdmissible.Parameters n

/-- The scale-list and coloring data fixed in the Prediction Principle. -/
structure InputData (n r : ℕ) where
  color : ℕ → Fin r
  scales : Finset (Scale n)
  multipliers : Finset ℚ
  scales_pos : ∀ b ∈ scales, ∀ j, 0 < b j
  multipliers_pos : ∀ a ∈ multipliers, 0 < a
  block_multiplier_closed : ∀ b ∈ scales, ∀ B : Block n,
    blockProduct b B.set ∈ multipliers

/-- A chain is the §2 chain predicate, represented by the shared `IsChain` definition.
Its OAI blocks are generated from the same tails and pivots. -/
structure BlockChain (n m : ℕ) where
  tails : Fin m → Finset (Fin n)
  pivots : Fin m → Fin n
  isChain : HindmanSumsProducts.IsChain tails pivots

def BlockChain.block {n m : ℕ} (C : BlockChain n m) (d : Fin m) : Block n :=
  ⟨C.pivots d, ⟨C.tails d, ⟨C.isChain.1 d, C.isChain.2.2.1 d d⟩⟩⟩

abbrev integerHeight {n : ℕ} (h : Fin n → ℤ) (S : Finset (Fin n)) : ℤ :=
  OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height h S

/-- §2 block sample `t_B`, as the product of its raw coordinates. -/
def rawBlockProduct {n : ℕ} (B : Block n) (t : Fin n → ℕ) : ℕ :=
  ∏ j ∈ B.set, t j

/-- The integer block product used as an argument of an OAI model. -/
def rawBlockProductInt {n : ℕ} (B : Block n) (t : Fin n → ℕ) : ℤ :=
  integerHeight (fun j => (t j : ℤ)) B.set

/-- The paper's coefficient `c_B = h_B a`, with the scale supplied by OAI's `Parameters.ht`.
The fixed rational factor is retained as a rational until the paper's eventual integrality applies. -/
def blockCoefficient {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) (a : ℚ) : ℚ :=
  (integerHeight (A.ht N) B.set : ℚ) * a

/-- Total extension of an eventually integral positive rational color argument. -/
def rationalToNat (q : ℚ) : ℕ := Int.toNat (Int.floor q)

/-- The paper's color indicator is zero off positive arguments. `rationalToNat` only fixes Lean's
total behavior at the finitely many indices where integrality has not yet been arranged. -/
def colorIndicator {r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (q : ℚ) : ℝ :=
  if 0 < q ∧ χ (rationalToNat q) = c then 1 else 0

/-- Exact finite product law supplied by OpenAI when the admissibility cutoff condition holds.
Outside that eventual range a Dirac measure is used solely to make the sequence total. -/
noncomputable def rawLaw {n : ℕ} (A : Parameters n) (N : ℕ) : Measure (Fin n → ℕ) :=
  if hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i then
    A.law N hX
  else Measure.dirac (fun _ => 0)

/-- The pivot harmonic law `μ_i`, obtained as the coordinate marginal of `Parameters.law`. -/
noncomputable def pivotLaw {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n) : Measure ℤ :=
  Measure.map (fun t : Fin n → ℕ => (t i : ℤ)) (rawLaw A N)

/-- The divisor weight `ν_B(y)=E_{t_T} t_T 1_{t_T|y}` from (eq:divisor-weight), §2, lines 125–143.
It averages over the OAI product law and depends only on the tail coordinates by definition. -/
noncomputable def divisorWeight {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) (y : ℤ) : ℝ :=
    ∫ t, (∏ j ∈ B.2.val, t j : ℝ) *
    (if (∏ j ∈ B.2.val, (t j : ℤ)) ∣ y then 1 else 0) ∂rawLaw A N

/-- The color-weighted factor `ρ=ν_B 1_{χ(h_B a y)=c}` used by §5. -/
noncomputable def rho {n r : ℕ} (A : Parameters n) (D : InputData n r) (N : ℕ)
    (B : Block n) (a : ℚ) (c : Fin r) (y : ℤ) : ℝ :=
  divisorWeight A N B y *
    colorIndicator D.color c (blockCoefficient A N B a * (y : ℚ))

/-- Nonempty subsets of a finite index set. -/
def nonemptySubsets (m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter Finset.Nonempty

/-- The largest position of a nonempty subset, matching `d(J)=max J`. -/
noncomputable def subsetLast {m : ℕ} (J : Finset (Fin m)) (hJ : J.Nonempty) : Fin m :=
  J.max' hJ

/-- Sum form `L_J(z)=Σ_{k∈J}(c_k/c_{d(J)})z_k`, kept rational until its proved integrality. -/
noncomputable def sumForm {m : ℕ} (coeff : Fin m → ℚ) (z : Fin m → ℤ)
    (J : Finset (Fin m)) (hJ : J.Nonempty) : ℚ :=
  ∑ k ∈ J, (coeff k / coeff (subsetLast J hJ)) * (z k : ℚ)

/-- Product mask `U(z)` from (eq:product-mask), over every nonempty subset. -/
def productMask {n m r : ℕ} (A : Parameters n) (D : InputData n r) (N : ℕ)
    (C : BlockChain n m) (b : Scale n) (c : Fin r) (z : Fin m → ℤ) : ℝ :=
  ∏ J ∈ nonemptySubsets m,
    colorIndicator D.color c
      (∏ k ∈ J, blockCoefficient A N (C.block k) (blockProduct b (C.block k).set) *
        (z k : ℚ))

/-- The `L_J` color/divisor-weight factor from (eq:weighted-count), for non-singletons. -/
noncomputable def weightedSumFactor {n m r : ℕ} (A : Parameters n)
    (D : InputData n r) (N : ℕ) (C : BlockChain n m) (b : Scale n)
    (c : Fin r) (z : Fin m → ℤ) (J : Finset (Fin m))
    (hcard : 2 ≤ J.card) : ℝ :=
  let hJ : J.Nonempty := Finset.card_pos.mp (by omega)
  let d := subsetLast J hJ
  let L := sumForm (fun k => blockCoefficient A N (C.block k)
      (blockProduct b (C.block k).set)) z J hJ
  divisorWeight A N (C.block d) (Int.floor L) *
    colorIndicator D.color c (blockCoefficient A N (C.block d)
      (blockProduct b (C.block d).set) * L)

/-- The weighted count `𝓘_{b,c,𝐁}` of (eq:weighted-count), §2, lines 185–200.
`pivotLaw` is the product of the independent `μ_{i_d}`; the total law convention above only
affects finitely many initial indices. -/
noncomputable def weightedCount {n m r : ℕ} (A : Parameters n)
    (D : InputData n r) (N : ℕ) (C : BlockChain n m) (b : Scale n)
    (c : Fin r) : ℝ :=
  ∫ z, productMask A D N C b c z *
      (∏ d : Fin m, divisorWeight A N (C.block d) (z d)) *
      (∏ J ∈ nonemptySubsets m,
        if hcard : 2 ≤ J.card then
          weightedSumFactor A D N C b c z J hcard else 1)
    ∂Measure.pi (fun d : Fin m => pivotLaw A N (C.block d).1)

/-- Model-only count in (eq:prediction-counting), sampled from the product law of the raw
variables. The rational sum is sent to `Int.floor`; for the admissible scales it is exactly the
integer `L_J` for all sufficiently large `N`. -/
noncomputable def modelCount {n m r s : ℕ} (A : Parameters n)
    (D : InputData n r) (N : ℕ) (C : BlockChain n m) (b : Scale n)
    (c : Fin r) (F : Menu s) (S : ModelsSystem A D.multipliers r F) : ℝ :=
  ∫ t, productMask A D N C b c (fun d => rawBlockProductInt (C.block d) t) *
      (∏ J ∈ nonemptySubsets m,
        if hcard : 2 ≤ J.card then
        let hJ : J.Nonempty := Finset.card_pos.mp (by omega)
        let d := subsetLast J hJ
        let L := sumForm (fun k => blockCoefficient A N (C.block k)
          (blockProduct b (C.block k).set))
          (fun k => rawBlockProductInt (C.block k) t) J hJ
        S.model N (C.block d) (blockProduct b (C.block d).set) c (Int.floor L)
        else 1)
    ∂rawLaw A N

/-- Probability in (eq:prediction-calibration), with OAI's `ModelsSystem.model`. -/
noncomputable def calibrationProbability {n r s : ℕ} (A : Parameters n)
    (D : InputData n r) (N : ℕ) (τ : ℝ) (B : Block n) (a : ℚ) (c : Fin r)
    (F : Menu s) (S : ModelsSystem A D.multipliers r F) : ℝ :=
  (rawLaw A N).real {t | colorIndicator D.color c
      (blockCoefficient A N B a * (rawBlockProductInt B t : ℚ)) = 1 ∧
      S.model N B a c (rawBlockProductInt B t) ≤ 2 * τ}

/-- Upper-bound formulation of an ultrafilter limit, equivalent to `lim_U f ≤ C` for bounded
real sequences. The index is `N`, so the paper's `w` is `N+1`. -/
def UltrafilterUpperBound (U : Ultrafilter ℕ) (f : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ N in (U : Filter ℕ), f N ≤ C + ε

/-- Exact atTop meaning of `o(1)` used throughout §§3–5. -/
def tendsToZeroAtTop (f : ℕ → ℝ) : Prop := Tendsto f atTop (𝓝 0)

/-- `A` dominates every fixed power of `B` in the paper's asymptotic convention. -/
def dominatesPowers (A B : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → Tendsto (fun N => A N / B N ^ C) atTop atTop

/-- Calibration conclusion (eq:prediction-calibration), expressed as the upper bound for the
ultrafilter limit of the exact OAI raw-law probability. -/
def CalibrationConclusion {n r s : ℕ} (U : Ultrafilter ℕ) (D : InputData n r)
    (τ η : ℝ) (A : Parameters n) (F : Menu s)
    (S : ModelsSystem A D.multipliers r F) : Prop :=
  ∀ B : Block n, ∀ a ∈ D.multipliers, ∀ c : Fin r,
    UltrafilterUpperBound U
      (fun N => calibrationProbability A D N τ B a c F S) (3 * τ + η)

/-- Counting conclusion (eq:prediction-counting), for every paper chain, scale, and color. -/
def CountingConclusion {n r s : ℕ} (m : ℕ) (U : Ultrafilter ℕ) (D : InputData n r)
    (η : ℝ) (A : Parameters n) (F : Menu s)
    (S : ModelsSystem A D.multipliers r F) : Prop :=
  ∀ C : BlockChain n m, ∀ b ∈ D.scales, ∀ c : Fin r,
    UltrafilterUpperBound U
      (fun N => |weightedCount A D N C b c - modelCount A D N C b c F S|) η

/-- The two conclusions of the Prediction Principle, with shared OAI parameters and models. -/
def PredictionOutput {n m r s : ℕ} (U : Ultrafilter ℕ) (D : InputData n r)
  (τ η : ℝ) : Prop :=
  ∃ A : Parameters n, ∃ F : Menu s, ∃ S : ModelsSystem A D.multipliers r F,
    CalibrationConclusion U D τ η A F S ∧ CountingConclusion m U D η A F S

/-- The family of dense models `F_{B,a,c}`. -/
abbrev DenseModelFamily (n r : ℕ) := ℕ → Block n → ℚ → Fin r → ℤ → ℝ

/-- Pointwise range condition for the bounded models. -/
def IsDenseModelFamily {n r : ℕ} (F : DenseModelFamily n r) : Prop :=
  ∀ N B a c y, 0 ≤ F N B a c y ∧ F N B a c y ≤ 1

/-- Gap-dependent orthogonal projections in the Hilbert ultraproduct of the `L²(μ_i)` spaces.
This interface records the projections themselves; `Projection.lean` states the nested-space and
energy consequences used in §5. -/
structure GapProjection (n : ℕ) where
  norm : (i : Fin n) → (ℕ → ℤ → ℝ) → ℝ
  project : (i l : Fin n) → l < i → (ℕ → ℤ → ℝ) → (ℕ → ℤ → ℝ)

end HindmanSumsProducts.Prediction
