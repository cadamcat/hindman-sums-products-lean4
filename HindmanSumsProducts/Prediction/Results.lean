import HindmanSumsProducts.Prediction.Outside

open scoped BigOperators NNReal Topology
open MeasureTheory Filter Classical

namespace HindmanSumsProducts.Prediction

/-- A family of allowed §5 dual tests of uniformly bounded dimension. The tests may vary with
the asymptotic index and may use different permissible gaps and prime-dependent moduli. -/
def IsDualTestFamily {n : ℕ} (B : Block n) (A : Parameters n) (dStar : ℕ)
    (D : ∀ N, DualTest B (divisorWeight A N B)) : Prop :=
  (∀ N, (D N).dimension ≤ dStar) ∧ DualTestFamilyGood A D

/-- Pairing of `ν_B-1` with a finite product of independently chosen dual tests. -/
noncomputable def dualProductPairing {n b : ℕ} (A : Parameters n) (B : Block n)
    (N : ℕ) (D : Fin b → DualTest B (divisorWeight A N B)) : ℝ :=
  ∫ y, (divisorWeight A N B y - 1) * ∏ q, (D q).value y
    ∂pivotLaw A N B.1

/-- `A_*` from (eq:prediction-dual-moments). -/
def dualMomentConstant (dStar : ℕ) : ℝ := (2 : ℝ) ^ (2 ^ dStar - 1)

/-- §5, Lemma `lem:dual-pseudorandomness`, equation `eq:prediction-dual-products` (lines 68–74).
The fixed product length is chosen before the limit; the test family itself may vary arbitrarily
with `N`. -/
theorem dual_products_orthogonal {n b : ℕ} (A : Parameters n) (B : Block n)
    (dStar : ℕ) (D : ∀ N, Fin b → DualTest B (divisorWeight A N B))
    (hD : ∀ N q, (D N q).dimension ≤ dStar)
    (hgood : ∀ q, DualTestFamilyGood A (fun N => D N q)) :
    tendsToZeroAtTop (fun N => |dualProductPairing A B N (D N)|) := by
  sorry

/-- §5, Lemma `lem:dual-pseudorandomness`, equation `eq:prediction-dual-moments` (lines 75–79). -/
theorem dual_moment_bound {n : ℕ} (A : Parameters n) (B : Block n)
    (dStar b : ℕ) (hb : 0 < b)
    (D : ∀ N, DualTest B (divisorWeight A N B))
    (hD : ∀ N, (D N).dimension ≤ dStar)
    (hgood : DualTestFamilyGood A D) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      dualWeightedMoment A N B (D N) b ≤
        2 * (dualMomentConstant dStar) ^ b + ε := by
  sorry

/-- §5, Lemma `lem:dual-pseudorandomness`, clipping conclusion (lines 80–82, 177–189).
Every fixed weighted `L^p` clipping error tends to zero, and clipping each factor preserves the
orthogonality of every fixed product. -/
theorem dual_clipping_transfer {n b : ℕ} (A : Parameters n) (B : Block n)
    (dStar : ℕ) (K : ℝ) (hK : dualMomentConstant dStar < K)
    (D : ∀ N, Fin b → DualTest B (divisorWeight A N B))
    (hD : ∀ N q, (D N q).dimension ≤ dStar)
    (hgood : ∀ q, DualTestFamilyGood A (fun N => D N q)) :
    (∀ q p, 0 < p → tendsToZeroAtTop (fun N =>
      dualClippingMoment A N B (D N q) K p)) ∧
    tendsToZeroAtTop (fun N => |∫ y,
      (divisorWeight A N B y - 1) *
        ∏ q, clipTest K ((D N q).value y) ∂pivotLaw A N B.1|) := by
  sorry

/-- Main numbered lemma `lem:dual-pseudorandomness`, §5, lines 68–190. -/
theorem dual_pseudorandomness {n : ℕ} (A : Parameters n) (B : Block n)
    (dStar : ℕ) :
    (∀ b : ℕ,
      ∀ D : ∀ N, Fin b → DualTest B (divisorWeight A N B),
        (∀ N q, (D N q).dimension ≤ dStar) →
        (∀ q, DualTestFamilyGood A (fun N => D N q)) →
          tendsToZeroAtTop (fun N => |dualProductPairing A B N (D N)|)) ∧
    (∀ b : ℕ, 0 < b →
      ∀ D : ∀ N, DualTest B (divisorWeight A N B),
        (∀ N, (D N).dimension ≤ dStar) →
        DualTestFamilyGood A D →
          ∀ ε > 0, ∀ᶠ N in atTop,
            dualWeightedMoment A N B (D N) b ≤
              2 * (dualMomentConstant dStar) ^ b + ε) ∧
    (∀ (b : ℕ) (K : ℝ), dualMomentConstant dStar < K →
      ∀ D : ∀ N, Fin b → DualTest B (divisorWeight A N B),
        (∀ N q, (D N q).dimension ≤ dStar) →
        (∀ q, DualTestFamilyGood A (fun N => D N q)) →
          tendsToZeroAtTop (fun N => abs (∫ y,
            (divisorWeight A N B y - 1) *
              (∏ q, clipTest K ((D N q).value y)) ∂pivotLaw A N B.1))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b D hD hgood
    exact dual_products_orthogonal A B dStar D hD hgood
  · intro b hb D hD hgood ε hε
    exact dual_moment_bound A B dStar b hb D hD hgood ε hε
  · intro b K hK D hD hgood
    exact (dual_clipping_transfer A B dStar K hK D hD hgood).2

/-- Pairing in (eq:prediction-dense-approximation). -/
noncomputable def denseModelPairing {n r : ℕ} (A : Parameters n)
    (D : InputData n r) (N : ℕ) (B : Block n) (a : ℚ) (c : Fin r)
    (F : DenseModelFamily n r) (T : DualTest B (divisorWeight A N B)) : ℝ :=
  ∫ y, (rho A D N B a c y - F N B a c y) * T.value y ∂pivotLaw A N B.1

/-- Finite-support minimax identity from the bounded dense-model proof, §5, lines 213–226. -/
theorem finite_dense_model_minimax {X : Type} [Fintype X]
    (μ : X → ℝ) (ρ : X → ℝ) (T : Set (X → ℝ))
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hcompact : IsCompact T) (hconvex : Convex ℝ T) (hne : T.Nonempty) :
    sInf (Set.range fun f : X → Set.Icc (0 : ℝ) 1 =>
      sSup (Set.range fun g : T => ∑ x, μ x * (ρ x - (f x : ℝ)) * g.1 x)) =
    sSup (Set.range fun g : T =>
      ∑ x, μ x * (ρ x * g.1 x - max (g.1 x) 0)) := by
  sorry

/-- The polynomial positive-part/separation claim used after minimax in Proposition
`prop:dense-model`, §5, lines 228–238. -/
theorem dense_model_polynomial_separation {X : Type} [Fintype X]
    (μ ν : X → ℝ) (G : X → ℝ) (K δ : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hK : 0 < K) (hG : ∀ x, |G x| ≤ K) (hδ : 0 < δ)
    (P : Polynomial ℝ) (hP : ∀ t ∈ Set.Icc (-K) K,
      |P.eval t - max t 0| ≤ δ) :
    |∑ x, μ x * (ν x - 1) * max (G x) 0 -
      ∑ x, μ x * (ν x - 1) * P.eval (G x)| ≤
      δ * ∑ x, μ x * (1 + ν x) := by
  sorry

/-- A fixed finite list of dual tests and a fixed tolerance admit bounded models on every finite
stage; the common finite support is the support of the harmonic pivot law. -/
theorem dense_model_finite_stage {n r : ℕ} (A : Parameters n) (D : InputData n r)
    (q dStar : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : DenseModelFamily n r, IsDenseModelFamily F ∧
      ∀ J0 : ℕ, J0 ≤ q → ∀ B : Block n, ∀ a ∈ D.multipliers, ∀ c : Fin r,
      ∀ T : ∀ N, DualTest B (divisorWeight A N B),
        (∀ N, (T N).J0 = J0 ∧ (T N).dimension ≤ dStar) →
        DualTestFamilyGood A T →
        ∀ᶠ N in atTop, |denseModelPairing A D N B a c F (T N)| ≤ ε := by
  sorry

/-- Slow diagonalization of the fixed-stage dense models, with no estimate for moments growing
with `N`; this is the diagonal step at §5, lines 240–247. -/
theorem dense_model_slow_diagonal {n r : ℕ} (A : Parameters n) (D : InputData n r)
    (stage : ℕ → DenseModelFamily n r) (hstage : ∀ q, IsDenseModelFamily (stage q))
    (stageThreshold : ℕ → ℕ)
    (hfinite : ∀ q, ∀ J0 ≤ q, ∀ B : Block n, ∀ a ∈ D.multipliers, ∀ c : Fin r,
      ∀ T : ∀ N, DualTest B (divisorWeight A N B),
        (∀ N, (T N).J0 = J0 ∧ (T N).dimension ≤ q) →
        DualTestFamilyGood A T →
        ∀ᶠ N in atTop, stageThreshold q ≤ N →
          |denseModelPairing A D N B a c (stage q) (T N)| ≤ (1 / (q + 1 : ℝ))) :
    ∃ F : DenseModelFamily n r, IsDenseModelFamily F ∧
      ∀ J0 dStar : ℕ, ∀ B : Block n, ∀ a ∈ D.multipliers, ∀ c : Fin r,
      ∀ T : ∀ N, DualTest B (divisorWeight A N B),
        (∀ N, (T N).J0 = J0 ∧ (T N).dimension ≤ dStar) →
        DualTestFamilyGood A T →
        tendsToZeroAtTop (fun N => |denseModelPairing A D N B a c F (T N)|) := by
  sorry

/-- Proposition `prop:dense-model`, §5, lines 199–248: a single family of `[0,1]`-valued
models works for every fixed `J₀`, every fixed cube template (uniformly bounded dimension), and
every dual test input at that block. -/
theorem bounded_dense_models {n r : ℕ} (A : Parameters n) (D : InputData n r) :
    ∃ F : DenseModelFamily n r, IsDenseModelFamily F ∧
      ∀ J0 dStar : ℕ, ∀ B : Block n, ∀ a ∈ D.multipliers, ∀ c : Fin r,
      ∀ T : ∀ N, DualTest B (divisorWeight A N B),
        (∀ N, (T N).J0 = J0 ∧ (T N).dimension ≤ dStar) →
        DualTestFamilyGood A T →
        tendsToZeroAtTop (fun N => |denseModelPairing A D N B a c F (T N)|) := by
  sorry

/-- The boundary strip discarded when a dual cube crosses a piece boundary. The three clauses
cover internal interval endpoints and the two cutoff cells of `[X_i,X_i²)`. -/
noncomputable def isPredictionBoundary {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (R : ℕ → ℕ) (J0 s : ℕ) (y : ℤ) : Prop :=
  let width : ℤ := (((s + 1) * R N) / J0 : ℕ)
  (A.X N i : ℤ) ≤ y ∧ y < (A.X N i : ℤ) ^ 2 ∧
    (|y - (A.X N i : ℤ)| ≤ width ∨
      |y - (A.X N i : ℤ) ^ 2| ≤ width ∨
      ∃ k : ℤ, |y - k * (R N : ℤ)| ≤ width)

/-- Weighted boundary estimate (eq:prediction-weighted-boundary), §5, lines 325–342. -/
theorem weighted_boundary_estimate {n : ℕ} (A : Parameters n) (B : Block n)
    (R : ℕ → ℕ) (J0 s : ℕ) (hJ0 : 0 < J0) (i : Fin n) (hi : i = B.1) :
    ∃ C_s : ℝ, 0 ≤ C_s ∧ ∀ ε > 0, ∀ᶠ N in atTop,
      ∫ y, (1 + divisorWeight A N B y) *
        (if isPredictionBoundary A N i R J0 s y then 1 else 0)
        ∂pivotLaw A N i ≤ C_s / J0 + ε := by
  sorry

/-- Lemma `lem:nilsequence-testing`, §5, lines 275–353. OAI's `ModelsSystem` records exactly
the finite nilmanifold list, uniform Lipschitz bounds, and piecewise orbit structure. The statement
for bounded real observables follows by affine normalization to `[0,1]`. -/
theorem nilsequence_testing {n r s s' : ℕ} (A : Parameters n) (D : InputData n r)
    (Fden : DenseModelFamily n r) (hFden : IsDenseModelFamily Fden)
    (B : Block n) (a : ℚ) (c : Fin r)
    (G : Menu s') (S : ModelsSystem A D.multipliers r G) :
    tendsToZeroAtTop (fun N => |∫ y,
      (rho A D N B a c y - Fden N B a c y) *
        S.model N B a c y ∂pivotLaw A N B.1|) := by
  sorry

end HindmanSumsProducts.Prediction
