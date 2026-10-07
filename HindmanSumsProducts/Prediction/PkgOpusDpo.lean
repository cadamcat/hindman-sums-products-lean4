import HindmanSumsProducts.Prediction.PkgB2

/-!
# Lead helpers for `dual_products_orthogonal` (lane opus-dpo)

Shared definitions for the part lemmas stated above `dual_products_orthogonal` in `Results.lean`,
built on the `PkgB2` state machinery (replicated prime slots, occurrence rows, mixed base law):

* `opus_dpo_average`: the normalized joint average of `pkgB2_stateAverage`, for an arbitrary
  integrand (joint good prime event, `pkgB2_baseMass`).
* `opus_dpo_prefactor`: the Cauchy–Schwarz prefactor `E Ω`, `Ω = ∏_{copies of row s} (1 + ν)`.
* `opus_dpo_zeroTranslations`, `opus_dpo_untranslatedAverage`: the stage-`∅` state with every
  translation coordinate set to zero (the replica expansion of the original pairing).
* `opus_dpo_iterate`: the finite iteration of `|a_j|² ≤ C_j |a_{j+1}|`.
-/

namespace HindmanSumsProducts
namespace Prediction

open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

noncomputable section

/-- Normalized joint average over the replica prime law, conditioned on the joint good event, and
the mixed base-coordinate law `pkgB2_baseMass`, of an arbitrary integrand `F p x`.  This is the
averaging operator of `pkgB2_stateAverage`. -/
def opus_dpo_average {K sl b : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (F : (Fin (b * sl) → ℕ) → (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) → ℝ) : ℝ :=
  (independentPrimePoolProbability
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
    (pkgB2_goodPrimeEvent MS gap T hT N))⁻¹ *
  ∑' p : Fin (b * sl) → ℕ,
    independentPrimePoolMass
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p *
      (if pkgB2_goodPrimeEvent MS gap T hT N p then
        ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
          pkgB2_baseMass MS B T J0 gap hT N p x * F p x
       else 0)

/-- The Cauchy–Schwarz prefactor at stage `E` for the direction of the nonroot row `s`:
the normalized average of `Ω = ∏_{copies o of row s} (1 + ν(L_o))`.  It does not involve the
inputs. -/
def opus_dpo_prefactor {K sl b : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (s : pkgB2_Nonroot T) (N : ℕ) : ℝ :=
  opus_dpo_average MS B gap T J0 hT N fun p x =>
    ∏ o ∈ (Finset.univ.filter fun o : Fin (Fintype.card (pkgB2_Occurrence T E)) =>
        (pkgB2_occurrenceEnum T E o).1 = Sum.inr s),
      (1 + nu MS.core.parameters N B
        (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x))

/-- Set every translation coordinate (the `inr` part of `pkgB2_Coord`) to zero. -/
def opus_dpo_zeroTranslations {b : ℕ} (T : Fin b → CubeTemplate)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    Fin (Fintype.card (pkgB2_Coord T)) → ℤ :=
  fun i => Sum.elim (fun _ => x i) (fun _ => 0) (pkgB2_coordEnum T i)

/-- The stage-`∅` state before the translations are inserted: the integrand of
`pkgB2_stateAverage … ∅` evaluated with all translation coordinates zero. -/
def opus_dpo_untranslatedAverage {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) : ℝ :=
  opus_dpo_average MS B gap T J0 hT N fun p x =>
    pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p (opus_dpo_zeroTranslations T x)

/-- `pkgB2_stateAverage` is `opus_dpo_average` of the stage integrand. -/
theorem opus_dpo_stateAverage_eq {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (I : ∀ k, DualInput MS B (T k) N) :
    pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 E N I =
      opus_dpo_average MS B gap T J0 hT N
        (pkgB2_stateIntegrand MS B gap T hT J0 direction E N I) := by
  unfold pkgB2_stateAverage opus_dpo_average
  congr 1

/-- Downward iteration of `|a_j|² ≤ C_j |a_{j+1}|` from a uniformly small last term. -/
theorem opus_dpo_iterate {X : ℕ → Type*} (n : ℕ) (a : ℕ → (N : ℕ) → X N → ℝ)
    (hstep : ∀ j < n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ x : X N, |a j N x| ^ 2 ≤ C * |a (j + 1) N x|)
    (hlast : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x : X N, |a n N x| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x : X N, |a 0 N x| ≤ ε := by
  -- Downward induction: the claim at `n - m` for `m ≤ n`.
  suffices h : ∀ m ≤ n, ∀ ε > 0, ∀ᶠ N in atTop, ∀ x : X N, |a (n - m) N x| ≤ ε by
    simpa using h n le_rfl
  intro m
  induction m with
  | zero => intro _; simpa using hlast
  | succ m ih =>
    intro hm ε hε
    have hj : n - (m + 1) < n := by omega
    obtain ⟨C, hC, hCstep⟩ := hstep (n - (m + 1)) hj
    have hsucc : n - (m + 1) + 1 = n - m := by omega
    have hδ : 0 < ε ^ 2 / (C + 1) := by positivity
    filter_upwards [hCstep, ih (by omega) _ hδ] with N hN hsmall x
    have h1 := hN x
    rw [hsucc] at h1
    have h2 : C * |a (n - m) N x| ≤ C * (ε ^ 2 / (C + 1)) :=
      mul_le_mul_of_nonneg_left (hsmall x) hC
    have h3 : C * (ε ^ 2 / (C + 1)) ≤ ε ^ 2 := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg ε]
    have h4 : |a (n - (m + 1)) N x| ^ 2 ≤ ε ^ 2 := h1.trans (h2.trans h3)
    have h5 := sq_le_sq.mp h4
    simpa [abs_abs, abs_of_pos hε] using h5

end

end Prediction
end HindmanSumsProducts
