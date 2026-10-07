import HindmanSumsProducts.InverseBridge.Menu

/-!
Final assembly of the cyclic inverse theorem into the fixed charted menu (IB.d1).
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3 OAI.SourceChartedMenu OAI.SourceMenuLiteral
open scoped NNReal BigOperators


private noncomputable def inverseInputBudget (δ : ℝ) : ℝ := max 2 (-Real.log δ)

/-- The cyclic inverse theorem supplies a concrete native model with an exponential
correlation lower bound at the complexity scale used by the bridge. -/
private theorem exists_inverse_native_model (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (v : ZMod N → ℝ),
      (∀ x, |v x| ≤ 1) → δ ≤ gowersNorm t (fun x => (v x : ℂ)) →
      ∃ g : ZMod N → ℂ,
        ∃ M : NativeCyclicModel (t - 1) N
          ((inverseInputBudget δ + C) ^ C) g,
          Real.exp (-((inverseInputBudget δ + C) ^ C)) ≤
            ‖𝔼 x, (v x : ℂ) * star (g x)‖ := by
  obtain ⟨C, hC, hinverse⟩ := exists_cyclicNativeInverse_positive (t - 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro N hN v hv hG
  let p := inverseInputBudget δ
  have hp : 2 ≤ p := by
    dsimp [p, inverseInputBudget]
    exact le_max_left _ _
  have hpδ : Real.exp (-p) ≤ δ := by
    have hlog : -p ≤ Real.log δ := by
      have hbudget : -Real.log δ ≤ p := by
        dsimp [p, inverseInputBudget]
        exact le_max_right _ _
      linarith
    calc
      Real.exp (-p) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hlog
      _ = δ := Real.exp_log hδ
  have hvComplex : ∀ x, ‖(v x : ℂ)‖ ≤ 1 := by
    intro x
    simpa [Complex.norm_real, Real.norm_eq_abs] using hv x
  have hG' : Real.exp (-p) ≤ gowersNorm ((t - 1) + 1) (fun x => (v x : ℂ)) := by
    have hdegree : (t - 1) + 1 = t := Nat.sub_add_cancel (by omega)
    rw [hdegree]
    exact hpδ.trans hG
  obtain ⟨g, hg, hcorr⟩ :=
    hinverse (N := N) (p := p) hp (fun x => (v x : ℂ)) hvComplex hG'
  have hmodel : Nonempty (NativeCyclicModel (t - 1) N ((p + C) ^ C) g) := by
    simpa [nativeCyclicFunctions] using hg
  have M : NativeCyclicModel (t - 1) N ((p + C) ^ C) g := Classical.choice hmodel
  refine ⟨g, ?_, ?_⟩
  · simpa [p, inverseInputBudget] using M
  · simpa [p, inverseInputBudget] using hcorr

private theorem expect_real_rotated (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    (g : ZMod N → ℂ) (u : ℂ) :
    𝔼 x, v x * (u * g x).re =
      (star u * 𝔼 x, (v x : ℂ) * star (g x)).re := by
  calc
    𝔼 x, v x * (u * g x).re =
        𝔼 x, (star u * ((v x : ℂ) * star (g x))).re := by
          apply Finset.expect_congr rfl
          intro x _
          simp [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
    _ = Complex.reCLM (𝔼 x, star u * ((v x : ℂ) * star (g x))) := by
          symm
          exact map_expect (Complex.reCLM.restrictScalars ℚ≥0) _ _
    _ = Complex.reCLM (star u * 𝔼 x, (v x : ℂ) * star (g x)) := by
          rw [Finset.mul_expect]
    _ = (star u * 𝔼 x, (v x : ℂ) * star (g x)).re := rfl

private theorem exists_unit_phase (z : ℂ) (hz : 0 < ‖z‖) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ (star u * z).re = ‖z‖ := by
  let u : ℂ := z / (‖z‖ : ℂ)
  have hden : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
    exact div_self (ne_of_gt hz)
  have huRotate : star u * z = (‖z‖ : ℂ) := by
    dsimp [u]
    change star (z / (‖z‖ : ℂ)) * z = (‖z‖ : ℂ)
    have hzmul : star z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.conj_mul']
    calc
      star (z / (‖z‖ : ℂ)) * z = (star z / (‖z‖ : ℂ)) * z := by
        rw [star_div₀]
        simp
      _ = (star z * z) / (‖z‖ : ℂ) := by ring
      _ = (‖z‖ : ℂ) ^ 2 / (‖z‖ : ℂ) := by rw [hzmul]
      _ = (‖z‖ : ℂ) := by field_simp [hden]
  refine ⟨u, hu, ?_⟩
  rw [huRotate]
  simp

private theorem exists_rotated_real_correlation (N : ℕ) [NeZero N]
    (v : ZMod N → ℝ) (g : ZMod N → ℂ) (c : ℝ) (hc : 0 < c)
    (hcor : c ≤ ‖𝔼 x, (v x : ℂ) * star (g x)‖) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ c ≤ 𝔼 x, v x * (u * g x).re := by
  let z : ℂ := 𝔼 x, (v x : ℂ) * star (g x)
  have hcz : c ≤ ‖z‖ := by simpa [z] using hcor
  have hz : 0 < ‖z‖ := lt_of_lt_of_le hc hcz
  obtain ⟨u, hu, hphase⟩ := exists_unit_phase z hz
  refine ⟨u, hu, ?_⟩
  have hrot : 𝔼 x, v x * (u * g x).re = (star u * z).re := by
    simpa [z] using expect_real_rotated N v g u
  rw [hrot, hphase]
  exact hcz

private theorem affine_rotated_expectation (N : ℕ) [NeZero N]
    (v : ZMod N → ℝ) (g : ZMod N → ℂ) (u : ℂ) :
    𝔼 x, v x * (2 * ((1 + (u * g x).re) / 2) - 1) =
      𝔼 x, v x * (u * g x).re := by
  apply Finset.expect_congr rfl
  intro x _
  ring

private theorem exists_affine_rotated_correlation (N : ℕ) [NeZero N]
    (v : ZMod N → ℝ) (g : ZMod N → ℂ) (c : ℝ) (hc : 0 < c)
    (hcor : c ≤ ‖𝔼 x, (v x : ℂ) * star (g x)‖) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      c ≤ 𝔼 x, v x * (2 * ((1 + (u * g x).re) / 2) - 1) := by
  obtain ⟨u, hu, hrot⟩ := exists_rotated_real_correlation N v g c hc hcor
  refine ⟨u, hu, ?_⟩
  rw [affine_rotated_expectation]
  exact hrot


/-- IB.d1: assemble the cyclic polynomial inverse theorem, finite canonical list,
linearization, and real observable rotation into the frozen consumer statement. -/
theorem inverse_bridge_assembly (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔐 : Menu (2 * (t - 1))) (K : ℝ≥0) (c : ℝ), 0 < 𝔐.size ∧ 0 < c ∧
      ∀ (N : ℕ) [NeZero N] (v : ZMod N → ℝ), (∀ x, |v x| ≤ 1) →
        δ ≤ gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece 𝔐 K,
          c ≤ 𝔼 x, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1) := by
  obtain ⟨C, hC, hmodels⟩ := exists_inverse_native_model t ht δ hδ
  let K₀ : ℝ := (inverseInputBudget δ + C) ^ C
  have hK₀ : 0 ≤ K₀ := by
    dsimp [K₀, inverseInputBudget]
    positivity
  obtain ⟨𝔐, K, hM, hrep⟩ := exists_bridgeMenu (t - 1) K₀ hK₀
  refine ⟨𝔐, K, Real.exp (-K₀), hM, Real.exp_pos _, ?_⟩
  intro N hN v hv hG
  obtain ⟨g, F, hcor⟩ := hmodels N v hv hG
  let z : ℂ := 𝔼 x, (v x : ℂ) * star (g x)
  have hcz : Real.exp (-K₀) ≤ ‖z‖ := by simpa [z, K₀] using hcor
  have hz : 0 < ‖z‖ := lt_of_lt_of_le (Real.exp_pos _) hcz
  obtain ⟨u, hu, hphase⟩ := exists_unit_phase z hz
  letI := F.lie
  letI := F.algebra
  letI := F.topology
  letI := F.topologicalAdd
  letI := F.continuousSMul
  letI := F.hausdorff
  obtain ⟨P, hP⟩ := hrep F.model F.test F.norm F.complexity u hu
  have hPcyc (x : ZMod N) :
      2 * P.eval ((x.val : ℕ) : ℤ) - 1 = (u * g x).re := by
    rw [hP ((x.val : ℕ) : ℤ), F.eval x]
    rfl
  refine ⟨P, ?_⟩
  calc
    Real.exp (-K₀) ≤ ‖z‖ := hcz
    _ = 𝔼 x, v x * (u * g x).re := by
      symm
      rw [expect_real_rotated]
      simpa [z] using hphase
    _ = 𝔼 x, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [hPcyc x]

end HindmanSumsProducts.InverseBridge
