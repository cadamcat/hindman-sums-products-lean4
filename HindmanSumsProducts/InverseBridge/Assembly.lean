import HindmanSumsProducts.InverseBridge.Menu
import HindmanSumsProducts.InverseBridge.Assembly.AdjointExp

/-!
Final assembly of the cyclic inverse theorem into the fixed charted menu (IB.d1).
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3 OAI.SourceChartedMenu OAI.SourceMenuLiteral
open scoped NNReal BigOperators

local instance assemblyLineLieRing : LieRing Line := LieRing.ofAssociativeRing
local instance assemblyLineLieAlgebra : LieAlgebra ℚ Line := LieAlgebra.ofAssociativeAlgebra

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

private theorem bracket_Dhat_inl {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : OAI.Erdos3.NilpotentLieFiltration L s) (Q : Poly F) :
    ⁅Dhat F, LieAlgebra.SemiDirectSum.inl (shiftAction F) Q⁆ =
      LieAlgebra.SemiDirectSum.inl (shiftAction F) (shiftAction F 1 Q) := by
  simp [Dhat, LieAlgebra.SemiDirectSum.inr_eq_mk,
    LieAlgebra.SemiDirectSum.inl_eq_mk, LieAlgebra.SemiDirectSum.lie_eq_mk]

private theorem evLin_conjugation_shift {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : OAI.Erdos3.NilpotentLieFiltration L s) (hs : 0 < s)
    (c : ℚ) (m : ℤ) (Q : Poly F) :
    evLin F m (lieBCH (2 * s)
      (lieBCH (2 * s) (c • Dhat F)
        (LieAlgebra.SemiDirectSum.inl (shiftAction F) Q))
      (-(c • Dhat F))) =
      VectorPolynomial.eval (fun _ : Unit => (m : ℚ) + c)
        (Q : VectorPolynomial Unit ℚ L) := by
  let ι : Poly F →ₗ⁅ℚ⁆ Lin F := LieAlgebra.SemiDirectSum.inl (shiftAction F)
  let d : Poly F →ₗ[ℚ] Poly F := shiftAction F 1
  let adc : Module.End ℚ (Lin F) := LieAlgebra.ad ℚ (Lin F) (c • Dhat F)
  have hbracket (R : Poly F) : adc (ι R) = ι (c • d R) := by
    change ⁅c • Dhat F, ι R⁆ = ι (c • d R)
    rw [smul_lie, bracket_Dhat_inl]
    simp [ι, d]
  have hpow (j : ℕ) : (adc ^ j) (ι Q) = c ^ j • ι (d^[j] (Q)) := by
    induction j with
    | zero => simp [adc, ι]
    | succ j ih =>
      conv_lhs => rw [pow_succ']
      simp only [Module.End.mul_apply]
      change ⁅c • Dhat F, (adc ^ j) (ι Q)⁆ =
        c ^ (j + 1) • ι (d^[j + 1] (Q))
      calc
        ⁅c • Dhat F, (adc ^ j) (ι Q)⁆ = adc (c ^ j • ι (d^[j] (Q))) := by
          change adc ((adc ^ j) (ι Q)) = adc (c ^ j • ι (d^[j] (Q)))
          rw [ih]
        _ = c ^ j • adc (ι (d^[j] (Q))) := map_smul adc _ _
        _ = c ^ j • ι (c • d (d^[j] (Q))) := by rw [hbracket]
        _ = c ^ j • (c • ι (d (d^[j] (Q)))) := by
          rw [map_smul]
        _ = (c ^ j * c) • ι (d (d^[j] (Q))) := by rw [smul_smul]
        _ = c ^ (j + 1) • ι (d (d^[j] (Q))) := by
          exact congrArg (fun r : ℚ => r • ι (d (d^[j] (Q)))) (pow_succ c j).symm
        _ = c ^ (j + 1) • ι (d^[j + 1] (Q)) := by
          rw [Function.iterate_succ_apply']
  have hd : shiftAction F 1 = hD F := by
    simpa [shiftAction] using (Classical.choose_spec (exists_shiftAction F) 1)
  have hiter (j : ℕ) :
      (d^[j] (Q) : VectorPolynomial Unit ℚ L) =
        polyDeriv^[j] (Q : VectorPolynomial Unit ℚ L) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      change (shiftAction F 1 (d^[j] (Q)) : VectorPolynomial Unit ℚ L) = _
      rw [hd, hD_apply, ih, Function.iterate_succ_apply']
  have hev (R : Poly F) : evLin F m (ι R) =
      VectorPolynomial.eval (fun _ : Unit => (m : ℚ)) (R : VectorPolynomial Unit ℚ L) := by
    simp [evLin, ι, LieAlgebra.SemiDirectSum.projl_inl_apply]
  have hQadapt : F.Adapted (fun _ : Unit => 1) (Q : VectorPolynomial Unit ℚ L) := by
    apply (F.mem_adaptedSubmodule (fun _ : Unit => 1) _).mp
    change (Q : VectorPolynomial Unit ℚ L) ∈ F.adaptedLieSubalgebra (fun _ : Unit => 1)
    exact Q.property
  have hdegree (j : ℕ) (hj : 2 * s < j) :
      VectorPolynomial.coefficients (Q : VectorPolynomial Unit ℚ L)
          (Finsupp.single () j) = 0 := by
    exact F.adapted_degreeLE (fun _ : Unit => 1) hQadapt (Finsupp.single () j)
      (by simpa [Finsupp.weight_single] using (show s < j by omega))
  have hTaylor := polynomial_translation_taylor (2 * s)
    (Q : VectorPolynomial Unit ℚ L) hdegree c
  have hsum (j : ℕ) :
      evLin F m (((j.factorial : ℚ)⁻¹) • ((adc ^ j) (ι Q))) =
        VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
          ((c ^ j / (j.factorial : ℚ)) •
            polyDeriv^[j] (Q : VectorPolynomial Unit ℚ L)) := by
    simp only [map_smul, hpow j, map_smul, hev, hiter j]
    rw [smul_smul]
    congr 1
    ring
  rw [AssemblyAdjoint.lieBCH_conj_eq_exp_ad_aux
    ((weightFiltration F hs).lowerCentralSeries_eq_bot)]
  calc
    evLin F m (∑ j ∈ Finset.range (2 * s + 1),
        ((j.factorial : ℚ)⁻¹) • ((adc ^ j) (ι Q))) =
      ∑ j ∈ Finset.range (2 * s + 1),
        VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
          ((c ^ j / (j.factorial : ℚ)) •
            polyDeriv^[j] (Q : VectorPolynomial Unit ℚ L)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j hj
          exact hsum j
    _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
        (∑ j ∈ Finset.range (2 * s + 1),
          (c ^ j / (j.factorial : ℚ)) •
            polyDeriv^[j] (Q : VectorPolynomial Unit ℚ L)) := by rw [map_sum]
    _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
        (VectorPolynomial.translate (fun _ : Unit => c) Q) := by rw [hTaylor]
    _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ) + c) Q := by
          rw [VectorPolynomial.eval_translate]

/-- IB.d1: assemble the cyclic polynomial inverse theorem, finite canonical list,
linearization, and real observable rotation into the frozen consumer statement. -/
theorem inverse_bridge_assembly (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔐 : Menu (2 * (t - 1))) (K : ℝ≥0) (c : ℝ), 0 < 𝔐.size ∧ 0 < c ∧
      ∀ (N : ℕ) [NeZero N] (v : ZMod N → ℝ), (∀ x, |v x| ≤ 1) →
        δ ≤ gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece 𝔐 K,
          c ≤ 𝔼 x, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1) := by
  sorry

end HindmanSumsProducts.InverseBridge
