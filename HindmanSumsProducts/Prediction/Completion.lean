import HindmanSumsProducts.Prediction.Projections

open scoped BigOperators NNReal Topology
open MeasureTheory Filter Classical

namespace HindmanSumsProducts.Prediction

/-- Number `q_m=2^m-m-1` of nonsingleton factors in each weighted count. -/
def nonsingletonFactorCount (m : ℕ) : ℕ := 2 ^ m - m - 1

/-- Coarse dense-model replacement in the divisor-weighted count. -/
noncomputable def denseModelWeightedCount {n m r : ℕ} (A : Parameters n)
    (D : InputData n r) (N : ℕ) (C : BlockChain n m) (b : Scale n)
    (c : Fin r) (F : DenseModelFamily n r) : ℝ :=
  ∫ z, productMask A D N C b c z *
      (∏ d : Fin m, divisorWeight A N (C.block d) (z d)) *
      (∏ J ∈ nonemptySubsets m,
        if hcard : 2 ≤ J.card then
          let hJ : J.Nonempty := Finset.card_pos.mp (by omega)
          let d := subsetLast J hJ
          let L := sumForm (fun k => blockCoefficient A N (C.block k)
            (blockProduct b (C.block k).set)) z J hJ
          F N (C.block d) (blockProduct b (C.block d).set) c (Int.floor L)
        else 1)
    ∂Measure.pi (fun d : Fin m => pivotLaw A N (C.block d).1)

/-- Count obtained after replacing each nonsingleton color factor by its OAI piecewise model,
while retaining the center divisor weights and product masks. -/
noncomputable def pivotModelCount {n m r s : ℕ} (A : Parameters n)
    (D : InputData n r) (N : ℕ) (C : BlockChain n m) (b : Scale n)
    (c : Fin r) (F : Menu s) (S : ModelsSystem A D.multipliers r F) : ℝ :=
  ∫ z, productMask A D N C b c z *
      (∏ d : Fin m, divisorWeight A N (C.block d) (z d)) *
      (∏ J ∈ nonemptySubsets m,
        if hcard : 2 ≤ J.card then
          let hJ : J.Nonempty := Finset.card_pos.mp (by omega)
          let d := subsetLast J hJ
          let L := sumForm (fun k => blockCoefficient A N (C.block k)
            (blockProduct b (C.block k).set)) z J hJ
          S.model N (C.block d) (blockProduct b (C.block d).set) c (Int.floor L)
        else 1)
    ∂Measure.pi (fun d : Fin m => pivotLaw A N (C.block d).1)

/-- The parameter `κ(d,J₀,γ)` in Lemma `lem:subgroup-inverse`, chosen independently of every
master-scale, gap, cutoff, and cell-probability parameter. -/
noncomputable def subgroupCubeThreshold (d J0 : ℕ) (hJ0 : 0 < J0)
    (γ : ℝ) (hγ : 0 < γ) : ℝ :=
  Classical.choose (subgroup_cube_to_fine_projection d J0 hJ0 γ hγ)

theorem subgroupCubeThreshold_pos (d J0 : ℕ) (hJ0 : 0 < J0)
    (γ : ℝ) (hγ : 0 < γ) : 0 < subgroupCubeThreshold d J0 hJ0 γ hγ :=
  (Classical.choose_spec (subgroup_cube_to_fine_projection d J0 hJ0 γ hγ)).1

/-- Choice order for the final proof, §5.4, lines 694–719 and 750–761: first `ζ`, then `J₀`,
then the finitely many subgroup thresholds, then `eps<η`, all before selecting the master count. -/
theorem prediction_error_parameter_choice {m : ℕ} (hm : 2 ≤ m)
    (C : CorrelationTemplateFamily m) (η : ℝ) (hη : 0 < η) :
    ∃ ζ : ℝ, ∃ hζ : 0 < ζ, ∃ J0 : ℕ, ∃ hJ0 : 0 < J0,
      (∀ t : C.Template,
        (C.instanceFor t).C * (2 * ζ) ^ (C.instanceFor t).theta <
          η / (2 * nonsingletonFactorCount m)) ∧
      ∃ eps : ℝ, 0 < eps ∧ eps < η ∧
        ∀ d, d < C.orderBound →
          2 * eps < subgroupCubeThreshold d J0 hJ0 ζ hζ := by
  sorry

/-- The bounded dense models replace all nonsingleton color weights in a fixed chain count;
product masks and center weights remain unchanged. This is the consequence after
`prop:dense-model`, §5, lines 250–261. -/
theorem replace_color_weights_by_dense_models {n m r : ℕ}
    (A : Parameters n) (D : InputData n r) (F : DenseModelFamily n r)
    (hF : IsDenseModelFamily F) (C : BlockChain n m)
    (b : Scale n) (hb : b ∈ D.scales) (c : Fin r) :
    tendsToZeroAtTop (fun N =>
      |weightedCount A D N C b c - denseModelWeightedCount A D N C b c F|) := by
  sorry

/-- Projection control, the subgroup-cube lemma, and correlation testing telescope the dense
models to the selected OAI piecewise models. -/
theorem replace_dense_models_by_piecewise_models {n m r s : ℕ}
    (A : Parameters n) (D : InputData n r) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (F : DenseModelFamily n r) (hF : IsDenseModelFamily F)
    (G : Menu s) (S : ModelsSystem A D.multipliers r G)
    (C : BlockChain n m) (b : Scale n) (hb : b ∈ D.scales) (c : Fin r)
    (η : ℝ) (hη : 0 < η) :
    UltrafilterUpperBound U
      (fun N => |denseModelWeightedCount A D N C b c F -
        pivotModelCount A D N C b c G S|) (η / 2) := by
  sorry

/-- The last product-law replacement in the count comparison, §5.4, lines 768–775. -/
theorem pivot_model_count_to_raw_model_count {n m r s : ℕ}
    (A : Parameters n) (D : InputData n r) (G : Menu s)
    (S : ModelsSystem A D.multipliers r G) (C : BlockChain n m)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C.block i).set (C.block j).set)
    (b : Scale n) (hb : b ∈ D.scales) (c : Fin r) :
    tendsToZeroAtTop (fun N =>
      |pivotModelCount A D N C b c G S - modelCount A D N C b c G S|) := by
  sorry

/-- Calibration from nilsequence testing and the bounded distribution replacement, §5.4,
lines 721–740. -/
theorem calibration_from_nilsequence_testing {n r s : ℕ}
    (A : Parameters n) (D : InputData n r) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (G : Menu s) (S : ModelsSystem A D.multipliers r G)
    (B : Block n) (a : ℚ) (ha : a ∈ D.multipliers) (c : Fin r)
    (τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) :
    UltrafilterUpperBound U
      (fun N => calibrationProbability A D N τ B a c G S) (3 * τ + η) := by
  sorry

/-- Build the common OAI admissible parameters and OAI `Menu`/`ModelsSystem` after the choices
`ζ,J₀,eps,N`, then prove both conclusions (eq:prediction-calibration) and
(eq:prediction-counting), §5.4, lines 685–783. -/
theorem prediction_completion {m n r : ℕ} (hm : 2 ≤ m)
    (D : InputData n r) (τ η : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1 / 4) (hη : 0 < η)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    ∃ s : ℕ, 3 ≤ s ∧
      (∀ d, d < (Classical.choice (correlation_templates_exist m hm)).orderBound →
        s + 1 ≥ 2 * (2 ^ d) - 1) ∧
      PredictionOutput (n := n) (m := m) (r := r) (s := s) U D τ η := by
  sorry

/-- Calibration half of the Prediction Principle completion (eq:prediction-calibration),
stated with OpenAI's admissible parameters and piecewise models. -/
theorem prediction_calibration_conclusion {m n r : ℕ} (hm : 2 ≤ m)
    (D : InputData n r) (τ η : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1 / 4) (hη : 0 < η)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    ∃ s : ℕ, 3 ≤ s ∧
      (∀ d, d < (Classical.choice (correlation_templates_exist m hm)).orderBound →
        s + 1 ≥ 2 * (2 ^ d) - 1) ∧
      ∃ A : Parameters n, ∃ G : Menu s, ∃ S : ModelsSystem A D.multipliers r G,
        CalibrationConclusion U D τ η A G S := by
  rcases prediction_completion hm D τ η hτ0 hτ1 hη U hU with
    ⟨s, hs, hstep, hout⟩
  rcases hout with ⟨A, G, S, hcal, hcount⟩
  exact ⟨s, hs, hstep, A, G, S, hcal⟩

/-- Counting half of the Prediction Principle completion (eq:prediction-counting), for all
OAI block chains, scale labels, and colors. -/
theorem prediction_counting_conclusion {m n r : ℕ} (hm : 2 ≤ m)
    (D : InputData n r) (τ η : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1 / 4) (hη : 0 < η)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    ∃ s : ℕ, 3 ≤ s ∧
      (∀ d, d < (Classical.choice (correlation_templates_exist m hm)).orderBound →
        s + 1 ≥ 2 * (2 ^ d) - 1) ∧
      ∃ A : Parameters n, ∃ G : Menu s, ∃ S : ModelsSystem A D.multipliers r G,
        CountingConclusion m U D η A G S := by
  rcases prediction_completion hm D τ η hτ0 hτ1 hη U hU with
    ⟨s, hs, hstep, hout⟩
  rcases hout with ⟨A, G, S, hcal, hcount⟩
  exact ⟨s, hs, hstep, A, G, S, hcount⟩

end HindmanSumsProducts.Prediction
