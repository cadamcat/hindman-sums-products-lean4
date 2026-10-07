import HindmanSumsProducts.Prediction.Projections
import HindmanSumsProducts.Concatenation
import HindmanSumsProducts.Prediction.PkgG
import HindmanSumsProducts.Prediction.Pkgg2
import HindmanSumsProducts.Prediction.PkgG3

/-!
# Subgroup cubes and the inverse theorem (§5.3, `05_prediction.tex` 432–683)

Lemma `lem:subgroup-inverse` with two replacements:

* Tao–Ziegler's Bessel inequality is replaced by `SubgroupBox.combine_subgroups`
  (`Concatenation.lean`): the global norm has degree `t = 2^k − 1` with `k = 2^d`
  (CONCATENATION.md §0).
* The inverse theorem is `InverseBridge.cyclic_inverse_menu` (cyclic, step `2(t − 1)`); the
  cyclic-to-interval periodization of 05:597–642 is deleted.

Hence the hypothesis `2(2^d) − 2 ≤ s` of 05:494 becomes `inverseStep d = 2(2^{2^d} − 2) ≤ s`.

The finite cell system `𝒳_l` (05:526–536): the `R_l`-intervals `[kR_l, (k+1)R_l)` inside
`[X_i, X_i²)`, split by residues `ρ` modulo `M`; the cell `(k, ρ)` has the `q_l = R_l/M` points
`kR_l + ρ + Mx`, `x ∈ [0, q_l)`, identified with `G_l = ℤ/q_lℤ`, and probability proportional to
its `μ_i`-mass.
-/

open scoped BigOperators NNReal Topology
open Filter Finset

namespace HindmanSumsProducts.Prediction

noncomputable section

/-! ### Changed parameters -/

/-- Concatenation and inverse-theorem degree `t = 2^k − 1`, `k = 2^d` (CONCATENATION.md §0). -/
def inverseDegree (d : ℕ) : ℕ := 2 ^ (2 ^ d) - 1

/-- Step of the inverse-theorem nilsequences at degree `t = inverseDegree d`: `2(t − 1)`
(INVERSE-BRIDGE.md §0: the step doubles under linearization). -/
def inverseStep (d : ℕ) : ℕ := 2 * (inverseDegree d - 1)

/-- The step `s(m)` of (eq:prediction-step-choice), with the changed parameters:
`s(m) = max(3, 2(t_max(m) − 1))`, `t_max(m) = 2^{2^{K_m − 1}} − 1`, where `K_m = maskRowBound m`
bounds the cube orders of Proposition `prop:correlation-test` (`d ≤ K_m − 1`). -/
def stepOf (m : ℕ) : ℕ := max 3 (inverseStep (maskRowBound m - 1))

/-- `s(m) ≥ 3`, and `inverseStep d ≤ s(m)` for every cube order `d ≤ K_m − 1`. -/
theorem stepOf_spec (m d : ℕ) (hd : d ≤ maskRowBound m - 1) :
    3 ≤ stepOf m ∧ inverseStep d ≤ stepOf m := by
  constructor
  · exact le_max_left _ _
  · apply le_trans _ (le_max_right _ _)
    unfold inverseStep inverseDegree
    have hpow : 2 ^ (2 ^ d) ≤ 2 ^ (2 ^ (maskRowBound m - 1)) := by
      exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hd)
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.sub_le_sub_right hpow 1) 1)

/-! ### The cell system `𝒳_l` -/

variable {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

/-- `q_l = R_l / M` (05:526). -/
def cellOrder (A : Parameters K) (N : ℕ) (l : Fin K) : ℕ := A.H N l / A.M N

/-- Indices `k` of the `R_l`-intervals `[kR_l, (k+1)R_l)` contained in `[X_i, X_i²)`. -/
def fullIntervals (A : Parameters K) (N : ℕ) (i l : Fin K) : Finset ℤ :=
  Finset.Ico (((A.X N i : ℤ) + A.H N l - 1) / A.H N l) ((A.X N i : ℤ) ^ 2 / A.H N l)

/-- Cells `(k, ρ)`: a full interval and a residue `ρ ∈ [0, M)`. -/
def cells (A : Parameters K) (N : ℕ) (i l : Fin K) : Finset (ℤ × ℕ) :=
  fullIntervals A N i l ×ˢ Finset.range (A.M N)

/-- The point `kR_l + ρ + Mx` of the cell `(k, ρ)` with progression coordinate `x`. -/
def cellPoint (A : Parameters K) (N : ℕ) (l : Fin K) (C : ℤ × ℕ) (x : ℕ) : ℤ :=
  C.1 * A.H N l + C.2 + A.M N * x

/-- `μ_i`-mass of a cell. -/
def cellMass (A : Parameters K) (N : ℕ) (i l : Fin K) (C : ℤ × ℕ) : ℝ :=
  ∑ x ∈ Finset.range (cellOrder A N l), mu A N i (cellPoint A N l C x)

/-- Cell probabilities `α_C`, normalized after discarding the partial intervals (05:526–529). -/
def cellWeight (A : Parameters K) (N : ℕ) (i l : Fin K) (C : ℤ × ℕ) : ℝ :=
  cellMass A N i l C / ∑ C' ∈ cells A N i l, cellMass A N i l C'

/-- `q_p = M(p)/M = |D(p)|_{>w}` (05:539). -/
def cubeRatio (T : CubeTemplate) (N : ℕ) (p : Fin T.q → ℕ) : ℕ :=
  roughPart (N + 1) (evalIntegerPolynomial T.D (fun j => (p j : ℤ)))

/-- The periodized cube on `𝒳_l` (05:529–536): in each cell, translation by `1 ∈ G_l` is
translation by `M` with wrapping inside the cell, and the cube increments are
`q_p (u_j^1 − u_j^0)`. -/
def periodizedCube (MS : MasterScales K As sl Dm) (T : CubeTemplate) (l i : Fin K)
    (J0 N : ℕ) (h : ℤ → ℝ) : ℝ :=
  goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N) fun p =>
    ∑ C ∈ cells MS.core.parameters N i l, cellWeight MS.core.parameters N i l C *
      ((cellOrder MS.core.parameters N l : ℝ)⁻¹ *
        ∑ x ∈ Finset.range (cellOrder MS.core.parameters N l),
          shiftAverage (Fin T.d) (T.length (corrScales MS) l J0 N p) fun u =>
            ∏ ω : Finset (Fin T.d),
              h (cellPoint MS.core.parameters N l C
                ((((x : ℤ) + (cubeRatio T N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) %
                  (cellOrder MS.core.parameters N l : ℤ)).toNat)))

/-- `‖h‖^{2^t}_{U^t_{G_l}(𝒳_l)} = ∑_C α_C ‖h_C‖^{2^t}_{U^t(G_l)}` (05:644–648), with the cellwise
moments given by `SubgroupBox.boxMoment` along `t` copies of `G_l` (`= OAI.Erdos3.gowersMoment`,
`boxMoment_replicate_top`). -/
def cellGlobalMoment (A : Parameters K) (N : ℕ) (i l : Fin K) (t : ℕ) (h : ℤ → ℝ) : ℝ :=
  if hq : cellOrder A N l = 0 then 0 else
    haveI : NeZero (cellOrder A N l) := ⟨hq⟩
    ∑ C ∈ cells A N i l, cellWeight A N i l C *
      (SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup (ZMod (cellOrder A N l))))
        (fun x => ((h (cellPoint A N l C x.val) : ℝ) : ℂ))).re

/-! ### Sub-lemmas -/

/-- The box moment along `t` copies of the whole group is OpenAI's Gowers moment. -/
theorem boxMoment_replicate_top (t q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup (ZMod q))) f =
      OAI.Erdos3.gowersMoment t f := by
  exact HindmanSumsProducts.Prediction.boxMoment_replicate_top_helper t f

set_option maxHeartbeats 1000000
/-- Periodization (05:518–536): replacing the cube with root `y ∼ μ_i` by the periodized cube on
`𝒳_l` costs `O_d(J₀^{-1}) + o(1)`, uniformly in `h : ℤ → [−1,1]`; the constant depends on `d`
only (partial intervals have `μ_i`-mass `o(1)`; harmonic and uniform measure agree within cells up
to relative `o(1)` since `R_l/X_i = o(1)`; only roots within `dR_l/J₀` of an interval end wrap). -/
theorem periodization_error (d : ℕ) :
    ∃ C : ℝ, ∀ {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
      (MS : MasterScales K As sl Dm) (T : CubeTemplate), Allowed Dm T → T.d = d →
      ∀ (i l : Fin K), l < i → ∀ J0 : ℕ, 0 < J0 → ∀ ε > 0, ∀ᶠ N in atTop,
        ∀ h : ℤ → ℝ, (∀ y, |h y| ≤ 1) →
          |cubeAverage MS T l i J0 N h - periodizedCube MS T l i J0 N h| ≤ C / J0 + ε := by
  classical
  refine ⟨336 * (d + 1 : ℝ), ?_⟩
  intro K sl As Dm MS T hT hTd i l hli J0 hJ0 ε hε
  let A := MS.core.parameters
  let W : ℕ → ℕ := fun N => primorial (N + 1)
  let Xl : ℕ → ℕ := fun N => A.X N l
  let Xi : ℕ → ℕ := fun N => A.X N i
  let H : ℕ → ℕ := fun N => A.H N l
  let M : ℕ → ℕ := fun N => A.M N
  let Q : ℕ → ℕ := fun N => cellOrder A N l
  have hXl : Tendsto (fun N => Xl N) atTop atTop := by simpa [Xl] using A.Xtendsto l
  have hXlReal : Tendsto (fun N => (Xl N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hXl
  have hlogDiv : Tendsto (fun N =>
      Real.log (Xl N : ℝ) / (Xl N : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, div_eq_mul_inv] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hXlReal)
  have hHlog : ∀ᶠ N in atTop, (H N : ℝ) ≤ Real.log (Xl N : ℝ) := by
    have hdom := A.Xdom l 1 (by norm_num)
    filter_upwards [hdom.eventually_gt_atTop 1] with N hN
    have hHpos : 0 < (H N : ℝ) := by exact_mod_cast A.Hpos N l
    have hratio : (1 : ℝ) < Real.log (Xl N : ℝ) / (H N : ℝ) := by
      simpa [H, Xl, pow_one] using hN
    have hmul := (lt_div_iff₀ hHpos).mp hratio
    linarith
  have hXorder : ∀ᶠ N in atTop, (Xi N : ℝ) > (Xl N : ℝ) ^ 2 := by
    have hdom := HindmanSumsProducts.Parameters.eventually_X_dominates_earlier_square A i 1 (by norm_num)
    filter_upwards [hdom] with N hN
    have hprev : Xl N ≤ OAI.SourceAdmissible.previous (A.X N) i := by
      dsimp [Xl, OAI.SourceAdmissible.previous]
      apply Finset.single_le_prod
      · intro j hj
        exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (A.Xpos N j))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hli⟩
    have hM : (1 : ℝ) ≤ (M N : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (A.Mpos N).ne'
    have hprevR : (Xl N : ℝ) ≤
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) := by exact_mod_cast hprev
    have hscale : (Xi N : ℝ) > (M N : ℝ) *
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 := by
      simpa [Xi, M] using hN
    have hle : (Xl N : ℝ) ^ 2 ≤ (M N : ℝ) *
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 := by
      have hprevSq : (Xl N : ℝ) ^ 2 ≤
          (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hprevR 2
      have hMmul : (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 ≤
          (M N : ℝ) * (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 := by
        calc
          _ = 1 * (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hM (sq_nonneg _)
      exact hprevSq.trans hMmul
    dsimp [Xi, Xl]
    nlinarith
  have hlogSq : Tendsto (fun N =>
      (Real.log (Xl N : ℝ) / (Xl N : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using hlogDiv.pow 2
  have hHsqXi : Tendsto (fun N => (H N : ℝ) ^ 2 / (Xi N : ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hlogSq
    · filter_upwards [Filter.Eventually.of_forall (fun N => A.Hpos N l),
        Filter.Eventually.of_forall (fun N => A.Xpos N i)] with N hHN hXN
      positivity
    · filter_upwards [hHlog, hXorder, hXl.eventually_gt_atTop 1] with N hHN hXNi hXlpos
      have hHpos : 0 ≤ (H N : ℝ) := by positivity
      have hupper : (H N : ℝ) ^ 2 ≤ (Real.log (Xl N : ℝ)) ^ 2 := by
        exact pow_le_pow_left₀ hHpos hHN 2
      have hXlposR : (0 : ℝ) < (Xl N : ℝ) := by
        exact_mod_cast (show 0 < Xl N by omega)
      have hden : 0 < (Xl N : ℝ) ^ 2 := pow_pos hXlposR _
      have hratio : ((Real.log (Xl N : ℝ)) ^ 2) / (Xl N : ℝ) ^ 2 =
          (Real.log (Xl N : ℝ) / (Xl N : ℝ)) ^ 2 := by
        field_simp
      have hdenle : (Xl N : ℝ) ^ 2 ≤ (Xi N : ℝ) := by nlinarith [hXNi]
      have hle : (H N : ℝ) ^ 2 / (Xi N : ℝ) ≤
          (Real.log (Xl N : ℝ)) ^ 2 / (Xl N : ℝ) ^ 2 := by
        apply (div_le_div_iff₀ (by exact_mod_cast A.Xpos N i) hden).2
        calc
          (H N : ℝ) ^ 2 * (Xl N : ℝ) ^ 2 ≤
              (Real.log (Xl N : ℝ)) ^ 2 * (Xl N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hupper (sq_nonneg _)
          _ ≤ (Real.log (Xl N : ℝ)) ^ 2 * (Xi N : ℝ) :=
            mul_le_mul_of_nonneg_left hdenle (sq_nonneg _)
      exact hle.trans_eq hratio
  have hHXi : Tendsto (fun N => (H N : ℝ) / (Xi N : ℝ)) atTop (𝓝 0) := by
    have hge : ∀ᶠ N in atTop, (1 : ℝ) ≤ (H N : ℝ) := by
      filter_upwards [Filter.Eventually.of_forall (fun N => A.Hpos N l)] with N hN
      exact_mod_cast hN
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hHsqXi
    · filter_upwards [hge] with N hN
      have hXi : 0 < (Xi N : ℝ) := by exact_mod_cast A.Xpos N i
      exact div_nonneg (by positivity) hXi.le
    · filter_upwards [hge] with N hN
      have hXi : 0 < (Xi N : ℝ) := by exact_mod_cast A.Xpos N i
      have h : (H N : ℝ) ≤ (H N : ℝ) ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_right h hXi.le
  have hsmall : Tendsto (fun N => 100 * (H N : ℝ) ^ 2 / (Xi N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using hHsqXi.const_mul 100
  have hbase : ∀ᶠ N in atTop, 4 * W N ≤ Xi N := by
    filter_upwards [hHlog, hXorder, hXl.eventually_ge_atTop 4,
      Filter.Eventually.of_forall (fun N => A.Wle N),
      Filter.Eventually.of_forall (fun N => A.Hpos N l),
      Filter.Eventually.of_forall (fun N => A.Hdiv N l)] with N hHN hXi hXl4 hWM hHp hHd
    have hMleH : M N ≤ H N := Nat.le_of_dvd hHp hHd
    have hWleH : W N ≤ H N := hWM.trans hMleH
    have hXlcast : (1 : ℝ) ≤ (Xl N : ℝ) := by
      exact_mod_cast (show 1 ≤ Xl N by omega)
    have hXge4 : (4 : ℝ) ≤ (Xl N : ℝ) := by exact_mod_cast hXl4
    have hlogleX : Real.log (Xl N : ℝ) ≤ (Xl N : ℝ) :=
      Real.log_le_self (by positivity)
    have h4H : (4 * (H N : ℝ)) ≤ (Xl N : ℝ) ^ 2 := by
      have hHleX : (H N : ℝ) ≤ (Xl N : ℝ) := hHN.trans hlogleX
      have hxnonneg : 0 ≤ (Xl N : ℝ) := by positivity
      have h4X : (4 : ℝ) * (Xl N : ℝ) ≤ (Xl N : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hXge4) hxnonneg]
      exact (mul_le_mul_of_nonneg_left hHleX (by norm_num)).trans h4X
    have hWle : 4 * (W N : ℝ) ≤ (Xl N : ℝ) ^ 2 := by
      exact le_trans (by exact_mod_cast (Nat.mul_le_mul_left 4 hWleH)) h4H
    exact_mod_cast (le_of_lt (lt_of_le_of_lt hWle hXi))
  have hqpos : ∀ᶠ N in atTop, 0 < Q N := by
    dsimp [Q, cellOrder]
    filter_upwards [Filter.Eventually.of_forall (fun N => A.Hpos N l),
      Filter.Eventually.of_forall (fun N => A.Mpos N)] with N hHN hMN
    exact Nat.div_pos (Nat.le_of_dvd hHN (A.Hdiv N l)) hMN
  let width : ℕ → ℕ := fun N => ((d + 1) * H N) / J0
  let radius : ℕ → ℕ := fun N => width N + 1
  have hHtop : Tendsto (fun N => (H N : ℝ)) atTop atTop := by
    have hEarlier : Tendsto (fun N => (H N : ℝ) /
        OAI.AdmissibleMicrocellBoundary.earlierScale M
          (fun N => OAI.SourceAdmissible.previous (A.X N) l) N) atTop atTop := by
      simpa [H, M] using A.Hdom l 1 (by norm_num)
    have hSge1 : ∀ N, 1 ≤ OAI.AdmissibleMicrocellBoundary.earlierScale M
        (fun N => OAI.SourceAdmissible.previous (A.X N) l) N := by
      intro N
      change (1 : ℝ) ≤ 2 + (M N : ℝ) +
        (OAI.SourceAdmissible.previous (A.X N) l : ℝ)
      have hMnonneg : (0 : ℝ) ≤ M N := by positivity
      have hPnonneg : (0 : ℝ) ≤ OAI.SourceAdmissible.previous (A.X N) l := by positivity
      linarith
    have hSposN (N : ℕ) : 0 < OAI.AdmissibleMicrocellBoundary.earlierScale M
        (fun N => OAI.SourceAdmissible.previous (A.X N) l) N :=
      lt_of_lt_of_le zero_lt_one (hSge1 N)
    have hSpos (N : ℕ) : 0 < OAI.AdmissibleMicrocellBoundary.earlierScale M
        (fun N => OAI.SourceAdmissible.previous (A.X N) l) N :=
      lt_of_lt_of_le zero_lt_one (hSge1 N)
    have hle : ∀ᶠ N in atTop, (H N : ℝ) /
        OAI.AdmissibleMicrocellBoundary.earlierScale M
          (fun N => OAI.SourceAdmissible.previous (A.X N) l) N ≤ (H N : ℝ) := by
      filter_upwards [Filter.Eventually.of_forall (fun N => A.Hpos N l)] with N hN
      apply (div_le_iff₀ (hSposN N)).2
      have h := mul_le_mul_of_nonneg_left (hSge1 N)
        (by positivity : (0 : ℝ) ≤ (H N : ℝ))
      simpa [mul_comm] using h
    exact Filter.tendsto_atTop_mono' atTop hle hEarlier
  have hInvH : Tendsto (fun N => (H N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hHtop
  have hInvX : Tendsto (fun N => (Xi N : ℝ)⁻¹) atTop (𝓝 0) := by
    have hXiTop : Tendsto (fun N => (Xi N : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (by simpa [Xi] using A.Xtendsto i)
    exact tendsto_inv_atTop_zero.comp hXiTop
  have hWXi : Tendsto (fun N => (W N : ℝ) / (Xi N : ℝ)) atTop (𝓝 0) := by
    have hWleH : ∀ N, W N ≤ H N := by
      intro N
      exact (A.Wle N).trans (Nat.le_of_dvd (A.Hpos N l) (A.Hdiv N l))
    have hle : ∀ᶠ N in atTop, (W N : ℝ) / (Xi N : ℝ) ≤
        (H N : ℝ) / (Xi N : ℝ) := by
      filter_upwards [Filter.Eventually.of_forall (fun N => A.Xpos N i)] with N hN
      exact div_le_div_of_nonneg_right (by exact_mod_cast hWleH N) (by positivity)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hHXi
      (Filter.Eventually.of_forall (fun N => by positivity)) hle
  have hWoverH : Tendsto (fun N => (W N : ℝ) / (H N : ℝ)) atTop (𝓝 0) := by
    let earlier : ℕ → ℝ := fun N =>
      OAI.AdmissibleMicrocellBoundary.earlierScale M
        (fun N => OAI.SourceAdmissible.previous (A.X N) l) N
    have hEarlier : Tendsto (fun N => (H N : ℝ) / earlier N) atTop atTop := by
      simpa [earlier, H, M] using A.Hdom l 1 (by norm_num)
    have hEarlierH : Tendsto (fun N => earlier N / (H N : ℝ)) atTop (𝓝 0) := by
      have hInv := tendsto_inv_atTop_zero.comp hEarlier
      have heq : (fun N => ((H N : ℝ) / earlier N)⁻¹) =
          fun N => earlier N / (H N : ℝ) := by
        funext N
        have hHpos : 0 < (H N : ℝ) := by exact_mod_cast A.Hpos N l
        have hSpos : 0 < earlier N := by
          change 0 < 2 + (M N : ℝ) +
            (OAI.SourceAdmissible.previous (A.X N) l : ℝ)
          positivity
        field_simp [ne_of_gt hHpos, ne_of_gt hSpos]
      rw [← heq]
      exact hInv
    have hMleEarlier : ∀ N, (M N : ℝ) ≤ earlier N := by
      intro N
      dsimp [earlier, OAI.AdmissibleMicrocellBoundary.earlierScale]
      have hMnonneg : (0 : ℝ) ≤ M N := by positivity
      have hPnonneg : (0 : ℝ) ≤ OAI.SourceAdmissible.previous (A.X N) l := by positivity
      linarith
    have hMle : ∀ᶠ N in atTop, (M N : ℝ) / (H N : ℝ) ≤ earlier N / (H N : ℝ) := by
      filter_upwards [Filter.Eventually.of_forall (fun N => A.Hpos N l)] with N hN
      exact div_le_div_of_nonneg_right (hMleEarlier N) (by positivity)
    have hMnonneg : ∀ᶠ N in atTop, 0 ≤ (M N : ℝ) / (H N : ℝ) := by
      filter_upwards [Filter.Eventually.of_forall (fun N => A.Hpos N l)] with N hN
      positivity
    have hMoverH := tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hEarlierH hMnonneg hMle
    have hWleM : ∀ N, W N ≤ M N := fun N => A.Wle N
    have hWle : ∀ᶠ N in atTop, (W N : ℝ) / (H N : ℝ) ≤ (M N : ℝ) / (H N : ℝ) := by
      filter_upwards [Filter.Eventually.of_forall (fun N => A.Hpos N l)] with N hN
      exact div_le_div_of_nonneg_right (by exact_mod_cast hWleM N) (by positivity)
    have hWnonneg : ∀ᶠ N in atTop, 0 ≤ (W N : ℝ) / (H N : ℝ) := by
      filter_upwards [Filter.Eventually.of_forall (fun N => A.Hpos N l)] with N hN
      positivity
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hMoverH hWnonneg hWle
  have hPartialRate : Tendsto (fun N => (H N : ℝ) ^ 2 / (Xi N : ℝ)) atTop (𝓝 0) := hHsqXi
  have hBoundaryRate : Tendsto (fun N =>
      168 * ((W N : ℝ) + 2) / (H N : ℝ) +
        112 * ((d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ) +
          ((W N : ℝ) + 2) / (Xi N : ℝ)) ) atTop (𝓝 0) := by
    have hWplusH : Tendsto (fun N => ((W N : ℝ) + 2) / (H N : ℝ)) atTop (𝓝 0) := by
      have h := hWoverH.add (hInvH.const_mul 2)
      have heq : (fun N => ((W N : ℝ) + 2) / (H N : ℝ)) =
          fun N => (W N : ℝ) / (H N : ℝ) + 2 * (H N : ℝ)⁻¹ := by
        funext N
        rw [add_div]
        ring
      rw [heq]
      simpa using h
    have hWplusX : Tendsto (fun N => ((W N : ℝ) + 2) / (Xi N : ℝ)) atTop (𝓝 0) := by
      have h := hWXi.add (hInvX.const_mul 2)
      have heq : (fun N => ((W N : ℝ) + 2) / (Xi N : ℝ)) =
          fun N => (W N : ℝ) / (Xi N : ℝ) + 2 * (Xi N : ℝ)⁻¹ := by
        funext N
        rw [add_div]
        ring
      rw [heq]
      simpa using h
    have hHX : Tendsto (fun N => (d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ)) atTop (𝓝 0) := by
      have h := hHXi.const_mul (d + 1 : ℝ)
      have heq : (fun N => (d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ)) =
          fun N => (d + 1 : ℝ) * ((H N : ℝ) / (Xi N : ℝ)) := by
        funext N
        ring
      rw [heq]
      simpa using h
    have hsum := (hWplusH.const_mul 168).add ((hHX.add hWplusX).const_mul 112)
    have heq : (fun N => 168 * ((W N : ℝ) + 2) / (H N : ℝ) +
        112 * ((d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ) +
          ((W N : ℝ) + 2) / (Xi N : ℝ))) =
        fun N => 168 * (((W N : ℝ) + 2) / (H N : ℝ)) +
          112 * ((d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ) +
            ((W N : ℝ) + 2) / (Xi N : ℝ)) := by
      funext N
      ring
    rw [heq]
    simpa using hsum
  have hRleX : ∀ᶠ N in atTop, radius N ≤ Xi N := by
    have hHsmall : ∀ᶠ N in atTop, (H N : ℝ) / (Xi N : ℝ) <
        1 / (2 * (d + 1 : ℝ)) :=
      hHXi.eventually (Iio_mem_nhds (by positivity))
    have hXsmall : ∀ᶠ N in atTop, (Xi N : ℝ)⁻¹ < 1 / 2 :=
      hInvX.eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hHsmall, hXsmall] with N hN hX
    have hw : (radius N : ℝ) ≤ (d + 1 : ℝ) * (H N : ℝ) + 1 := by
      dsimp [radius, width]
      have hdv : ((d + 1) * H N) / J0 ≤ (d + 1) * H N := Nat.div_le_self _ _
      exact_mod_cast Nat.add_le_add_right hdv 1
    have hXi : (0 : ℝ) < (Xi N : ℝ) := by exact_mod_cast A.Xpos N i
    have hscaled : (d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ) < 1 / 2 := by
      calc
        _ = (d + 1 : ℝ) * ((H N : ℝ) / (Xi N : ℝ)) := by ring
        _ < (d + 1 : ℝ) * (1 / (2 * (d + 1 : ℝ))) :=
          mul_lt_mul_of_pos_left hN (by positivity)
        _ = 1 / 2 := by field_simp
    have hradRatio : ((d + 1 : ℝ) * (H N : ℝ) + 1) / (Xi N : ℝ) < 1 := by
      rw [add_div]
      have hXinv : 1 / (Xi N : ℝ) < 1 / 2 := by simpa [one_div] using hX
      linarith
    have hXbig : (d + 1 : ℝ) * (H N : ℝ) + 1 < Xi N := by
      simpa using (div_lt_iff₀ hXi).mp hradRatio
    have hsum : (radius N : ℝ) ≤ (Xi N : ℝ) := by
      exact hw.trans hXbig.le
    exact_mod_cast hsum
  let boundaryError : ℕ → ℝ := fun N =>
    168 * ((W N : ℝ) + 2) / (H N : ℝ) +
      112 * ((d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ) +
        ((W N : ℝ) + 2) / (Xi N : ℝ))
  have hBoundaryN (N : ℕ) (hcut : 4 * W N ≤ Xi N) (hRad : radius N ≤ Xi N) :
      Emu A N i (fun y => boundaryIndicator (H N) (width N) y) ≤
        (168 * (d + 1 : ℝ)) / J0 + boundaryError N := by
    have hXpos : 0 < Xi N := by exact A.Xpos N i
    have hWpos : 0 < W N := primorial_pos _
    have hHpos : 0 < H N := A.Hpos N l
    have hJreal : (0 : ℝ) < J0 := by exact_mod_cast hJ0
    have hwidth_mul : width N * J0 ≤ (d + 1) * H N := by
      dsimp [width]
      exact Nat.div_mul_le_self _ _
    have hwidth : (width N : ℝ) / (H N : ℝ) ≤ (d + 1 : ℝ) / J0 := by
      apply (div_le_div_iff₀ (by exact_mod_cast hHpos) hJreal).2
      exact_mod_cast hwidth_mul
    have hwidthX : (width N : ℝ) ≤ (d + 1 : ℝ) * (H N : ℝ) := by
      dsimp [width]
      exact_mod_cast Nat.div_le_self _ _
    have htermH : ((radius N + W N + 1 : ℕ) : ℝ) / (H N : ℝ) ≤
        (d + 1 : ℝ) / J0 + ((W N : ℝ) + 2) / (H N : ℝ) := by
      calc
        _ = ((width N : ℝ) + (W N : ℝ) + 2) / (H N : ℝ) := by
              simp [radius]
              push_cast
              ring
        _ = (width N : ℝ) / (H N : ℝ) + ((W N : ℝ) + 2) / (H N : ℝ) := by
              ring
        _ ≤ (d + 1 : ℝ) / J0 + ((W N : ℝ) + 2) / (H N : ℝ) :=
              add_le_add_left hwidth _
    have htermX : ((radius N + W N + 1 : ℕ) : ℝ) / (Xi N : ℝ) ≤
        (d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ) +
          ((W N : ℝ) + 2) / (Xi N : ℝ) := by
      calc
        _ = ((width N : ℝ) + (W N : ℝ) + 2) / (Xi N : ℝ) := by
              simp [radius]
              push_cast
              ring
        _ = (width N : ℝ) / (Xi N : ℝ) + ((W N : ℝ) + 2) / (Xi N : ℝ) := by
              ring
        _ ≤ (d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ) +
              ((W N : ℝ) + 2) / (Xi N : ℝ) := by
                exact add_le_add_left
                  (div_le_div_of_nonneg_right hwidthX (by exact_mod_cast (Nat.zero_le (Xi N)))) _
    have hraw := OAI.DyadicHarmonicBoundary.raw_bad_bound
      (Xi N) (W N) 1 (H N) (radius N) hWpos hcut
      (by norm_num) hHpos hRad
    have hmass := HindmanSumsProducts.Prediction.harmonicBoundary_mass_le_raw
      (X := Xi N) (W := W N) (H := H N) (width := width N) (R := radius N)
      hXpos hWpos hcut hHpos
      (by dsimp [radius]; omega) hRad
    have hnormEq : harmonicNormalizer (Xi N) (W N) =
        OAI.DyadicHarmonicBoundary.mass (Xi N) ((Xi N) ^ 2) (W N) := by
      simp [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
        Finset.sum_filter, one_div, Nat.coprime_comm]
    rw [hnormEq] at hmass
    have hmass' : Emu A N i (fun y => boundaryIndicator (H N) (width N) y) ≤
        168 * ((radius N + W N + 1 : ℕ) : ℝ) / (H N : ℝ) +
          112 * ((radius N + W N + 1 : ℕ) : ℝ) / (Xi N : ℝ) := by
      exact hmass.trans (by simpa [Nat.cast_one, Nat.cast_mul] using hraw)
    calc
      _ ≤ 168 * ((radius N + W N + 1 : ℕ) : ℝ) / (H N : ℝ) +
          112 * ((radius N + W N + 1 : ℕ) : ℝ) / (Xi N : ℝ) := hmass'
      _ ≤ 168 * ((d + 1 : ℝ) / J0 + ((W N : ℝ) + 2) / (H N : ℝ)) +
          112 * ((d + 1 : ℝ) * (H N : ℝ) / (Xi N : ℝ) +
            ((W N : ℝ) + 2) / (Xi N : ℝ)) := by
              apply add_le_add
              · calc
                  168 * ((radius N + W N + 1 : ℕ) : ℝ) / (H N : ℝ) =
                      168 * (((radius N + W N + 1 : ℕ) : ℝ) / (H N : ℝ)) := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left htermH (by norm_num)
              · calc
                  112 * ((radius N + W N + 1 : ℕ) : ℝ) / (Xi N : ℝ) =
                      112 * (((radius N + W N + 1 : ℕ) : ℝ) / (Xi N : ℝ)) := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left htermX (by norm_num)
      _ = (168 * (d + 1 : ℝ)) / J0 + boundaryError N := by
              dsimp [boundaryError]
              ring
  have hpointDecomp (N : ℕ) (hQ : 0 < Q N) (C : ℤ × ℕ)
      (hC : C ∈ cells A N i l) (x : ℕ) (hx : x < Q N) :
      cellPoint A N l C x / (H N : ℤ) = C.1 ∧
        cellPoint A N l C x % (H N : ℤ) = (C.2 : ℤ) + (M N : ℤ) * x := by
    have hMpos : 0 < M N := A.Mpos N
    have hMq : M N * Q N = H N := by
      dsimp [Q, cellOrder]
      simpa [Nat.mul_comm] using Nat.div_mul_cancel (A.Hdiv N l)
    have hCmem : C.1 ∈ fullIntervals A N i l ∧ C.2 < M N := by simpa [cells] using hC
    have hρ : C.2 < M N := hCmem.2
    have hx1 : x + 1 ≤ Q N := Nat.succ_le_of_lt hx
    have hstep : M N * (x + 1) ≤ M N * Q N := Nat.mul_le_mul_left _ hx1
    have hremNat : C.2 + M N * x < H N := by
      have hremStep : C.2 + M N * x < M N * (x + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [hMq] at hstep
      exact hremStep.trans_le hstep
    have hrem0 : (0 : ℤ) ≤ (C.2 : ℤ) + (M N : ℤ) * x := by positivity
    have hremLt : (C.2 : ℤ) + (M N : ℤ) * x < (H N : ℤ) := by exact_mod_cast hremNat
    have hrepr : (C.2 : ℤ) + (M N : ℤ) * x + (H N : ℤ) * C.1 =
        cellPoint A N l C x := by
      simp [cellPoint]
      ring
    have hHposInt : 0 < (H N : ℤ) := by exact_mod_cast A.Hpos N l
    have hHne : (H N : ℤ) ≠ 0 := ne_of_gt hHposInt
    have hremAbs : (C.2 : ℤ) + (M N : ℤ) * x < |(H N : ℤ)| := by
      simpa [abs_of_pos hHposInt] using hremLt
    have huniq := (Int.ediv_emod_unique'' (a := cellPoint A N l C x)
      (b := (H N : ℤ)) (r := (C.2 : ℤ) + (M N : ℤ) * x) (q := C.1)
      hHne).2
      ⟨hrepr, hrem0, hremAbs⟩
    exact huniq
  have hqM (N : ℕ) : M N * Q N = H N := by
    dsimp [M, Q, cellOrder]
    simpa [Nat.mul_comm] using Nat.div_mul_cancel (A.Hdiv N l)
  have hfullBounds (N : ℕ) (k : ℤ)
      (hk : k ∈ fullIntervals A N i l) :
      (Xi N : ℤ) ≤ k * (H N : ℤ) ∧
        (k + 1) * (H N : ℤ) ≤ (Xi N : ℤ) ^ 2 := by
    have hk' :
        (((Xi N : ℤ) + H N - 1) / H N) ≤ k ∧
          k < ((Xi N : ℤ) ^ 2 / H N) := by
      simpa [fullIntervals, H, Xi] using (Finset.mem_Ico.mp hk)
    have hHpos : 0 < (H N : ℤ) := by exact_mod_cast A.Hpos N l
    have hHne : (H N : ℤ) ≠ 0 := hHpos.ne'
    have hremLo := Int.emod_nonneg ((Xi N : ℤ) + H N - 1) hHne
    have hremLoLt := Int.emod_lt_abs ((Xi N : ℤ) + H N - 1) hHne
    have hdivLo := Int.emod_add_mul_ediv ((Xi N : ℤ) + H N - 1) (H N : ℤ)
    have hLoMul : (Xi N : ℤ) ≤ (H N : ℤ) *
        (((Xi N : ℤ) + H N - 1) / H N) := by
      have hremPosLt : ((Xi N : ℤ) + H N - 1) % H N < H N := by
        simpa [abs_of_pos hHpos] using hremLoLt
      have hremBound : ((Xi N : ℤ) + H N - 1) % H N ≤ H N - 1 := by omega
      omega
    have hKLo : (H N : ℤ) * (((Xi N : ℤ) + H N - 1) / H N) ≤
        (H N : ℤ) * k := Int.mul_le_mul_of_nonneg_left hk'.1 hHpos.le
    have hremHi := Int.emod_nonneg ((Xi N : ℤ) ^ 2) hHne
    have hdivHi := Int.emod_add_mul_ediv ((Xi N : ℤ) ^ 2) (H N : ℤ)
    have hHiMul : (H N : ℤ) * ((Xi N : ℤ) ^ 2 / H N) ≤
        (Xi N : ℤ) ^ 2 := by omega
    have hkStep : k + 1 ≤ (Xi N : ℤ) ^ 2 / H N := by omega
    have hKHi : (H N : ℤ) * (k + 1) ≤
        (H N : ℤ) * ((Xi N : ℤ) ^ 2 / H N) :=
      Int.mul_le_mul_of_nonneg_left hkStep hHpos.le
    constructor
    · calc
        (Xi N : ℤ) ≤ (H N : ℤ) * (((Xi N : ℤ) + H N - 1) / H N) := hLoMul
        _ ≤ (H N : ℤ) * k := hKLo
        _ = k * (H N : ℤ) := by ring
    · calc
        (k + 1) * (H N : ℤ) = (H N : ℤ) * (k + 1) := by ring
        _ ≤ (H N : ℤ) * ((Xi N : ℤ) ^ 2 / H N) := hKHi
        _ ≤ (Xi N : ℤ) ^ 2 := hHiMul
  have hcellPointBounds (N : ℕ) (hQ : 0 < Q N) (C : ℤ × ℕ)
      (hC : C ∈ cells A N i l) (x : ℕ) (hx : x < Q N) :
      (Xi N : ℤ) ≤ cellPoint A N l C x ∧
        cellPoint A N l C x < (Xi N : ℤ) ^ 2 := by
    have hCmem : C.1 ∈ fullIntervals A N i l ∧ C.2 < M N := by simpa [cells] using hC
    have hb := hfullBounds N C.1 hCmem.1
    have hdec := hpointDecomp N hQ C hC x hx
    have hremPos : (0 : ℤ) ≤ (C.2 : ℤ) + (M N : ℤ) * x := by positivity
    have hremLt : (C.2 : ℤ) + (M N : ℤ) * x < (H N : ℤ) := by
      exact_mod_cast (show C.2 + M N * x < H N from by
        have hρ : C.2 < M N := hCmem.2
        have hx1 : x + 1 ≤ Q N := Nat.succ_le_of_lt hx
        have hmul : M N * (x + 1) ≤ M N * Q N := Nat.mul_le_mul_left _ hx1
        have hsmall : C.2 + M N * x < M N * (x + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
        rw [hqM N] at hmul
        exact hsmall.trans_le hmul)
    constructor
    · have := hdec.1
      have hpoint_eq : cellPoint A N l C x =
          C.1 * (H N : ℤ) + ((C.2 : ℤ) + (M N : ℤ) * x) := by
        simp [cellPoint]
        ring
      rw [hpoint_eq]
      exact hb.1.trans (le_add_of_nonneg_right hremPos)
    · have hpoint_eq : cellPoint A N l C x =
          C.1 * (H N : ℤ) + ((C.2 : ℤ) + (M N : ℤ) * x) := by
        simp [cellPoint]
        ring
      calc
        cellPoint A N l C x = C.1 * (H N : ℤ) +
            ((C.2 : ℤ) + (M N : ℤ) * x) := hpoint_eq
        _ < C.1 * (H N : ℤ) + (H N : ℤ) := by
              simpa [add_comm] using add_lt_add_left hremLt (C.1 * (H N : ℤ))
        _ = (C.1 + 1) * (H N : ℤ) := by ring
        _ ≤ _ := hb.2
  have hpointInjective (N : ℕ) (hQ : 0 < Q N) :
      Set.InjOn (fun z : (ℤ × ℕ) × ℕ => cellPoint A N l z.1 z.2)
        (↑((cells A N i l).product (Finset.range (Q N))) : Set ((ℤ × ℕ) × ℕ)) := by
    intro p hp p' hp' heq
    have hpParts := Finset.mem_product.mp hp
    have hpParts' := Finset.mem_product.mp hp'
    have hpCell : p.1.1 ∈ fullIntervals A N i l ∧ p.1.2 < M N := by
      simpa [cells] using hpParts.1
    have hpCell' : p'.1.1 ∈ fullIntervals A N i l ∧ p'.1.2 < M N := by
      simpa [cells] using hpParts'.1
    have hpX : p.2 < Q N := Finset.mem_range.mp hpParts.2
    have hpX' : p'.2 < Q N := Finset.mem_range.mp hpParts'.2
    have hdec := hpointDecomp N hQ p.1 hpParts.1 p.2 hpX
    have hdec' := hpointDecomp N hQ p'.1 hpParts'.1 p'.2 hpX'
    have hk : p.1.1 = p'.1.1 := by
      have h := congrArg (fun z : ℤ => z / (H N : ℤ)) heq
      rw [hdec.1, hdec'.1] at h
      exact h
    have hr : (p.1.2 : ℤ) + (M N : ℤ) * p.2 =
        (p'.1.2 : ℤ) + (M N : ℤ) * p'.2 := by
      have h := congrArg (fun z : ℤ => z % (H N : ℤ)) heq
      rw [hdec.2, hdec'.2] at h
      exact h
    have hMposInt : 0 < (M N : ℤ) := by exact_mod_cast A.Mpos N
    have hρpos : 0 ≤ (p.1.2 : ℤ) := by positivity
    have hρpos' : 0 ≤ (p'.1.2 : ℤ) := by positivity
    have hρlt : (p.1.2 : ℤ) < |(M N : ℤ)| := by
      simpa [abs_of_pos hMposInt] using
        (show (p.1.2 : ℤ) < (M N : ℤ) by exact_mod_cast hpCell.2)
    have hρlt' : (p'.1.2 : ℤ) < |(M N : ℤ)| := by
      simpa [abs_of_pos hMposInt] using
        (show (p'.1.2 : ℤ) < (M N : ℤ) by exact_mod_cast hpCell'.2)
    have hmod := congrArg (fun z : ℤ => z % (M N : ℤ)) hr
    have hρ : (p.1.2 : ℤ) = (p'.1.2 : ℤ) := by
      have hmodCast : ((p.1.2 % M N : ℕ) : ℤ) =
          ((p'.1.2 % M N : ℕ) : ℤ) := by
        have hmod' := hmod
        rw [Int.add_mul_emod_self_left, Int.add_mul_emod_self_left] at hmod'
        simpa only [← Int.natCast_mod] using hmod'
      have hmodNat : p.1.2 % M N = p'.1.2 % M N := by exact_mod_cast hmodCast
      have hρNat : p.1.2 = p'.1.2 := by
        simpa [Nat.mod_eq_of_lt hpCell.2, Nat.mod_eq_of_lt hpCell'.2] using hmodNat
      exact_mod_cast hρNat
    have hxmul : (M N : ℤ) * p.2 = (M N : ℤ) * p'.2 := by
      rw [hρ] at hr
      exact add_left_cancel hr
    have hx : p.2 = p'.2 := by
      have hxInt : (p.2 : ℤ) = (p'.2 : ℤ) := mul_left_cancel₀ hMposInt.ne' hxmul
      exact_mod_cast hxInt
    apply Prod.ext
    · apply Prod.ext
      · exact hk
      · exact_mod_cast hρ
    · exact hx
  let cellPairs : ℕ → Finset ((ℤ × ℕ) × ℕ) := fun N =>
    (cells A N i l).product (Finset.range (Q N))
  let pointImage : ℕ → Finset ℤ := fun N =>
    ((cells A N i l).product (Finset.range (Q N))).image
      (fun z : (ℤ × ℕ) × ℕ => cellPoint A N l z.1 z.2)
  let totalCellMass : ℕ → ℝ := fun N =>
    ∑ C ∈ cells A N i l, cellMass A N i l C
  let tailMass : ℕ → ℝ := fun N =>
    ∑ z ∈ (harmonicLawIntSupport (Xi N) (W N) \ pointImage N), mu A N i z
  have hcellMassSum (N : ℕ) (hQ : 0 < Q N) :
      totalCellMass N = ∑ z ∈ pointImage N, mu A N i z := by
    calc
      totalCellMass N = ∑ p ∈ cellPairs N,
          mu A N i (cellPoint A N l p.1 p.2) := by
            dsimp [totalCellMass, cellMass, cellPairs]
            rw [Finset.sum_product]
      _ = ∑ z ∈ pointImage N, mu A N i z := by
            simpa [cellPairs, pointImage] using
              (Finset.sum_image (hpointInjective N hQ)).symm
  have hsupportCore (N : ℕ) (hQ : 0 < Q N) (z : ℤ)
      (hz : z ∈ HindmanSumsProducts.Prediction.harmonicLawIntSupport (Xi N) (W N))
      (hk : z / (H N : ℤ) ∈ fullIntervals A N i l) : z ∈ pointImage N := by
    have hzrange := Finset.mem_filter.mp hz
    have hzIco := Finset.mem_Ico.mp hzrange.1
    have hzpos : 0 ≤ z := le_trans (by positivity : (0 : ℤ) ≤ (Xi N : ℤ)) hzIco.1
    have hnCast : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hzpos
    let n : ℕ := z.toNat
    let r : ℕ := n % H N
    let ρ : ℕ := r % M N
    let x : ℕ := r / M N
    have hdivCast : ((n / H N : ℕ) : ℤ) = z / (H N : ℤ) := by
      dsimp [n]
      rw [← hnCast]
      exact Int.natCast_div _ _
    have hmodCast : ((r : ℕ) : ℤ) = z % (H N : ℤ) := by
      dsimp [r, n]
      rw [← hnCast]
      exact Int.natCast_mod _ _
    have hkNat : ((n / H N : ℕ) : ℤ) ∈ fullIntervals A N i l := by
      simpa [hdivCast] using hk
    have hρlt : ρ < M N := by dsimp [ρ]; exact Nat.mod_lt _ (A.Mpos N)
    have hrlt : r < H N := by dsimp [r]; exact Nat.mod_lt _ (A.Hpos N l)
    have hMq : M N * Q N = H N := hqM N
    have hxlt : x < Q N := by
      dsimp [x]
      apply (Nat.div_lt_iff_lt_mul (A.Mpos N)).2
      have hrLt' : r < M N * Q N := by simpa [hMq] using hrlt
      simpa [Nat.mul_comm] using hrLt'
    let C : ℤ × ℕ := ((n / H N : ℕ), ρ)
    have hC : C ∈ cells A N i l := by
      exact Finset.mem_product.mpr ⟨hkNat, Finset.mem_range.mpr hρlt⟩
    have hDecompH : (n : ℤ) = (r : ℤ) + (H N : ℤ) * (n / H N : ℕ) := by
      exact_mod_cast (Nat.mod_add_div n (H N)).symm
    have hDecompM : (r : ℤ) = (ρ : ℤ) + (M N : ℤ) * x := by
      exact_mod_cast (Nat.mod_add_div r (M N)).symm
    have hBase : z = (r : ℤ) + (H N : ℤ) * (z / (H N : ℤ)) := by
      calc
        z = (n : ℤ) := hnCast.symm
        _ = (r : ℤ) + (H N : ℤ) * (n / H N : ℕ) := hDecompH
        _ = (r : ℤ) + (H N : ℤ) * (z / (H N : ℤ)) := by rw [hdivCast]
    have hPointEq : cellPoint A N l C x = z := by
      calc
        cellPoint A N l C x = C.1 * (H N : ℤ) + (C.2 : ℤ) + (M N : ℤ) * x := by
          simp [cellPoint, C]
          ring
        _ = (H N : ℤ) * (z / (H N : ℤ)) + (r : ℤ) := by
          dsimp [C]
          rw [add_assoc]
          rw [← hDecompM]
          rw [← hdivCast]
          rw [Int.natCast_div]
          ring
        _ = z := by
          calc
            (H N : ℤ) * (z / (H N : ℤ)) + (r : ℤ) =
                (r : ℤ) + (H N : ℤ) * (z / (H N : ℤ)) := by ring
            _ = z := hBase.symm
    apply Finset.mem_image.mpr
    refine ⟨(C, x), Finset.mem_product.mpr ⟨hC, Finset.mem_range.mpr hxlt⟩, hPointEq⟩
  let partialIntervals : ℕ → Finset ℤ := fun N =>
    Finset.Ico (Xi N : ℤ) ((Xi N + H N : ℕ) : ℤ) ∪
      Finset.Ico (((Xi N) ^ 2 - H N : ℕ) : ℤ) ((Xi N) ^ 2 : ℤ)
  have hsupportOutside (N : ℕ) (hQ : 0 < Q N) (hHleX : H N ≤ Xi N)
      (z : ℤ) (hz : z ∈ harmonicLawIntSupport (Xi N) (W N))
      (hzn : z ∉ pointImage N) : z ∈ partialIntervals N := by
    have hzrange := Finset.mem_filter.mp hz
    have hIco := Finset.mem_Ico.mp hzrange.1
    let k : ℤ := z / (H N : ℤ)
    let r : ℤ := z % (H N : ℤ)
    have hHpos : 0 < (H N : ℤ) := by exact_mod_cast A.Hpos N l
    have hHne : (H N : ℤ) ≠ 0 := hHpos.ne'
    have hr0 : 0 ≤ r := by dsimp [r]; exact Int.emod_nonneg _ hHne
    have hrlt : r < (H N : ℤ) := by
      dsimp [r]
      simpa [abs_of_pos hHpos] using Int.emod_lt_abs z hHne
    have hdecomp : r + (H N : ℤ) * k = z := by
      dsimp [r, k]
      exact Int.emod_add_mul_ediv z (H N : ℤ)
    have hknot : k ∉ fullIntervals A N i l := by
      intro hk
      exact hzn (hsupportCore N hQ z hz hk)
    have hkcase : k < (((Xi N : ℤ) + H N - 1) / H N) ∨
        ((Xi N : ℤ) ^ 2 / H N) ≤ k := by
      have hnotBounds : ¬ ((((Xi N : ℤ) + H N - 1) / H N) ≤ k ∧
          k < ((Xi N : ℤ) ^ 2 / H N)) := by
        intro h
        exact hknot (Finset.mem_Ico.mpr h)
      omega
    rcases hkcase with hlo | hhi
    · have hk1 : k + 1 ≤ ((Xi N : ℤ) + H N - 1) / H N := by omega
      have hmul : (H N : ℤ) * (k + 1) ≤ (Xi N : ℤ) + H N - 1 :=
        by simpa [mul_comm] using (Int.le_ediv_iff_mul_le hHpos).mp hk1
      have hzlt : z < (Xi N : ℤ) + H N := by
        calc
          z = r + (H N : ℤ) * k := hdecomp.symm
          _ < (H N : ℤ) * (k + 1) := by nlinarith [hrlt]
          _ ≤ (Xi N : ℤ) + H N - 1 := hmul
          _ < (Xi N : ℤ) + H N := by omega
      exact Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨hIco.1, hzlt⟩)
    · have hremHi := Int.emod_nonneg ((Xi N : ℤ) ^ 2) hHne
      have hremHiLt := Int.emod_lt_abs ((Xi N : ℤ) ^ 2) hHne
      have hdivHi := Int.emod_add_mul_ediv ((Xi N : ℤ) ^ 2) (H N : ℤ)
      have hHiMul : (H N : ℤ) * ((Xi N : ℤ) ^ 2 / H N) ≤ (Xi N : ℤ) ^ 2 := by
        omega
      have hHiLower : (Xi N : ℤ) ^ 2 - H N <
          (H N : ℤ) * ((Xi N : ℤ) ^ 2 / H N) := by
        have hremHiLt' : ((Xi N : ℤ) ^ 2 % H N) < (H N : ℤ) := by
          simpa [abs_of_pos hHpos] using hremHiLt
        omega
      have hkMul : (H N : ℤ) * ((Xi N : ℤ) ^ 2 / H N) ≤
          (H N : ℤ) * k := Int.mul_le_mul_of_nonneg_left hhi hHpos.le
      have hzge : (Xi N : ℤ) ^ 2 - H N < z := by
        have hHkLeZ : (H N : ℤ) * k ≤ z := by
          rw [← hdecomp]
          exact le_add_of_nonneg_left hr0
        calc
          _ < (H N : ℤ) * ((Xi N : ℤ) ^ 2 / H N) := hHiLower
          _ ≤ (H N : ℤ) * k := hkMul
          _ ≤ z := hHkLeZ
      have hHleXsq : H N ≤ (Xi N) ^ 2 := by nlinarith [hHleX]
      have hbelow : (((Xi N) ^ 2 - H N : ℕ) : ℤ) < z := by
        simpa [Int.natCast_sub hHleXsq] using hzge
      exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_of_lt hbelow, hIco.2⟩)
  have hpartialCard (N : ℕ) (hHleX : H N ≤ Xi N) :
      (partialIntervals N).card ≤ 2 * H N := by
    have hXiPos : 0 < Xi N := A.Xpos N i
    have hHleXsq : H N ≤ (Xi N) ^ 2 := by nlinarith [hHleX]
    have hStartLe : (Xi N : ℤ) ≤ ((Xi N + H N : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_add_right (Xi N) (H N)
    have hStartCardZ :
        ((Finset.Ico (Xi N : ℤ) ((Xi N + H N : ℕ) : ℤ)).card : ℤ) = (H N : ℤ) := by
      rw [Int.card_Ico_of_le (Xi N : ℤ) ((Xi N + H N : ℕ) : ℤ) hStartLe]
      push_cast
      ring
    have hStartCard :
        (Finset.Ico (Xi N : ℤ) ((Xi N + H N : ℕ) : ℤ)).card = H N := by
      exact_mod_cast hStartCardZ
    have hEndLo : (((Xi N) ^ 2 - H N : ℕ) : ℤ) ≤ ((Xi N) ^ 2 : ℤ) := by
      exact_mod_cast Nat.sub_le _ _
    have hEndCardZ :
        ((Finset.Ico (((Xi N) ^ 2 - H N : ℕ) : ℤ) ((Xi N) ^ 2 : ℤ)).card : ℤ) =
          (H N : ℤ) := by
      rw [Int.card_Ico_of_le (((Xi N) ^ 2 - H N : ℕ) : ℤ) ((Xi N) ^ 2 : ℤ) hEndLo]
      rw [Int.natCast_sub hHleXsq]
      simp
    have hEndCard :
        (Finset.Ico (((Xi N) ^ 2 - H N : ℕ) : ℤ) ((Xi N) ^ 2 : ℤ)).card = H N := by
      exact_mod_cast hEndCardZ
    dsimp [partialIntervals]
    calc
      _ ≤ (Finset.Ico (Xi N : ℤ) ((Xi N + H N : ℕ) : ℤ)).card +
          (Finset.Ico (((Xi N) ^ 2 - H N : ℕ) : ℤ) ((Xi N) ^ 2 : ℤ)).card :=
            Finset.card_union_le _ _
      _ = H N + H N := by rw [hStartCard, hEndCard]
      _ = 2 * H N := by omega
  have hpartialMassBound (N : ℕ) (hQ : 0 < Q N) (hcut : 4 * W N ≤ Xi N)
      (hHleX : H N ≤ Xi N) :
      (∑ z ∈ (harmonicLawIntSupport (Xi N) (W N) \ pointImage N),
        mu A N i z) ≤ 8 * (H N : ℝ) * (W N : ℝ) / (Xi N : ℝ) := by
    have hXpos : 0 < Xi N := A.Xpos N i
    have hWpos : 0 < W N := primorial_pos _
    have hHnorm : 0 < harmonicNormalizer (Xi N) (W N) := by
      have hm := OAI.RawHarmonicProbability.mass_pos (Xi N) (W N) hWpos hcut
      simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
        Finset.sum_filter, one_div, Nat.coprime_comm] using hm
    have hNormEq : harmonicNormalizer (Xi N) (W N) =
        OAI.DyadicHarmonicBoundary.mass (Xi N) ((Xi N) ^ 2) (W N) := by
      simp [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
        Finset.sum_filter, one_div, Nat.coprime_comm]
    have hNormLower : (1 : ℝ) / (4 * W N) ≤ harmonicNormalizer (Xi N) (W N) := by
      have hraw := OAI.DyadicHarmonicBoundary.dyadic_lower
        (Xi N) (W N) hWpos hcut
      have hXX : Xi N + Xi N ≤ (Xi N) ^ 2 := by
        have hX4 : 4 ≤ Xi N := by omega
        nlinarith
      have htotient : (1 : ℝ) ≤ (Nat.totient (W N) : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hWpos).ne')
      rw [hNormEq]
      have hraw' := hraw.trans (OAI.DyadicHarmonicBoundary.mass_mono hXX)
      exact (div_le_div_of_nonneg_right htotient (by positivity)).trans hraw'
    have hNormPos : 0 < harmonicNormalizer (Xi N) (W N) :=
      lt_of_lt_of_le (by positivity) hNormLower
    have hMuNonneg (z : ℤ) : 0 ≤ mu A N i z := by
      simp [mu, Xi, W, harmonicLaw]
      split_ifs <;> positivity
    have hsubset :
        harmonicLawIntSupport (Xi N) (W N) \ pointImage N ⊆ partialIntervals N := by
      intro z hz
      exact hsupportOutside N hQ hHleX z
        (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2
    have hpointBound (z : ℤ) (hz : z ∈ partialIntervals N) :
        mu A N i z ≤ (4 * (W N : ℝ)) / (Xi N : ℝ) := by
      by_cases hsupp : z ∈ harmonicLawIntSupport (Xi N) (W N)
      · have hIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hsupp).1
        have hz0 : 0 ≤ z := le_trans (by positivity : (0:ℤ) ≤ (Xi N:ℤ)) hIco.1
        have hzNat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
        have hnat : Xi N ≤ z.toNat := by
          have hnatInt : (Xi N : ℤ) ≤ (z.toNat : ℤ) := by
            simpa [hzNat] using hIco.1
          exact_mod_cast hnatInt
        have hnupper : z.toNat < (Xi N) ^ 2 := by
          have hInt : (z.toNat : ℤ) < (Xi N : ℤ) ^ 2 := by
            simpa [hzNat] using hIco.2
          exact_mod_cast hInt
        have hpoint : mu A N i z =
            1 / ((z.toNat : ℝ) * harmonicNormalizer (Xi N) (W N)) := by
          change harmonicLaw (Xi N) (W N) z = _
          simp [harmonicLaw, hz0, hnat, hnupper, (Finset.mem_filter.mp hsupp).2]
        have hXNorm : (Xi N : ℝ) / (4 * W N : ℝ) ≤
            (z.toNat : ℝ) * harmonicNormalizer (Xi N) (W N) := by
          calc
            (Xi N : ℝ) / (4 * W N : ℝ) =
                (Xi N : ℝ) * (1 / (4 * W N : ℝ)) := by ring
            _ ≤ (Xi N : ℝ) * harmonicNormalizer (Xi N) (W N) :=
                mul_le_mul_of_nonneg_left hNormLower (by positivity)
            _ ≤ (z.toNat : ℝ) * harmonicNormalizer (Xi N) (W N) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) hNormPos.le
        have hpos : 0 < (Xi N : ℝ) / (4 * W N : ℝ) := by positivity
        rw [hpoint]
        calc
          _ ≤ ((Xi N : ℝ) / (4 * W N : ℝ))⁻¹ :=
            by simpa [one_div] using one_div_le_one_div_of_le hpos hXNorm
          _ = (4 * (W N : ℝ)) / (Xi N : ℝ) := by field_simp
      · have hz0 : mu A N i z = 0 := by
          simpa [mu, Xi, W] using
            harmonicLaw_zero_of_not_mem (Xi N) (W N) z (by simpa using hsupp)
        rw [hz0]
        positivity
    have hsumSupport :
        (∑ z ∈ (harmonicLawIntSupport (Xi N) (W N) \ pointImage N), mu A N i z) ≤
          ∑ z ∈ partialIntervals N, mu A N i z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z hz hznot
      exact hMuNonneg z
    have hsumBound :
        (∑ z ∈ partialIntervals N, mu A N i z) ≤
          ∑ z ∈ partialIntervals N, (4 * (W N : ℝ)) / (Xi N : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact hpointBound z hz
    calc
      _ ≤ ∑ z ∈ partialIntervals N, mu A N i z := hsumSupport
      _ ≤ ∑ z ∈ partialIntervals N, (4 * (W N : ℝ)) / (Xi N : ℝ) := hsumBound
      _ = (partialIntervals N).card * ((4 * (W N : ℝ)) / (Xi N : ℝ)) := by
        simp [Finset.sum_const]
      _ ≤ (2 * H N : ℝ) * ((4 * (W N : ℝ)) / (Xi N : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hpartialCard N hHleX) (by positivity)
      _ = 8 * (H N : ℝ) * (W N : ℝ) / (Xi N : ℝ) := by ring
  have hcellComparison (N : ℕ) (hQ : 0 < Q N) (hcut : 4 * W N ≤ Xi N) (C : ℤ × ℕ)
      (hC : C ∈ cells A N i l) (g : ℕ → ℝ) (hg : ∀ x < Q N, |g x| ≤ 1) :
      |(∑ x ∈ Finset.range (Q N), mu A N i (cellPoint A N l C x) * g x) -
        cellMass A N i l C *
          ((Q N : ℝ)⁻¹ * ∑ x ∈ Finset.range (Q N), g x)| ≤
        cellMass A N i l C * ((H N : ℝ) / (Xi N : ℝ)) := by
    classical
    let baseInt : ℤ := C.1 * (H N : ℤ) + (C.2 : ℤ)
    let base : ℕ := baseInt.toNat
    have hCmem : C.1 ∈ fullIntervals A N i l ∧ C.2 < M N := by
      simpa [cells] using hC
    have hb := hfullBounds N C.1 hCmem.1
    have hXiInt : 0 < (Xi N : ℤ) := by exact_mod_cast A.Xpos N i
    have hHpos : 0 < H N := A.Hpos N l
    have hC1nonneg : 0 ≤ C.1 := by
      have hXile : (0 : ℤ) ≤ (Xi N : ℤ) := le_of_lt hXiInt
      have hC1mul : 0 ≤ C.1 * (H N : ℤ) := le_trans hXile hb.1
      nlinarith
    have hbaseIntNonneg : 0 ≤ baseInt := by
      dsimp [baseInt]
      positivity
    have hbaseCast : (base : ℤ) = baseInt := by
      simp [base, Int.toNat_of_nonneg hbaseIntNonneg]
    have hbaseLower : (Xi N : ℝ) ≤ (base : ℝ) := by
      have hLowerInt : (Xi N : ℤ) ≤ baseInt := by
        dsimp [baseInt]
        have hρ : (0 : ℤ) ≤ (C.2 : ℤ) := by positivity
        nlinarith
      have hLowerInt' : (Xi N : ℤ) ≤ (base : ℤ) := by
        rw [hbaseCast]
        exact hLowerInt
      have hLowerNat : Xi N ≤ base := by exact_mod_cast hLowerInt'
      exact_mod_cast hLowerNat
    have hbasePos : 0 < (base : ℝ) := lt_of_lt_of_le (by exact_mod_cast A.Xpos N i) hbaseLower
    have hnormPos : 0 < harmonicNormalizer (Xi N) (W N) := by
      have hm := OAI.RawHarmonicProbability.mass_pos (Xi N) (W N)
        (primorial_pos _) hcut
      simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
        Finset.sum_filter, one_div, Nat.coprime_comm] using hm
    have hrootCast (x : ℕ) (hx : x < Q N) :
        (base + M N * x : ℕ) = (cellPoint A N l C x).toNat := by
      have hbnds := hcellPointBounds N (by omega) C hC x hx
      have hpointNonneg : 0 ≤ cellPoint A N l C x := by
        exact le_trans (by exact_mod_cast (A.Xpos N i).le) hbnds.1
      have hrootInt : cellPoint A N l C x = baseInt + (M N : ℤ) * x := by
        simp [cellPoint, baseInt]
        ring
      have hcastEq : ((base + M N * x : ℕ) : ℤ) = cellPoint A N l C x := by
        rw [Nat.cast_add, Nat.cast_mul, hbaseCast, hrootInt]
      exact Int.natCast_inj.mp
        (hcastEq.trans (Int.toNat_of_nonneg hpointNonneg).symm)
    have hWM : W N ∣ M N := by
      obtain ⟨e, he⟩ := MS.core.modulus_power N
      have hMpow : M N = W N ^ e := by simpa [M, W, A] using he
      by_cases he0 : e = 0
      · subst e
        have hWle : W N ≤ M N := A.Wle N
        rw [hMpow] at hWle
        simp only [pow_zero] at hWle
        have hWone : W N = 1 := by
          have hWpos : 0 < W N := primorial_pos _
          omega
        rw [hWone]
        exact one_dvd _
      · have hepos : 0 < e := Nat.pos_of_ne_zero he0
        rw [hMpow]
        exact dvd_pow_self _ (Nat.ne_of_gt hepos)
    have hWdiv (x : ℕ) : W N ∣ M N * x := dvd_mul_of_dvd_left hWM x
    have hcop (x : ℕ) :
        Nat.Coprime (base + M N * x) (W N) ↔ Nat.Coprime base (W N) := by
      obtain ⟨k, hk⟩ := hWdiv x
      rw [hk, Nat.coprime_add_mul_left_left]
    have hpointFormula (x : ℕ) (hx : x < Q N) (hc : Nat.Coprime base (W N)) :
        mu A N i (cellPoint A N l C x) =
          1 / ((base + M N * x : ℕ) * harmonicNormalizer (Xi N) (W N)) := by
      have hbnds := hcellPointBounds N hQ C hC x hx
      have hpointNonneg : 0 ≤ cellPoint A N l C x := by
        exact le_trans (by exact_mod_cast (A.Xpos N i).le) hbnds.1
      have hnatlo : Xi N ≤ (cellPoint A N l C x).toNat := by
        have hnatloInt : (Xi N : ℤ) ≤ ((cellPoint A N l C x).toNat : ℤ) := by
          simpa [Int.toNat_of_nonneg hpointNonneg] using hbnds.1
        exact_mod_cast hnatloInt
      have hnathi : (cellPoint A N l C x).toNat < Xi N ^ 2 := by
        have hnathiInt : ((cellPoint A N l C x).toNat : ℤ) < (Xi N : ℤ) ^ 2 := by
          simpa [Int.toNat_of_nonneg hpointNonneg] using hbnds.2
        exact_mod_cast hnathiInt
      have hcopPoint : Nat.Coprime (cellPoint A N l C x).toNat (W N) := by
        rw [← hrootCast x hx]
        exact (hcop x).2 hc
      have hvalNat : 0 < base + M N * x := by omega
      have hvalPos : 0 < ((base + M N * x : ℕ) : ℝ) := by exact_mod_cast hvalNat
      change harmonicLaw (Xi N) (W N) (cellPoint A N l C x) = _
      simp only [harmonicLaw]
      rw [if_pos ⟨hpointNonneg, hnatlo, hnathi, hcopPoint⟩]
      rw [← hrootCast x hx]
    have hpointZero (x : ℕ) (hx : x < Q N) (hc : ¬ Nat.Coprime base (W N)) :
        mu A N i (cellPoint A N l C x) = 0 := by
      have hbnds := hcellPointBounds N hQ C hC x hx
      have hpointNonneg : 0 ≤ cellPoint A N l C x := by
        exact le_trans (by exact_mod_cast (A.Xpos N i).le) hbnds.1
      have hnatlo : Xi N ≤ (cellPoint A N l C x).toNat := by
        have hnatloInt : (Xi N : ℤ) ≤ ((cellPoint A N l C x).toNat : ℤ) := by
          simpa [Int.toNat_of_nonneg hpointNonneg] using hbnds.1
        exact_mod_cast hnatloInt
      have hnathi : (cellPoint A N l C x).toNat < Xi N ^ 2 := by
        have hnathiInt : ((cellPoint A N l C x).toNat : ℤ) < (Xi N : ℤ) ^ 2 := by
          simpa [Int.toNat_of_nonneg hpointNonneg] using hbnds.2
        exact_mod_cast hnathiInt
      have hcopPoint : ¬ Nat.Coprime (cellPoint A N l C x).toNat (W N) := by
        intro hc'
        have hc'' : Nat.Coprime (base + M N * x) (W N) := by
          rw [← hrootCast x hx] at hc'
          exact hc'
        exact hc ((hcop x).1 hc'')
      change harmonicLaw (Xi N) (W N) (cellPoint A N l C x) = 0
      simp only [harmonicLaw]
      have hfalse :
          ¬ (0 ≤ cellPoint A N l C x ∧ Xi N ≤ (cellPoint A N l C x).toNat ∧
            (cellPoint A N l C x).toNat < Xi N ^ 2 ∧
              Nat.Coprime (cellPoint A N l C x).toNat (W N)) := by
        rintro ⟨_, _, _, hc'⟩
        exact hcopPoint hc'
      rw [if_neg hfalse]
    by_cases hc : Nat.Coprime base (W N)
    · let y : Fin (Q N) → ℝ := fun x => (base + M N * x.val : ℕ)
      let f : Fin (Q N) → ℝ := fun x => g x.val
      letI : NeZero (Q N) := ⟨by omega⟩
      letI : Nonempty (Fin (Q N)) := ⟨⟨0, hQ⟩⟩
      have hvalPos (x : Fin (Q N)) :
          0 < ((base + M N * x.val : ℕ) : ℝ) := by
        have hnat : 0 < base + M N * x.val := by omega
        exact_mod_cast hnat
      have hfactor (x : Fin (Q N)) :
          (1 / (y x * harmonicNormalizer (Xi N) (W N))) * g x.val =
            ((y x)⁻¹ * g x.val / harmonicNormalizer (Xi N) (W N)) := by
        field_simp [ne_of_gt (hvalPos x), ne_of_gt hnormPos]
      have hfactorMass (x : Fin (Q N)) :
          1 / (y x * harmonicNormalizer (Xi N) (W N)) =
            (y x)⁻¹ / harmonicNormalizer (Xi N) (W N) := by
        field_simp [ne_of_gt (hvalPos x), ne_of_gt hnormPos]
      have hy (x : Fin (Q N)) : (base : ℝ) ≤ y x ∧ y x ≤ (base : ℝ) + H N := by
        constructor
        · dsimp [y]
          exact_mod_cast (Nat.le_add_right base (M N * x.val))
        · dsimp [y]
          have hx : x.val < Q N := x.isLt
          have hmul : M N * x.val < H N := by
            calc
              M N * x.val < M N * Q N := Nat.mul_lt_mul_of_pos_left hx (A.Mpos N)
              _ = H N := hqM N
          exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt hmul) base
      have hf (x : Fin (Q N)) : |f x| ≤ 1 := hg x.val x.isLt
      have hrecip := reciprocalWeights_uniform_expect_diff
        (base : ℝ) (H N : ℝ) hbasePos (by positivity) y f hy hf
      let S0 : ℝ := ∑ x : Fin (Q N), (y x)⁻¹
      let T0 : ℝ := ∑ x : Fin (Q N), (y x)⁻¹ * f x
      let U0 : ℝ := (Q N : ℝ)⁻¹ * ∑ x : Fin (Q N), f x
      have hSpos : 0 < ∑ x : Fin (Q N), (y x)⁻¹ := by
        apply Finset.sum_pos
        · intro x hx
          exact inv_pos.mpr (lt_of_lt_of_le hbasePos (hy x).1)
        · exact Finset.univ_nonempty_iff.mpr (by exact ⟨⟨0, hQ⟩⟩)
      have hS0pos : 0 < S0 := by simpa [S0] using hSpos
      have hmuSum :
          (∑ x ∈ Finset.range (Q N), mu A N i (cellPoint A N l C x) * g x) =
            T0 / harmonicNormalizer (Xi N) (W N) := by
        change (∑ x ∈ Finset.range (Q N), mu A N i (cellPoint A N l C x) * g x) =
          (∑ x : Fin (Q N), (y x)⁻¹ * f x) / harmonicNormalizer (Xi N) (W N)
        rw [← Fin.sum_univ_eq_sum_range]
        simp only [y, f]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        have hpt := hpointFormula x.val x.isLt hc
        rw [hpt]
        simpa only [y, f] using hfactor x
      have hmassSum :
          cellMass A N i l C = S0 /
            harmonicNormalizer (Xi N) (W N) := by
        change cellMass A N i l C = (∑ x : Fin (Q N), (y x)⁻¹) /
          harmonicNormalizer (Xi N) (W N)
        rw [cellMass, ← Fin.sum_univ_eq_sum_range]
        simp only [y]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        have hpt := hpointFormula x.val x.isLt hc
        rw [hpt]
        simpa only [y] using hfactorMass x
      have hmassPos : 0 < cellMass A N i l C := by
        rw [hmassSum]
        exact div_pos hS0pos hnormPos
      have hbaseNatPos : 0 < base := by exact_mod_cast hbasePos
      have hratioBound :
          |T0 / S0 - U0| ≤ (H N : ℝ) / (Xi N : ℝ) := by
        have hcard : Fintype.card (Fin (Q N)) = Q N := Fintype.card_fin _
        have hXiPos : 0 < (Xi N : ℝ) := by exact_mod_cast A.Xpos N i
        have hquot : (H N : ℝ) / (base : ℝ) ≤ (H N : ℝ) / (Xi N : ℝ) := by
          apply (div_le_div_iff₀ hbasePos hXiPos).2
          exact mul_le_mul_of_nonneg_left hbaseLower (by positivity)
        simpa [S0, T0, U0, hcard, Fintype.card_fin] using hrecip.trans hquot
      have havg :
          (Q N : ℝ)⁻¹ * ∑ x ∈ Finset.range (Q N), g x =
            U0 := by
        change (Q N : ℝ)⁻¹ * ∑ x ∈ Finset.range (Q N), g x =
          (Q N : ℝ)⁻¹ * ∑ x : Fin (Q N), f x
        rw [← Fin.sum_univ_eq_sum_range]
      rw [hmuSum, hmassSum, havg]
      have hnorm : 0 < harmonicNormalizer (Xi N) (W N) := hnormPos
      have hscaled (S T Z U : ℝ) (hS : S ≠ 0) (hZ : Z ≠ 0) :
          T / Z - S / Z * U = S / Z * (T / S - U) := by
        field_simp [hS, hZ]
      have hSratioPos : 0 < S0 / harmonicNormalizer (Xi N) (W N) :=
        div_pos hS0pos hnormPos
      rw [hscaled S0 T0 (harmonicNormalizer (Xi N) (W N)) U0
        (ne_of_gt hS0pos) (ne_of_gt hnorm), abs_mul, abs_of_pos hSratioPos]
      exact mul_le_mul_of_nonneg_left hratioBound (le_of_lt hSratioPos)
    · have hzeroMass : cellMass A N i l C = 0 := by
        rw [cellMass]
        apply Finset.sum_eq_zero
        intro x hx
        rw [hpointZero x (Finset.mem_range.mp hx) hc]
      rw [hzeroMass]
      have hzeroNum :
          (∑ x ∈ Finset.range (Q N), mu A N i (cellPoint A N l C x) * g x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [hpointZero x (Finset.mem_range.mp hx) hc]
        simp
      rw [hzeroNum]
      simp
  let rootCube : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → ℤ → ℝ := fun h N p y =>
    shiftAverage (Fin T.d) (T.length (corrScales MS) l J0 N p) fun u =>
      ∏ ω : Finset (Fin T.d),
        h (y + (T.modulus (corrScales MS) N p : ℤ) *
          ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))
  let wrappedCube : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → (ℤ × ℕ) → ℕ → ℝ :=
    fun h N p C x =>
    shiftAverage (Fin T.d) (T.length (corrScales MS) l J0 N p) fun u =>
      ∏ ω : Finset (Fin T.d),
        h (cellPoint A N l C
          ((((x : ℤ) + (cubeRatio T N p : ℤ) *
            ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) % (Q N : ℤ)).toNat))
  let cellUniform : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → (ℤ × ℕ) → ℝ := fun h N p C =>
    (Q N : ℝ)⁻¹ * ∑ x ∈ Finset.range (Q N), wrappedCube h N p C x
  let periodizedAt : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → ℝ := fun h N p =>
    ∑ C ∈ cells MS.core.parameters N i l,
      cellWeight MS.core.parameters N i l C *
        ((cellOrder MS.core.parameters N l : ℝ)⁻¹ *
          ∑ x ∈ Finset.range (cellOrder MS.core.parameters N l),
            shiftAverage (Fin T.d) (T.length (corrScales MS) l J0 N p) fun u =>
              ∏ ω : Finset (Fin T.d),
                h (cellPoint MS.core.parameters N l C
                  ((((x : ℤ) + (cubeRatio T N p : ℤ) *
                    ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) %
                    (cellOrder MS.core.parameters N l : ℤ)).toNat)))
  have hsafeVertex (N : ℕ) (hQ : 0 < Q N) (p : Fin T.q → ℕ)
      (C : ℤ × ℕ) (hC : C ∈ cells A N i l) (x : ℕ) (hx : x < Q N)
      (L : ℕ) (hL : L = T.length (corrScales MS) l J0 N p)
      (ω : Finset (Fin T.d)) (u : Fin T.d → Fin 2 → ℕ)
      (hu : ∀ j b, u j b < L)
      (hsafe : ¬ InBoundaryStrip (H N) (width N) (cellPoint A N l C x)) :
      cellPoint A N l C x + (T.modulus (corrScales MS) N p : ℤ) *
          ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) =
        cellPoint A N l C
          ((((x : ℤ) + (cubeRatio T N p : ℤ) *
            ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) % (Q N : ℤ)).toNat) := by
    classical
    let a : ℕ := cubeRatio T N p
    let S : ℤ := ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)
    let z : ℤ := (x : ℤ) + (a : ℤ) * S
    let mp : ℕ := T.modulus (corrScales MS) N p
    have hratio : mp = M N * a := by
      rfl
    have hlen : L = H N / (J0 * mp) := by rw [hL]; rfl
    have hroughPos : 0 < roughPart (N + 1)
        (evalIntegerPolynomial T.D (fun j => (p j : ℤ))) := by
      unfold roughPart
      apply Finset.prod_pos
      intro q hq
      exact Nat.pow_pos (Finset.mem_filter.mp hq).2.1.pos
    have hMpPos : 0 < mp := by
      dsimp [mp, CubeTemplate.modulus, directionModulus, corrScales, M]
      exact Nat.mul_pos (A.Mpos N) hroughPos
    have hLmul : L * (J0 * mp) ≤ H N := by
      rw [hlen]
      exact Nat.div_mul_le_self _ _
    have hwidthMul : (d * mp * L) * J0 ≤ (d + 1) * H N := by
      calc
        (d * mp * L) * J0 = d * (L * (J0 * mp)) := by ac_rfl
        _ ≤ d * H N := Nat.mul_le_mul_left d hLmul
        _ ≤ (d + 1) * H N := Nat.mul_le_mul_right (H N) (Nat.le_succ d)
    have hshiftBound : d * mp * L ≤ width N := by
      dsimp [width]
      exact (Nat.le_div_iff_mul_le hJ0).2 hwidthMul
    have hsumBound :
        |∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)| ≤ (T.d : ℤ) * L := by
      have hterm (j : Fin T.d) (hj : j ∈ ω) :
          |(u j 1 : ℤ) - u j 0| ≤ (L : ℤ) := by
        exact abs_int_natCast_sub_le (hu j 1) (hu j 0)
      have hcardT : ω.card ≤ T.d := by
        calc
          ω.card ≤ (Finset.univ : Finset (Fin T.d)).card :=
            Finset.card_le_card (Finset.subset_univ ω)
          _ = T.d := by rw [Finset.card_univ, Fintype.card_fin]
      calc
        |∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)| ≤
            ∑ j ∈ ω, |(u j 1 : ℤ) - u j 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ ω, (L : ℤ) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hterm j hj
        _ = (ω.card : ℤ) * L := by simp [Finset.sum_const, mul_comm]
        _ ≤ (T.d : ℤ) * L := by exact_mod_cast Nat.mul_le_mul_right L hcardT
    have hdispBound : |(mp : ℤ) * S| ≤ (width N : ℤ) := by
      change |(mp : ℤ) * (∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))| ≤ (width N : ℤ)
      calc
        |(mp : ℤ) * (∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))| =
            (mp : ℤ) * |∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (mp : ℤ))]
        _ ≤ (mp : ℤ) * ((T.d : ℤ) * L) :=
          mul_le_mul_of_nonneg_left hsumBound (by positivity)
        _ = (d * mp * L : ℕ) := by rw [hTd]; push_cast; ring
        _ ≤ width N := by exact_mod_cast hshiftBound
    have hparts' : C.1 ∈ fullIntervals A N i l ∧ C.2 ∈ Finset.range (M N) := by
      simpa only [cells, Finset.mem_product, Finset.mem_range] using hC
    have hparts : C.1 ∈ fullIntervals A N i l ∧ C.2 < M N :=
      ⟨hparts'.1, Finset.mem_range.mp hparts'.2⟩
    have hpoint := hpointDecomp N hQ C hC x hx
    have hHposInt : 0 < (H N : ℤ) := by exact_mod_cast A.Hpos N l
    have hHne : (H N : ℤ) ≠ 0 := hHposInt.ne'
    have hMposInt : 0 < (M N : ℤ) := by exact_mod_cast A.Mpos N
    have hMne : (M N : ℤ) ≠ 0 := hMposInt.ne'
    have hqMInt : (M N : ℤ) * (Q N : ℤ) = (H N : ℤ) := by
      exact_mod_cast hqM N
    have hremNonneg :
        0 ≤ cellPoint A N l C x % (H N : ℤ) := Int.emod_nonneg _ hHne
    have hremGt : (width N : ℤ) < cellPoint A N l C x % (H N : ℤ) := by
      have h := hsafe
      change ¬ ((cellPoint A N l C x % (H N : ℤ) ≤ (width N : ℤ)) ∨
        (H N : ℤ) ≤ cellPoint A N l C x % (H N : ℤ) + width N) at h
      exact lt_of_not_ge fun hle => h (Or.inl hle)
    have hremEnd : cellPoint A N l C x % (H N : ℤ) + width N < (H N : ℤ) := by
      have h := hsafe
      change ¬ ((cellPoint A N l C x % (H N : ℤ) ≤ (width N : ℤ)) ∨
        (H N : ℤ) ≤ cellPoint A N l C x % (H N : ℤ) + width N) at h
      exact lt_of_not_ge fun hge => h (Or.inr hge)
    have hnewRemEq :
        (C.2 : ℤ) + (M N : ℤ) * z =
          cellPoint A N l C x % (H N : ℤ) + (mp : ℤ) * S := by
      rw [hpoint.2, hratio]
      dsimp [z, S, a]
      ring
    have hnewRem :
        0 ≤ (C.2 : ℤ) + (M N : ℤ) * z ∧
          (C.2 : ℤ) + (M N : ℤ) * z < (H N : ℤ) := by
      rw [hnewRemEq]
      constructor
      · have hDlo := (abs_le.mp hdispBound).1
        nlinarith
      · have hDhi := (abs_le.mp hdispBound).2
        nlinarith
    have hzNonneg : 0 ≤ z := by
      by_contra hz
      have hz' : z ≤ -1 := by omega
      have hmz : (M N : ℤ) * z ≤ -(M N : ℤ) := by
        have hm := Int.mul_le_mul_of_nonneg_left hz' hMposInt.le
        nlinarith
      have hρ : (C.2 : ℤ) < (M N : ℤ) := by exact_mod_cast hparts.2
      nlinarith [hnewRem.1]
    have hzLt : z < (Q N : ℤ) := by
      by_contra hz
      have hz' : (Q N : ℤ) ≤ z := by omega
      have hmz := Int.mul_le_mul_of_nonneg_left hz' hMposInt.le
      rw [hqMInt] at hmz
      have hρ : (0 : ℤ) ≤ (C.2 : ℤ) := by positivity
      nlinarith [hnewRem.2]
    have hQne : (Q N : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
    have hmodCast :
        ((z.toNat % Q N : ℕ) : ℤ) = z % (Q N : ℤ) := by
      rw [← Int.toNat_of_nonneg hzNonneg]
      exact Int.natCast_mod _ _
    have hremQnonneg : 0 ≤ z % (Q N : ℤ) := Int.emod_nonneg _ hQne
    have hzNatLtInt : (z.toNat : ℤ) < (Q N : ℤ) := by
      simpa [Int.toNat_of_nonneg hzNonneg] using hzLt
    have hzNatLt : z.toNat < Q N := by exact_mod_cast hzNatLtInt
    have hmodNat : (z % (Q N : ℤ)).toNat = z.toNat := by
      have hmodNatCast : z.toNat % Q N = (z % (Q N : ℤ)).toNat := by
        apply Int.natCast_inj.mp
        calc
          ((z.toNat % Q N : ℕ) : ℤ) = z % (Q N : ℤ) := hmodCast
          _ = ((z % (Q N : ℤ)).toNat : ℤ) :=
            (Int.toNat_of_nonneg hremQnonneg).symm
      rw [Nat.mod_eq_of_lt hzNatLt] at hmodNatCast
      exact hmodNatCast.symm
    have hnewPoint :
      cellPoint A N l C z.toNat =
          cellPoint A N l C x + (T.modulus (corrScales MS) N p : ℤ) * S := by
      have hzCast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzNonneg
      change C.1 * (H N : ℤ) + (C.2 : ℤ) + (M N : ℤ) * (z.toNat : ℤ) =
        C.1 * (H N : ℤ) + (C.2 : ℤ) + (M N : ℤ) * x + (mp : ℤ) * S
      rw [hzCast, hratio]
      dsimp [z]
      ring
    change cellPoint A N l C x +
        (T.modulus (corrScales MS) N p : ℤ) * S =
      cellPoint A N l C ((z % (Q N : ℤ)).toNat)
    calc
      _ = cellPoint A N l C z.toNat := hnewPoint.symm
      _ = cellPoint A N l C ((z % (Q N : ℤ)).toNat) :=
        congrArg (cellPoint A N l C) hmodNat.symm
  have hsafeCube (h : ℤ → ℝ) (N : ℕ) (hQ : 0 < Q N) (p : Fin T.q → ℕ)
      (C : ℤ × ℕ) (hC : C ∈ cells A N i l) (x : ℕ) (hx : x < Q N)
      (hsafe : ¬ InBoundaryStrip (H N) (width N) (cellPoint A N l C x)) :
      rootCube h N p (cellPoint A N l C x) = wrappedCube h N p C x := by
    unfold rootCube wrappedCube
    apply shiftAverage_congr_of_mem
    intro u hu
    apply Finset.prod_congr rfl
    intro ω hω
    exact congrArg h (hsafeVertex N hQ p C hC x hx
      (T.length (corrScales MS) l J0 N p) rfl ω u hu hsafe)
  have hprodBound (F : Finset (Fin T.d) → ℝ) (hF : ∀ ω, |F ω| ≤ 1) :
      |∏ ω : Finset (Fin T.d), F ω| ≤ 1 := by
    rw [abs_prod]
    exact Finset.prod_le_one₀ (fun ω hω => abs_nonneg _) (fun ω hω => hF ω)
  have hrootAbs (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1) (N : ℕ)
      (p : Fin T.q → ℕ) (y : ℤ) :
      |rootCube h N p y| ≤ 1 := by
    unfold rootCube
    apply shiftAverage_abs_le
    · norm_num
    · intro u
      apply hprodBound
      intro ω
      exact hh _
  have hwrappedAbs (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1) (N : ℕ)
      (p : Fin T.q → ℕ) (C : ℤ × ℕ) (x : ℕ) :
      |wrappedCube h N p C x| ≤ 1 := by
    unfold wrappedCube
    apply shiftAverage_abs_le
    · norm_num
    · intro u
      apply hprodBound
      intro ω
      exact hh _
  have hrootWrapDiff (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1) (N : ℕ)
      (hQ : 0 < Q N) (p : Fin T.q → ℕ)
      (C : ℤ × ℕ) (hC : C ∈ cells A N i l) (x : ℕ) (hx : x < Q N) :
      |rootCube h N p (cellPoint A N l C x) - wrappedCube h N p C x| ≤
        2 * boundaryIndicator (H N) (width N) (cellPoint A N l C x) := by
    by_cases hsafe : ¬ InBoundaryStrip (H N) (width N) (cellPoint A N l C x)
    · rw [hsafeCube h N hQ p C hC x hx hsafe]
      simp [boundaryIndicator, hsafe]
    · have hstrip : InBoundaryStrip (H N) (width N) (cellPoint A N l C x) := by
        exact Classical.byContradiction hsafe
      rw [boundaryIndicator]
      simp only [if_pos hstrip]
      have hdiff : |rootCube h N p (cellPoint A N l C x) - wrappedCube h N p C x| ≤ 2 := by
        apply abs_le.mpr
        constructor <;> linarith [abs_le.mp (hrootAbs h hh N p (cellPoint A N l C x)),
          abs_le.mp (hwrappedAbs h hh N p C x)]
      linarith
  have hCubeAverageEq (N : ℕ) (h : ℤ → ℝ) :
      cubeAverage MS T l i J0 N h =
        goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N)
          (fun p => Emu A N i (rootCube h N p)) := by
    unfold cubeAverage CubeTemplate.cubeTest
    rfl
  have hPeriodizedEq (N : ℕ) (h : ℤ → ℝ) :
      periodizedCube MS T l i J0 N h =
        goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N)
          (periodizedAt h N) := by
    unfold periodizedCube periodizedAt
    rfl
  have hNormNonneg (N : ℕ) : 0 ≤ harmonicNormalizer (Xi N) (W N) := by
    unfold harmonicNormalizer
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hmuNonneg (N : ℕ) (z : ℤ) : 0 ≤ mu A N i z := by
    change 0 ≤ harmonicLaw (Xi N) (W N) z
    unfold harmonicLaw
    split_ifs
    · exact one_div_nonneg.mpr
        (mul_nonneg (by positivity) (hNormNonneg N))
    · positivity
  have hcellMassNonneg (N : ℕ) (C : ℤ × ℕ) : 0 ≤ cellMass A N i l C := by
    unfold cellMass
    apply Finset.sum_nonneg
    intro x hx
    exact hmuNonneg N (cellPoint A N l C x)
  have hcellUniformAbs (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
      (N : ℕ) (p : Fin T.q → ℕ) (C : ℤ × ℕ) (hQ : 0 < Q N) :
      |cellUniform h N p C| ≤ 1 := by
    have hQposR : 0 < (Q N : ℝ) := by exact_mod_cast hQ
    have hsum :
        |∑ x ∈ Finset.range (Q N), wrappedCube h N p C x| ≤ (Q N : ℝ) := by
      calc
        _ ≤ ∑ x ∈ Finset.range (Q N), |wrappedCube h N p C x| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x ∈ Finset.range (Q N), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x hx
          exact hwrappedAbs h hh N p C x
        _ = (Q N : ℝ) := by simp
    unfold cellUniform
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hQposR.le)]
    calc
      (Q N : ℝ)⁻¹ * |∑ x ∈ Finset.range (Q N), wrappedCube h N p C x| ≤
          (Q N : ℝ)⁻¹ * (Q N : ℝ) :=
            mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hQposR.le)
      _ = 1 := inv_mul_cancel₀ hQposR.ne'
  let rawUniform : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → ℝ := fun h N p =>
    ∑ C ∈ cells A N i l, cellMass A N i l C * cellUniform h N p C
  have hrawUniformAbs (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
      (N : ℕ) (p : Fin T.q → ℕ) (hQ : 0 < Q N) :
      |rawUniform h N p| ≤ totalCellMass N := by
    unfold rawUniform
    calc
      _ ≤ ∑ C ∈ cells A N i l,
          |cellMass A N i l C * cellUniform h N p C| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ C ∈ cells A N i l, cellMass A N i l C := by
          apply Finset.sum_le_sum
          intro C hC
          rw [abs_mul, abs_of_nonneg (hcellMassNonneg N C)]
          exact mul_le_of_le_one_right (hcellMassNonneg N C)
            (hcellUniformAbs h hh N p C hQ)
      _ = totalCellMass N := rfl
  have hPeriodizedDiv (h : ℤ → ℝ) (N : ℕ) (p : Fin T.q → ℕ)
      (hSpos : 0 < totalCellMass N) :
      periodizedAt h N p = rawUniform h N p / totalCellMass N := by
    unfold periodizedAt rawUniform cellWeight totalCellMass cellUniform
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro C hC
    field_simp [ne_of_gt hSpos]
    ring
  have hEmuSupportSum (N : ℕ) (f : ℤ → ℝ) :
      Emu A N i f =
        ∑ z ∈ harmonicLawIntSupport (Xi N) (W N), mu A N i z * f z := by
    change (∑' z : ℤ, harmonicLaw (Xi N) (W N) z * f z) = _
    exact harmonicLaw_expect_finset (Xi N) (W N) f
  have hnormPosFor (N : ℕ) (hcut : 4 * W N ≤ Xi N) :
      0 < harmonicNormalizer (Xi N) (W N) := by
    have hm := OAI.RawHarmonicProbability.mass_pos (Xi N) (W N)
      (primorial_pos _) hcut
    simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, one_div, Nat.coprime_comm] using hm
  have hSupportMassOne (N : ℕ) (hcut : 4 * W N ≤ Xi N) :
      (∑ z ∈ harmonicLawIntSupport (Xi N) (W N), mu A N i z) = 1 := by
    have hsum := harmonicLaw_tsum_eq_one (Xi N) (W N) (A.Xpos N i)
      (hnormPosFor N hcut)
    calc
      _ = ∑ z ∈ harmonicLawIntSupport (Xi N) (W N),
            mu A N i z * (1 : ℝ) := by simp
      _ = ∑' z : ℤ, harmonicLaw (Xi N) (W N) z := by
            simpa [mu] using
              (harmonicLaw_expect_finset (Xi N) (W N) (fun _ => 1)).symm
      _ = 1 := by simpa [mu] using hsum
  have himageSum (N : ℕ) (hQ : 0 < Q N) (f : ℤ → ℝ) :
      (∑ z ∈ pointImage N, mu A N i z * f z) =
        ∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
          mu A N i (cellPoint A N l C x) * f (cellPoint A N l C x) := by
    classical
    calc
      _ = ∑ z ∈ ((cells A N i l).product (Finset.range (Q N))),
          mu A N i (cellPoint A N l z.1 z.2) * f (cellPoint A N l z.1 z.2) := by
            dsimp [pointImage]
            exact Finset.sum_image (hpointInjective N hQ)
      _ = _ := Finset.sum_product' (cells A N i l) (Finset.range (Q N))
        (fun (C : ℤ × ℕ) (x : ℕ) =>
          mu A N i (cellPoint A N l C x) * f (cellPoint A N l C x))
  have hMassPartition (N : ℕ) (hQ : 0 < Q N) (hcut : 4 * W N ≤ Xi N) :
      totalCellMass N + tailMass N = 1 := by
    classical
    let S := harmonicLawIntSupport (Xi N) (W N)
    let I := pointImage N
    let J := S ∩ I
    have hJS : J ⊆ S := Finset.inter_subset_left
    have hJI : J ⊆ I := Finset.inter_subset_right
    have hIdiff : I \ J = I \ S := by
      ext z
      simp [J, and_left_comm, and_assoc]
    have hIextra : (∑ z ∈ I \ J, mu A N i z) = 0 := by
      rw [hIdiff]
      apply Finset.sum_eq_zero
      intro z hz
      have hzS : z ∉ S := (Finset.mem_sdiff.mp hz).2
      simpa [mu, S, Xi, W] using
        harmonicLaw_zero_of_not_mem (Xi N) (W N) z hzS
    have hIsplit := Finset.sum_sdiff (s₁ := J) (s₂ := I)
      (f := fun z => mu A N i z) hJI
    have hImageEq : (∑ z ∈ I, mu A N i z) = ∑ z ∈ J, mu A N i z := by
      linarith [hIsplit, hIextra]
    have hSdiff : S \ J = S \ I := by
      ext z
      simp [J, and_left_comm, and_assoc]
    have hSsplit := Finset.sum_sdiff (s₁ := J) (s₂ := S)
      (f := fun z => mu A N i z) hJS
    have hTailEq : tailMass N =
        (∑ z ∈ S, mu A N i z) - ∑ z ∈ J, mu A N i z := by
      change (∑ z ∈ S \ I, mu A N i z) = _
      rw [← hSdiff]
      linarith [hSsplit]
    have htotalEq :
        (∑ z ∈ S, mu A N i z) = totalCellMass N + tailMass N := by
      rw [hTailEq, ← hImageEq, ← hcellMassSum N hQ]
      ring
    have hsumS : (∑ z ∈ S, mu A N i z) = 1 := by
      simpa [S] using hSupportMassOne N hcut
    rw [← htotalEq, hsumS]
  have hSupportImageSplit (N : ℕ) (f : ℤ → ℝ) :
      (∑ z ∈ harmonicLawIntSupport (Xi N) (W N), mu A N i z * f z) =
        (∑ z ∈ pointImage N, mu A N i z * f z) +
          ∑ z ∈ (harmonicLawIntSupport (Xi N) (W N) \ pointImage N),
            mu A N i z * f z := by
    classical
    let S := harmonicLawIntSupport (Xi N) (W N)
    let I := pointImage N
    let J := S ∩ I
    have hJS : J ⊆ S := Finset.inter_subset_left
    have hJI : J ⊆ I := Finset.inter_subset_right
    have hIdiff : I \ J = I \ S := by ext z; simp [J]
    have hIextra : (∑ z ∈ I \ J, mu A N i z * f z) = 0 := by
      rw [hIdiff]
      apply Finset.sum_eq_zero
      intro z hz
      have hzS : z ∉ S := (Finset.mem_sdiff.mp hz).2
      have hμ : mu A N i z = 0 := by
        change harmonicLaw (Xi N) (W N) z = 0
        exact harmonicLaw_zero_of_not_mem (Xi N) (W N) z (by simpa [S] using hzS)
      rw [hμ]
      simp
    have hIsplit := Finset.sum_sdiff (s₁ := J) (s₂ := I)
      (f := fun z => mu A N i z * f z) hJI
    have hImageEq : (∑ z ∈ I, mu A N i z * f z) =
        ∑ z ∈ J, mu A N i z * f z := by
      rw [hIextra] at hIsplit
      linarith [hIsplit]
    have hSdiff : S \ J = S \ I := by ext z; simp [J]
    have hSsplit := Finset.sum_sdiff (s₁ := J) (s₂ := S)
      (f := fun z => mu A N i z * f z) hJS
    have hSupportSplit : (∑ z ∈ S, mu A N i z * f z) =
        (∑ z ∈ J, mu A N i z * f z) +
          ∑ z ∈ S \ I, mu A N i z * f z := by
      rw [← hSdiff]
      linarith [hSsplit]
    rw [hSupportSplit, hImageEq]

  have htailNonneg (N : ℕ) : 0 ≤ tailMass N := by
    unfold tailMass
    apply Finset.sum_nonneg
    intro z hz
    exact hmuNonneg N z
  have htotalNonneg (N : ℕ) : 0 ≤ totalCellMass N := by
    unfold totalCellMass
    apply Finset.sum_nonneg
    intro C hC
    exact hcellMassNonneg N C
  have htotalLeOne (N : ℕ) (hQ : 0 < Q N) (hcut : 4 * W N ≤ Xi N) :
      totalCellMass N ≤ 1 := by
    rw [← hMassPartition N hQ hcut]
    linarith [htailNonneg N]
  let imageRoot : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → ℝ := fun h N p =>
    ∑ z ∈ pointImage N, mu A N i z * rootCube h N p z
  let cellRootSum : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → ℝ := fun h N p =>
    ∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
      mu A N i (cellPoint A N l C x) * rootCube h N p (cellPoint A N l C x)
  let cellWrappedSum : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → ℝ := fun h N p =>
    ∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
      mu A N i (cellPoint A N l C x) * wrappedCube h N p C x
  let boundaryImageSum : ℕ → ℝ := fun N =>
    ∑ z ∈ pointImage N, mu A N i z * boundaryIndicator (H N) (width N) z
  let boundaryPairSum : ℕ → ℝ := fun N =>
    ∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
      mu A N i (cellPoint A N l C x) *
        boundaryIndicator (H N) (width N) (cellPoint A N l C x)
  let tailRoot : (ℤ → ℝ) → ℕ → (Fin T.q → ℕ) → ℝ := fun h N p =>
    ∑ z ∈ (harmonicLawIntSupport (Xi N) (W N) \ pointImage N),
      mu A N i z * rootCube h N p z
  have hImageRootEq (h : ℤ → ℝ) (N : ℕ) (hQ : 0 < Q N) (p : Fin T.q → ℕ) :
      imageRoot h N p = cellRootSum h N p := by
    dsimp [imageRoot, cellRootSum]
    exact himageSum N hQ (fun z => rootCube h N p z)
  have hImageDiffEq (h : ℤ → ℝ) (N : ℕ) (hQ : 0 < Q N) (p : Fin T.q → ℕ) :
      imageRoot h N p - cellWrappedSum h N p =
        ∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
          mu A N i (cellPoint A N l C x) *
            (rootCube h N p (cellPoint A N l C x) - wrappedCube h N p C x) := by
    rw [hImageRootEq h N hQ p]
    dsimp [cellRootSum, cellWrappedSum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro C hC
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hBoundaryPairEq (N : ℕ) (hQ : 0 < Q N) :
      boundaryImageSum N = boundaryPairSum N := by
    dsimp [boundaryImageSum, boundaryPairSum]
    exact himageSum N hQ (fun z => boundaryIndicator (H N) (width N) z)
  have hBoundaryImageLe (N : ℕ) :
      boundaryImageSum N ≤ Emu A N i (fun y => boundaryIndicator (H N) (width N) y) := by
    have hsplit := hSupportImageSplit N (fun y => boundaryIndicator (H N) (width N) y)
    have htail : 0 ≤
        ∑ z ∈ (harmonicLawIntSupport (Xi N) (W N) \ pointImage N),
          mu A N i z * boundaryIndicator (H N) (width N) z := by
      apply Finset.sum_nonneg
      intro z hz
      apply mul_nonneg (hmuNonneg N z)
      unfold boundaryIndicator
      split_ifs <;> positivity
    have heq : Emu A N i (fun y => boundaryIndicator (H N) (width N) y) =
        boundaryImageSum N +
          ∑ z ∈ (harmonicLawIntSupport (Xi N) (W N) \ pointImage N),
            mu A N i z * boundaryIndicator (H N) (width N) z := by
      calc
        _ = ∑ z ∈ harmonicLawIntSupport (Xi N) (W N),
            mu A N i z * boundaryIndicator (H N) (width N) z :=
              hEmuSupportSum N _
        _ = _ := hsplit
        _ = _ := rfl
    linarith
  have hTailRootBound (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
      (N : ℕ) (p : Fin T.q → ℕ) : |tailRoot h N p| ≤ tailMass N := by
    unfold tailRoot tailMass
    calc
      _ ≤ ∑ z ∈ harmonicLawIntSupport (Xi N) (W N) \ pointImage N,
          |mu A N i z * rootCube h N p z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ harmonicLawIntSupport (Xi N) (W N) \ pointImage N,
          mu A N i z := by
        apply Finset.sum_le_sum
        intro z hz
        rw [abs_mul, abs_of_nonneg (hmuNonneg N z)]
        exact mul_le_of_le_one_right (hmuNonneg N z) (hrootAbs h hh N p z)
  have hRootSplit (h : ℤ → ℝ) (N : ℕ) (p : Fin T.q → ℕ) :
      Emu A N i (rootCube h N p) = imageRoot h N p + tailRoot h N p := by
    calc
      _ = ∑ z ∈ harmonicLawIntSupport (Xi N) (W N),
          mu A N i z * rootCube h N p z := hEmuSupportSum N _
      _ = _ := hSupportImageSplit N (rootCube h N p)
      _ = _ := rfl
  have hRootImageBound (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
      (N : ℕ) (p : Fin T.q → ℕ) :
      |Emu A N i (rootCube h N p) - imageRoot h N p| ≤ tailMass N := by
    rw [hRootSplit]
    simpa only [add_sub_cancel_left] using hTailRootBound h hh N p
  have hDiffPairBound (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
      (N : ℕ) (hQ : 0 < Q N) (p : Fin T.q → ℕ) :
      |∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
          mu A N i (cellPoint A N l C x) *
            (rootCube h N p (cellPoint A N l C x) - wrappedCube h N p C x)| ≤
        2 * boundaryPairSum N := by
    calc
      _ ≤ ∑ C ∈ cells A N i l,
          |∑ x ∈ Finset.range (Q N),
            mu A N i (cellPoint A N l C x) *
              (rootCube h N p (cellPoint A N l C x) - wrappedCube h N p C x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
          |mu A N i (cellPoint A N l C x) *
            (rootCube h N p (cellPoint A N l C x) - wrappedCube h N p C x)| := by
          apply Finset.sum_le_sum
          intro C hC
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
          2 * (mu A N i (cellPoint A N l C x) *
            boundaryIndicator (H N) (width N) (cellPoint A N l C x)) := by
          apply Finset.sum_le_sum
          intro C hC
          apply Finset.sum_le_sum
          intro x hx
          rw [abs_mul, abs_of_nonneg (hmuNonneg N (cellPoint A N l C x))]
          have hdiff := hrootWrapDiff h hh N hQ p C hC x (Finset.mem_range.mp hx)
          calc
            mu A N i (cellPoint A N l C x) *
                |rootCube h N p (cellPoint A N l C x) - wrappedCube h N p C x| ≤
              mu A N i (cellPoint A N l C x) *
                (2 * boundaryIndicator (H N) (width N) (cellPoint A N l C x)) :=
              mul_le_mul_of_nonneg_left hdiff (hmuNonneg N (cellPoint A N l C x))
            _ = 2 * (mu A N i (cellPoint A N l C x) *
                boundaryIndicator (H N) (width N) (cellPoint A N l C x)) := by ring
      _ = 2 * boundaryPairSum N := by
          dsimp [boundaryPairSum]
          calc
            (∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
                2 * (mu A N i (cellPoint A N l C x) *
                  boundaryIndicator (H N) (width N) (cellPoint A N l C x))) =
                ∑ C ∈ cells A N i l, 2 * (∑ x ∈ Finset.range (Q N),
                  mu A N i (cellPoint A N l C x) *
                    boundaryIndicator (H N) (width N) (cellPoint A N l C x)) := by
              apply Finset.sum_congr rfl
              intro C hC
              rw [Finset.mul_sum]
            _ = 2 * ∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
                mu A N i (cellPoint A N l C x) *
                  boundaryIndicator (H N) (width N) (cellPoint A N l C x) := by
              rw [Finset.mul_sum]
  have hWrapRawDiffEq (h : ℤ → ℝ) (N : ℕ) (p : Fin T.q → ℕ) :
      cellWrappedSum h N p - rawUniform h N p =
        ∑ C ∈ cells A N i l,
          ((∑ x ∈ Finset.range (Q N),
            mu A N i (cellPoint A N l C x) * wrappedCube h N p C x) -
            cellMass A N i l C * cellUniform h N p C) := by
    dsimp [cellWrappedSum, rawUniform]
    rw [← Finset.sum_sub_distrib]
  have hWrapRawBound (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
      (N : ℕ) (hQ : 0 < Q N) (hcut : 4 * W N ≤ Xi N)
      (p : Fin T.q → ℕ) :
      |cellWrappedSum h N p - rawUniform h N p| ≤
        totalCellMass N * ((H N : ℝ) / (Xi N : ℝ)) := by
    rw [hWrapRawDiffEq]
    calc
      _ ≤ ∑ C ∈ cells A N i l,
          |(∑ x ∈ Finset.range (Q N),
            mu A N i (cellPoint A N l C x) * wrappedCube h N p C x) -
            cellMass A N i l C * cellUniform h N p C| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ C ∈ cells A N i l,
          cellMass A N i l C * ((H N : ℝ) / (Xi N : ℝ)) := by
          apply Finset.sum_le_sum
          intro C hC
          have hc := hcellComparison N hQ hcut C hC
            (fun x => wrappedCube h N p C x)
            (fun x hx => hwrappedAbs h hh N p C x)
          simpa [cellUniform] using hc
      _ = totalCellMass N * ((H N : ℝ) / (Xi N : ℝ)) := by
          simp [totalCellMass, Finset.sum_mul]
  have hPeriodizedNormBound (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
      (N : ℕ) (hQ : 0 < Q N) (hcut : 4 * W N ≤ Xi N)
      (p : Fin T.q → ℕ) (hSpos : 0 < totalCellMass N) :
      |rawUniform h N p - periodizedAt h N p| ≤ tailMass N := by
    have hpart := hMassPartition N hQ hcut
    have hfactor : 1 - (totalCellMass N)⁻¹ =
        -(tailMass N / totalCellMass N) := by
      calc
        1 - (totalCellMass N)⁻¹ =
            (totalCellMass N + tailMass N) - (totalCellMass N)⁻¹ := by rw [hpart]
        _ = -(tailMass N / totalCellMass N) := by
          field_simp [ne_of_gt hSpos]
          rw [hpart]
          linarith [hpart]
    rw [hPeriodizedDiv h N p hSpos]
    calc
      _ = |rawUniform h N p * (1 - (totalCellMass N)⁻¹)| := by
          congr 1
          ring
      _ = |rawUniform h N p| * (tailMass N / totalCellMass N) := by
          rw [abs_mul, hfactor, abs_neg,
            abs_of_nonneg (div_nonneg (htailNonneg N) (le_of_lt hSpos))]
      _ ≤ totalCellMass N * (tailMass N / totalCellMass N) :=
          mul_le_mul_of_nonneg_right (hrawUniformAbs h hh N p hQ)
            (div_nonneg (htailNonneg N) (le_of_lt hSpos))
      _ = tailMass N := by field_simp [ne_of_gt hSpos]
  have hPointwiseError (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
      (N : ℕ) (hQ : 0 < Q N) (hcut : 4 * W N ≤ Xi N)
      (hRad : radius N ≤ Xi N) (hHleX : H N ≤ Xi N)
      (htailLtOne : tailMass N < 1) (p : Fin T.q → ℕ) :
      |Emu A N i (rootCube h N p) - periodizedAt h N p| ≤
        2 * tailMass N + 2 * (168 * (d + 1 : ℝ) / J0 + boundaryError N) +
          (H N : ℝ) / (Xi N : ℝ) := by
    have hSpos : 0 < totalCellMass N := by
      have hPart := hMassPartition N hQ hcut
      have hSN := htotalNonneg N
      linarith [hPart, htailLtOne]
    have hSleOne := htotalLeOne N hQ hcut
    have hBoundary := hBoundaryN N hcut hRad
    have hBoundaryPair := hBoundaryPairEq N hQ
    have hRootWrapped : |imageRoot h N p - cellWrappedSum h N p| ≤
        2 * Emu A N i (fun y => boundaryIndicator (H N) (width N) y) := by
      calc
        _ = |∑ C ∈ cells A N i l, ∑ x ∈ Finset.range (Q N),
            mu A N i (cellPoint A N l C x) *
              (rootCube h N p (cellPoint A N l C x) - wrappedCube h N p C x)| :=
              congrArg abs (hImageDiffEq h N hQ p)
        _ ≤ 2 * boundaryPairSum N := hDiffPairBound h hh N hQ p
        _ = 2 * boundaryImageSum N := by rw [← hBoundaryPair]
        _ ≤ 2 * Emu A N i (fun y => boundaryIndicator (H N) (width N) y) :=
              mul_le_mul_of_nonneg_left (hBoundaryImageLe N) (by norm_num)
    have hWrapPeriodized : |cellWrappedSum h N p - periodizedAt h N p| ≤
        (H N : ℝ) / (Xi N : ℝ) + tailMass N := by
      calc
        _ = |(cellWrappedSum h N p - rawUniform h N p) +
              (rawUniform h N p - periodizedAt h N p)| := by congr 1; ring
        _ ≤ |cellWrappedSum h N p - rawUniform h N p| +
              |rawUniform h N p - periodizedAt h N p| := abs_add_le _ _
        _ ≤ totalCellMass N * ((H N : ℝ) / (Xi N : ℝ)) + tailMass N :=
              add_le_add (hWrapRawBound h hh N hQ hcut p)
                (hPeriodizedNormBound h hh N hQ hcut p hSpos)
        _ ≤ (H N : ℝ) / (Xi N : ℝ) + tailMass N := by
              have hXi : 0 < (Xi N : ℝ) := by exact_mod_cast A.Xpos N i
              have hmul := mul_le_mul_of_nonneg_right hSleOne (by positivity :
                0 ≤ (H N : ℝ) / (Xi N : ℝ))
              linarith
    have htriangle : |Emu A N i (rootCube h N p) - periodizedAt h N p| ≤
        |Emu A N i (rootCube h N p) - imageRoot h N p| +
          |imageRoot h N p - cellWrappedSum h N p| +
          |cellWrappedSum h N p - periodizedAt h N p| := by
      have h1 :
          |Emu A N i (rootCube h N p) - periodizedAt h N p| ≤
            |Emu A N i (rootCube h N p) - imageRoot h N p| +
              |imageRoot h N p - periodizedAt h N p| := by
        calc
          _ = |(Emu A N i (rootCube h N p) - imageRoot h N p) +
                (imageRoot h N p - periodizedAt h N p)| := by congr 1 <;> ring
          _ ≤ _ := abs_add_le _ _
      have h2 :
          |imageRoot h N p - periodizedAt h N p| ≤
            |imageRoot h N p - cellWrappedSum h N p| +
              |cellWrappedSum h N p - periodizedAt h N p| := by
        calc
          _ = |(imageRoot h N p - cellWrappedSum h N p) +
                (cellWrappedSum h N p - periodizedAt h N p)| := by congr 1 <;> ring
          _ ≤ _ := abs_add_le _ _
      calc
        _ ≤ |Emu A N i (rootCube h N p) - imageRoot h N p| +
              |imageRoot h N p - periodizedAt h N p| := h1
        _ ≤ _ := by linarith [h2]
    calc
      _ ≤ _ := htriangle
      _ ≤ tailMass N + 2 *
            Emu A N i (fun y => boundaryIndicator (H N) (width N) y) +
            ((H N : ℝ) / (Xi N : ℝ) + tailMass N) :=
          add_le_add (add_le_add (hRootImageBound h hh N p) hRootWrapped) hWrapPeriodized
      _ ≤ 2 * tailMass N +
            2 * (168 * (d + 1 : ℝ) / J0 + boundaryError N) +
            (H N : ℝ) / (Xi N : ℝ) := by
          have hB := mul_le_mul_of_nonneg_left hBoundary
            (by norm_num : (0 : ℝ) ≤ 2)
          linarith
  have hHleX : ∀ᶠ N in atTop, H N ≤ Xi N := by
    have hratio : ∀ᶠ N in atTop, (H N : ℝ) / (Xi N : ℝ) < 1 :=
      hHXi.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hratio] with N hN
    have hXiPos : 0 < (Xi N : ℝ) := by exact_mod_cast A.Xpos N i
    have hlt : (H N : ℝ) < (Xi N : ℝ) := by
      simpa using (div_lt_iff₀ hXiPos).mp hN
    exact_mod_cast hlt.le
  have hWleH : ∀ᶠ N in atTop, W N ≤ H N := by
    have hratio : ∀ᶠ N in atTop, (W N : ℝ) / (H N : ℝ) < 1 :=
      hWoverH.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hratio] with N hN
    have hHpos : 0 < (H N : ℝ) := by exact_mod_cast A.Hpos N l
    have hlt : (W N : ℝ) < (H N : ℝ) := by
      simpa using (div_lt_iff₀ hHpos).mp hN
    exact_mod_cast hlt.le
  let tailBound : ℕ → ℝ := fun N =>
    8 * (H N : ℝ) * (W N : ℝ) / (Xi N : ℝ)
  have hTailBoundRate : Tendsto tailBound atTop (𝓝 0) := by
    have hupper : Tendsto
        (fun N => 8 * ((H N : ℝ) ^ 2 / (Xi N : ℝ))) atTop (𝓝 0) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        hPartialRate.const_mul (8 : ℝ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall (fun N => by
        dsimp [tailBound]
        have hXi : 0 < (Xi N : ℝ) := by exact_mod_cast A.Xpos N i
        positivity)
    · filter_upwards [hWleH, Filter.Eventually.of_forall (fun N => A.Xpos N i)]
        with N hWH hXN
      have hWle : (W N : ℝ) ≤ (H N : ℝ) := by exact_mod_cast hWH
      have hHW : (H N : ℝ) * (W N : ℝ) ≤ (H N : ℝ) ^ 2 := by
        have hHnonneg : 0 ≤ (H N : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hWle hHnonneg]
      have hfrac := div_le_div_of_nonneg_right hHW (by positivity :
        0 ≤ (Xi N : ℝ))
      dsimp [tailBound]
      calc
        8 * (H N : ℝ) * (W N : ℝ) / (Xi N : ℝ) =
            8 * ((H N : ℝ) * (W N : ℝ) / (Xi N : ℝ)) := by ring
        _ ≤ 8 * ((H N : ℝ) ^ 2 / (Xi N : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac (by norm_num)
  have hTailMassRate : Tendsto (fun N => tailMass N) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTailBoundRate
    · exact Filter.Eventually.of_forall htailNonneg
    · filter_upwards [hqpos, hbase, hHleX] with N hQ hcut hHle
      simpa [tailBound] using hpartialMassBound N hQ hcut hHle
  let remainderError : ℕ → ℝ := fun N =>
    2 * tailMass N + 2 * boundaryError N + (H N : ℝ) / (Xi N : ℝ)
  have hRemainderRate : Tendsto remainderError atTop (𝓝 0) := by
    have hsum := (hTailMassRate.const_mul (2 : ℝ)).add
      ((hBoundaryRate.const_mul (2 : ℝ)).add hHXi)
    simpa [remainderError, boundaryError, add_assoc] using hsum
  have hRemainderSmall : ∀ᶠ N in atTop, remainderError N < ε :=
    hRemainderRate.eventually (Iio_mem_nhds hε)
  have hTailSmall : ∀ᶠ N in atTop, tailMass N < 1 :=
    hTailMassRate.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hqpos, hbase, hRleX, hHleX, hRemainderSmall, hTailSmall]
    with N hQ hcut hRad hHle hRsmall htailSmall
  intro h hh
  let err : ℝ :=
    2 * tailMass N + 2 * (168 * (d + 1 : ℝ) / J0 + boundaryError N) +
      (H N : ℝ) / (Xi N : ℝ)
  have hErrNonneg : 0 ≤ err := by
    dsimp [err, boundaryError]
    have hXi : 0 < (Xi N : ℝ) := by exact_mod_cast A.Xpos N i
    have hH : 0 < (H N : ℝ) := by exact_mod_cast A.Hpos N l
    have ht := htailNonneg N
    positivity
  have hPointwise : ∀ p, T.Good (corrScales MS) l N p →
      |Emu A N i (rootCube h N p) - periodizedAt h N p| ≤ err := by
    intro p hp
    exact hPointwiseError h hh N hQ hcut hRad hHle htailSmall p
  have hAvgBound := goodSlotAverage_abs_le (corrScales MS) l N
    (T.Good (corrScales MS) l N)
    (fun p => Emu A N i (rootCube h N p) - periodizedAt h N p)
    err hErrNonneg hPointwise
  have hAvgEq : cubeAverage MS T l i J0 N h - periodizedCube MS T l i J0 N h =
      goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N)
        (fun p => Emu A N i (rootCube h N p) - periodizedAt h N p) := by
    rw [hCubeAverageEq N h, hPeriodizedEq N h]
    exact (goodSlotAverage_sub (corrScales MS) l N
      (T.Good (corrScales MS) l N)
      (fun p => Emu A N i (rootCube h N p))
      (fun p => periodizedAt h N p)).symm
  have hErrSplit : err = 336 * (d + 1 : ℝ) / J0 + remainderError N := by
    dsimp [err, remainderError]
    ring
  have hErrLe : err ≤ 336 * (d + 1 : ℝ) / J0 + ε := by
    rw [hErrSplit]
    linarith
  calc
    _ = |goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N)
          (fun p => Emu A N i (rootCube h N p) - periodizedAt h N p)| :=
        congrArg abs hAvgEq
    _ ≤ err := hAvgBound
    _ ≤ 336 * (d + 1 : ℝ) / J0 + ε := hErrLe

set_option maxHeartbeats 200000
/-- (eq:prediction-cube-subgroup-bound), 05:538–578, finitary form: on `G = ℤ/qℤ` with cell
probabilities `α`, a subgroup step `a ∣ q` and shift length `L = ⌊q/(J₀a)⌋ ≥ 1`, the periodized
cube is at most `C_{d,J₀} ‖h‖_{U^{2^d}_{aG}(𝒳)}`; the increment density is `≤ (2J₀)^d` and `2^d`
Cauchy–Schwarz steps remove it.  The constant is independent of `q`, `a` and the cells. -/
theorem periodized_cube_le_subgroup_norm (d J0 : ℕ) (hJ0 : 0 < J0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q a : ℕ) [NeZero q], 0 < a → a ∣ q → 1 ≤ q / (J0 * a) →
      ∀ {Cl : Type} [Fintype Cl] (α : SubgroupBox.ProbWeights Cl) (f : Cl → ZMod q → ℝ),
        (∀ c x, |f c x| ≤ 1) →
        |∑ c, α.w c * 𝔼 x : ZMod q, shiftAverage (Fin d) (q / (J0 * a)) (fun u =>
            ∏ ω : Finset (Fin d),
              f c (x + (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q)))| ≤
          C * (∑ c, α.w c * (SubgroupBox.boxMoment
            (List.replicate (2 ^ d) (AddSubgroup.zmultiples (a : ZMod q)))
              (fun x => (f c x : ℂ))).re) ^ ((1 : ℝ) / 2 ^ (2 ^ d)) := by
  refine ⟨Real.sqrt ((2 * J0 : ℝ) ^ d), Real.sqrt_nonneg _, ?_⟩
  intro q a hq ha hadiv hL Cl hCl α f hf
  let L : ℕ := q / (J0 * a)
  have hLone : 1 ≤ L := by simpa [L] using hL
  have hLpos : 0 < L := by omega
  have hLdecomp : L = (q / a) / J0 := by
    dsimp [L]
    rw [Nat.mul_comm J0 a]
    exact (Nat.div_div_eq_div_mul q a J0).symm
  have hLn : L ≤ q / a := by
    rw [hLdecomp]
    exact Nat.div_le_self _ _
  have hJ0pos : 0 < J0 := hJ0
  have hn : q / a ≤ 2 * J0 * L := by
    have hremdiv : (q / a) % J0 + J0 * L = q / a := by
      have hh := Nat.mod_add_div (q / a) J0
      rw [← hLdecomp] at hh
      exact hh
    have hrem : (q / a) % J0 < J0 := Nat.mod_lt _ hJ0pos
    have hJL : J0 ≤ J0 * L := by
      simpa using Nat.mul_le_mul_left J0 hLone
    have hremle : (q / a) % J0 ≤ J0 * L := (Nat.le_of_lt hrem).trans hJL
    calc
      q / a = (q / a) % J0 + J0 * L := hremdiv.symm
      _ ≤ J0 * L + J0 * L := Nat.add_le_add_right hremle _
      _ = 2 * J0 * L := by ring
  simpa [L] using
    HindmanSumsProducts.Prediction.periodizedShiftCube_le_boxNorm
      ha hadiv hLpos hLn hn α f hf

/-- Combining the subgroups (05:580–585): for independent good tuples, `q_p` and `q_{p'}` are
coprime with probability `1 − o(1)` (§3 `rough_coprimality_survives_high_probability_restrictions`),
so `Q_p + Q_{p'} = G_l` (`SubgroupBox.zmultiples_sup_eq_top`) and the bad-pair mass of
`SubgroupBox.combine_subgroups` tends to `0`. -/
theorem good_pairs_coprime (MS : MasterScales K As sl Dm) (T : CubeTemplate) (hT : Allowed Dm T)
    (l : Fin K) :
    Tendsto (fun N => goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N) fun p =>
      goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N) fun p' =>
        if Nat.Coprime (cubeRatio T N p) (cubeRatio T N p') then (0 : ℝ) else 1)
      atTop (𝓝 0) := by
  classical
  let S := corrScales MS
  let goodN : ℕ → (Fin T.q → ℕ) → Prop := fun N p => T.Good S l N p
  let copN : ℕ → (Fin T.q → ℕ) → (Fin T.q → ℕ) → Prop := fun N p p' =>
    Nat.Coprime (cubeRatio T N p) (cubeRatio T N p')
  let lo : ℕ → Fin T.q → ℕ := fun N _ => (S.primeStage.pool N l).lower
  let hi : ℕ → Fin T.q → ℕ := fun N _ => (S.primeStage.pool N l).upper
  let pairGood : ℕ → ℝ := fun N =>
    independentPrimePairProbability (lo N) (hi N) (lo N) (hi N)
      (fun p p' => goodN N p ∧ goodN N p')
  let pairCoprime : ℕ → ℝ := fun N =>
    independentPrimePairProbability (lo N) (hi N) (lo N) (hi N)
      (fun p p' => goodN N p ∧ goodN N p' ∧ copN N p p')
  let pairBad : ℕ → ℝ := fun N =>
    independentPrimePairProbability (lo N) (hi N) (lo N) (hi N)
      (fun p p' => goodN N p ∧ goodN N p' ∧ ¬ copN N p p')
  have hGood : Tendsto (fun N => gapSlotProbability S l N (goodN N)) atTop (𝓝 1) := by
    simpa [goodN] using good_probability_tendsto_one MS T hT l
  have hEF : Tendsto (fun N => independentPrimePoolProbability (lo N) (hi N) (goodN N))
      atTop (𝓝 1) := by
    simpa [gapSlotProbability, lo, hi] using hGood
  have hD : T.D ≠ 0 := T.tests_ne_zero T.D T.D_mem
  have hLower : ∀ i : Fin T.q, Tendsto (fun N => (S.primeStage.pool N l).lower) atTop atTop :=
    fun _ => poolLower_tendsto MS l
  have hRough := rough_coprimality_survives_high_probability_restrictions
    T.D T.D hD hD
    (fun N _ => S.primeStage.pool N l) (fun N _ => S.primeStage.pool N l)
    goodN goodN hEF hEF hLower hLower
  have hPairCoprime : Tendsto pairCoprime atTop (𝓝 1) := by
    simpa [pairCoprime, lo, hi, goodN, copN, cubeRatio] using hRough
  have hPairGood : Tendsto pairGood atTop (𝓝 1) := by
    have hm := hGood.mul hGood
    simpa [pairGood, lo, hi, goodN, gapSlotProbability, pairProbability_product] using hm
  have hSplit : ∀ N, pairGood N = pairCoprime N + pairBad N := by
    intro N
    let E : (Fin T.q → ℕ) → (Fin T.q → ℕ) → Prop :=
      fun p p' => goodN N p ∧ goodN N p' ∧ copN N p p'
    let F : (Fin T.q → ℕ) → (Fin T.q → ℕ) → Prop :=
      fun p p' => goodN N p ∧ goodN N p' ∧ ¬ copN N p p'
    have hdisj : ∀ p p', ¬ (E p p' ∧ F p p') := by
      intro p p' h
      exact h.2.2.2 h.1.2.2
    have hadd := pairProbability_add_disjoint (lo N) (hi N) (lo N) (hi N) E F hdisj
    have hunion : (fun p p' => E p p' ∨ F p p') =
        (fun p p' => goodN N p ∧ goodN N p') := by
      funext p p'
      apply propext
      constructor
      · rintro (h | h) <;> exact ⟨h.1, h.2.1⟩
      · rintro ⟨hp, hp'⟩
        by_cases hc : copN N p p'
        · exact Or.inl ⟨hp, hp', hc⟩
        · exact Or.inr ⟨hp, hp', hc⟩
    dsimp [pairGood, pairCoprime, pairBad]
    rw [← hunion]
    exact hadd
  have hBad : Tendsto pairBad atTop (𝓝 0) := by
    have hDiff : Tendsto (fun N => pairGood N - pairCoprime N) atTop (𝓝 (1 - 1)) :=
      hPairGood.sub hPairCoprime
    have hEq : pairBad = fun N => pairGood N - pairCoprime N := by
      funext N
      linarith [hSplit N]
    rw [hEq]
    simpa using hDiff
  have hInv : Tendsto (fun N => (gapSlotProbability S l N (goodN N))⁻¹) atTop (𝓝 1) := by
    simpa using hGood.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hTargetEq :
      (fun N => goodSlotAverage S l N (T.Good S l N) fun p =>
        goodSlotAverage S l N (T.Good S l N) fun p' =>
          if Nat.Coprime (cubeRatio T N p) (cubeRatio T N p') then (0 : ℝ) else 1) =
      (fun N => (gapSlotProbability S l N (goodN N))⁻¹ *
        (gapSlotProbability S l N (goodN N))⁻¹ * pairBad N) := by
    funext N
    have hinner (p : Fin T.q → ℕ) :
        goodSlotAverage S l N (goodN N)
          (fun p' => @ite ℝ (copN N p p') (Classical.propDecidable _) 0 1) =
        goodSlotAverage S l N (goodN N)
          (fun p' => if Nat.Coprime (cubeRatio T N p) (cubeRatio T N p') then 0 else 1) := by
      apply congrArg (goodSlotAverage S l N (goodN N))
      funext p'
      by_cases hc : Nat.Coprime (cubeRatio T N p) (cubeRatio T N p')
      · simp [copN, hc]
      · simp [copN, hc]
    have houter :
        goodSlotAverage S l N (goodN N) (fun p =>
          goodSlotAverage S l N (goodN N) (fun p' =>
            @ite ℝ (copN N p p') (Classical.propDecidable _) 0 1)) =
        goodSlotAverage S l N (goodN N) (fun p =>
          goodSlotAverage S l N (goodN N) (fun p' =>
            if Nat.Coprime (cubeRatio T N p) (cubeRatio T N p') then 0 else 1)) := by
      apply congrArg (goodSlotAverage S l N (goodN N))
      funext p
      exact hinner p
    calc
      _ = goodSlotAverage S l N (goodN N) (fun p =>
          goodSlotAverage S l N (goodN N) (fun p' =>
            @ite ℝ (copN N p p') (Classical.propDecidable _) 0 1)) := houter.symm
      _ = _ := by
        simpa [goodN, copN, pairBad, lo, hi, cubeRatio] using
          nested_goodSlotAverage_bad_eq S l N (goodN N) (copN N)
  rw [hTargetEq]
  have hlim := (hInv.mul hInv).mul hBad
  simpa using hlim

/-- A fixed positive global norm forces a fixed positive fine projection (05:644–674, with
`InverseBridge.cyclic_inverse_menu` in place of 05:597–642): if `‖h‖^{2^t}_{U^t_{G_l}(𝒳_l)} ≥ δ^{2^t}`
along `𝒰`, the cellwise correlators (one finite menu of step `2(t−1) ≤ s`, raised to `s`,
re-based to the global progression index, `V = 2W − 1`, zero on the other cells) form a span
element `V` with `‖V‖ ≤ 1` and `⟨h, V⟩ ≥ c`, so `‖P_{i,l}h‖ ≥ c`.  `c` depends on `t, δ` only. -/
theorem projection_lower_bound (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 2 * (t - 1) ≤ s →
      ∀ {K : ℕ} (A : Parameters K) (i l : Fin K), l < i →
      ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.cofinite →
      ∀ h : ℕ → ℤ → ℝ, (∀ N y, |h N y| ≤ 1) →
        (∀ᶠ N in (U : Filter ℕ), δ ^ (2 ^ t) ≤ cellGlobalMoment A N i l t (h N)) →
        c ≤ projNorm A U i l s h := by
  change ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 2 * (t - 1) ≤ s →
    ∀ {K : ℕ} (A : Parameters K) (i l : Fin K), l < i →
    ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.cofinite →
    ∀ h : ℕ → ℤ → ℝ, (∀ N y, |h N y| ≤ 1) →
      (∀ᶠ N in (U : Filter ℕ), δ ^ (2 ^ t) ≤ p_g3_cellGlobalMoment A N i l t (h N)) →
      c ≤ projNorm A U i l s h
  exact p_g3_projection_lower_bound t ht δ hδ

/-- Lemma `lem:subgroup-inverse` (eq:prediction-subgroup-conclusion), 05:491–510, 676–683, with
the changed hypothesis `inverseStep d ≤ s`: for a cube type of order `d ≥ 1`, `J₀` and `γ > 0`
there is `κ(d, J₀, γ) > 0`, independent of the master count, the gap, the cutoffs and the cell
probabilities, such that every `[−1,1]`-valued family with `‖P_{i,l}h‖ < κ` has
`lim_𝒰 |E_{p,y,u} ∏_{ω⊆[d]} h(y + M(p) ∑_{j∈ω}(u_j^1 − u_j^0))| ≤ γ + O_d(J₀^{-1})`, the
constant depending on `d` only. -/
theorem subgroup_inverse :
    ∃ C : ℕ → ℝ, ∀ (d J0 : ℕ), 1 ≤ d → 0 < J0 → ∀ γ : ℝ, 0 < γ → ∃ κ : ℝ, 0 < κ ∧
      ∀ s : ℕ, inverseStep d ≤ s →
      ∀ {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
        (MS : MasterScales K As sl Dm) (T : CubeTemplate), Allowed Dm T → T.d = d →
      ∀ (i l : Fin K), l < i → ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.cofinite →
      ∀ h : ℕ → ℤ → ℝ, (∀ N y, |h N y| ≤ 1) →
        projNorm MS.core.parameters U i l s h < κ →
        UltrafilterUpperBound U (fun N => |cubeAverage MS T l i J0 N (h N)|) (γ + C d / J0) := by
  classical
  choose Cper hper using periodization_error
  refine ⟨Cper, ?_⟩
  intro d J0 hd hJ0 γ hγ
  obtain ⟨Ccube, hCcube, hcubeBound⟩ :=
    periodized_cube_le_subgroup_norm d J0 hJ0
  let k : ℕ := 2 ^ d
  let t : ℕ := inverseDegree d
  let rn : ℕ := 2 ^ k
  have hkpos : 1 ≤ k := by
    dsimp [k]
    have hp : 0 < 2 ^ d := by positivity
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp)
  have htwoPow : 2 ≤ 2 ^ d := by
    cases d with
    | zero => omega
    | succ d =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ d := Nat.pow_pos (by omega)
      nlinarith
  have ht : 2 ≤ t := by
    dsimp [t, inverseDegree]
    have hlarge : 4 ≤ 2 ^ (2 ^ d) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ d) := Nat.pow_le_pow_right (by omega) htwoPow
    omega
  let θ : ℝ := γ / (Ccube + 1)
  have hθ : 0 < θ := by
    dsimp [θ]
    positivity
  let β : ℝ := θ ^ (rn : ℝ)
  have hβ : 0 < β := by
    dsimp [β]
    exact Real.rpow_pos_of_pos hθ _
  have hβroot : β ^ ((1 : ℝ) / rn) = θ := by
    dsimp [β]
    have hmul : (rn : ℝ) * ((1 : ℝ) / rn) = 1 := by
      dsimp [rn, k]
      have hp : (0 : ℝ) < (2 ^ (2 ^ d) : ℝ) := by positivity
      field_simp
    calc
      (θ ^ (rn : ℝ)) ^ ((1 : ℝ) / rn) =
          θ ^ ((rn : ℝ) * ((1 : ℝ) / rn)) :=
        (Real.rpow_mul hθ.le _ _).symm
      _ = θ := by rw [hmul, Real.rpow_one]
  have hθbound : Ccube * θ ≤ γ := by
    dsimp [θ]
    have hden : 0 < Ccube + 1 := by linarith
    calc
      Ccube * (γ / (Ccube + 1)) ≤ (Ccube + 1) * (γ / (Ccube + 1)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = γ := by field_simp
  obtain ⟨δcomb, hδcomb, η, hη, hcombine⟩ :=
    SubgroupBox.combine_subgroups k hkpos β hβ
  let δg : ℝ := min 1 δcomb
  have hδg : 0 < δg := by
    dsimp [δg]
    exact lt_min (by norm_num) hδcomb
  have hδgpow : δg ^ (2 ^ t) ≤ δcomb := by
    have hpow : δg ^ (2 ^ t) ≤ δg :=
      pow_le_of_le_one hδg.le (min_le_left _ _) (by positivity)
    exact hpow.trans (min_le_right _ _)
  obtain ⟨cproj, hcproj, hprojection⟩ := projection_lower_bound t ht δg hδg
  let κ : ℝ := cproj / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  refine ⟨κ, hκ, ?_⟩
  intro s hs K sl As Dm MS T hT hTd i l hli U hU h hbound hproj ε hε
  let S := corrScales MS
  let goodN : ℕ → (Fin T.q → ℕ) → Prop := fun N p => T.Good S l N p
  let badPairSeq : ℕ → ℝ := fun N =>
    goodSlotAverage S l N (T.Good S l N) fun p =>
      goodSlotAverage S l N (T.Good S l N) fun p' =>
        if Nat.Coprime (cubeRatio T N p) (cubeRatio T N p') then (0 : ℝ) else 1
  have hgoodLimit : Tendsto (fun N => gapSlotProbability S l N (T.Good S l N))
      atTop (𝓝 1) := by
    simpa [S] using good_probability_tendsto_one MS T hT l
  have hgoodPosTop : ∀ᶠ N in atTop,
      0 < gapSlotProbability S l N (T.Good S l N) := by
    filter_upwards [hgoodLimit.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with N hN
    linarith
  have hgoodPosCof : ∀ᶠ N in Filter.cofinite,
      0 < gapSlotProbability S l N (T.Good S l N) := by
    simpa [Nat.cofinite_eq_atTop] using hgoodPosTop
  have hgoodPos : ∀ᶠ N in (U : Filter ℕ),
      0 < gapSlotProbability S l N (T.Good S l N) :=
    Filter.Eventually.filter_mono hU hgoodPosCof
  have hbadLimit : Tendsto badPairSeq atTop (𝓝 0) := by
    simpa [badPairSeq, S] using good_pairs_coprime MS T hT l
  have hbadTop : ∀ᶠ N in atTop, badPairSeq N < η :=
    hbadLimit.eventually (Iio_mem_nhds hη)
  have hbadCof : ∀ᶠ N in Filter.cofinite, badPairSeq N ≤ η := by
    have hbadTopLe : ∀ᶠ N in atTop, badPairSeq N ≤ η := by
      filter_upwards [hbadTop] with N hN
      exact hN.le
    simpa [Nat.cofinite_eq_atTop] using hbadTopLe
  have hbadU : ∀ᶠ N in (U : Filter ℕ), badPairSeq N ≤ η :=
    Filter.Eventually.filter_mono hU hbadCof
  have hpoolLower : Tendsto (fun N => (S.primeStage.pool N l).lower) atTop atTop :=
    pkgg2_poolLower_tendsto MS l
  have hpoolTop : ∀ᶠ N in atTop, 2 ≤ (S.primeStage.pool N l).lower :=
    hpoolLower.eventually_ge_atTop 2
  have hpoolCof : ∀ᶠ N in Filter.cofinite, 2 ≤ (S.primeStage.pool N l).lower :=
    by simpa [Nat.cofinite_eq_atTop] using hpoolTop
  have hpoolU : ∀ᶠ N in (U : Filter ℕ), 2 ≤ (S.primeStage.pool N l).lower :=
    Filter.Eventually.filter_mono hU hpoolCof
  have hmomentSmall : ∀ᶠ N in (U : Filter ℕ),
      cellGlobalMoment MS.core.parameters N i l t (h N) < δg ^ (2 ^ t) := by
    have hnot : ¬ ∀ᶠ N in (U : Filter ℕ),
        δg ^ (2 ^ t) ≤ cellGlobalMoment MS.core.parameters N i l t (h N) := by
      intro hlarge
      have hc := hprojection s (by simpa [t, inverseStep] using hs)
        MS.core.parameters i l hli U hU h hbound hlarge
      dsimp [κ] at hproj
      linarith
    have hnot' : ∀ᶠ N in (U : Filter ℕ),
        ¬ δg ^ (2 ^ t) ≤ cellGlobalMoment MS.core.parameters N i l t (h N) :=
      (U.eventually_not).2 hnot
    filter_upwards [hnot'] with N hN
    exact lt_of_not_ge hN
  have hmomentBound : ∀ᶠ N in (U : Filter ℕ),
      cellGlobalMoment MS.core.parameters N i l t (h N) ≤ δcomb := by
    filter_upwards [hmomentSmall] with N hN
    exact le_trans hN.le hδgpow
  have hperiodizedN : ∀ N,
      0 < gapSlotProbability S l N (T.Good S l N) →
      badPairSeq N ≤ η →
      cellGlobalMoment MS.core.parameters N i l t (h N) ≤ δcomb →
      2 ≤ (S.primeStage.pool N l).lower →
      |periodizedCube MS T l i J0 N (h N)| ≤ γ := by
    intro N hprob hbad hmoment hpool
    let A0 := MS.core.parameters
    let cellSet := cells A0 N i l
    let den : ℝ := ∑ C ∈ cellSet, cellMass A0 N i l C
    have hmassNonneg (C : ℤ × ℕ) : 0 ≤ cellMass A0 N i l C := by
      unfold cellMass
      apply Finset.sum_nonneg
      intro x hx
      exact mu_nonneg A0 N i (cellPoint A0 N l C x)
    have hdenNonneg : 0 ≤ den := by
      dsimp [den]
      apply Finset.sum_nonneg
      intro C hC
      exact hmassNonneg C
    by_cases hdenZero : den = 0
    · have hcellZero (C : ℤ × ℕ) (hC : C ∈ cellSet) :
          cellMass A0 N i l C = 0 := by
        have hle : cellMass A0 N i l C ≤ den := by
          dsimp [den]
          exact Finset.single_le_sum (fun C hC => hmassNonneg C) hC
        have hle0 : cellMass A0 N i l C ≤ 0 := by
          rw [hdenZero] at hle
          exact hle
        exact le_antisymm hle0 (hmassNonneg C)
      have hperZero : periodizedCube MS T l i J0 N (h N) = 0 := by
        unfold periodizedCube
        have hzero : (fun p =>
            ∑ C ∈ cells A0 N i l, cellWeight A0 N i l C *
              ((cellOrder A0 N l : ℝ)⁻¹ *
                ∑ x ∈ Finset.range (cellOrder A0 N l),
                  shiftAverage (Fin T.d) (T.length S l J0 N p) fun u =>
                    ∏ ω : Finset (Fin T.d),
                      h N (cellPoint A0 N l C
                        ((((x : ℤ) + (cubeRatio T N p : ℤ) *
                          ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) %
                            (cellOrder A0 N l : ℤ)).toNat)))) = fun _ => 0 := by
          funext p
          apply Finset.sum_eq_zero
          intro C hC
          simp [cellWeight, den, cellSet, hdenZero, hcellZero C hC]
        rw [hzero]
        simp [goodSlotAverage]
      rw [hperZero]
      simp
      exact hγ.le
    · have hdenPos : 0 < den := lt_of_le_of_ne hdenNonneg (Ne.symm hdenZero)
      let Cl : Type := {C : ℤ × ℕ // C ∈ cellSet}
      let α : SubgroupBox.ProbWeights Cl :=
        finsetMassProbWeights cellSet (cellMass A0 N i l)
          (fun C hC => hmassNonneg C) hdenPos
      have hαw (C : Cl) : α.w C = cellWeight A0 N i l C.1 := rfl
      let q : ℕ := cellOrder A0 N l
      have hqPos : 0 < q := by
        dsimp [q, cellOrder]
        exact Nat.div_pos (Nat.le_of_dvd (A0.Hpos N l) (A0.Hdiv N l)) (A0.Mpos N)
      letI : NeZero q := ⟨Nat.ne_of_gt hqPos⟩
      let lo : Fin T.q → ℕ := fun _ => (S.primeStage.pool N l).lower
      let hi : Fin T.q → ℕ := fun _ => (S.primeStage.pool N l).upper
      let good : (Fin T.q → ℕ) → Prop := T.Good S l N
      have hgoodProb : 0 < independentPrimePoolProbability lo hi good := by
        simpa [gapSlotProbability, S, lo, hi, good] using hprob
      let π : SubgroupBox.ProbWeights (PoolIndex lo hi) :=
        goodPoolProbWeights lo hi good hgoodProb
      let a : PoolIndex lo hi → ℕ := fun p => cubeRatio T N p.1
      rcases hT with ⟨ι, hlisted⟩
      have hRatioDvd (p : PoolIndex lo hi) (hp : good p.1) : a p ∣ q := by
        obtain ⟨p0, hp0lo, hp0hi, hp0prime⟩ :=
          primePool_exists_prime (S.primeStage.pool N l) hpool
        let pfull := extendPrimeTuple ι p.1 p0
        have hpfull : ∀ j : Fin sl,
            (S.primeStage.pool N l).lower ≤ pfull j ∧
              pfull j < (S.primeStage.pool N l).upper ∧ (pfull j).Prime := by
          intro j
          by_cases hex : ∃ i, ι i = j
          · obtain ⟨i, hi⟩ := hex
            have hval : pfull j = p.1 i := by
              rw [show j = ι i from hi.symm]
              exact extendPrimeTuple_on_image ι p.1 p0 i
            rw [hval]
            exact hp.1 i
          · have hval : pfull j = p0 := by
              simp [pfull, extendPrimeTuple, hex]
            rw [hval]
            exact ⟨hp0lo, hp0hi, hp0prime⟩
        have hDlisted : MvPolynomial.rename ι T.D ∈ Dm := hlisted T.D T.D_mem
        have hDne : evalIntegerPolynomial T.D (fun j => (p.1 j : ℤ)) ≠ 0 :=
          hp.2.2.1 T.D T.D_mem
        have hpEval :
            evalIntegerPolynomial T.D (fun j => (pfull (ι j) : ℤ)) =
              evalIntegerPolynomial T.D (fun j => (p.1 j : ℤ)) := by
          apply congrArg (evalIntegerPolynomial T.D)
          funext j
          have hval : pfull (ι j) = p.1 j := by
            simpa [pfull] using extendPrimeTuple_on_image ι p.1 p0 j
          exact congrArg Int.ofNat hval
        have hDneFull : evalIntegerPolynomial (MvPolynomial.rename ι T.D)
            (fun j => (pfull j : ℤ)) ≠ 0 := by
          rw [evalIntegerPolynomial_rename, hpEval]
          exact hDne
        have hgap := MS.gapStage.polynomial_values_divide_gap N l pfull
          (MvPolynomial.rename ι T.D) hDlisted hpfull hDneFull
        have hrough := roughPart_dvd_natAbs (w := N + 1) hDne
        have hmult : A0.M N * a p ∣
            A0.M N * (evalIntegerPolynomial T.D (fun j => (p.1 j : ℤ))).natAbs := by
          dsimp [a, cubeRatio]
          exact Nat.mul_dvd_mul_left _ hrough
        have hgap' : A0.M N *
            (evalIntegerPolynomial T.D (fun j => (p.1 j : ℤ))).natAbs ∣ A0.H N l := by
          have h' := hgap
          rw [evalIntegerPolynomial_rename, hpEval] at h'
          exact h'
        have hmulDvd : A0.M N * a p ∣ A0.H N l := hmult.trans hgap'
        dsimp [q, cellOrder]
        exact Nat.dvd_div_of_mul_dvd (by simpa [Nat.mul_comm] using hmulDvd)
      have hlengthEq (p : PoolIndex lo hi) :
          T.length S l J0 N p.1 = q / (J0 * a p) := by
        dsimp [CubeTemplate.length, shiftLength, directionModulus, cubeRatio, q, cellOrder, a]
        calc
          A0.H N l / (J0 * (A0.M N * roughPart (N + 1)
              (evalIntegerPolynomial T.D (fun j => (p.1 j : ℤ))))) =
              A0.H N l / (A0.M N *
                (J0 * roughPart (N + 1) (evalIntegerPolynomial T.D
                  (fun j => (p.1 j : ℤ))))) := by
                    congr 1
                    ring
          _ = (A0.H N l / A0.M N) /
                (J0 * roughPart (N + 1) (evalIntegerPolynomial T.D
                  (fun j => (p.1 j : ℤ)))) :=
              (Nat.div_div_eq_div_mul _ _ _).symm
      let Q : PoolIndex lo hi → AddSubgroup (ZMod q) := fun p =>
        AddSubgroup.zmultiples (a p : ZMod q)
      let fRaw : (ℤ × ℕ) → ZMod q → ℝ := fun C x =>
        h N (cellPoint A0 N l C x.val)
      let f : Cl → ZMod q → ℝ := fun C x => fRaw C.1 x
      let topMoment : (ℤ × ℕ) → ℝ := fun C =>
        (SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup (ZMod q)))
          (fun x => ((fRaw C x : ℝ) : ℂ))).re
      have hCellWeight (C : Cl) :
          α.w C = cellWeight A0 N i l C.1 := by rfl
      have hglobalFin :
          cellGlobalMoment A0 N i l t (h N) =
            ∑ C ∈ cellSet, cellWeight A0 N i l C * topMoment C := by
        have hqne : cellOrder A0 N l ≠ 0 := by
          exact Nat.ne_of_gt (by simpa [q] using hqPos)
        unfold cellGlobalMoment
        simp only [dif_neg hqne]
        dsimp [topMoment, fRaw, cellSet]
      have hglobalSubtype :
          (∑ C : Cl, cellWeight A0 N i l C.1 * topMoment C.1) =
            ∑ C ∈ cellSet, cellWeight A0 N i l C * topMoment C :=
        subtype_sum_eq_finset_sum cellSet (fun C => cellWeight A0 N i l C * topMoment C)
      have hglobalEq :
          cellGlobalMoment A0 N i l t (h N) =
            ∑ C : Cl, α.w C * topMoment C.1 := by
        calc
          _ = ∑ C ∈ cellSet, cellWeight A0 N i l C * topMoment C := hglobalFin
          _ = ∑ C : Cl, cellWeight A0 N i l C.1 * topMoment C.1 := hglobalSubtype.symm
          _ = ∑ C : Cl, α.w C * topMoment C.1 := by
            apply Finset.sum_congr rfl
            intro C hC
            rw [hCellWeight]
      have hfull :
          ∑ C : Cl, α.w C *
            (SubgroupBox.boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup (ZMod q)))
              (fun x => ((f C x : ℝ) : ℂ))).re ≤ δcomb := by
        have hglobalEq' : cellGlobalMoment A0 N i l t (h N) =
            ∑ C : Cl, α.w C *
              (SubgroupBox.boxMoment
                (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup (ZMod q)))
                (fun x => ((f C x : ℝ) : ℂ))).re := by
          simpa [topMoment, f, fRaw, t, k, inverseDegree] using hglobalEq
        rw [← hglobalEq']
        exact hmoment
      have hcop (p p' : PoolIndex lo hi) :
          Nat.Coprime (a p) (a p') → Q p ⊔ Q p' = ⊤ := by
        intro hp
        exact SubgroupBox.zmultiples_sup_eq_top q (a p) (a p') hp
      have hbadEq : badPairSeq N =
          ∑ p : PoolIndex lo hi, π.w p *
            ∑ p' : PoolIndex lo hi, π.w p' *
              (if Nat.Coprime (a p) (a p') then (0 : ℝ) else 1) := by
        simpa [badPairSeq, good, S, lo, hi, a] using
          goodSlotAverage_nested_eq_probWeights S l N good hgoodProb
            (fun p p' => if Nat.Coprime (cubeRatio T N p) (cubeRatio T N p') then
              (0 : ℝ) else 1)
      have hbadMass : SubgroupBox.badPairMass π Q ≤ η := by
        calc
          SubgroupBox.badPairMass π Q ≤
              ∑ p : PoolIndex lo hi, π.w p *
                ∑ p' : PoolIndex lo hi, π.w p' *
                  (if Nat.Coprime (a p) (a p') then (0 : ℝ) else 1) :=
            subgroupBadPairMass_le_coprimeBad π Q a hcop
          _ = badPairSeq N := hbadEq.symm
          _ ≤ η := hbad
      let momentP : PoolIndex lo hi → ℝ := fun p =>
        ∑ C : Cl, α.w C *
          (SubgroupBox.boxMoment (List.replicate k (Q p))
            (fun x => ((f C x : ℝ) : ℂ))).re
      have hmeanMoment : ∑ p : PoolIndex lo hi, π.w p * momentP p ≤ β := by
        have h := hcombine π Q α (fun C x => (f C x : ℂ))
          (by
            intro C x
            simpa [Complex.norm_real] using hbound N (cellPoint A0 N l C.1 x.val))
          hbadMass hfull
        simpa [momentP, t, k, inverseDegree] using h
      have hmomentPNonneg (p : PoolIndex lo hi) : 0 ≤ momentP p := by
        apply Finset.sum_nonneg
        intro C hC
        apply mul_nonneg (α.nonneg C)
        apply SubgroupBox.boxMoment_re_nonneg
        · have hkne : k ≠ 0 := by omega
          simp [hkne]
      let cellShiftAvg (C : ℤ × ℕ) (p : Fin T.q → ℕ) : ℝ :=
        𝔼 x : ZMod q, shiftAverage (Fin T.d) (T.length S l J0 N p) fun u =>
          ∏ ω : Finset (Fin T.d),
            fRaw C (x + (((cubeRatio T N p : ℤ) *
              ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q))
      let cellRangeAvg (C : ℤ × ℕ) (p : Fin T.q → ℕ) : ℝ :=
        (q : ℝ)⁻¹ * ∑ x ∈ Finset.range q,
          shiftAverage (Fin T.d) (T.length S l J0 N p) fun u =>
            ∏ ω : Finset (Fin T.d),
              h N (cellPoint A0 N l C
                ((((x : ℤ) + (cubeRatio T N p : ℤ) *
                  ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) % (q : ℤ)).toNat))
      let perTupleRaw (p : Fin T.q → ℕ) : ℝ :=
        ∑ C ∈ cellSet, cellWeight A0 N i l C * cellRangeAvg C p
      have hcellAvg (C : ℤ × ℕ) (p : Fin T.q → ℕ) :
          cellRangeAvg C p = cellShiftAvg C p := by
        dsimp [cellRangeAvg, cellShiftAvg]
        rw [expect_zmod_eq_range]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < q := Finset.mem_range.mp hx
        have hfun :
            (fun u : Fin T.d → Fin 2 → ℕ =>
              ∏ ω : Finset (Fin T.d),
                h N (cellPoint A0 N l C
                  ((((x : ℤ) + (cubeRatio T N p : ℤ) *
                    ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) % (q : ℤ)).toNat))) =
            (fun u : Fin T.d → Fin 2 → ℕ =>
              ∏ ω : Finset (Fin T.d),
                fRaw C (x + (((cubeRatio T N p : ℤ) *
                  ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q))) := by
          funext u
          apply Finset.prod_congr rfl
          intro ω hω
          let z : ℤ := (cubeRatio T N p : ℤ) *
            ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)
          have hcoord :
              (((x : ℕ) : ZMod q) + (z : ZMod q)).val =
                (((x : ℤ) + z) % (q : ℤ)).toNat := by
            simpa [ZMod.val_natCast_of_lt hxlt] using
              zmod_val_add_intCast_toNat ((x : ℕ) : ZMod q) z
          change h N (cellPoint A0 N l C
              ((((x : ℤ) + z) % (q : ℤ)).toNat)) =
            h N (cellPoint A0 N l C
              (((x : ℕ) : ZMod q) + (z : ZMod q)).val)
          exact congrArg (fun n => h N (cellPoint A0 N l C n)) hcoord.symm
        exact congrArg (shiftAverage (Fin T.d) (T.length S l J0 N p)) hfun
      have hperTuple (p : Fin T.q → ℕ) :
          perTupleRaw p =
            ∑ C : Cl, α.w C * cellShiftAvg C.1 p := by
        calc
          perTupleRaw p =
              ∑ C ∈ cellSet, cellWeight A0 N i l C * cellShiftAvg C p := by
                dsimp [perTupleRaw]
                apply Finset.sum_congr rfl
                intro C hC
                rw [hcellAvg]
          _ = ∑ C : Cl, cellWeight A0 N i l C.1 * cellShiftAvg C.1 p :=
                (subtype_sum_eq_finset_sum cellSet
                  (fun C => cellWeight A0 N i l C * cellShiftAvg C p)).symm
          _ = ∑ C : Cl, α.w C * cellShiftAvg C.1 p := by
                apply Finset.sum_congr rfl
                intro C hC
                rw [hCellWeight]
      have hperiodizedEq :
          periodizedCube MS T l i J0 N (h N) =
            goodSlotAverage S l N good (fun p =>
              ∑ C : Cl, α.w C * cellShiftAvg C.1 p) := by
        unfold periodizedCube
        apply congrArg (goodSlotAverage S l N good)
        funext p
        simpa [perTupleRaw, cellRangeAvg, cellSet, A0, q, cellOrder, S, hTd] using hperTuple p
      have hperiodizedEqRaw :
          periodizedCube MS T l i J0 N (h N) =
            goodSlotAverage S l N good perTupleRaw := by
        calc
          _ = goodSlotAverage S l N good (fun p =>
              ∑ C : Cl, α.w C * cellShiftAvg C.1 p) := hperiodizedEq
          _ = goodSlotAverage S l N good perTupleRaw := by
            apply congrArg (goodSlotAverage S l N good)
            funext p
            exact (hperTuple p).symm
      have hperiodizedSum :
          periodizedCube MS T l i J0 N (h N) =
            ∑ p : PoolIndex lo hi, π.w p * perTupleRaw p.1 := by
        rw [hperiodizedEqRaw]
        simpa [π] using
          goodSlotAverage_eq_probWeights S l N good hgoodProb perTupleRaw
      have hperPoint (p : PoolIndex lo hi) (hp : good p.1) :
          |perTupleRaw p.1| ≤ Ccube * (momentP p) ^ ((1 : ℝ) / rn) := by
        by_cases hLzero : T.length S l J0 N p.1 = 0
        · have hz : perTupleRaw p.1 = 0 := by
            have hfd : Nonempty (Fin T.d) := ⟨⟨0, by omega⟩⟩
            simp [perTupleRaw, cellRangeAvg, hLzero,
              shiftAverage_zero_of_nonempty hfd]
          rw [hz]
          simpa using mul_nonneg hCcube (Real.rpow_nonneg (hmomentPNonneg p) _)
        · have hLpos : 0 < T.length S l J0 N p.1 := Nat.pos_of_ne_zero hLzero
          have hadiv : a p ∣ q := hRatioDvd p hp
          have hLq : T.length S l J0 N p.1 = q / (J0 * a p) := hlengthEq p
          have hratioPos : 1 ≤ q / (J0 * a p) := by
            rw [← hLq]
            exact Nat.one_le_iff_ne_zero.mpr hLzero
          have haPos : 0 < a p := by
            dsimp [a, cubeRatio]
            exact roughPart_pos (N + 1)
              (evalIntegerPolynomial T.D (fun j => (p.1 j : ℤ)))
          have hcube := hcubeBound q (a p) haPos hadiv hratioPos α f
            (by
              intro C x
              simpa [Complex.norm_real, f] using
                hbound N (cellPoint A0 N l C.1 x.val))
          rw [hperTuple p.1]
          dsimp [cellShiftAvg]
          rw [hTd]
          simpa [cellShiftAvg, f, fRaw, a, Q, momentP, k, rn, hLq] using hcube
      have hmeanMomentNonneg :
          0 ≤ ∑ p : PoolIndex lo hi, π.w p * momentP p :=
        Finset.sum_nonneg fun p _ => mul_nonneg (π.nonneg p) (hmomentPNonneg p)
      have hJensen := probWeights_invPow_mean_le π momentP hmomentPNonneg rn (by positivity)
      have hmeanRpow :
          ∑ p : PoolIndex lo hi, π.w p * (momentP p) ^ ((1 : ℝ) / rn) ≤
            β ^ ((1 : ℝ) / rn) := by
        exact (hJensen.trans (Real.rpow_le_rpow hmeanMomentNonneg hmeanMoment (by positivity)))
      have hperAbs :
          |∑ p : PoolIndex lo hi, π.w p * perTupleRaw p.1| ≤ γ := by
        calc
          |∑ p : PoolIndex lo hi, π.w p * perTupleRaw p.1| ≤
              ∑ p : PoolIndex lo hi, π.w p * |perTupleRaw p.1| := by
                calc
                  _ ≤ ∑ p : PoolIndex lo hi, |π.w p * perTupleRaw p.1| :=
                    Finset.abs_sum_le_sum_abs _ _
                  _ = _ := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    rw [abs_mul, abs_of_nonneg (π.nonneg p)]
          _ ≤ ∑ p : PoolIndex lo hi,
                π.w p * (Ccube * (momentP p) ^ ((1 : ℝ) / rn)) := by
                  apply Finset.sum_le_sum
                  intro p hp
                  by_cases hgoodp : good p.1
                  · exact mul_le_mul_of_nonneg_left (hperPoint p hgoodp) (π.nonneg p)
                  · have hπzero : π.w p = 0 := by
                      simp [π, goodPoolProbWeights, good, hgoodp]
                    simp [hπzero]
          _ = Ccube *
                (∑ p : PoolIndex lo hi, π.w p * (momentP p) ^ ((1 : ℝ) / rn)) := by
                  calc
                    _ = ∑ p : PoolIndex lo hi,
                        Ccube * (π.w p * (momentP p) ^ ((1 : ℝ) / rn)) := by
                          apply Finset.sum_congr rfl
                          intro p hp
                          ring
                    _ = _ := by rw [Finset.mul_sum]
          _ ≤ Ccube * β ^ ((1 : ℝ) / rn) :=
                mul_le_mul_of_nonneg_left hmeanRpow hCcube
          _ ≤ γ := by
                rw [hβroot]
                exact hθbound
      rw [hperiodizedSum]
      exact hperAbs
  have hperiodizedU : ∀ᶠ N in (U : Filter ℕ),
      |periodizedCube MS T l i J0 N (h N)| ≤ γ := by
    filter_upwards [hgoodPos, hbadU, hmomentBound, hpoolU] with N hprob hbad hmoment hpool
    exact hperiodizedN N hprob hbad hmoment hpool
  have hperErrorTop : ∀ᶠ N in atTop,
      ∀ g : ℤ → ℝ, (∀ y, |g y| ≤ 1) →
        |cubeAverage MS T l i J0 N g - periodizedCube MS T l i J0 N g| ≤
          Cper d / J0 + ε / 2 :=
    hper d MS T hT hTd i l hli J0 hJ0 (ε / 2) (by linarith)
  have hperErrorCof : ∀ᶠ N in Filter.cofinite,
      ∀ g : ℤ → ℝ, (∀ y, |g y| ≤ 1) →
        |cubeAverage MS T l i J0 N g - periodizedCube MS T l i J0 N g| ≤
          Cper d / J0 + ε / 2 := by
    simpa [Nat.cofinite_eq_atTop] using hperErrorTop
  have hperErrorU : ∀ᶠ N in (U : Filter ℕ),
      ∀ g : ℤ → ℝ, (∀ y, |g y| ≤ 1) →
        |cubeAverage MS T l i J0 N g - periodizedCube MS T l i J0 N g| ≤
          Cper d / J0 + ε / 2 :=
    Filter.Eventually.filter_mono hU hperErrorCof
  filter_upwards [hperiodizedU, hperErrorU] with N hper herror
  have herror' := herror (h N) (hbound N)
  calc
    |cubeAverage MS T l i J0 N (h N)| ≤
        |cubeAverage MS T l i J0 N (h N) - periodizedCube MS T l i J0 N (h N)| +
          |periodizedCube MS T l i J0 N (h N)| := by
            calc
              _ = |(cubeAverage MS T l i J0 N (h N) -
                    periodizedCube MS T l i J0 N (h N)) +
                    periodizedCube MS T l i J0 N (h N)| := by congr 1 <;> ring
              _ ≤ _ := abs_add_le _ _
    _ ≤ (Cper d / J0 + ε / 2) + γ := add_le_add herror' hper
    _ ≤ γ + Cper d / J0 + ε := by linarith

end

end HindmanSumsProducts.Prediction
