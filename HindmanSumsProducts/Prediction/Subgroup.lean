import HindmanSumsProducts.Prediction.Projections
import HindmanSumsProducts.Concatenation
import HindmanSumsProducts.Prediction.PkgG
import HindmanSumsProducts.Prediction.Pkgg2
import HindmanSumsProducts.Prediction.PkgG3

/-!
# Subgroup cubes and the inverse theorem (§5.3, `05_prediction.tex` 432–683)

Lemma `lem:subgroup-inverse` with the two coordinator decisions applied:

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
    poolLower_tendsto MS l
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
