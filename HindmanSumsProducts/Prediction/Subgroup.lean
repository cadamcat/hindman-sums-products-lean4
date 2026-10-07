import HindmanSumsProducts.Prediction.Projections
import HindmanSumsProducts.Concatenation
import HindmanSumsProducts.Prediction.PkgG

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
  sorry

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
  sorry

end

end HindmanSumsProducts.Prediction
