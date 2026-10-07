import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.PkgPrime
import HindmanSumsProducts.Correlation.PkgMask
import HindmanSumsProducts.Correlation.PkgRows
import HindmanSumsProducts.Correlation.PkgElim
import HindmanSumsProducts.Correlation.PkgElim2
import HindmanSumsProducts.Correlation.PkgTest
import HindmanSumsProducts.Correlation.PkgTest2
import HindmanSumsProducts.Correlation.PkgOpusCorr
import HindmanSumsProducts.Correlation.PkgVarS

/-!
# Removing multiplicative masks and detecting a shifted error (§4)

Statements of `04_correlation.tex`. The setting and vocabulary are in `Correlation/Defs.lean`;
the §3 results used here are copied in `Correlation/FromArithmetic.lean`.

Order of choices (04:53–57, 135–155, 607–611). Everything determined by `m` and `J_*` (row
templates, polynomial directions, polynomial tests, `d`, `C_m`, `θ`) is chosen first. Then come
the master scales, whose polynomial list must contain the tests (`TestsListed`); then the chain,
its gap and its multipliers; then the fixed `J_0`; then `ε` and the threshold in `N`; the
functions come last. "Uniform over the functions" is the order `∀ ε, ∀ᶠ N, ∀ b g`.
-/

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section
attribute [local instance] Classical.propDecidable
open FromArithmetic

/-! ## Prime insertion (Lemma `lem:prime-insertion`, 04:61–111) -/

/-- Equation `eq:prime-average-insertion`: for a pivot `i` after the gap `l`, `Y ∼ μ_i` and
`p ∼ λ_l`, `E F(Y)=E F(pY)+o(1)` uniformly over `|F| ≤ V_l^A`. Parameters are covered by the
uniformity in `F`. -/
theorem prime_insertion_average {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K)
    (hli : l < i) (A : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ F : ℤ → ℝ,
      (∀ y, |F y| ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A) →
      |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y * F y) -
        poolAverage S l N fun p =>
          ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            F ((p : ℤ) * y)| ≤ ε := by
  exact prime_insertion_average_aux S l i hli A

/-- Equation `eq:prime-fixed-dilation`: for `k` coprime to `W` and at most `(P_l^++V_l)^B`,
uniformly in `k`, the total mass `‖Law(kY)-k1_{k∣Y}μ_i‖₁` is smaller than every fixed negative
power of `P_l^++V_l`, and hence `E F(kY)=E k1_{k∣Y}F(Y)+o(1)` uniformly over `|F| ≤ V_l^A`. -/
theorem prime_insertion_fixed_dilation {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K)
    (hli : l < i) (B : ℕ) :
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      Nat.Coprime k (primorial (N + 1)) →
      k ≤ ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B →
      (((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℕ) : ℝ) ^ C *
        arithmeticL1
          (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
          (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
        ≤ ε) ∧
    ∀ A : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      Nat.Coprime k (primorial (N + 1)) →
      k ≤ ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B →
      ∀ F : ℤ → ℝ, (∀ y, |F y| ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A) →
        |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            F ((k : ℤ) * y)) -
          ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            ((if (k : ℤ) ∣ y then (k : ℝ) else 0) * F y)| ≤ ε := by
  exact prime_insertion_fixed_dilation_aux S l i hli B

/-- Lemma `lem:prime-insertion` (04:61–111), both assertions. -/
theorem prime_insertion {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K)
    (hli : l < i) :
    (∀ A : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ F : ℤ → ℝ,
      (∀ y, |F y| ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A) →
      |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y * F y) -
        poolAverage S l N fun p =>
          ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
            F ((p : ℤ) * y)| ≤ ε) ∧
    ∀ B : ℕ,
      (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k : ℕ, 0 < k →
        Nat.Coprime k (primorial (N + 1)) →
        k ≤ ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B →
        (((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l : ℕ) : ℝ) ^ C *
          arithmeticL1
            (dilatedLaw (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
            (dilationReference (harmonicLaw (S.core.parameters.X N i) (primorial (N + 1))) k)
          ≤ ε) ∧
      ∀ A : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k : ℕ, 0 < k →
        Nat.Coprime k (primorial (N + 1)) →
        k ≤ ((S.primeStage.pool N l).upper + FromArithmetic.masterScaleV S.core.parameters N l) ^ B →
        ∀ F : ℤ → ℝ, (∀ y, |F y| ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ^ A) →
          |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
              F ((k : ℤ) * y)) -
            ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
              ((if (k : ℤ) ∣ y then (k : ℝ) else 0) * F y)| ≤ ε :=
  ⟨fun A => prime_insertion_average S l i hli A,
    fun B => prime_insertion_fixed_dilation S l i hli B⟩

/-! ## Weighted Cauchy–Schwarz (equations `eq:mask-weighted-cs`, `eq:additive-weighted-cs`) -/

/-- `|E H₀H₁|² ≤ (E Ω)(E ΩH₁²)` for a nonnegative weight `μ`, `Ω ≥ 0` and `|H₀| ≤ Ω`. This is the
exact inequality behind both `eq:mask-weighted-cs` (`H₀=b_UΩ`, `H₁=E_pη_pH_p`) and
`eq:additive-weighted-cs` (`H₀=H_out`, `H₁=E_{u_R}H_in`); expanding `H₁²` with two independent
copies gives the displayed right sides. -/
theorem weighted_cauchy_schwarz {α : Type*} (μ Ω H₀ H₁ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hΩ : ∀ x, 0 ≤ Ω x) (h0 : ∀ x, |H₀ x| ≤ Ω x)
    (hΩs : Summable fun x => μ x * Ω x)
    (h1s : Summable fun x => μ x * (Ω x * H₁ x ^ 2)) :
    |∑' x, μ x * (H₀ x * H₁ x)| ^ 2 ≤
      (∑' x, μ x * Ω x) * ∑' x, μ x * (Ω x * H₁ x ^ 2) := by
  exact weighted_cauchy_schwarz_aux μ Ω H₀ H₁ hμ hΩ h0 hΩs h1s

/-! ## Weighted removal of multiplicative masks (Lemma `lem:mask-removal`, 04:128–307) -/

/-- Part of Lemma `lem:mask-removal`: one step with the one-coordinate substitution
`z_u ↦ pz_u` (04:175–178), for `u ∈ J_*` outside the removed mask `U`. -/
theorem opus_corr_mask_step_outside {m q r : ℕ} (Jstar : Finset (Fin m)) (hJ : 2 ≤ Jstar.card)
    (Sh : RowShape m q r) (hStar : (Sh.row Sh.star).support = Jstar)
    (masks : Finset (Finset (Fin m))) (U : Finset (Fin m)) (hU : U ∈ masks)
    (u : Fin m) (huJ : u ∈ Jstar) (huU : u ∉ U) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r') (tests : Finset (IntegerPolynomial (q + 2)))
      (C₁ : ℝ),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar ∧ (∀ P ∈ tests, P ≠ 0) ∧ 0 < C₁ ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin (q + 2) ↪ Fin s),
        TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ∀ (st : MaskRemovalState m q r) (gstar : ℤ → ℝ),
          st.shape = Sh → st.masks = masks → st.Valid S C a N Jstar gstar →
          ∃ st' : MaskRemovalState m (q + 2) r',
            st'.shape = Sh' ∧ st'.masks = masks.erase U ∧ st'.Valid S C a N Jstar gstar ∧
            |st.correlation S C a N| ^ 2 ≤ C₁ * |st'.correlation S C a N| + ε := by
  sorry

/-- Part of Lemma `lem:mask-removal`: one step with the balanced substitution
`z_u ↦ z_u/p`, `z_v ↦ pz_v` (equation `eq:balanced-prime-substitution`, 04:176–186), for distinct
`u, v ∈ J_*` when `J_*` is contained in the removed mask `U`. -/
theorem opus_corr_mask_step_balanced {m q r : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) (Sh : RowShape m q r) (hStar : (Sh.row Sh.star).support = Jstar)
    (masks : Finset (Finset (Fin m))) (U : Finset (Fin m)) (hU : U ∈ masks)
    (hJU : Jstar ⊆ U) (u v : Fin m) (huJ : u ∈ Jstar) (hvJ : v ∈ Jstar) (huv : u ≠ v) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r') (tests : Finset (IntegerPolynomial (q + 2)))
      (C₁ : ℝ),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar ∧ (∀ P ∈ tests, P ≠ 0) ∧ 0 < C₁ ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin (q + 2) ↪ Fin s),
        TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ∀ (st : MaskRemovalState m q r) (gstar : ℤ → ℝ),
          st.shape = Sh → st.masks = masks → st.Valid S C a N Jstar gstar →
          ∃ st' : MaskRemovalState m (q + 2) r',
            st'.shape = Sh' ∧ st'.masks = masks.erase U ∧ st'.Valid S C a N Jstar gstar ∧
            |st.correlation S C a N| ^ 2 ≤ C₁ * |st'.correlation S C a N| + ε := by
  sorry

/-- One mask-removal step (04:173–297): the outside substitution when `J_*` has a coordinate
outside `U`, the balanced one otherwise. -/
theorem opus_corr_mask_step (m : ℕ) (Jstar : Finset (Fin m)) (hJ : 2 ≤ Jstar.card) :
    opus_corr_MaskStep m Jstar := by
  intro q r Sh hStar masks U hU
  by_cases hout : ∃ u ∈ Jstar, u ∉ U
  · obtain ⟨u, huJ, huU⟩ := hout
    exact opus_corr_mask_step_outside Jstar hJ Sh hStar masks U hU u huJ huU
  · have hJU : Jstar ⊆ U := by
      intro x hx
      by_contra hxU
      exact hout ⟨x, hx, hxU⟩
    obtain ⟨u, huJ, v, hvJ, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < Jstar.card)
    exact opus_corr_mask_step_balanced Jstar hJ Sh hStar masks U hU hJU u v huJ hvJ huv

/-- Lemma `lem:mask-removal`, equation `eq:mask-removal-output`:
`|𝒞|^{2^{q_mask}} ≤ C_m|E_{p,z}∏_R f_R(ℓ_R(z))|+o(1)`. The row family (at most `K_m` pairwise
nonparallel templates, the distinguished row having support `J_*`), the number of prime slots,
the polynomial tests used for deletion and pair independence, and `C_m` depend only on `m` and
`J_*`. The functions `f_R` may depend on the primes; `|f_R| ≤ W_R=1+ν_{a(R)}` and `f_*=g_*`.
The primes are independent with law `λ_l` (before deletion of exceptional tuples). -/
theorem weighted_mask_removal (m : ℕ) (Jstar : Finset (Fin m)) (hJ : 2 ≤ Jstar.card) :
    ∃ (q r : ℕ) (Sh : RowShape m q r) (tests : Finset (IntegerPolynomial q)) (Cm : ℝ),
      r ≤ maskRowBound m ∧ q ≤ 2 * maskCount m ∧ (Sh.row Sh.star).support = Jstar ∧
      (∀ P ∈ tests, P ≠ 0) ∧ 0 < Cm ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s), TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ b g : Finset (Fin m) → ℤ → ℝ,
        FunctionsValid S.core.parameters C N b g →
        ∃ f : Fin r → (Fin q → ℕ) → ℤ → ℝ,
          (∀ R p y, |f R p y| ≤ 1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) ∧
          (∀ p, f Sh.star p = g Jstar) ∧
          |maskedCorrelation S.core.parameters C a N b g| ^ (2 ^ maskCount m) ≤
            Cm * |rowCorrelation S C a N Sh f| + ε := by
  classical
  obtain ⟨q, r, Sh, tests, Cm, hq, hr, hStar, htests, hCm, hmain⟩ :=
    opus_corr_mask_iterate m Jstar hJ (opus_corr_mask_step m Jstar hJ)
      (nonemptyMaskFinset m).toList (Finset.nodup_toList _)
      (fun U hU => by simpa [nonemptyMaskFinset] using hU)
  have hlen : (nonemptyMaskFinset m).toList.length = maskCount m := by
    rw [Finset.length_toList, nonemptyMaskFinset_card]
  refine ⟨q, r, Sh, tests, Cm, ?_, ?_, hStar, htests, hCm, ?_⟩
  · unfold maskRowBound
    rw [hlen] at hr
    exact hr
  · rw [hq, hlen]
  · intro K s Aset Dm S ι hlisted C a ha ε hε
    filter_upwards [hmain S ι hlisted C a ha ε hε] with N hN
    intro b g hv
    obtain ⟨st, hsh, hmasks, hvalid, hineq⟩ := hN b g hv
    subst hsh
    have hempty : st.masks = ∅ := by
      rw [hmasks, Finset.toList_toFinset, Finset.sdiff_self]
    refine ⟨st.rowFunction, hvalid.2.2.1, hvalid.2.2.2, ?_⟩
    rw [← MaskRemovalState.correlation_empty st S C a N hempty, ← hlen]
    exact hineq

/-! ## Polynomial directions and integer translations (Lemma `lem:row-directions`,
04:316–418) -/

/-- First part of Lemma `lem:row-directions` (04:357–373): for a pairwise nonparallel family
there are integer polynomial vectors `w_R` (`R ≠ *`) and `w_0` with `A_Rw_R=0`,
`A_Iw_R ≠ 0` (`I ≠ R`), `A_*w_0=0`, `A_Iw_0 ≠ 0` (`I ≠ *`), chosen from the templates alone. -/
theorem row_directions_polynomial {m q r : ℕ} (Sh : RowShape m q r) :
    ∃ dirs : RowDirections Sh, dirs.Valid := by
  classical
  have starSep (I : Fin r) (hI : I ≠ Sh.star) :
      ¬ (Sh.row Sh.star).Parallel (Sh.row I) := Sh.nonparallel Sh.star I (Ne.symm hI)
  obtain ⟨w0, hw0, hw0other⟩ :=
    rowDirections_exists_kernel_separating Sh Sh.star starSep
  let w : Fin r → Fin m → IntegerPolynomial q := fun R =>
    if hR : R ≠ Sh.star then
      Classical.choose (rowDirections_exists_kernel_separating Sh R
        (fun I hI => Sh.nonparallel R I (Ne.symm hI)))
    else fun _ => 0
  have hw (R : Fin r) (hR : R ≠ Sh.star) :
      templateResponse (Sh.row R) (w R) = 0 ∧
        ∀ I, I ≠ R → templateResponse (Sh.row I) (w R) ≠ 0 := by
    simpa [w, hR] using Classical.choose_spec
      (rowDirections_exists_kernel_separating Sh R
        (fun I hI => Sh.nonparallel R I (Ne.symm hI)))
  refine ⟨⟨w, w0⟩, ?_⟩
  refine ⟨?_, ?_, hw0, hw0other⟩
  · intro R hR
    exact (hw R hR).1
  · intro R I hR hIR
    exact (hw R hR).2 I hIR

/-- The conclusions of the second part of Lemma `lem:row-directions` for fixed directions and
tests, with size exponent `B`: for all master scales whose list contains the tests, every chain
and multipliers from `Aset`, (i) the non-good tuples have probability `o(1)` (04:378–380),
(ii) `M(p) ∣ R_l` on good tuples for all large `N` (04:610–611, 702–704; at small `N` the
modulus need not divide `R_l`), (iii) eventually every good tuple
satisfies `IntegerDirectionFacts`. -/
def RowDirections.IntegerConclusions {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q)) (B : ℕ) : Prop :=
  ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s), TestsListed Dm ι tests →
  ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
    Tendsto (fun N => gapSlotProbability S C.gap N fun p =>
      ¬ GoodTuple S C.gap N tests dirs.poly p) atTop (𝓝 0) ∧
    (∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      directionModulus S N dirs.poly p ∣ S.core.parameters.H N C.gap) ∧
    ∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      IntegerDirectionFacts S C a N dirs tests B p

/-- Second part of Lemma `lem:row-directions` (04:337–354, 375–418): integrality, size and
responses of `v_R`, `v_0` on the good tuples, for any test list containing `D`, the nonzero
responses and the nonzero template minors. The exponent `B` depends only on the templates and
directions. -/
theorem row_directions_integer {m q r : ℕ} (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (hdirs : dirs.Valid) (tests : Finset (IntegerPolynomial q))
    (htests : ∀ P ∈ tests, P ≠ 0) (hdt : dirs.tests ⊆ tests) :
    ∃ B : ℕ, dirs.IntegerConclusions tests B := by
  obtain ⟨B, hcore⟩ := row_directions_integer_core Sh dirs hdirs tests htests hdt
  refine ⟨B, ?_⟩
  intro K s Aset Dm S ι hlisted C a ha
  exact hcore S ι hlisted C a ha

/-- Lemma `lem:row-directions` (04:322–418). -/
theorem row_directions {m q r : ℕ} (Sh : RowShape m q r) :
    ∃ dirs : RowDirections Sh, dirs.Valid ∧
      ∀ tests : Finset (IntegerPolynomial q), (∀ P ∈ tests, P ≠ 0) → dirs.tests ⊆ tests →
        ∃ B : ℕ, dirs.IntegerConclusions tests B := by
  obtain ⟨dirs, hdirs⟩ := row_directions_polynomial Sh
  exact ⟨dirs, hdirs, fun tests htests hdt =>
    row_directions_integer Sh dirs hdirs tests htests hdt⟩

/-! ## Weighted additive elimination (Lemma `lem:additive-elimination`, 04:420–573) -/

/-- Equation `eq:auxiliary-weight-moments` (04:530–571): with `d=|ℛ|-1` and `t=d2^{d-1}`,
`E B=2^{2^d}+o(1)`, `E BH=2^{2^d+t}+o(1)`, `E BH²=2^{2^d+2t}+o(1)`, the expectations being over
the normalized good-tuple law, the pivots and the shifts on `[0,L(p))`. -/
theorem additive_elimination_auxiliary_moments {m q r : ℕ} (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (hdirs : dirs.Valid) (tests : Finset (IntegerPolynomial q))
    (htests : ∀ P ∈ tests, P ≠ 0) (hdt : dirs.tests ⊆ tests) :
    ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
      (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s), TestsListed Dm ι tests →
    ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
    ∀ J0 : ℕ, 0 < J0 →
      Tendsto (fun N => eliminationAverage S C N dirs tests J0 fun p z u =>
          targetBound S C a N dirs p z u) atTop
        (𝓝 ((2 : ℝ) ^ 2 ^ Fintype.card (NonTarget Sh))) ∧
      Tendsto (fun N => eliminationAverage S C N dirs tests J0 fun p z u =>
          targetBound S C a N dirs p z u * averagedRetainedWeights S C a N dirs p z u) atTop
        (𝓝 ((2 : ℝ) ^ (2 ^ Fintype.card (NonTarget Sh) +
          Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1)))) ∧
      Tendsto (fun N => eliminationAverage S C N dirs tests J0 fun p z u =>
          targetBound S C a N dirs p z u * averagedRetainedWeights S C a N dirs p z u ^ 2)
        atTop
        (𝓝 ((2 : ℝ) ^ (2 ^ Fintype.card (NonTarget Sh) +
          2 * (Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1))))) := by
  intro K s Aset Dm S ι hlisted C a ha J0 hJ0
  obtain ⟨B, hconclusions⟩ := row_directions_integer Sh dirs hdirs tests htests hdt
  rcases hconclusions S ι hlisted C a ha with ⟨hbad, hmodulus, hfactsEvent⟩
  let hGlobalEvent :=
    AdditiveMoment.pkgElim_momentGlobalData_eventually S C a ha Sh dirs tests J0 B hJ0 hfactsEvent
  let h : ℕ := Fintype.card (AdditiveMoment.Occurrence Sh)
  let d : ℕ := Fintype.card (AdditiveMoment.Coordinate Sh)
  let eO : AdditiveMoment.Occurrence Sh ≃ Fin h := Fintype.equivFin _
  let eX : AdditiveMoment.Coordinate Sh ≃ Fin d := Fintype.equivFin _
  have hEach (F : Finset (AdditiveMoment.Occurrence Sh)) :
      Tendsto (AdditiveMoment.pkgElim_expandedAuxiliaryMoment S ι C a Sh dirs tests J0 eX F)
        atTop (𝓝 1) :=
    AdditiveMoment.pkgElim_expandedAuxiliaryMoment_tendsto_one S ι C a ha Sh dirs tests hlisted
      J0 hJ0 B hbad hfactsEvent eO eX F
  have hmoment (k : ℕ) (hk : k ≤ 2) :
      Tendsto
        (fun N => eliminationAverage S C N dirs tests J0 fun p z u =>
          targetBound S C a N dirs p z u * averagedRetainedWeights S C a N dirs p z u ^ k)
        atTop (𝓝 ((2 : ℝ) ^ (AdditiveMoment.activeOccurrences Sh k).card)) := by
    have hsum : Tendsto
        (fun N => ∑ F ∈ (AdditiveMoment.activeOccurrences Sh k).powerset,
          AdditiveMoment.pkgElim_expandedAuxiliaryMoment S ι C a Sh dirs tests J0 eX F N)
        atTop (𝓝 ((2 : ℝ) ^ (AdditiveMoment.activeOccurrences Sh k).card)) := by
      apply tendsto_powerset_sum_of_tendsto_one
      intro F hF
      exact hEach F
    exact (tendsto_congr'
      (AdditiveMoment.pkgElim_eliminationMoment_eq_powersetSum S ι C a Sh dirs tests J0 hJ0 B
        hGlobalEvent (h := h) eX k hk)).2 hsum
  have hcard0 : (AdditiveMoment.activeOccurrences Sh 0).card = 2 ^ Fintype.card (NonTarget Sh) := by
    simpa using AdditiveMoment.pkgElim_activeOccurrences_card Sh 0 (by omega)
  have hcard1 : (AdditiveMoment.activeOccurrences Sh 1).card =
      2 ^ Fintype.card (NonTarget Sh) +
        Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1) := by
    simpa using AdditiveMoment.pkgElim_activeOccurrences_card Sh 1 (by omega)
  have hcard2 : (AdditiveMoment.activeOccurrences Sh 2).card =
      2 ^ Fintype.card (NonTarget Sh) +
        2 * (Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1)) := by
    rw [AdditiveMoment.pkgElim_activeOccurrences_card Sh 2 (by omega)]
    ring
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · simpa [hcard0] using hmoment 0 (by omega)
  · simpa [hcard1] using hmoment 1 (by omega)
  · simpa [hcard2] using hmoment 2 (by omega)

/-- Part of Lemma `lem:additive-elimination` (04:442–509): the translation by
`∑_{R≠*}v_Ru_R` and the `d` weighted Cauchy–Schwarz steps `eq:additive-weighted-cs` give
`|E∏_I f_I(ℓ_I(z))|^{2^d} ≤ C₁|E GΨ|+o(1)`, with `G` the target cube of `f_*` and `Ψ` the
retained weights `eq:correlation-retained-weights`. `C₁` depends only on the templates. -/
theorem opus_corr_elim_cauchy {m q r : ℕ} (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (hdirs : dirs.Valid) (tests : Finset (IntegerPolynomial q))
    (htests : ∀ P ∈ tests, P ≠ 0) (hdt : dirs.tests ⊆ tests) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s), TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ J0 : ℕ, 0 < J0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ∀ f : Fin r → (Fin q → ℕ) → ℤ → ℝ,
          (∀ R p y, |f R p y| ≤ 1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) →
          |goodRowCorrelation S C a N dirs tests f| ^ (2 ^ Fintype.card (NonTarget Sh)) ≤
            C₁ * |eliminationAverage S C N dirs tests J0 fun p z u =>
              (∏ ω : NonTarget Sh → Fin 2, atQ (f Sh.star p)
                (targetVertex (chainScale S.core.parameters C a N) Sh p
                  (directionModulus S N dirs.poly p) z u ω)) *
                retainedWeights S C a N dirs p z u| + ε := by
  sorry

/-- Part of Lemma `lem:additive-elimination` (04:516–530): translating `z` by `v_0u_0`, `u_0`
uniform on `[0,R)`, changes `E GΨ` by `o(1)`; `G` is unchanged since `ℓ_*(v_0)=0`, so
`E GΨ = E GH+o(1)` with `H(z,u)=E_{u_0}Ψ(z+v_0u_0,u)`. -/
theorem opus_corr_elim_root {m q r : ℕ} (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (hdirs : dirs.Valid) (tests : Finset (IntegerPolynomial q))
    (htests : ∀ P ∈ tests, P ≠ 0) (hdt : dirs.tests ⊆ tests) :
    ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
      (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s), TestsListed Dm ι tests →
    ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
    ∀ J0 : ℕ, 0 < J0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ h : (Fin q → ℕ) → ℤ → ℝ,
        (∀ p y, |h p y| ≤ 1 + chainWeight S.core.parameters C N (Sh.row Sh.star).anchor y) →
        |(eliminationAverage S C N dirs tests J0 fun p z u =>
            (∏ ω : NonTarget Sh → Fin 2, atQ (h p)
              (targetVertex (chainScale S.core.parameters C a N) Sh p
                (directionModulus S N dirs.poly p) z u ω)) *
              retainedWeights S C a N dirs p z u) -
          eliminationAverage S C N dirs tests J0 fun p z u =>
            (∏ ω : NonTarget Sh → Fin 2, atQ (h p)
              (targetVertex (chainScale S.core.parameters C a N) Sh p
                (directionModulus S N dirs.poly p) z u ω)) *
              averagedRetainedWeights S C a N dirs p z u| ≤ ε := by
  sorry

/-- Part of Lemma `lem:additive-elimination` (04:530–572): the weighted replacement
`|E G(H-2^t)| ≤ (E B)^{1/2}(E B(H-2^t)²)^{1/2} = o(1)`, from `|G| ≤ B` and the moments
`eq:auxiliary-weight-moments`; `E G` is the target cube. -/
theorem opus_corr_elim_variance {m q r : ℕ} (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (hdirs : dirs.Valid) (tests : Finset (IntegerPolynomial q))
    (htests : ∀ P ∈ tests, P ≠ 0) (hdt : dirs.tests ⊆ tests) :
    ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
      (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s), TestsListed Dm ι tests →
    ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
    ∀ J0 : ℕ, 0 < J0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ h : (Fin q → ℕ) → ℤ → ℝ,
        (∀ p y, |h p y| ≤ 1 + chainWeight S.core.parameters C N (Sh.row Sh.star).anchor y) →
        |(eliminationAverage S C N dirs tests J0 fun p z u =>
            (∏ ω : NonTarget Sh → Fin 2, atQ (h p)
              (targetVertex (chainScale S.core.parameters C a N) Sh p
                (directionModulus S N dirs.poly p) z u ω)) *
              averagedRetainedWeights S C a N dirs p z u) -
          (2 : ℝ) ^ (Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1)) *
            additiveCube S C a N dirs tests J0 h| ≤ ε := by
  intro K s Aset Dm S ι hlisted C a ha J0 hJ0 ε hε
  obtain ⟨hm0, hm1, hm2⟩ :=
    additive_elimination_auxiliary_moments Sh dirs hdirs tests htests hdt
      S ι hlisted C a ha J0 hJ0
  let b : ℝ := (2 : ℝ) ^ 2 ^ Fintype.card (NonTarget Sh)
  let c : ℝ := (2 : ℝ) ^
    (Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1))
  let E N := sol_var_eliminationLinear S C N dirs tests J0
  let B N : ((Fin q → ℕ) × (Fin m → ℚ) × (NonTarget Sh → Fin 2 → ℕ)) → ℝ :=
    fun x => targetBound S C a N dirs x.1 x.2.1 x.2.2
  let H N : ((Fin q → ℕ) × (Fin m → ℚ) × (NonTarget Sh → Fin 2 → ℕ)) → ℝ :=
    fun x => averagedRetainedWeights S C a N dirs x.1 x.2.1 x.2.2
  have h0 : Tendsto (fun N => E N (B N)) atTop (𝓝 b) := hm0
  have h1 : Tendsto (fun N => E N (fun x => B N x * H N x)) atTop (𝓝 (b * c)) := by
    dsimp only [b, c]
    rw [← pow_add]
    exact hm1
  have h2 : Tendsto (fun N => E N (fun x => B N x * H N x ^ 2))
      atTop (𝓝 (b * c ^ 2)) := by
    dsimp only [b, c]
    rw [← pow_mul, ← pow_add,
      Nat.mul_comm (Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1)) 2]
    exact hm2
  let V N := E N (fun x => B N x * (H N x - c) ^ 2)
  have hV : Tendsto V atTop (𝓝 0) := by
    have hlinear := (h2.sub (h1.const_mul (2 * c))).add (h0.const_mul (c ^ 2))
    have hzero : b * c ^ 2 - (2 * c) * (b * c) + c ^ 2 * b = 0 := by ring
    rw [hzero] at hlinear
    simpa only [V, sol_var_centered_moment] using hlinear
  have hbound : Tendsto (fun N => E N (B N) * V N) atTop (𝓝 0) := by
    simpa only [mul_zero] using h0.mul hV
  filter_upwards [hbound.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with N hN
  intro h hh
  let G : ((Fin q → ℕ) × (Fin m → ℚ) × (NonTarget Sh → Fin 2 → ℕ)) → ℝ :=
    fun x => ∏ ω : NonTarget Sh → Fin 2, atQ (h x.1)
      (targetVertex (chainScale S.core.parameters C a N) Sh x.1
        (directionModulus S N dirs.poly x.1) x.2.1 x.2.2 ω)
  have hG (x) : |G x| ≤ B N x :=
    c_elim2_target_cube_product_abs_le_targetBound S C a N dirs
      x.1 x.2.1 x.2.2 (h x.1) (hh x.1)
  have hCS := sol_var_weighted_cauchy (E N)
    (sol_var_eliminationLinear_nonneg S C N dirs tests J0)
    (B N) G (fun x => H N x - c)
    (fun x => (abs_nonneg (G x)).trans (hG x)) hG
  have hdiff : E N (fun x => G x * (H N x - c)) =
      E N (fun x => G x * H N x) - c * additiveCube S C a N dirs tests J0 h := by
    have heq : (fun x => G x * (H N x - c)) = (fun x => G x * H N x) - c • G := by
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, map_sub, map_smul]
    rfl
  rw [hdiff] at hCS
  change |E N (fun x => G x * H N x) - c * additiveCube S C a N dirs tests J0 h| ≤ ε
  change E N (B N) * V N < ε ^ 2 at hN
  nlinarith only [hCS, hN, hε,
    abs_nonneg (E N (fun x => G x * H N x) - c * additiveCube S C a N dirs tests J0 h)]

/-- Lemma `lem:additive-elimination`, equation `eq:additive-elimination-output`: under the
normalized good-tuple law, `|E∏_I f_I(ℓ_I(z))|^{2^d} ≤ C_m|E∏_{ω∈{0,1}^d}
f_*(ℓ_*(z)+M(p)∑_{R≠*}u_R^{ω_R})|+o(1)`, uniformly over `|f_I| ≤ W_I`. The constant depends only
on the templates (it is chosen before `J_0`); the error is for fixed `J_0`. -/
theorem weighted_additive_elimination {m q r : ℕ} (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (hdirs : dirs.Valid) (tests : Finset (IntegerPolynomial q))
    (htests : ∀ P ∈ tests, P ≠ 0) (hdt : dirs.tests ⊆ tests) :
    ∃ Cm : ℝ, 0 < Cm ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s), TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ J0 : ℕ, 0 < J0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ∀ f : Fin r → (Fin q → ℕ) → ℤ → ℝ,
          (∀ R p y, |f R p y| ≤ 1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) →
          |goodRowCorrelation S C a N dirs tests f| ^ (2 ^ Fintype.card (NonTarget Sh)) ≤
            Cm * |additiveCube S C a N dirs tests J0 (f Sh.star)| + ε := by
  obtain ⟨C₁, hC₁, hA⟩ := opus_corr_elim_cauchy Sh dirs hdirs tests htests hdt
  let t : ℕ := Fintype.card (NonTarget Sh) * 2 ^ (Fintype.card (NonTarget Sh) - 1)
  refine ⟨C₁ * (2 : ℝ) ^ t, by positivity, ?_⟩
  intro K s Aset Dm S ι hlisted C a ha J0 hJ0 ε hε
  let δ : ℝ := ε / (3 * (C₁ + 1))
  have hδ : 0 < δ := by positivity
  filter_upwards [hA S ι hlisted C a ha J0 hJ0 (ε / 3) (by positivity),
    opus_corr_elim_root Sh dirs hdirs tests htests hdt S ι hlisted C a ha J0 hJ0 δ hδ,
    opus_corr_elim_variance Sh dirs hdirs tests htests hdt S ι hlisted C a ha J0 hJ0 δ hδ]
    with N hAN hRoot hVar
  intro f hf
  have h1 := hAN f hf
  have h2 := hRoot (f Sh.star) (hf Sh.star)
  have h3 := hVar (f Sh.star) (hf Sh.star)
  set Y := eliminationAverage S C N dirs tests J0 fun p z u =>
    (∏ ω : NonTarget Sh → Fin 2, atQ (f Sh.star p)
      (targetVertex (chainScale S.core.parameters C a N) Sh p
        (directionModulus S N dirs.poly p) z u ω)) *
      retainedWeights S C a N dirs p z u with hY
  set Z := eliminationAverage S C N dirs tests J0 fun p z u =>
    (∏ ω : NonTarget Sh → Fin 2, atQ (f Sh.star p)
      (targetVertex (chainScale S.core.parameters C a N) Sh p
        (directionModulus S N dirs.poly p) z u ω)) *
      averagedRetainedWeights S C a N dirs p z u with hZ
  set W := additiveCube S C a N dirs tests J0 (f Sh.star) with hW
  have hct : (0 : ℝ) ≤ (2 : ℝ) ^ t := by positivity
  have hYle : |Y| ≤ (2 : ℝ) ^ t * |W| + 2 * δ := by
    have e1 : |Y| ≤ |Z| + δ := by
      have := abs_sub_abs_le_abs_sub Y Z
      linarith
    have e2 : |Z| ≤ |(2 : ℝ) ^ t * W| + δ := by
      have := abs_sub_abs_le_abs_sub Z ((2 : ℝ) ^ t * W)
      linarith
    rw [abs_mul, abs_of_nonneg hct] at e2
    linarith
  have hδC : C₁ * (2 * δ) ≤ 2 * ε / 3 := by
    have hden : 0 < 3 * (C₁ + 1) := by positivity
    have : C₁ * (2 * δ) = 2 * ε * C₁ / (3 * (C₁ + 1)) := by
      simp only [δ]
      field_simp
    rw [this, div_le_iff₀ hden]
    nlinarith
  calc
    |goodRowCorrelation S C a N dirs tests f| ^ (2 ^ Fintype.card (NonTarget Sh)) ≤
        C₁ * |Y| + ε / 3 := h1
    _ ≤ C₁ * ((2 : ℝ) ^ t * |W| + 2 * δ) + ε / 3 := by
      gcongr
    _ = C₁ * (2 : ℝ) ^ t * |W| + C₁ * (2 * δ) + ε / 3 := by ring
    _ ≤ C₁ * (2 : ℝ) ^ t * |W| + ε := by linarith

/-! ## The cube root (04:614–683) -/

/-- Equation `eq:correlation-root-tv-bound`, with an absolute implied constant: for
`h ∈ [0,H]∩Wℤ`, `1 ≤ k ≤ X` coprime to `W` and `2H < X`,
`‖Law(kY+h)-k1_{y≡h (mod k)}μ_X‖₁ ≤ C₀(log(2k)/log X+H/X+Wk²/(ϑ_W X log X))`. -/
theorem correlation_cube_root_tv_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (X W k H : ℕ) (h : ℤ), 0 < W → 4 * W ≤ X → 0 < k → k ≤ X →
      Nat.Coprime k W → 0 ≤ h → h ≤ H → (W : ℤ) ∣ h → 2 * H < X →
      arithmeticL1 (translatedLaw (dilatedLaw (harmonicLaw X W) k) h)
          (progressionReference (harmonicLaw X W) k h) ≤
        C₀ * (Real.log (2 * k) / Real.log X + (H : ℝ) / X +
          (W : ℝ) * (k : ℝ) ^ 2 / ((Nat.totient W : ℝ) / W * X * Real.log X)) := by
  refine ⟨10, by norm_num, ?_⟩
  intro X W k H h hW hX hk hkX hcop h0 hH hdiv hHX
  let μ : ℤ → ℝ := harmonicLaw X W
  have hlog : Real.log X > (W : ℝ) / X := correlation_root_log_condition hW hX
  have hsample : FromArithmetic.SamplingPointwiseBounds X W :=
    FromArithmetic.sampling_pointwise_claim X W hW (by omega) hlog
  have hdilation := hsample.dilation (by omega) hlog k (by omega) hkX hcop
  have href := correlationRoot_reference_shift_numeric_bound X W k H h
    hW hX hk hkX hcop h0 hH hdiv hHX
  let B : ℤ := ((k * X ^ 2 + H : ℕ) : ℤ)
  have hk1 : 1 ≤ k := Nat.succ_le_iff.mpr hk
  have hsqLe : X ^ 2 ≤ k * X ^ 2 := by
    calc
      X ^ 2 = 1 * X ^ 2 := by simp
      _ ≤ k * X ^ 2 := Nat.mul_le_mul_right (X ^ 2) hk1
  have hShiftUpper (A : ℕ) (hA : A ≤ k * X ^ 2) :
      (A : ℤ) + h ≤ B := by
    have hA' : (A : ℤ) ≤ ((k * X ^ 2 : ℕ) : ℤ) := by exact_mod_cast hA
    have hH' : h ≤ (H : ℤ) := hH
    calc
      (A : ℤ) + h ≤ ((k * X ^ 2 : ℕ) : ℤ) + (H : ℤ) := add_le_add hA' hH'
      _ = B := by
        change ((k * X ^ 2 : ℕ) : ℤ) + (H : ℤ) =
          ((k * X ^ 2 + H : ℕ) : ℤ)
        exact (Nat.cast_add _ _).symm
  have hfSupport : ∀ z, translatedLaw (dilatedLaw μ k) h z ≠ 0 →
      0 ≤ z ∧ z ≤ B := by
    intro z hz
    have hs := translated_support h0 (fun y hy => by
      have hy' := dilatedLaw_support hk hy
      exact ⟨hy'.1, hy'.2.2⟩) hz
    exact ⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 (hShiftUpper (k * X ^ 2) le_rfl))⟩
  have hgSupport : ∀ z, translatedLaw (dilationReference μ k) h z ≠ 0 →
      0 ≤ z ∧ z ≤ B := by
    intro z hz
    have hs := translated_support h0 (fun y hy => by
      have hy' := dilationReference_support hy
      exact ⟨hy'.1, hy'.2.2⟩) hz
    have hupper := hShiftUpper (X ^ 2) hsqLe
    exact ⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 hupper)⟩
  have hrSupport : ∀ z, progressionReference (harmonicLaw X W) k h z ≠ 0 →
      0 ≤ z ∧ z ≤ B := by
    intro z hz
    have hs := progressionReference_support hz
    have hupper : (X ^ 2 : ℤ) ≤ B := by
      have hu := hShiftUpper (X ^ 2) hsqLe
      exact le_trans (by omega : (X ^ 2 : ℤ) ≤ (X ^ 2 : ℤ) + h) hu
    exact ⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2.2 hupper)⟩
  have htri := arithmeticL1_triangle_of_Icc_support B hfSupport hgSupport hrSupport
  calc
    arithmeticL1 (translatedLaw (dilatedLaw μ k) h)
        (progressionReference (harmonicLaw X W) k h) ≤
        arithmeticL1 (translatedLaw (dilatedLaw μ k) h)
            (translatedLaw (dilationReference μ k) h) +
          arithmeticL1 (translatedLaw (dilationReference μ k) h)
            (progressionReference (harmonicLaw X W) k h) := htri
    _ = arithmeticL1 (dilatedLaw (harmonicLaw X W) k)
            (dilationReference (harmonicLaw X W) k) +
          arithmeticL1 (translatedLaw (dilationReference (harmonicLaw X W) k) h)
          (progressionReference (harmonicLaw X W) k h) := by
          rw [arithmeticL1_translate_int]
          
    _ ≤ (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) /
            (Real.log X - (W : ℝ) / X) +
          (7 * (H : ℝ) / X + 7 * (W : ℝ) * k / (X * Real.log X)) :=
          add_le_add hdilation.1 href
    _ ≤ 10 * (Real.log (2 * k) / Real.log X + (H : ℝ) / X +
          (W : ℝ) * (k : ℝ) ^ 2 /
            ((Nat.totient W : ℝ) / W * X * Real.log X)) :=
          by simpa [add_assoc] using
            (correlationRoot_error_comparison X W k H hW hX hk)

/-- The law of the cube root (04:614–683): for `z_a ∼ μ_{X_a}`, `z_j ∼ μ_{X_j}` independent,
`k` coprime to `W`, `b ∈ Wℤ` coprime to `k`, `bX_j² ≤ H` and `h ∈ [0,H]∩Wℤ`, the law of
`kz_a+bz_j+h` is within `o(V^{-C})` of `μ_{X_a}` for every fixed `C`, tested against `|F| ≤ V^A`,
uniformly in `h` and `F`, once `log X_a` dominates the powers of `2+W+k+H+V` and `log X_j` those
of `2+W+k+V`. In the chain, `a=a_*`, `k=A_{*,a_*}(p)`, `b=(c_j/c_{a_*})A_{*,j}(p)` for some
`j ∈ J_*`, `j<a_*`, and `h` collects the other coordinates and the shifts. -/
theorem correlation_cube_root_sampling (Xa Xj k b H V : ℕ → ℕ)
    (hk : ∀ N, 0 < k N) (hkW : ∀ N, Nat.Coprime (k N) (primorial (N + 1)))
    (hbk : ∀ N, Nat.Coprime (b N) (k N)) (hWb : ∀ N, primorial (N + 1) ∣ b N)
    (hbH : ∀ N, b N * Xj N ^ 2 ≤ H N) (hV : ∀ N, 1 ≤ V N)
    (hXa : OAI.MicrocellScale.Dominates (fun N => Real.log (Xa N))
      (fun N => ((2 + primorial (N + 1) + k N + H N + V N : ℕ) : ℝ)))
    (hXj : OAI.MicrocellScale.Dominates (fun N => Real.log (Xj N))
      (fun N => ((2 + primorial (N + 1) + k N + V N : ℕ) : ℝ)))
    (A C : ℝ) (hC : 0 < C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ h : ℤ, 0 ≤ h → h ≤ H N →
      (primorial (N + 1) : ℤ) ∣ h → ∀ F : ℤ → ℝ, (∀ y, |F y| ≤ (V N : ℝ) ^ A) →
        (V N : ℝ) ^ C *
          |(∑' za : ℤ, ∑' zj : ℤ, harmonicLaw (Xa N) (primorial (N + 1)) za *
              harmonicLaw (Xj N) (primorial (N + 1)) zj *
                F ((k N : ℤ) * za + (b N : ℤ) * zj + h)) -
            ∑' y : ℤ, harmonicLaw (Xa N) (primorial (N + 1)) y * F y| ≤ ε := by
  let Wseq : ℕ → ℕ := fun N => primorial (N + 1)
  let Sa : ℕ → ℝ := fun N =>
    ((2 + Wseq N + k N + H N + V N : ℕ) : ℝ)
  let Sj : ℕ → ℝ := fun N =>
    ((2 + Wseq N + k N + V N : ℕ) : ℝ)
  let Uj : ℕ → ℝ := fun N => 2 + (Wseq N : ℝ) + (k N : ℝ) + (V N : ℝ)
  let Tj : ℕ → ℝ := fun N => 2 + (Wseq N : ℝ) + (k N : ℝ) + 1 + (V N : ℝ)
  let e : ℝ := max (A + C) 1
  let q : ℝ := e + 10
  have he : 0 < e := by
    dsimp [e]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have heAC : A + C ≤ e := by dsimp [e]; exact le_max_left _ _
  have hq : 0 < q := by dsimp [q]; linarith
  have hq2 : 2 ≤ q := by dsimp [q]; linarith
  have heq : e + 5 ≤ q := by dsimp [q]; linarith
  have hWposNat (N : ℕ) : 0 < Wseq N := by
    exact primorial_pos _
  have hSa1 (N : ℕ) : 1 ≤ Sa N := by
    change (1 : ℝ) ≤ ((2 + Wseq N + k N + H N + V N : ℕ) : ℝ)
    exact_mod_cast (show 1 ≤ 2 + Wseq N + k N + H N + V N by omega)
  have hSaW (N : ℕ) : (Wseq N : ℝ) ≤ Sa N := by
    change (Wseq N : ℝ) ≤ ((2 + Wseq N + k N + H N + V N : ℕ) : ℝ)
    exact_mod_cast (show Wseq N ≤ 2 + Wseq N + k N + H N + V N by omega)
  have hSaK (N : ℕ) : (k N : ℝ) ≤ Sa N := by
    change (k N : ℝ) ≤ ((2 + Wseq N + k N + H N + V N : ℕ) : ℝ)
    exact_mod_cast (show k N ≤ 2 + Wseq N + k N + H N + V N by omega)
  have hSaH (N : ℕ) : (H N : ℝ) ≤ Sa N := by
    change (H N : ℝ) ≤ ((2 + Wseq N + k N + H N + V N : ℕ) : ℝ)
    exact_mod_cast (show H N ≤ 2 + Wseq N + k N + H N + V N by omega)
  have hSaV (N : ℕ) : (V N : ℝ) ≤ Sa N := by
    change (V N : ℝ) ≤ ((2 + Wseq N + k N + H N + V N : ℕ) : ℝ)
    exact_mod_cast (show V N ≤ 2 + Wseq N + k N + H N + V N by omega)
  have hSa4 (N : ℕ) : 4 ≤ Sa N := by
    have hw := hWposNat N
    have hkN := hk N
    have hv := hV N
    change (4 : ℝ) ≤ ((2 + Wseq N + k N + H N + V N : ℕ) : ℝ)
    exact_mod_cast (show 4 ≤ 2 + Wseq N + k N + H N + V N by omega)
  have hSaHlt (N : ℕ) : (H N : ℝ) < Sa N := by
    have hw := hWposNat N
    have hkN := hk N
    have hv := hV N
    change (H N : ℝ) < ((2 + Wseq N + k N + H N + V N : ℕ) : ℝ)
    exact_mod_cast (show H N < 2 + Wseq N + k N + H N + V N by omega)
  have hSj1 (N : ℕ) : 1 ≤ Sj N := by
    change (1 : ℝ) ≤ ((2 + Wseq N + k N + V N : ℕ) : ℝ)
    exact_mod_cast (show 1 ≤ 2 + Wseq N + k N + V N by omega)
  have hSjW (N : ℕ) : (Wseq N : ℝ) ≤ Sj N := by
    change (Wseq N : ℝ) ≤ ((2 + Wseq N + k N + V N : ℕ) : ℝ)
    exact_mod_cast (show Wseq N ≤ 2 + Wseq N + k N + V N by omega)
  have hSj4 (N : ℕ) : 4 ≤ Sj N := by
    have hw := hWposNat N
    have hkN := hk N
    have hv := hV N
    change (4 : ℝ) ≤ ((2 + Wseq N + k N + V N : ℕ) : ℝ)
    exact_mod_cast (show 4 ≤ 2 + Wseq N + k N + V N by omega)
  have hDomA : OAI.MicrocellScale.Dominates (fun N => Real.log (Xa N : ℝ)) Sa := by
    simpa [Sa, Wseq] using hXa
  have hDomJ : OAI.MicrocellScale.Dominates (fun N => Real.log (Xj N : ℝ)) Sj := by
    simpa [Sj, Wseq] using hXj
  have hPowerA : ∀ᶠ N in atTop, Sa N ^ q ≤ Real.log (Xa N : ℝ) := by
    have hdom := hDomA q hq
    have hevent := (Filter.tendsto_atTop.1 hdom) (1 : ℝ)
    filter_upwards [hevent] with N hN
    have hden : 0 < Sa N ^ q := Real.rpow_pos_of_pos (by linarith [hSa1 N]) q
    have hmul : 1 * Sa N ^ q ≤ Real.log (Xa N : ℝ) := (le_div_iff₀ hden).mp hN
    simpa using hmul
  have hPowerJ : ∀ᶠ N in atTop, Sj N ^ q ≤ Real.log (Xj N : ℝ) := by
    have hdom := hDomJ q hq
    have hevent := (Filter.tendsto_atTop.1 hdom) (1 : ℝ)
    filter_upwards [hevent] with N hN
    have hden : 0 < Sj N ^ q := Real.rpow_pos_of_pos (by linarith [hSj1 N]) q
    have hmul : 1 * Sj N ^ q ≤ Real.log (Xj N : ℝ) := (le_div_iff₀ hden).mp hN
    simpa using hmul
  have hSaLePow (N : ℕ) : Sa N ≤ Sa N ^ q := by
    calc
      Sa N = Sa N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ Sa N ^ q := Real.rpow_le_rpow_of_exponent_le (by linarith [hSa1 N]) (by linarith)
  have hSaSqLePow (N : ℕ) : Sa N ^ (2 : ℝ) ≤ Sa N ^ q :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hSa1 N]) hq2
  have hSjSqLePow (N : ℕ) : Sj N ^ (2 : ℝ) ≤ Sj N ^ q :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hSj1 N]) hq2
  have hA_facts (N : ℕ) (hp : Sa N ^ q ≤ Real.log (Xa N : ℝ)) :
      2 ≤ Xa N ∧ 4 * Wseq N ≤ Xa N ∧ k N ≤ Xa N ∧ 4 * H N < Xa N := by
    have hSpos : 0 < Sa N := by linarith [hSa1 N]
    have hlogpos : 0 < Real.log (Xa N : ℝ) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hSpos q) hp
    have hXnonneg : 0 ≤ (Xa N : ℝ) := by positivity
    have hXgt : 1 < (Xa N : ℝ) := (Real.log_pos_iff hXnonneg).mp hlogpos
    have hXtwo : 2 ≤ Xa N := by
      have hNat : 1 < Xa N := by exact_mod_cast hXgt
      omega
    have hlogle : Real.log (Xa N : ℝ) ≤ (Xa N : ℝ) := Real.log_le_self hXnonneg
    have hSaLeX : Sa N ≤ (Xa N : ℝ) := le_trans (hSaLePow N) (le_trans hp hlogle)
    have hSaSqW : 4 * (Wseq N : ℝ) ≤ Sa N ^ (2 : ℝ) := by
      calc
        4 * (Wseq N : ℝ) ≤ 4 * Sa N := mul_le_mul_of_nonneg_left (hSaW N) (by norm_num)
        _ ≤ Sa N * Sa N := mul_le_mul_of_nonneg_right (hSa4 N) (by positivity)
        _ = Sa N ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
    have hSaSqH : 4 * (H N : ℝ) < Sa N ^ (2 : ℝ) := by
      calc
        4 * (H N : ℝ) < 4 * Sa N := mul_lt_mul_of_pos_left (hSaHlt N) (by norm_num)
        _ ≤ Sa N * Sa N := mul_le_mul_of_nonneg_right (hSa4 N) (by positivity)
        _ = Sa N ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
    have hWreal : 4 * (Wseq N : ℝ) ≤ (Xa N : ℝ) :=
      le_trans hSaSqW (le_trans (hSaSqLePow N) (le_trans hp hlogle))
    have hHreal : 4 * (H N : ℝ) < (Xa N : ℝ) :=
      lt_of_lt_of_le hSaSqH (le_trans (hSaSqLePow N) (le_trans hp hlogle))
    have hWnat : 4 * Wseq N ≤ Xa N := by exact_mod_cast hWreal
    have hKreal : (k N : ℝ) ≤ (Xa N : ℝ) := le_trans (hSaK N) hSaLeX
    have hKnat : k N ≤ Xa N := by exact_mod_cast hKreal
    have hHnat : 4 * H N < Xa N := by exact_mod_cast hHreal
    exact ⟨hXtwo, hWnat, hKnat, hHnat⟩
  have hJ_facts (N : ℕ) (hp : Sj N ^ q ≤ Real.log (Xj N : ℝ)) :
      2 ≤ Xj N ∧ 4 * Wseq N ≤ Xj N := by
    have hSpos : 0 < Sj N := by linarith [hSj1 N]
    have hlogpos : 0 < Real.log (Xj N : ℝ) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hSpos q) hp
    have hXnonneg : 0 ≤ (Xj N : ℝ) := by positivity
    have hXgt : 1 < (Xj N : ℝ) := (Real.log_pos_iff hXnonneg).mp hlogpos
    have hXtwo : 2 ≤ Xj N := by
      have hNat : 1 < Xj N := by exact_mod_cast hXgt
      omega
    have hlogle : Real.log (Xj N : ℝ) ≤ (Xj N : ℝ) := Real.log_le_self hXnonneg
    have hSjSqW : 4 * (Wseq N : ℝ) ≤ Sj N ^ (2 : ℝ) := by
      calc
        4 * (Wseq N : ℝ) ≤ 4 * Sj N := mul_le_mul_of_nonneg_left (hSjW N) (by norm_num)
        _ ≤ Sj N * Sj N := mul_le_mul_of_nonneg_right (hSj4 N) (by positivity)
        _ = Sj N ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
    have hWreal : 4 * (Wseq N : ℝ) ≤ (Xj N : ℝ) :=
      le_trans hSjSqW (le_trans (hSjSqLePow N) (le_trans hp hlogle))
    exact ⟨hXtwo, by exact_mod_cast hWreal⟩
  have hJfactsEventually : ∀ᶠ N in atTop, 2 ≤ Xj N ∧ 4 * Wseq N ≤ Xj N := by
    filter_upwards [hPowerJ] with N hp
    exact hJ_facts N hp
  have hDenJ : ∀ᶠ N in atTop, Real.log (Xj N : ℝ) > (Wseq N : ℝ) / Xj N := by
    filter_upwards [hJfactsEventually] with N hN
    exact correlation_root_log_condition (hWposNat N) hN.2
  have hDomXjNat : OAI.MicrocellScale.Dominates (fun N => (Xj N : ℝ)) Uj :=
    dominates_nat_of_log_dominates (by intro N; positivity) (by simpa [Uj, Wseq] using hXj)
  have hDomXjSample : OAI.MicrocellScale.Dominates (fun N => (Xj N : ℝ)) Tj := by
    apply dominates_weaken_target_sq
      (hF := by intro N; positivity)
      (hS := by
        intro N
        have hw : 0 ≤ (Wseq N : ℝ) := by positivity
        have hkN : 0 ≤ (k N : ℝ) := by positivity
        have hv : 0 ≤ (V N : ℝ) := by positivity
        dsimp [Uj]
        linarith)
      (hT := by intro N; dsimp [Tj]; positivity)
      (hTS := by
        intro N
        have hU4 : 4 ≤ Uj N := by
          have hw := hWposNat N
          have hkN := hk N
          have hv := hV N
          change (4 : ℝ) ≤ 2 + (Wseq N : ℝ) + (k N : ℝ) + (V N : ℝ)
          exact_mod_cast (show 4 ≤ 2 + Wseq N + k N + V N by omega)
        have hEq : Tj N = Uj N + 1 := by dsimp [Tj, Uj]; ring
        rw [hEq]
        calc
          Uj N + 1 ≤ Uj N ^ 2 := by nlinarith [sq_nonneg (Uj N - 1)]
          _ = Uj N ^ (2 : ℝ) := (Real.rpow_natCast (Uj N) 2).symm)
      hDomXjNat
  have hSamplingAsym := FromArithmetic.sampling_asymptotics
      Wseq k (fun _ => 1) V Xj
      (by intro N; have := hk N; omega)
      (by intro N; norm_num)
      hV
      (by intro N; rfl)
      (by filter_upwards [hJfactsEventually] with N hN; exact hN.1)
      hDenJ (by simpa [Tj] using hDomXjSample)
      (by simpa [Uj, Wseq] using hXj)
  rcases correlation_cube_root_tv_bound with ⟨C₀, hC₀, hCube⟩
  let δseq : ℕ → ℝ := fun N => (Nat.totient (Wseq N) : ℝ) / Wseq N
  let Eroot : ℕ → ℝ := fun N => C₀ *
    (Real.log (2 * (k N : ℝ)) / Real.log (Xa N : ℝ) +
      (2 * (H N : ℝ)) / Xa N +
      (Wseq N : ℝ) * (k N : ℝ) ^ 2 /
        (δseq N * Xa N * Real.log (Xa N : ℝ)))
  let Eres : ℕ → ℝ := fun N => FromArithmetic.harmonicResidueError (Xj N) (Wseq N) (k N)
  have hResidueSuper : SuperPolynomialSmall Eres (fun N => (V N : ℝ)) := by
    simpa [Eres, FromArithmetic.harmonicResidueUniformError,
      FromArithmetic.harmonicResidueError, Wseq] using hSamplingAsym.1
  have hResidueWeighted : Tendsto (fun N => (V N : ℝ) ^ e * Eres N) atTop (𝓝 0) := by
    have h := hResidueSuper e he
    simpa [mul_comm] using h
  have hResidueNonneg : ∀ᶠ N in atTop, 0 ≤ Eres N := by
    filter_upwards [hDenJ, hJfactsEventually] with N hden hfacts
    have hW : 0 < (Wseq N : ℝ) := by exact_mod_cast hWposNat N
    have hX : 0 < (Xj N : ℝ) := by
      exact_mod_cast (show 0 < Xj N by omega)
    have hD : 0 < Real.log (Xj N : ℝ) - (Wseq N : ℝ) / Xj N := by linarith
    unfold Eres FromArithmetic.harmonicResidueError
    apply div_nonneg
    · positivity
    · exact (mul_pos hX hD).le
  have hSaTop : Tendsto Sa atTop atTop := by
    have hNatTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hle : (fun N : ℕ => (N : ℝ)) ≤ᶠ[atTop] Sa := by
      filter_upwards [] with N
      have hNW : N ≤ Wseq N := by
        dsimp [Wseq]
        exact le_trans (Nat.le_succ N) (le_primorial_self (n := N + 1))
      have hNWreal : (N : ℝ) ≤ (Wseq N : ℝ) := by exact_mod_cast hNW
      exact le_trans hNWreal (hSaW N)
    exact Filter.tendsto_atTop_mono' Filter.atTop hle hNatTop
  have hSaInv : Tendsto (fun N => 1 / Sa N) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp hSaTop) using 1 <;> funext N <;> simp [one_div]
  have hRootUpper : Tendsto (fun N => C₀ * (7 / Sa N)) atTop (𝓝 0) := by
    have h := Filter.Tendsto.const_mul (C₀ * 7) hSaInv
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hRootEst : ∀ᶠ N in atTop,
      0 ≤ (V N : ℝ) ^ e * Eroot N ∧ (V N : ℝ) ^ e * Eroot N ≤ C₀ * (7 / Sa N) := by
    filter_upwards [hPowerA] with N hp
    rcases hA_facts N hp with ⟨hXa2, hXaW, hXak, hXaH⟩
    have hW : 0 < Wseq N := hWposNat N
    have hkN := hk N
    have hK : 1 ≤ k N := by omega
    have hVreal : 1 ≤ (V N : ℝ) := by exact_mod_cast hV N
    have hWreal : 0 < (Wseq N : ℝ) := by exact_mod_cast hW
    have hXreal : 0 < (Xa N : ℝ) := by exact_mod_cast (show 0 < Xa N by omega)
    have hLog : 0 < Real.log (Xa N : ℝ) := by
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith [hSa1 N]) q) hp
    have hXbound : Sa N ^ q ≤ (Xa N : ℝ) :=
      le_trans hp (Real.log_le_self (by positivity))
    have hPhi : (1 : ℝ) ≤ (Nat.totient (Wseq N) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hW))
    have hDeltaPos : 0 < δseq N := by
      dsimp [δseq]
      exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) hWreal
    have hDelta : 1 / (Wseq N : ℝ) ≤ δseq N := by
      dsimp [δseq]
      exact div_le_div_of_nonneg_right hPhi (by positivity)
    have hHreal : 0 ≤ (H N : ℝ) := by positivity
    have hHS : (H N : ℝ) ≤ 2 * Sa N := by linarith [hSaH N]
    have hKreal : (1 : ℝ) ≤ (k N : ℝ) := by exact_mod_cast hK
    have hLarg : 0 ≤ C₀ := le_of_lt hC₀
    have hBound := rootTV_error_weight_bound (Sa N) (V N) (Wseq N) (k N) (H N)
      (Xa N) (Real.log (Xa N : ℝ)) (δseq N) e q C₀
      (hSa1 N) (by exact_mod_cast hV N) (hSaV N)
      hWreal (hSaW N) hKreal (hSaK N) hHreal hHS hXbound hp hDelta he.le heq hLarg
    have hlog2 : 0 ≤ Real.log (2 * (k N : ℝ)) := by
      apply Real.log_nonneg
      have hkN : 1 ≤ k N := hK
      exact_mod_cast (show 1 ≤ 2 * k N by omega)
    have hEroot : 0 ≤ Eroot N := by
      unfold Eroot
      apply mul_nonneg hLarg
      apply add_nonneg
      · apply add_nonneg
        · exact div_nonneg hlog2 hLog.le
        · exact div_nonneg (by positivity) (by positivity)
      · apply div_nonneg
        · positivity
        · exact mul_nonneg (mul_nonneg hDeltaPos.le hXreal.le) hLog.le
    constructor
    · exact mul_nonneg (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (V N))) e) hEroot
    · simpa [Eroot, δseq, Wseq, Nat.cast_mul] using hBound
  have hRootWeighted : Tendsto (fun N => (V N : ℝ) ^ e * Eroot N) atTop (𝓝 0) :=
    squeeze_zero' (hRootEst.mono fun N hN => hN.1)
      (hRootEst.mono fun N hN => hN.2) hRootUpper
  have hWeightedTotal : Tendsto
      (fun N => (V N : ℝ) ^ e * (Eroot N + Eres N)) atTop (𝓝 0) := by
    have hsum := hRootWeighted.add hResidueWeighted
    simpa [mul_add] using hsum
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ N in atTop, (V N : ℝ) ^ e * (Eroot N + Eres N) < ε :=
    hWeightedTotal.eventually (Iio_mem_nhds hε)
  intro ε hε
  filter_upwards [hPowerA, hPowerJ, hResidueNonneg, hsmall ε hε] with N hpA hpJ hrespos hsmallN
  intro h h0 hH hdiv F hF
  rcases hA_facts N hpA with ⟨hXa2, hXaW, hXak, hXaH⟩
  rcases hJ_facts N hpJ with ⟨hXj2, hXjW⟩
  have hW : 0 < Wseq N := hWposNat N
  have hWreal : 0 < (Wseq N : ℝ) := by exact_mod_cast hW
  have hXaPos : 0 < Xa N := by omega
  have hXjPos : 0 < Xj N := by omega
  have hXaLog : Real.log (Xa N : ℝ) > (Wseq N : ℝ) / Xa N :=
    correlation_root_log_condition hW hXaW
  have hXjLog : Real.log (Xj N : ℝ) > (Wseq N : ℝ) / Xj N :=
    correlation_root_log_condition hW hXjW
  have hNormA : 0 < harmonicNormalizer (Xa N) (Wseq N) :=
    harmonicNormalizer_pos_of_root_conditions hW hXaW
  have hNormJ : 0 < harmonicNormalizer (Xj N) (Wseq N) :=
    harmonicNormalizer_pos_of_root_conditions hW hXjW
  have hSampJ : FromArithmetic.SamplingPointwiseBounds (Xj N) (Wseq N) :=
    FromArithmetic.sampling_pointwise_claim (Xj N) (Wseq N) hW hXj2 hXjLog
  have hTV : ∀ (h' : ℤ), 0 ≤ h' → h' ≤ 2 * H N → (Wseq N : ℤ) ∣ h' →
      arithmeticL1 (translatedLaw (dilatedLaw (harmonicLaw (Xa N) (Wseq N)) (k N)) h')
        (progressionReference (harmonicLaw (Xa N) (Wseq N)) (k N) h') ≤ Eroot N := by
    intro h' h'0 h'le h'div
    have hHX : 2 * (2 * H N) < Xa N := by omega
    have ht := hCube (Xa N) (Wseq N) (k N) (2 * H N) h'
      hW hXaW (hk N) hXak (hkW N) h'0 h'le h'div hHX
    simpa [Eroot, δseq, Wseq, Nat.cast_mul] using ht
  have hResidue : FromArithmetic.harmonicResidueError (Xj N) (Wseq N) (k N) ≤ Eres N := by
    rfl
  have hM : 0 ≤ (V N : ℝ) ^ A := Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (V N))) A
  have hErootLocal : 0 ≤ Eroot N := by
    have hLogApos : 0 < Real.log (Xa N : ℝ) := by
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith [hSa1 N]) q) hpA
    have hdeltaPos : 0 < δseq N := by
      dsimp [δseq]
      exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) hWreal
    have hlog2 : 0 ≤ Real.log (2 * (k N : ℝ)) := by
      apply Real.log_nonneg
      have hkN := hk N
      exact_mod_cast (show 1 ≤ 2 * k N by omega)
    unfold Eroot
    apply mul_nonneg (le_of_lt hC₀)
    apply add_nonneg
    · apply add_nonneg
      · exact div_nonneg hlog2 hLogApos.le
      · exact div_nonneg (by positivity) (by positivity)
    · apply div_nonneg
      · positivity
      · exact mul_nonneg (mul_nonneg hdeltaPos.le (by positivity)) hLogApos.le
  have hExpected := correlationRoot_expected_test_bound
      (Xa N) (Xj N) (Wseq N) (k N) (b N) (H N) h
      ((V N : ℝ) ^ A) (Eroot N) (Eres N)
      (by exact_mod_cast hXaPos) (by exact_mod_cast hXjPos) (hk N)
      (hWb N) (hbk N) (hkW N) (hbH N) h0 hH hdiv
      hNormA hNormJ hXj2 hXjLog hSampJ hM hErootLocal hrespos hTV hResidue F hF
  have hVN := hV N
  have hVpos : 0 < (V N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hVN)
  have hVpow : (V N : ℝ) ^ (A + C) ≤ (V N : ℝ) ^ e :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hV N) heAC
  have hErrorNonneg : 0 ≤ Eroot N + Eres N := add_nonneg hErootLocal hrespos
  have hScaleLe : (V N : ℝ) ^ (A + C) * (Eroot N + Eres N) ≤
      (V N : ℝ) ^ e * (Eroot N + Eres N) :=
    mul_le_mul_of_nonneg_right hVpow hErrorNonneg
  have hpowAC : (V N : ℝ) ^ C * ((V N : ℝ) ^ A * (Eroot N + Eres N)) =
      (V N : ℝ) ^ (A + C) * (Eroot N + Eres N) := by
    calc
      _ = ((V N : ℝ) ^ A * (V N : ℝ) ^ C) * (Eroot N + Eres N) := by ring
      _ = _ := by rw [← Real.rpow_add hVpos A C]
  simpa [Wseq] using (calc
    (V N : ℝ) ^ C *
        |(∑' za : ℤ, ∑' zj : ℤ, harmonicLaw (Xa N) (Wseq N) za *
            harmonicLaw (Xj N) (Wseq N) zj *
              F ((k N : ℤ) * za + (b N : ℤ) * zj + h)) -
          ∑' y : ℤ, harmonicLaw (Xa N) (Wseq N) y * F y| ≤
      (V N : ℝ) ^ C * ((V N : ℝ) ^ A * (Eroot N + Eres N) ) :=
        mul_le_mul_of_nonneg_left hExpected (by positivity)
    _ = (V N : ℝ) ^ (A + C) * (Eroot N + Eres N) := hpowAC
    _ ≤ (V N : ℝ) ^ e * (Eroot N + Eres N) := hScaleLe
    _ ≤ ε := le_of_lt hsmallN)

/-! ## The uniform correlation test (Proposition `prop:correlation-test`, 04:576–707) -/

/-- Proposition `prop:correlation-test`, equation `eq:correlation-test`:
`|𝒞| ≤ o(1)+C_m|E_{p,y,u}∏_{ω⊆[d]}g_*(y+M(p)∑_{R∈ω}(u_R^1-u_R^0))|^θ`, `θ=2^{-(q_mask+d)}`,
uniformly over all masks and functions with the bounds of `FunctionsValid` and over each fixed
finite set of `J_0`. The cube type `T` (prime slots, `D`, tests, `1 ≤ d ≤ K_m-1`), `C_m` and the
size exponent `B` depend only on `m` and `J_*`, before the master scales, whose polynomial list
must contain `T.tests` (renamed by an embedding of the slots). For every chain the output also
gives `M(p) ∣ R_l` on good tuples, the probability `o(1)` of non-good tuples, and
`M(p) ≤ (P_l^++V_l)^B`, which §5 uses. -/
theorem uniform_correlation_test (m : ℕ) (Jstar : Finset (Fin m)) (hJ : Jstar.Nonempty)
    (hJcard : 2 ≤ Jstar.card) :
    ∃ T : CubeTemplate, 1 ≤ T.d ∧ T.d ≤ maskRowBound m - 1 ∧ ∃ Cm : ℝ, 0 < Cm ∧ ∃ B : ℕ,
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin T.q ↪ Fin s), TestsListed Dm ι T.tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
        (∀ᶠ N in atTop, ∀ p, T.Good S C.gap N p → T.modulus S N p ∣ S.core.parameters.H N C.gap) ∧
        Tendsto (fun N => gapSlotProbability S C.gap N fun p => ¬ T.Good S C.gap N p)
          atTop (𝓝 0) ∧
        (∀ᶠ N in atTop, ∀ p, T.Good S C.gap N p →
          T.modulus S N p ≤
            ((S.primeStage.pool N C.gap).upper + FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ B) ∧
        ∀ J0s : Finset ℕ, (∀ J0 ∈ J0s, 0 < J0) → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
          ∀ J0 ∈ J0s, ∀ b g : Finset (Fin m) → ℤ → ℝ,
            FunctionsValid S.core.parameters C N b g →
            |maskedCorrelation S.core.parameters C a N b g| ≤
              ε + Cm * |T.cubeTest S C.gap (C.block (Jstar.max' hJ)).1 J0 N (g Jstar)| ^
                ((2 : ℝ) ^ (maskCount m + T.d))⁻¹ := by
  classical
  obtain ⟨q, r, Sh0, maskTests, CmMask, hrMask, hqMask, hstar0,
      hmaskTests, hCmMask, hMaskRemoval⟩ := weighted_mask_removal m Jstar hJcard
  let completion :=
    c_test2_completeRows Sh0 Jstar hJcard hstar0 hrMask
  let Sh := completion.shape
  have hstar : (Sh.row Sh.star).support = Jstar := by
    rw [completion.star_eq, completion.row_eq]
    exact hstar0
  obtain ⟨dirs, hdirs, hdir⟩ := row_directions Sh
  let testList := dirs.tests ∪ maskTests
  have htests : ∀ P ∈ testList, P ≠ 0 := by
    intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · have hpoly : dirs.poly ≠ 0 := by
        unfold RowDirections.poly
        apply Finset.prod_ne_zero_iff.mpr
        intro R hR
        have hRne : R ≠ Sh.star := (Finset.mem_erase.mp hR).1
        have hresp := hdirs.2.1 R Sh.star hRne (Ne.symm hRne)
        simpa [RowDirections.targetResponse] using hresp
      have htestsDirs : ∀ P ∈ dirs.tests, P ≠ 0 := by
        intro Q hQ
        simp only [RowDirections.tests, Finset.mem_insert, Finset.mem_union] at hQ
        rcases hQ with hQ | hQ
        · simpa [hQ] using hpoly
        · rcases hQ with hQ | hQ
          · exact (Finset.mem_filter.mp hQ).2
          · exact (Finset.mem_filter.mp hQ).2
      exact htestsDirs P hP
    · exact hmaskTests P hP
  have htestsSub : dirs.tests ⊆ testList := Finset.subset_union_left
  obtain ⟨B, hdirections⟩ := hdir testList htests htestsSub
  let T : CubeTemplate := {
    q := q
    d := Fintype.card (NonTarget Sh)
    D := dirs.poly
    tests := testList
    D_mem := by
      have hmem : dirs.poly ∈ dirs.tests := by simp [RowDirections.tests]
      exact Finset.mem_union_left _ hmem
    tests_ne_zero := htests
  }
  have hcardNT : T.d = completion.r' - 1 := by
    dsimp [T]
    exact c_test2_nonTarget_card Sh
  have hrowCount : 2 ≤ completion.r' := completion.two_rows
  have hrowBound : completion.r' ≤ maskRowBound m := completion.row_bound
  have hTlower : 1 ≤ T.d := by rw [hcardNT]; omega
  have hTupper : T.d ≤ maskRowBound m - 1 := by
    rw [hcardNT]
    exact Nat.sub_le_sub_right hrowBound 1
  obtain ⟨CmAdd, hCmAdd, hAddElim⟩ :=
    weighted_additive_elimination Sh dirs hdirs testList htests htestsSub
  let maskPow : ℕ := 2 ^ maskCount m
  let addPow : ℕ := 2 ^ T.d
  let finalPow : ℕ := maskPow * addPow
  let corrCoeff : ℝ := (2 : ℝ) ^ addPow * CmMask ^ addPow * CmAdd
  let finalCm : ℝ := (2 * corrCoeff) ^ (1 / (finalPow : ℝ))
  have hfinalCm : 0 < finalCm := by
    dsimp [finalCm, corrCoeff]
    positivity
  refine ⟨T, hTlower, hTupper, finalCm, hfinalCm, B, ?_⟩
  intro K s Aset Dm S ι hlistedAll C a ha
  have hlistedMask : TestsListed Dm ι maskTests := by
    intro P hP
    exact hlistedAll P (Finset.mem_union_right _ hP)
  have hrowFacts := hdirections S ι hlistedAll C a ha
  have hmodBound : ∀ᶠ N in atTop, ∀ p, T.Good S C.gap N p →
      T.modulus S N p ≤
        ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ B := by
    filter_upwards [hrowFacts.2.2] with N hfacts
    intro p hp
    change GoodTuple S C.gap N testList dirs.poly p at hp
    have hInt : IntegerDirectionFacts S C a N dirs testList B p := hfacts p hp
    rcases hInt with ⟨_, _, hMp, _, _, _, _, _⟩
    change directionModulus S N dirs.poly p ≤ _
    exact hMp
  have hJne : Jstar.Nonempty := hJ
  let aStar : Fin m := Jstar.max' hJne
  have hAnchor : (Sh.row Sh.star).anchor = aStar := by
    unfold RowTemplate.anchor
    apply (Finset.max'_eq_iff (s := (Sh.row Sh.star).support)
      (H := (Sh.row Sh.star).support_nonempty) aStar).2
    constructor
    · rw [hstar]
      exact Finset.max'_mem Jstar hJne
    · intro k hk
      rw [hstar] at hk
      exact Finset.le_max' Jstar k hk
  have hjExists : ∃ j ∈ Jstar, j ≠ aStar := by
    by_contra h
    push_neg at h
    have hsub : Jstar ⊆ {aStar} := by
      intro k hk
      simp [h k hk]
    have hcard := Finset.card_le_card hsub
    simp at hcard
    omega
  obtain ⟨j, hj, hjNe⟩ := hjExists
  have hja : j < aStar := lt_of_le_of_ne (Finset.le_max' Jstar j hj) hjNe
  have hjaT : j < (Sh.row Sh.star).anchor := by
    rw [hAnchor]
    exact hja
  let E : ℕ := c_test2_rowExponent (Sh.row Sh.star)
  let Xa : ℕ → ℕ := fun N => S.core.parameters.X N (C.block aStar).1
  let Xj : ℕ → ℕ := fun N => S.core.parameters.X N (C.block j).1
  let V : ℕ → ℕ := fun N => FromArithmetic.masterScaleV S.core.parameters N C.gap
  let Hroot : ℕ → ℕ := fun N => c_test2_rootOffsetScale S C aStar j E N
  let rootPair := fun N p =>
    c_test2_rootPairAt S C a (Sh.row Sh.star) Jstar hstar j hj hjaT testList dirs.poly N p
  let samplePred : ℝ → ℕ → (Fin q → ℕ) → Prop := fun δ N p =>
    ∀ h : ℤ, 0 ≤ h → h ≤ Hroot N → (primorial (N + 1) : ℤ) ∣ h →
      ∀ F : ℤ → ℝ, (∀ y, |F y| ≤ (V N : ℝ) ^ (2 * 2 ^ T.d : ℕ)) →
        (V N : ℝ) *
          |(∑' za : ℤ, ∑' zj : ℤ,
              harmonicLaw (Xa N) (primorial (N + 1)) za *
                harmonicLaw (Xj N) (primorial (N + 1)) zj *
                  F (((rootPair N p).k : ℤ) * za + ((rootPair N p).b : ℤ) * zj + h)) -
            ∑' y : ℤ, harmonicLaw (Xa N) (primorial (N + 1)) y * F y| ≤ δ
  have hRootSamplerAlong (pseq : ℕ → Fin q → ℕ) (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ N in atTop, samplePred δ N (pseq N) := by
    let kseq : ℕ → ℕ := fun N => (rootPair N (pseq N)).k
    let bseq : ℕ → ℕ := fun N => (rootPair N (pseq N)).b
    have hpairProps (N : ℕ) :=
      c_test2_rootPairAt_properties S C a (Sh.row Sh.star) Jstar hstar j hj hjaT
        testList dirs.poly N (pseq N)
    have hk : ∀ N, 0 < kseq N := fun N => (hpairProps N).1
    have hWk : ∀ N, Nat.Coprime (kseq N) (primorial (N + 1)) :=
      fun N => (hpairProps N).2.2.2.1
    have hbk : ∀ N, Nat.Coprime (bseq N) (kseq N) :=
      fun N => (hpairProps N).2.2.2.2.1
    have hWb : ∀ N, primorial (N + 1) ∣ bseq N :=
      fun N => (hpairProps N).2.2.1
    have hkBound : ∀ N, kseq N ≤
        ((S.primeStage.pool N C.gap).upper + V N) ^ E :=
      fun N => (hpairProps N).2.2.2.2.2.1
    have hbBound : ∀ N, bseq N ≤
        ((S.primeStage.pool N C.gap).upper + V N) ^ (E + 1) :=
      fun N => (hpairProps N).2.2.2.2.2.2
    have hScale := c_test2_rootSamplerScaleFacts S C aStar j hja E kseq bseq
      hkBound hbBound
    have hbH : ∀ N, bseq N * Xj N ^ 2 ≤ Hroot N := hScale.1
    have hV : ∀ N, 1 ≤ V N := by
      intro N
      unfold V FromArithmetic.masterScaleV
      omega
    have hXa := hScale.2.1
    have hXj := hScale.2.2
    have hSampler := correlation_cube_root_sampling Xa Xj kseq bseq Hroot V
      hk hWk hbk hWb hbH hV hXa hXj (2 * (2 : ℝ) ^ T.d) 1 (by norm_num) δ hδ
    filter_upwards [hSampler] with N hN
    intro h h0 hH hdiv F hF
    have hFreal : ∀ y : ℤ, |F y| ≤
        (V N : ℝ) ^ ((2 : ℝ) * (2 : ℝ) ^ T.d) := by
      intro y
      have hexp : (2 : ℝ) * (2 : ℝ) ^ T.d =
          ((2 * 2 ^ T.d : ℕ) : ℝ) := by norm_cast
      rw [hexp, Real.rpow_natCast]
      exact hF y
    simpa [samplePred, Real.rpow_one] using hN h h0 hH hdiv F hFreal
  have hSampleUniform (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ N in atTop, ∀ p, samplePred δ N p :=
    c_test2_eventually_forall_of_sequences (fun N p => samplePred δ N p)
      (fun pseq => hRootSamplerAlong pseq δ hδ)
  have hScaleEventually := c_test2_chainCoefficientData_eventually S C a ha
  have hPoolEventually := c_test2_poolLower_ge_twiceMasterV_eventually S C.gap
  have hRowPrimitive : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs testList N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        ∀ u, ∃ k,
          FromArithmetic.rationalResidue r' hr
            (c_test2_rowWeightedCoeff S C a ι Sh N p u k) ≠ 0 := by
    intro N p hgood r' hr hlarge hrV u
    exact c_test2_rowWeighted_primitive S C a (Sh := Sh) dirs ι testList N p hgood
      r' hr hlarge hrV u
  have hRowPairwise : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs testList N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        (∀ Q ∈ Dm, ¬ ((r' : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
        ∀ u v, u ≠ v → ∃ k l,
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u k) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v l) ≠
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u l) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v k) := by
    intro N p hgood r' hr hlarge hrV hnoD u v huv
    exact c_test2_rowWeighted_pairwise S C a (Sh := Sh) dirs ι testList
      hlistedAll htestsSub N p hgood r' hr hlarge hrV hnoD u v huv
  let weightedRowData : Finset (Fin completion.r') →
      FromArithmetic.WeightedLinearFormsData (q := completion.r') (d := m) (b := K) S :=
    fun included =>
      @c_test2_weightedRowData K s m q completion.r' Aset Dm S C a Sh dirs ι testList
        included hlistedAll hRowPrimitive hRowPairwise
  have hGoodProbabilityEventually :=
    c_test2_goodSlotProbability_pos_eventually S C.gap testList dirs.poly hrowFacts.1
  let A := S.core.parameters
  have hsizeAnchor := c_test2_masterSize_le_pivotGap_eventually S C aStar
    (C.pivots_after_gap aStar)
  have hpreviousAnchor := c_test2_previous_le_gap_eventually A (C.block aStar).1
  have hotherCutoffEventually : ∀ᶠ N in atTop,
      ∀ i : CTest2OtherPivot aStar j, i.1 < aStar →
        A.X N (C.block i.1).1 ≤ A.H N (C.block aStar).1 := by
    filter_upwards [hpreviousAnchor] with N hprevious
    intro i hi
    exact (c_test2_pivot_cutoff_le_previous A C i.1 aStar hi N).trans hprevious
  have hgapLeAnchor (N : ℕ) :
      A.H N C.gap ≤ A.H N (C.block aStar).1 := by
    exact Nat.le_of_dvd (A.Hpos N (C.block aStar).1)
      (S.gapStage.earlier_gaps_divide N C.gap (C.block aStar).1
        (C.pivots_after_gap aStar))
  have hCubeBaseBound (N : ℕ) (p : Fin q → ℕ) (g : ℤ → ℝ)
      (hGbound : ∀ y, |g y| ≤
        1 + chainWeight S.core.parameters C N aStar y)
      (u : NonTarget Sh → Fin 2 → ℕ) :
      ∀ y : ℤ,
        |∏ v : NonTarget Sh → Fin 2,
          (fun J y => if J = Jstar then g y else 0) Jstar
            (y + (T.modulus S N p : ℤ) *
              ∑ R : NonTarget Sh,
                if v R = 1 then (u R 1 : ℤ) - u R 0 else 0)| ≤
          (V N : ℝ) ^ (2 * 2 ^ T.d : ℕ) := by
    intro y
    have hV2 : 2 ≤ V N := by
      unfold V FromArithmetic.masterScaleV
      omega
    have hVreal : (2 : ℝ) ≤ (V N : ℝ) := by exact_mod_cast hV2
    have hfactor (v : NonTarget Sh → Fin 2) :
        |(fun J y => if J = Jstar then g y else 0) Jstar
          (y + (T.modulus S N p : ℤ) *
            ∑ R : NonTarget Sh,
              if v R = 1 then (u R 1 : ℤ) - u R 0 else 0)| ≤ (V N : ℝ) ^ 2 := by
      let x := y + (T.modulus S N p : ℤ) *
        ∑ R : NonTarget Sh, if v R = 1 then (u R 1 : ℤ) - u R 0 else 0
      have hvalidG := hGbound x
      have hweight := c_test2_chainWeight_le_masterScaleV S C N aStar x
      have hle : |g x| ≤ 1 + (V N : ℝ) := by
        nlinarith [hvalidG, hweight]
      have hsq : 1 + (V N : ℝ) ≤ (V N : ℝ) ^ 2 := by nlinarith
      simpa [x] using hle.trans hsq
    have hcard : Fintype.card (NonTarget Sh → Fin 2) = 2 ^ T.d := by
      simp [Fintype.card_fun, T]
    calc
      |∏ v : NonTarget Sh → Fin 2,
          (fun J y => if J = Jstar then g y else 0) Jstar
            (y + (T.modulus S N p : ℤ) *
              ∑ R : NonTarget Sh,
                if v R = 1 then (u R 1 : ℤ) - u R 0 else 0)| =
          ∏ v : NonTarget Sh → Fin 2,
            |(fun J y => if J = Jstar then g y else 0) Jstar
              (y + (T.modulus S N p : ℤ) *
                ∑ R : NonTarget Sh,
                  if v R = 1 then (u R 1 : ℤ) - u R 0 else 0)| := by
            simpa using Finset.abs_prod (Finset.univ : Finset (NonTarget Sh → Fin 2))
              (fun v : NonTarget Sh → Fin 2 =>
                (fun J y => if J = Jstar then g y else 0) Jstar
                  (y + (T.modulus S N p : ℤ) *
                    ∑ R : NonTarget Sh,
                      if v R = 1 then (u R 1 : ℤ) - u R 0 else 0))
      _ ≤ ∏ _ : NonTarget Sh → Fin 2, (V N : ℝ) ^ 2 := by
            apply Finset.prod_le_prod₀
            · intro v hv
              exact abs_nonneg _
            · intro v hv
              exact hfactor v
      _ = (V N : ℝ) ^ (2 * 2 ^ T.d : ℕ) := by
            simp [hcard, pow_mul]
  have hAtQInt (g : ℤ → ℝ) (y : ℤ) : atQ g (y : ℚ) = g y := by
    simp [atQ]
  have hCubePivotAverage
      (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
      (hscaleN : c_test2_ScaleData S C a N)
      (hpoolN : 2 * V N ≤ (S.primeStage.pool N C.gap).lower)
      (hSampleN : ∀ p, samplePred δ N p)
      (hsizeN : (S.primeStage.pool N C.gap).upper + V N ≤ A.H N (C.block aStar).1)
      (hprevN : OAI.SourceAdmissible.previous (A.X N) (C.block aStar).1 ≤
        A.H N (C.block aStar).1)
      (hotherN : ∀ i : CTest2OtherPivot aStar j, i.1 < aStar →
        A.X N (C.block i.1).1 ≤ A.H N (C.block aStar).1)
      (J0 : ℕ) (hJ0 : 0 < J0) (p : Fin q → ℕ)
      (hp : GoodTuple S C.gap N testList dirs.poly p)
      (g : ℤ → ℝ) (hGbound : ∀ y, |g y| ≤
        1 + chainWeight S.core.parameters C N aStar y)
      (u : NonTarget Sh → Fin 2 → ℕ)
      (hu : u ∈ Fintype.piFinset (fun _ : NonTarget Sh =>
        Fintype.piFinset fun _ : Fin 2 => Finset.range
          (T.length S C.gap J0 N p))) :
      |(∑' z : Fin m → ℤ, pivotMass A C N z *
          (∏ ω : NonTarget Sh → Fin 2,
            atQ g (targetVertex (chainScale A C a N) Sh p
              (T.modulus S N p) (fun k => (z k : ℚ)) u ω))) -
        ∑' y : ℤ, harmonicLaw (Xa N) (primorial (N + 1)) y *
          ∏ v : NonTarget Sh → Fin 2,
            g (y + (T.modulus S N p : ℤ) *
              ∑ R : NonTarget Sh,
                if v R = 1 then (u R 1 : ℤ) - u R 0 else 0)| ≤ δ := by
    let W := primorial (N + 1)
    let Mp := T.modulus S N p
    let Other := CTest2OtherPivot aStar j
    let alpha := c_test2_alphaFromGoodTuple S C a N (Sh.row Sh.star) Jstar hstar
      j hj hjaT p testList dirs.poly hp hpoolN hscaleN
    let cInt := Classical.choose hscaleN
    let c := chainScale A C a N
    have hcchain : ∀ i, (cInt i : ℚ) = c i := (Classical.choose_spec hscaleN).1
    have hAlphaData := c_test2_alphaFromGoodTuple_coefficients S C a N
      (Sh.row Sh.star) Jstar hstar j hj hjaT p testList dirs.poly hp hpoolN hscaleN
    have hcoeff : ∀ i, c i / c (Sh.row Sh.star).anchor *
        (Sh.row Sh.star).value p i = (alpha i : ℚ) := by
      intro i
      calc
        c i / c (Sh.row Sh.star).anchor * (Sh.row Sh.star).value p i =
            (cInt i : ℚ) / (cInt (Sh.row Sh.star).anchor : ℚ) *
              (Sh.row Sh.star).value p i := by rw [hcchain i, hcchain]
        _ = (alpha i : ℚ) := hAlphaData.2.2 i
    have hpair := c_test2_rootPairAt_matches_good_alpha S C a (Sh.row Sh.star)
      Jstar hstar j hj hjaT testList dirs.poly N p hp hscaleN hpoolN
    have hkEq : (rootPair N p).k = alpha aStar := by
      simpa [hAnchor] using hpair.1
    have hbEq : (rootPair N p).b = alpha j := hpair.2
    let offset : (Other → ℤ) → ℤ := fun r =>
      (∑ i : Other, (alpha i.1 : ℤ) * r i) +
        (Mp : ℤ) * ∑ R : NonTarget Sh, (u R 0 : ℤ)
    let Fbase : ℤ → ℝ := fun y =>
      ∏ v : NonTarget Sh → Fin 2,
        g (y + (Mp : ℤ) *
          ∑ R : NonTarget Sh,
            if v R = 1 then (u R 1 : ℤ) - u R 0 else 0)
    let Fwhole : (Fin m → ℤ) → ℝ := fun z =>
      ∏ ω : NonTarget Sh → Fin 2,
        atQ g (targetVertex c Sh p Mp (fun i => (z i : ℚ)) u ω)
    let shiftLengthN := T.length S C.gap J0 N p
    let shiftDomain := Fintype.piFinset (fun _ : NonTarget Sh =>
      Fintype.piFinset fun _ : Fin 2 => Finset.range shiftLengthN)
    let pivotSupport : Finset (Fin m → ℤ) := Fintype.piFinset fun i : Fin m =>
      Finset.Ico (A.X N (C.block i).1 : ℤ) ((A.X N (C.block i).1) ^ 2 : ℤ)
    have hPivotMassZero (z : Fin m → ℤ) (hz : z ∉ pivotSupport) :
        pivotMass A C N z = 0 := by
      have hnot : ¬ ∀ i : Fin m, z i ∈
          Finset.Ico (A.X N (C.block i).1 : ℤ) ((A.X N (C.block i).1) ^ 2 : ℤ) := by
        intro hall
        exact hz (Fintype.mem_piFinset.mpr hall)
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      have hLaw : harmonicLaw (A.X N (C.block i).1) (primorial (N + 1)) (z i) = 0 := by
        by_contra hne
        have hs := c_test2_harmonicLaw_support hne
        have hmem : z i ∈
            Finset.Ico (A.X N (C.block i).1 : ℤ) ((A.X N (C.block i).1) ^ 2 : ℤ) := by
          simp [Finset.mem_Ico]
          exact ⟨hs.2.1, hs.2.2⟩
        exact hi hmem
      unfold pivotMass
      exact Finset.prod_eq_zero (Finset.mem_univ i) hLaw
    have hPivotShiftCommute (F : (Fin m → ℤ) →
        (NonTarget Sh → Fin 2 → ℕ) → ℝ) :
        (∑' z : Fin m → ℤ, pivotMass A C N z *
          shiftAverage (NonTarget Sh) shiftLengthN (F z)) =
          shiftAverage (NonTarget Sh) shiftLengthN (fun u =>
            ∑' z : Fin m → ℤ, pivotMass A C N z * F z u) := by
      have hinterchange :
          (∑' z : Fin m → ℤ, pivotMass A C N z * ∑ u ∈ shiftDomain, F z u) =
            ∑ u ∈ shiftDomain, ∑' z : Fin m → ℤ, pivotMass A C N z * F z u := by
        have hzeroOuter (z : Fin m → ℤ) (hz : z ∉ pivotSupport) :
            pivotMass A C N z * ∑ u ∈ shiftDomain, F z u = 0 := by
          rw [hPivotMassZero z hz]
          simp
        have hzeroPoint (u : NonTarget Sh → Fin 2 → ℕ) (z : Fin m → ℤ)
            (hz : z ∉ pivotSupport) : pivotMass A C N z * F z u = 0 := by
          rw [hPivotMassZero z hz]
          simp
        calc
          _ = ∑ z ∈ pivotSupport, pivotMass A C N z * ∑ u ∈ shiftDomain, F z u :=
            tsum_eq_sum (s := pivotSupport) hzeroOuter
          _ = ∑ z ∈ pivotSupport, ∑ u ∈ shiftDomain, pivotMass A C N z * F z u := by
            apply Finset.sum_congr rfl
            intro z hz
            simp_rw [Finset.mul_sum]
          _ = ∑ u ∈ shiftDomain, ∑ z ∈ pivotSupport, pivotMass A C N z * F z u := by
            exact Finset.sum_comm
          _ = ∑ u ∈ shiftDomain, ∑' z : Fin m → ℤ, pivotMass A C N z * F z u := by
            apply Finset.sum_congr rfl
            intro u hu
            symm
            exact tsum_eq_sum (s := pivotSupport) (hzeroPoint u)
      unfold shiftAverage
      calc
        _ = ((shiftLengthN : ℝ) ^ (2 * Fintype.card (NonTarget Sh)))⁻¹ *
            ∑' z : Fin m → ℤ,
              pivotMass A C N z * ∑ u ∈ shiftDomain, F z u := by
          calc
            _ = ∑' z : Fin m → ℤ,
                ((shiftLengthN : ℝ) ^ (2 * Fintype.card (NonTarget Sh)))⁻¹ *
                  (pivotMass A C N z * ∑ u ∈ shiftDomain, F z u) := by
              apply tsum_congr
              intro z
              ring
            _ = _ := by rw [← tsum_mul_left]
        _ = ((shiftLengthN : ℝ) ^ (2 * Fintype.card (NonTarget Sh)))⁻¹ *
            ∑ u ∈ shiftDomain, ∑' z : Fin m → ℤ, pivotMass A C N z * F z u := by
          rw [hinterchange]
        _ = shiftAverage (NonTarget Sh) shiftLengthN (fun u =>
            ∑' z : Fin m → ℤ, pivotMass A C N z * F z u) := by
          rfl
    have hFbound : ∀ y, |Fbase y| ≤ (V N : ℝ) ^ (2 * 2 ^ T.d : ℕ) :=
      by simpa [Fbase] using hCubeBaseBound N p g hGbound u
    have hdecomp : ∀ r : Other → ℤ, ∀ za zj : ℤ,
        Fwhole ((c_test2_pivotPairRestEquiv aStar j (Ne.symm hjNe)).symm ((za, zj), r)) =
          Fbase ((rootPair N p).k * za + (rootPair N p).b * zj + offset r) := by
      intro r za zj
      let z := (c_test2_pivotPairRestEquiv aStar j (Ne.symm hjNe)).symm ((za, zj), r)
      have hcoords : c_test2_pivotPairRestEquiv aStar j (Ne.symm hjNe) z = ((za, zj), r) :=
        (c_test2_pivotPairRestEquiv aStar j (Ne.symm hjNe)).apply_symm_apply _
      have hza : z aStar = za := by
        calc
          z aStar = (c_test2_pivotPairRestEquiv aStar j (Ne.symm hjNe) z).1.1 :=
            (c_test2_pivotPairRestEquiv_apply_anchor aStar j (Ne.symm hjNe) z).symm
          _ = za := by rw [hcoords]
      have hzj : z j = zj := by
        calc
          z j = (c_test2_pivotPairRestEquiv aStar j (Ne.symm hjNe) z).1.2 :=
            (c_test2_pivotPairRestEquiv_apply_j aStar j (Ne.symm hjNe) z).symm
          _ = zj := by rw [hcoords]
      have hrest (i : Other) : z i.1 = r i := by
        calc
          z i.1 = (c_test2_pivotPairRestEquiv aStar j (Ne.symm hjNe) z).2 i :=
            (c_test2_pivotPairRestEquiv_apply_other aStar j (Ne.symm hjNe) z i).symm
          _ = r i := by rw [hcoords]
      have hvertex (ω : NonTarget Sh → Fin 2) :
          targetVertex c Sh p Mp (fun i => (z i : ℚ)) u ω =
            (((rootPair N p).k : ℤ) * za + ((rootPair N p).b : ℤ) * zj +
              offset r + (Mp : ℤ) *
                ∑ R : NonTarget Sh,
                  (if ω R = 1 then (u R 1 : ℤ) - u R 0 else 0) : ℤ) := by
        rw [c_test2_targetVertex_decomposition c Sh p Mp z u ω alpha aStar j
          (Ne.symm hjNe) hcoeff (rootPair N p).k (rootPair N p).b hkEq hbEq]
        simp [offset, z, hza, hzj, hrest]
        ring
      unfold Fwhole Fbase
      apply Finset.prod_congr rfl
      intro ω hω
      rw [hvertex ω]
      rw [hAtQInt]
    have hWpos : 0 < W := primorial_pos (N + 1)
    have hWdvdM : W ∣ A.M N := by
      obtain ⟨e, he⟩ := S.core.modulus_power N
      by_cases hWone : W = 1
      · simp [hWone]
      · have hWgt : 1 < W := by omega
        have hWM : W ≤ W ^ e := by
          have hle := A.Wle N
          rw [he] at hle
          exact hle
        have hepos : e ≠ 0 := by
          intro he0
          subst e
          simp at hWM
          omega
        rw [he]
        exact dvd_pow_self W hepos
    have hroughPos : 0 < roughPart (N + 1)
        (evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))) := by
      unfold roughPart
      apply Finset.prod_pos
      intro π hπ
      exact pow_pos
        (Nat.Prime.pos ((Finset.mem_filter.mp hπ).2.1)) _
    have hWdvdMp : W ∣ Mp := by
      change W ∣ directionModulus S N dirs.poly p
      unfold directionModulus
      exact dvd_mul_of_dvd_left hWdvdM _
    have hMpPos : 0 < Mp := by
      change 0 < directionModulus S N dirs.poly p
      unfold directionModulus
      exact Nat.mul_pos (A.Mpos N) hroughPos
    have hWalpha (i : Other) : W ∣ alpha i.1 := by
      by_cases hi : i.1 < aStar
      · have hi' : i.1 < (Sh.row Sh.star).anchor := by simpa [hAnchor] using hi
        exact hAlphaData.2.1 i.1 hi'
      · have hgt : (Sh.row Sh.star).anchor < i.1 := by
          have hne := i.2.1
          rw [hAnchor]
          omega
        have hz := c_test2_targetAlpha_zero_after_anchor (Sh.row Sh.star) p c alpha
          hcoeff i.1 hgt
        rw [hz]
        exact dvd_zero W
    have hdivOffset (r : Other → ℤ) : (W : ℤ) ∣ offset r := by
      unfold offset
      apply dvd_add
      · apply Finset.dvd_sum
        intro i hi
        exact dvd_mul_of_dvd_left
          (Int.natCast_dvd_natCast.mpr (hWalpha i)) _
      · have hWdvdMpInt : (W : ℤ) ∣ (Mp : ℤ) := by exact_mod_cast hWdvdMp
        exact dvd_mul_of_dvd_left hWdvdMpInt _
    have hL : T.length S C.gap J0 N p =
        A.H N C.gap / (J0 * Mp) := by
      rfl
    have hdenMul : (T.length S C.gap J0 N p) * (J0 * Mp) ≤ A.H N C.gap := by
      rw [hL]
      exact Nat.div_mul_le_self _ _
    have hMpL : Mp * T.length S C.gap J0 N p ≤ A.H N C.gap := by
      calc
        _ ≤ J0 * (Mp * T.length S C.gap J0 N p) :=
          Nat.le_mul_of_pos_left _ hJ0
        _ = T.length S C.gap J0 N p * (J0 * Mp) := by ring
        _ ≤ A.H N C.gap := hdenMul
    have hshiftRange (R : NonTarget Sh) (b : Fin 2) :
        u R b < T.length S C.gap J0 N p := by
      have hu' := Fintype.mem_piFinset.mp hu
      have huR := Fintype.mem_piFinset.mp (hu' R)
      exact Finset.mem_range.mp (huR b)
    have hsumU :
        (∑ R : NonTarget Sh, u R 0) ≤
          Fintype.card (NonTarget Sh) * T.length S C.gap J0 N p := by
      calc
        _ ≤ ∑ R : NonTarget Sh, T.length S C.gap J0 N p :=
          Finset.sum_le_sum fun R hR => Nat.le_of_lt (hshiftRange R 0)
        _ = _ := by simp
    have hcardNT : Fintype.card (NonTarget Sh) = T.d := by rfl
    have hshiftBound :
        Mp * (∑ R : NonTarget Sh, u R 0) ≤ T.d * A.H N (C.block aStar).1 := by
      calc
        _ ≤ Mp * (Fintype.card (NonTarget Sh) * T.length S C.gap J0 N p) :=
          Nat.mul_le_mul_left _ hsumU
        _ = T.d * (Mp * T.length S C.gap J0 N p) := by rw [hcardNT]; ring
        _ ≤ T.d * A.H N C.gap := Nat.mul_le_mul_left _ hMpL
        _ ≤ T.d * A.H N (C.block aStar).1 :=
          Nat.mul_le_mul_left _ (hgapLeAnchor N)
    have hHaOne : 1 ≤ A.H N (C.block aStar).1 := by
      have h := A.Hpos N (C.block aStar).1
      omega
    let HaPow : ℕ := (A.H N (C.block aStar).1) ^ (E + 3)
    have hHaLePow : A.H N (C.block aStar).1 ≤ HaPow := by
      dsimp [HaPow]
      calc
        A.H N (C.block aStar).1 = (A.H N (C.block aStar).1) ^ 1 := by simp
        _ ≤ (A.H N (C.block aStar).1) ^ (E + 3) :=
          Nat.pow_le_pow_right hHaOne (by omega : 1 ≤ E + 3)
    have hcardOther : Fintype.card Other ≤ m := by
      simpa using (Fintype.card_le_of_injective
        (fun i : Other => i.1) Subtype.val_injective)
    have hrestTerm (r : Other → ℤ) (hrestNZ : c_test2_restPivotMass A C N aStar j r ≠ 0)
        (i : Other) :
        (alpha i.1 : ℤ) * r i ≤ (HaPow : ℤ) := by
      have hprodNZ : (∏ i : Other,
          harmonicLaw (A.X N (C.block i.1).1) W (r i)) ≠ 0 := by
        simpa [c_test2_restPivotMass] using hrestNZ
      have hLawNZ : harmonicLaw (A.X N (C.block i.1).1) W (r i) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hprodNZ) i (Finset.mem_univ i)
      have hsupp := c_test2_harmonicLaw_support hLawNZ
      by_cases hi : i.1 < aStar
      · have hXi : A.X N (C.block i.1).1 ≤ A.H N (C.block aStar).1 := hotherN i hi
        have hAlphaSmall : alpha i.1 ≤ (A.H N (C.block aStar).1) ^ (E + 1) := by
          calc
            alpha i.1 ≤
                ((S.primeStage.pool N C.gap).upper + V N) ^ (E + 1) := hAlphaData.1 i.1
            _ ≤ (A.H N (C.block aStar).1) ^ (E + 1) :=
              Nat.pow_le_pow_left hsizeN (E + 1)
        have hAlpha : alpha i.1 ≤ HaPow := by
          dsimp [HaPow]
          calc
            alpha i.1 ≤ (A.H N (C.block aStar).1) ^ (E + 1) := hAlphaSmall
            _ ≤ (A.H N (C.block aStar).1) ^ (E + 3) :=
              Nat.pow_le_pow_right hHaOne (by omega : E + 1 ≤ E + 3)
        have hcastZ : ((r i).toNat : ℤ) = r i := Int.toNat_of_nonneg hsupp.1
        have hZlt : (r i).toNat < (A.X N (C.block i.1).1) ^ 2 := by
          have h := hsupp.2.2
          rw [← hcastZ] at h
          exact_mod_cast h
        have hZ : (r i).toNat ≤ (A.H N (C.block aStar).1) ^ 2 := by
          exact (Nat.le_of_lt hZlt).trans (Nat.pow_le_pow_left hXi 2)
        have hmul : alpha i.1 * (r i).toNat ≤ HaPow := by
          dsimp [HaPow] at hAlpha ⊢
          calc
            _ ≤ (A.H N (C.block aStar).1) ^ (E + 1) *
                (A.H N (C.block aStar).1) ^ 2 := Nat.mul_le_mul hAlphaSmall hZ
            _ = _ := by rw [← Nat.pow_add]
        rw [← hcastZ]
        exact_mod_cast hmul
      · have hgt : (Sh.row Sh.star).anchor < i.1 := by
          have hne := i.2.1
          rw [hAnchor]
          omega
        have hzeroAlpha := c_test2_targetAlpha_zero_after_anchor
          (Sh.row Sh.star) p c alpha hcoeff i.1 hgt
        simp [hzeroAlpha]
    have hrestSumBound (r : Other → ℤ)
        (hrestNZ : c_test2_restPivotMass A C N aStar j r ≠ 0) :
        (∑ i : Other, (alpha i.1 : ℤ) * r i) ≤
          (m : ℤ) * (HaPow : ℤ) := by
      calc
        _ ≤ ∑ i : Other, (HaPow : ℤ) :=
          Finset.sum_le_sum fun i hi => hrestTerm r hrestNZ i
        _ = (Fintype.card Other : ℤ) * (HaPow : ℤ) := by simp
        _ ≤ (m : ℤ) * (HaPow : ℤ) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcardOther
          · positivity
    have hshiftCast (r : Other → ℤ) :
        (Mp : ℤ) * ∑ R : NonTarget Sh, (u R 0 : ℤ) ≤
          (T.d : ℤ) * (A.H N (C.block aStar).1 : ℤ) := by
      exact_mod_cast hshiftBound
    have hshiftPow (r : Other → ℤ) :
        (Mp : ℤ) * ∑ R : NonTarget Sh, (u R 0 : ℤ) ≤
          (T.d : ℤ) * (HaPow : ℤ) := by
      exact le_trans (hshiftCast r)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hHaLePow)
          (by exact_mod_cast Nat.zero_le T.d))
    have hOffUpper (r : Other → ℤ)
        (hrestNZ : c_test2_restPivotMass A C N aStar j r ≠ 0) :
        offset r ≤ ((m + maskRowBound m) * HaPow : ℤ) := by
      dsimp [offset]
      have hTle : T.d ≤ maskRowBound m := by omega
      have hshiftBound' :
          (T.d : ℤ) * (HaPow : ℤ) ≤ (maskRowBound m : ℤ) * (HaPow : ℤ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hTle) (by positivity)
      have hRest := hrestSumBound r hrestNZ
      have hShift := hshiftPow r
      calc
        _ ≤ (m : ℤ) * (HaPow : ℤ) +
            (maskRowBound m : ℤ) * (HaPow : ℤ) := add_le_add hRest (hShift.trans hshiftBound')
        _ = ((m + maskRowBound m) * HaPow : ℤ) := by push_cast; ring
    have hOffRoot (r : Other → ℤ)
        (hrestNZ : c_test2_restPivotMass A C N aStar j r ≠ 0) :
        offset r ≤ (Hroot N : ℤ) := by
      have hrootNat : (m + maskRowBound m) * HaPow ≤ c_test2_rootOffsetScale S C aStar j E N := by
        dsimp [c_test2_rootOffsetScale, HaPow]
        calc
          _ ≤ (m + maskRowBound m + 2) *
              (A.H N (C.block aStar).1) ^ (E + 3) := by
                apply Nat.mul_le_mul_right
                omega
          _ ≤ (m + maskRowBound m + 2) *
                (A.H N (C.block aStar).1) ^ (E + 3) + _ := Nat.le_add_right _ _
      exact le_trans (hOffUpper r hrestNZ) (by exact_mod_cast hrootNat)
    have hOffNonneg (r : Other → ℤ)
        (hrestNZ : c_test2_restPivotMass A C N aStar j r ≠ 0) : 0 ≤ offset r := by
      unfold offset
      apply add_nonneg
      · apply Finset.sum_nonneg
        intro i hi
        have hprodNZ : (∏ i : Other,
            harmonicLaw (A.X N (C.block i.1).1) W (r i)) ≠ 0 := by
          simpa [c_test2_restPivotMass] using hrestNZ
        have hLawNZ : harmonicLaw (A.X N (C.block i.1).1) W (r i) ≠ 0 :=
          (Finset.prod_ne_zero_iff.mp hprodNZ) i (Finset.mem_univ i)
        exact mul_nonneg (by positivity) (c_test2_harmonicLaw_support hLawNZ).1
      · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun R hR => Int.natCast_nonneg _)
    have hdivOffset (r : Other → ℤ) : (W : ℤ) ∣ offset r := by
      apply dvd_add
      · apply Finset.dvd_sum
        intro i hi
        have hWalpha : W ∣ alpha i.1 := by
          by_cases hlt : i.1 < aStar
          · have hlt' : i.1 < (Sh.row Sh.star).anchor := by simpa [hAnchor] using hlt
            exact hAlphaData.2.1 i.1 hlt'
          · have hgt : (Sh.row Sh.star).anchor < i.1 := by
              have hne := i.2.1
              rw [hAnchor]
              omega
            rw [c_test2_targetAlpha_zero_after_anchor (Sh.row Sh.star) p c alpha hcoeff i.1 hgt]
            exact dvd_zero W
        exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hWalpha) _
      · have hWdvdM : W ∣ A.M N := by
          obtain ⟨e, he⟩ := S.core.modulus_power N
          by_cases hWone : W = 1
          · simp [hWone]
          · have hWM : W ≤ W ^ e := by
              have hle := A.Wle N
              rw [he] at hle
              exact hle
            have hepos : e ≠ 0 := by
              intro he0
              subst e
              simp at hWM
              omega
            rw [he]
            exact dvd_pow_self W hepos
        have hWdvdMp : W ∣ Mp := by
          change W ∣ directionModulus S N dirs.poly p
          unfold directionModulus
          exact dvd_mul_of_dvd_left hWdvdM _
        exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hWdvdMp) _
    have hNormRest : ∀ i : Other,
        0 < harmonicNormalizer (A.X N (C.block i.1).1) W := by
      intro i
      exact c_test2_harmonicNormalizer_pos_of_cutoff _ _ hWpos
        (S.gapStage.valid_raw_cutoffs N (C.block i.1).1)
    have hRestOne := c_test2_restPivotMass_tsum_one A C N aStar j
      (Ne.symm hjNe) hNormRest
    have hRestNonneg := c_test2_restPivotMass_nonneg A C N aStar j
      (Ne.symm hjNe) hNormRest
    have hRestSummable := c_test2_restPivotMass_summable A C N aStar j (Ne.symm hjNe)
    let restSupport : Finset (Other → ℤ) := Fintype.piFinset fun i : Other =>
      Finset.Ico (A.X N (C.block i.1).1 : ℤ) ((A.X N (C.block i.1).1) ^ 2 : ℤ)
    have hRestZero (r : Other → ℤ) (hr : r ∉ restSupport) :
        c_test2_restPivotMass A C N aStar j r = 0 := by
      have hnot : ¬ ∀ i : Other, r i ∈
          Finset.Ico (A.X N (C.block i.1).1 : ℤ) ((A.X N (C.block i.1).1) ^ 2 : ℤ) := by
        intro hall
        exact hr (Fintype.mem_piFinset.mpr hall)
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      have hLaw : harmonicLaw (A.X N (C.block i.1).1) (primorial (N + 1)) (r i) = 0 := by
        by_contra hne
        have hs := c_test2_harmonicLaw_support hne
        have hmem : r i ∈
            Finset.Ico (A.X N (C.block i.1).1 : ℤ) ((A.X N (C.block i.1).1) ^ 2 : ℤ) := by
          simp [Finset.mem_Ico]
          exact ⟨hs.2.1, hs.2.2⟩
        exact hi hmem
      unfold c_test2_restPivotMass
      exact Finset.prod_eq_zero (Finset.mem_univ i) hLaw
    let ref : ℝ := ∑' y : ℤ, harmonicLaw (Xa N) W y * Fbase y
    let pairAvg : (Other → ℤ) → ℝ := fun r =>
      ∑' za : ℤ, ∑' zj : ℤ,
        harmonicLaw (Xa N) W za * harmonicLaw (Xj N) W zj *
          Fbase (((rootPair N p).k : ℤ) * za + ((rootPair N p).b : ℤ) * zj + offset r)
    have hAvgSummable : Summable (fun r =>
        c_test2_restPivotMass A C N aStar j r * pairAvg r) := by
      apply summable_of_ne_finset_zero (s := restSupport)
      intro r hr
      rw [hRestZero r hr]
      simp
    have hsample : ∀ r : Other → ℤ,
        c_test2_restPivotMass A C N aStar j r = 0 ∨ |pairAvg r - ref| ≤ δ := by
      intro r
      by_cases hr : c_test2_restPivotMass A C N aStar j r = 0
      · exact Or.inl hr
      · right
        have hroot0 := hOffNonneg r hr
        have hrootH := hOffRoot r hr
        have hrootW := hdivOffset r
        have hVnat : 1 ≤ V N := by
          unfold V FromArithmetic.masterScaleV
          omega
        have hVreal : (1 : ℝ) ≤ (V N : ℝ) := by exact_mod_cast hVnat
        have hsamp := hSampleN p (offset r) hroot0 hrootH hrootW Fbase hFbound
        have herr :
            |(∑' za : ℤ, ∑' zj : ℤ,
                harmonicLaw (Xa N) W za * harmonicLaw (Xj N) W zj *
                  Fbase (((rootPair N p).k : ℤ) * za +
                    ((rootPair N p).b : ℤ) * zj + offset r)) - ref| ≤ δ := by
          have hle : |(∑' za : ℤ, ∑' zj : ℤ,
              harmonicLaw (Xa N) W za * harmonicLaw (Xj N) W zj *
                Fbase (((rootPair N p).k : ℤ) * za +
                  ((rootPair N p).b : ℤ) * zj + offset r)) - ref| ≤
              (V N : ℝ) * |(∑' za : ℤ, ∑' zj : ℤ,
                harmonicLaw (Xa N) W za * harmonicLaw (Xj N) W zj *
                  Fbase (((rootPair N p).k : ℤ) * za +
                    ((rootPair N p).b : ℤ) * zj + offset r)) - ref| := by
            calc
              _ = 1 * _ := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hVreal (abs_nonneg _)
          exact le_trans hle (by simpa [ref] using hsamp)
        simpa [pairAvg, ref] using herr
    exact c_test2_pivotSampling_expectation_error A C N aStar j (Ne.symm hjNe)
      (Xa N) (Xj N) (rootPair N p).k (rootPair N p).b rfl rfl Fbase Fwhole offset δ
      (le_of_lt hδ) hdecomp hsample hRestNonneg hRestSummable hRestOne hAvgSummable
  have hCubePerGoodTuple
      (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
      (hscaleN : c_test2_ScaleData S C a N)
      (hpoolN : 2 * V N ≤ (S.primeStage.pool N C.gap).lower)
      (hSampleN : ∀ p, samplePred δ N p)
      (hsizeN : (S.primeStage.pool N C.gap).upper + V N ≤ A.H N (C.block aStar).1)
      (hpreviousN : OAI.SourceAdmissible.previous (A.X N) (C.block aStar).1 ≤
        A.H N (C.block aStar).1)
      (hotherN : ∀ i : CTest2OtherPivot aStar j, i.1 < aStar →
        A.X N (C.block i.1).1 ≤ A.H N (C.block aStar).1)
      (J0 : ℕ) (hJ0 : 0 < J0) (p : Fin q → ℕ)
      (hp : GoodTuple S C.gap N testList dirs.poly p)
      (g : ℤ → ℝ) (hGbound : ∀ y, |g y| ≤
        1 + chainWeight S.core.parameters C N aStar y) :
      |(∑' z : Fin m → ℤ, pivotMass A C N z *
          shiftAverage (NonTarget Sh) (T.length S C.gap J0 N p) (fun u =>
            ∏ ω : NonTarget Sh → Fin 2,
              atQ g (targetVertex (chainScale A C a N) Sh p
                (T.modulus S N p) (fun k => (z k : ℚ)) u ω))) -
        ∑' y : ℤ, harmonicLaw (Xa N) (primorial (N + 1)) y *
          shiftAverage (Fin T.d) (T.length S C.gap J0 N p) (fun u =>
            ∏ s : Finset (Fin T.d),
              g (y + (T.modulus S N p : ℤ) *
                ∑ k ∈ s, ((u k 1 : ℤ) - u k 0)))| ≤ δ := by
    classical
    let L := T.length S C.gap J0 N p
    let U := Fintype.piFinset (fun _ : NonTarget Sh =>
      Fintype.piFinset fun _ : Fin 2 => Finset.range L)
    let Fshift : (Fin m → ℤ) → (NonTarget Sh → Fin 2 → ℕ) → ℝ := fun z u =>
      ∏ ω : NonTarget Sh → Fin 2,
        atQ g (targetVertex (chainScale A C a N) Sh p
          (T.modulus S N p) (fun k => (z k : ℚ)) u ω)
    let PivotAvg : (NonTarget Sh → Fin 2 → ℕ) → ℝ := fun u =>
      ∑' z : Fin m → ℤ, pivotMass A C N z * Fshift z u
    let RefShift : (NonTarget Sh → Fin 2 → ℕ) → ℝ := fun u =>
      ∑' y : ℤ, harmonicLaw (Xa N) (primorial (N + 1)) y *
        ∏ ω : NonTarget Sh → Fin 2,
          g (y + (T.modulus S N p : ℤ) *
            ∑ R : NonTarget Sh,
              if ω R = 1 then (u R 1 : ℤ) - u R 0 else 0)
    let PivotClamp : (NonTarget Sh → Fin 2 → ℕ) → ℝ := fun u =>
      if u ∈ U then PivotAvg u else RefShift u
    have hpoint : ∀ u, |PivotClamp u - RefShift u| ≤ δ := by
      intro u
      by_cases hu : u ∈ U
      · simpa [PivotClamp, hu] using
          hCubePivotAverage δ hδ N hscaleN hpoolN hSampleN hsizeN hpreviousN hotherN
            J0 hJ0 p hp g hGbound u hu
      · simpa [PivotClamp, hu] using (le_of_lt hδ)
    have hshiftClampEq :
        shiftAverage (NonTarget Sh) L PivotAvg = shiftAverage (NonTarget Sh) L PivotClamp := by
      unfold shiftAverage
      have hsum : (∑ u ∈ U, PivotAvg u) = ∑ u ∈ U, PivotClamp u := by
        apply Finset.sum_congr rfl
        intro u hu
        simp [PivotClamp, hu]
      rw [hsum]
    have hcardNT : Fintype.card (NonTarget Sh) = T.d := by rfl
    let pivotSupport : Finset (Fin m → ℤ) := Fintype.piFinset fun i : Fin m =>
      Finset.Ico (A.X N (C.block i).1 : ℤ) ((A.X N (C.block i).1) ^ 2 : ℤ)
    have hPivotMassZero (z : Fin m → ℤ) (hz : z ∉ pivotSupport) :
        pivotMass A C N z = 0 := by
      have hnot : ¬ ∀ i : Fin m, z i ∈
          Finset.Ico (A.X N (C.block i).1 : ℤ) ((A.X N (C.block i).1) ^ 2 : ℤ) := by
        intro hall
        exact hz (Fintype.mem_piFinset.mpr hall)
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      have hLaw : harmonicLaw (A.X N (C.block i).1) (primorial (N + 1)) (z i) = 0 := by
        by_contra hne
        have hs := c_test2_harmonicLaw_support hne
        have hmem : z i ∈
            Finset.Ico (A.X N (C.block i).1 : ℤ) ((A.X N (C.block i).1) ^ 2 : ℤ) := by
          simp [Finset.mem_Ico]
          exact ⟨hs.2.1, hs.2.2⟩
        exact hi hmem
      unfold pivotMass
      exact Finset.prod_eq_zero (Finset.mem_univ i) hLaw
    have hPivotShiftCommute (F : (Fin m → ℤ) →
        (NonTarget Sh → Fin 2 → ℕ) → ℝ) :
        (∑' z : Fin m → ℤ, pivotMass A C N z *
          shiftAverage (NonTarget Sh) L (F z)) =
          shiftAverage (NonTarget Sh) L (fun u =>
            ∑' z : Fin m → ℤ, pivotMass A C N z * F z u) := by
      have hinterchange :
          (∑' z : Fin m → ℤ, pivotMass A C N z * ∑ u ∈ U, F z u) =
            ∑ u ∈ U, ∑' z : Fin m → ℤ, pivotMass A C N z * F z u := by
        have hzeroOuter (z : Fin m → ℤ) (hz : z ∉ pivotSupport) :
            pivotMass A C N z * ∑ u ∈ U, F z u = 0 := by
          rw [hPivotMassZero z hz]
          simp
        have hzeroPoint (u : NonTarget Sh → Fin 2 → ℕ) (z : Fin m → ℤ)
            (hz : z ∉ pivotSupport) : pivotMass A C N z * F z u = 0 := by
          rw [hPivotMassZero z hz]
          simp
        calc
          _ = ∑ z ∈ pivotSupport, pivotMass A C N z * ∑ u ∈ U, F z u :=
            tsum_eq_sum (s := pivotSupport) hzeroOuter
          _ = ∑ z ∈ pivotSupport, ∑ u ∈ U, pivotMass A C N z * F z u := by
            apply Finset.sum_congr rfl
            intro z hz
            simp_rw [Finset.mul_sum]
          _ = ∑ u ∈ U, ∑ z ∈ pivotSupport, pivotMass A C N z * F z u := by
            exact Finset.sum_comm
          _ = ∑ u ∈ U, ∑' z : Fin m → ℤ, pivotMass A C N z * F z u := by
            apply Finset.sum_congr rfl
            intro u hu
            symm
            exact tsum_eq_sum (s := pivotSupport) (hzeroPoint u)
      unfold shiftAverage
      calc
        _ = ((L : ℝ) ^ (2 * Fintype.card (NonTarget Sh)))⁻¹ *
            ∑' z : Fin m → ℤ, pivotMass A C N z * ∑ u ∈ U, F z u := by
          calc
            _ = ∑' z : Fin m → ℤ,
                ((L : ℝ) ^ (2 * Fintype.card (NonTarget Sh)))⁻¹ *
                  (pivotMass A C N z * ∑ u ∈ U, F z u) := by
              apply tsum_congr
              intro z
              ring
            _ = _ := by rw [← tsum_mul_left]
        _ = ((L : ℝ) ^ (2 * Fintype.card (NonTarget Sh)))⁻¹ *
            ∑ u ∈ U, ∑' z : Fin m → ℤ, pivotMass A C N z * F z u := by
          rw [hinterchange]
        _ = shiftAverage (NonTarget Sh) L (fun u =>
            ∑' z : Fin m → ℤ, pivotMass A C N z * F z u) := by
          rfl
    have hshiftErr :
        |shiftAverage (NonTarget Sh) L PivotClamp -
          shiftAverage (NonTarget Sh) L RefShift| ≤ δ := by
      by_cases hL : 0 < L
      · exact c_test2_shiftAverage_error L PivotClamp RefShift δ hL hpoint
      · have hL0 : L = 0 := by omega
        have hcardPos : 0 < Fintype.card (NonTarget Sh) := by
          rw [hcardNT]
          omega
        have hpow : (0 : ℝ) ^ (2 * Fintype.card (NonTarget Sh)) = 0 :=
          zero_pow (by omega)
        letI : Nonempty (NonTarget Sh) := Fintype.card_pos_iff.mp hcardPos
        have hU : U = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro u hu
          obtain ⟨i⟩ : Nonempty (NonTarget Sh) := Fintype.card_pos_iff.mp hcardPos
          have hi := Fintype.mem_piFinset.mp hu i
          have h0 := Fintype.mem_piFinset.mp hi 0
          have hlt := Finset.mem_range.mp h0
          rw [hL0] at hlt
          omega
        have hzero (F : (NonTarget Sh → Fin 2 → ℕ) → ℝ) :
            shiftAverage (NonTarget Sh) L F = 0 := by
          simp [shiftAverage, hL0, hpow, hU, U]
        rw [hzero PivotClamp, hzero RefShift]
        simpa using (le_of_lt hδ)
    have hPivotErr :
        |(∑' z : Fin m → ℤ, pivotMass A C N z * shiftAverage (NonTarget Sh) L
              (fun u => Fshift z u)) - shiftAverage (NonTarget Sh) L RefShift| ≤ δ := by
      have hcommute := hPivotShiftCommute Fshift
      calc
        _ = |shiftAverage (NonTarget Sh) L PivotAvg -
              shiftAverage (NonTarget Sh) L RefShift| := by rw [hcommute]
        _ = |shiftAverage (NonTarget Sh) L PivotClamp -
              shiftAverage (NonTarget Sh) L RefShift| := by rw [hshiftClampEq]
        _ ≤ δ := hshiftErr
    let e : NonTarget Sh ≃ Fin T.d := Fintype.equivFin (NonTarget Sh)
    have hsubsetCube (u : Fin T.d → Fin 2 → ℕ) (y : ℤ) :
        (∏ ω : NonTarget Sh → Fin 2,
          g (y + (T.modulus S N p : ℤ) *
            ∑ R : NonTarget Sh,
              if ω R = 1 then ((u (e R) 1 : ℤ) - u (e R) 0) else 0)) =
        ∏ s : Finset (Fin T.d),
          g (y + (T.modulus S N p : ℤ) *
            ∑ k ∈ s, ((u k 1 : ℤ) - u k 0)) := by
      simpa using c_test2_cubeProduct_reindex_equiv e g y
        (T.modulus S N p : ℤ) (fun R b => u (e R) b)
    have hRefShiftReindex :
        shiftAverage (NonTarget Sh) L RefShift =
          ∑' y : ℤ, harmonicLaw (Xa N) (primorial (N + 1)) y *
            shiftAverage (Fin T.d) L (fun u =>
              ∏ s : Finset (Fin T.d),
                g (y + (T.modulus S N p : ℤ) *
                  ∑ k ∈ s, ((u k 1 : ℤ) - u k 0))) := by
      classical
      let μ : ℤ → ℝ := harmonicLaw (Xa N) (primorial (N + 1))
      let cube : (Fin T.d → Fin 2 → ℕ) → ℤ → ℝ := fun u y =>
        ∏ s : Finset (Fin T.d),
          g (y + (T.modulus S N p : ℤ) *
            ∑ k ∈ s, ((u k 1 : ℤ) - u k 0))
      have hsum (u : Fin T.d → Fin 2 → ℕ) :
          RefShift (fun R => fun b => u (e R) b) = ∑' y : ℤ, μ y * cube u y := by
        unfold RefShift μ cube
        apply tsum_congr
        intro y
        rw [hsubsetCube u y]
      have hzero (y : ℤ) (hy : y ∉ Finset.Ico (Xa N : ℤ) ((Xa N) ^ 2 : ℤ)) : μ y = 0 := by
        by_contra hne
        have hsup := c_test2_harmonicLaw_support (by simpa [μ] using hne)
        have hmem : y ∈ Finset.Ico (Xa N : ℤ) ((Xa N) ^ 2 : ℤ) := by
          simp [Finset.mem_Ico]
          exact ⟨hsup.2.1, hsup.2.2⟩
        exact hy hmem
      have hFsum : ∀ u, Summable (fun y : ℤ => μ y * cube u y) := by
        intro u
        apply summable_of_ne_finset_zero (s := Finset.Ico (Xa N : ℤ) ((Xa N) ^ 2 : ℤ))
        intro y hy
        rw [hzero y hy]
        simp
      have hswap := c_test2_shiftAverage_tsum_commute L μ cube hFsum
      calc
        shiftAverage (NonTarget Sh) L RefShift =
            shiftAverage (Fin T.d) L (fun u => RefShift (fun R => fun b => u (e R) b)) :=
              c_test2_shiftAverage_reindex e L RefShift
        _ = shiftAverage (Fin T.d) L (fun u => ∑' y : ℤ, μ y * cube u y) := by
              congr 1
              funext u
              exact hsum u
        _ = ∑' y : ℤ, μ y * shiftAverage (Fin T.d) L (fun u => cube u y) := hswap
        _ = _ := by rfl
    rw [← hRefShiftReindex]
    exact hPivotErr
  have hCubeComparison (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ N in atTop, ∀ J0 : ℕ, 0 < J0 → ∀ g : ℤ → ℝ,
        (∀ y, |g y| ≤ 1 + chainWeight S.core.parameters C N aStar y) →
        |additiveCube S C a N dirs testList J0 (fun _ => g) -
          T.cubeTest S C.gap (C.block aStar).1 J0 N g| ≤ δ := by
    have hMassEventually := c_test2_poolMass_positive_eventually S C.gap
    filter_upwards [hScaleEventually, hPoolEventually, hSampleUniform δ hδ,
      hsizeAnchor, hpreviousAnchor, hotherCutoffEventually,
      hGoodProbabilityEventually, hMassEventually]
      with N hscaleN hpoolN hSampleN hsizeN hpreviousN hotherN hGoodN hMassN
    intro J0 hJ0 g hGbound
    let Fcube (p : Fin q → ℕ) : ℝ :=
      ∑' z : Fin m → ℤ, pivotMass A C N z *
        shiftAverage (NonTarget Sh) (T.length S C.gap J0 N p) (fun u =>
          ∏ ω : NonTarget Sh → Fin 2,
            atQ g (targetVertex (chainScale A C a N) Sh p
              (T.modulus S N p) (fun k => (z k : ℚ)) u ω))
    let Gcube (p : Fin q → ℕ) : ℝ :=
      ∑' y : ℤ, harmonicLaw (Xa N) (primorial (N + 1)) y *
        shiftAverage (Fin T.d) (T.length S C.gap J0 N p) (fun u =>
          ∏ s : Finset (Fin T.d),
            g (y + (T.modulus S N p : ℤ) *
              ∑ k ∈ s, ((u k 1 : ℤ) - u k 0)))
    have hpoint (p : Fin q → ℕ) (hp : GoodTuple S C.gap N testList dirs.poly p) :
        |Fcube p - Gcube p| ≤ δ := by
      simpa [Fcube, Gcube] using
        hCubePerGoodTuple δ hδ N hscaleN hpoolN hSampleN hsizeN hpreviousN
          hotherN J0 hJ0 p hp g hGbound
    have havg := c_test2_goodSlotAverage_error S C.gap N
      (GoodTuple S C.gap N testList dirs.poly) Fcube Gcube δ hMassN hGoodN
      hpoint (le_of_lt hδ)
    have hTgood : T.Good S C.gap N =
        (fun p => GoodTuple S C.gap N testList dirs.poly p) := by
      funext p
      rfl
    unfold additiveCube CubeTemplate.cubeTest
    rw [hTgood]
    simpa [Fcube, Gcube, T, Xa, CubeTemplate.length, CubeTemplate.modulus] using havg
  refine ⟨hrowFacts.2.1, hrowFacts.1, hmodBound, ?_⟩
  intro J0s hJ0s ε hε
  let tau : ℝ := (ε / 2) ^ finalPow
  have hDpos : 0 < addPow := by dsimp [addPow]; positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hcorrCoeff : 0 < corrCoeff := by dsimp [corrCoeff]; positivity
  obtain ⟨eta, hEta, hEtaOne, hCombine⟩ :=
    c_test2_error_tolerance maskPow addPow hDpos CmMask CmAdd tau
      hCmMask hCmAdd htau
  have hAddUniform : ∀ᶠ N in atTop, ∀ J0 ∈ J0s,
      ∀ f : Fin completion.r' → (Fin q → ℕ) → ℤ → ℝ,
        (∀ R p y, |f R p y| ≤
          1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) →
        |goodRowCorrelation S C a N dirs testList f| ^ addPow ≤
          CmAdd * |additiveCube S C a N dirs testList J0 (f Sh.star)| + eta := by
    classical
    have hBuild : ∀ s : Finset ℕ, (∀ J0 ∈ s, 0 < J0) →
        ∀ᶠ N in atTop, ∀ J0 ∈ s,
          ∀ f : Fin completion.r' → (Fin q → ℕ) → ℤ → ℝ,
            (∀ R p y, |f R p y| ≤
              1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) →
            |goodRowCorrelation S C a N dirs testList f| ^ addPow ≤
              CmAdd * |additiveCube S C a N dirs testList J0 (f Sh.star)| + eta := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro _
          exact Filter.Eventually.of_forall (by simp)
      | @insert j s hj ih =>
          intro hpos
          have hjpos : 0 < j := hpos j (Finset.mem_insert_self j s)
          have hspos : ∀ J0 ∈ s, 0 < J0 := by
            intro J0 hJ0
            exact hpos J0 (Finset.mem_insert_of_mem hJ0)
          have hThis := hAddElim S ι hlistedAll C a ha j hjpos eta hEta
          have hRest := ih hspos
          filter_upwards [hThis, hRest] with N hThis hRest
          intro J0 hJ0 f hf
          rcases Finset.mem_insert.mp hJ0 with heq | hmem
          · subst J0
            exact hThis f hf
          · exact hRest J0 hmem f hf
    exact hBuild J0s hJ0s
  have hMaskEventually := hMaskRemoval S ι hlistedMask C a ha eta hEta
  have hRowDropEventually := c_test2_rowCorrelation_le_good_eventually
    S C a ha Sh dirs ι testList hlistedAll hRowPrimitive hRowPairwise hrowFacts.1 eta hEta
  have hCubeEventually := hCubeComparison eta hEta
  filter_upwards [hMaskEventually, hRowDropEventually, hCubeEventually, hAddUniform]
    with N hMaskN hRowDropN hCubeN hAddN
  intro J0 hJ0 b g hValid
  obtain ⟨f0, hf0Bound, hf0Star, hMaskBound⟩ := hMaskN b g hValid
  let f : Fin completion.r' → (Fin q → ℕ) → ℤ → ℝ := completion.extend f0
  have hfBound : ∀ R p y, |f R p y| ≤
      1 + chainWeight S.core.parameters C N (Sh.row R).anchor y :=
    completion.extend_bound S C N f0 hf0Bound
  have hfStar (p : Fin q → ℕ) (y : ℤ) : f Sh.star p y = g Jstar y := by
    dsimp [f]
    rw [completion.star_eq, completion.extend_map]
    exact congrFun (hf0Star p) y
  have hrowEq : rowCorrelation S C a N Sh f = rowCorrelation S C a N Sh0 f0 :=
    completion.rowCorrelation_eq S C a N f0
  have hMaskBound' :
      |maskedCorrelation S.core.parameters C a N b g| ^ maskPow ≤
        CmMask * |rowCorrelation S C a N Sh f| + eta := by
    rw [hrowEq]
    exact hMaskBound
  have hRowDrop : |rowCorrelation S C a N Sh f| ≤
      |goodRowCorrelation S C a N dirs testList f| + eta := hRowDropN f hfBound
  have hMaskPower :
      |maskedCorrelation S.core.parameters C a N b g| ^ maskPow ≤
        CmMask * (|goodRowCorrelation S C a N dirs testList f| + eta) + eta := by
    calc
      _ ≤ CmMask * |rowCorrelation S C a N Sh f| + eta := hMaskBound'
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hRowDrop hCmMask.le]
  have hAddPower :
      |goodRowCorrelation S C a N dirs testList f| ^ addPow ≤
        CmAdd * (|T.cubeTest S C.gap (C.block aStar).1 J0 N (g Jstar)| + eta) + eta := by
    have hAdd := hAddN J0 hJ0 f hfBound
    have hfStarFun : f Sh.star = (fun _ : Fin q → ℕ => g Jstar) := by
      funext p y
      exact hfStar p y
    have hAddCubeEq : additiveCube S C a N dirs testList J0 (f Sh.star) =
        additiveCube S C a N dirs testList J0 (fun _ => g Jstar) := by
      rw [hfStarFun]
    have hgBound : ∀ y, |g Jstar y| ≤
        1 + chainWeight S.core.parameters C N aStar y := by
      intro y
      simpa [hAnchor] using hValid.2 Jstar hJne y
    have hJ0pos : 0 < J0 := hJ0s J0 hJ0
    have hCube := hCubeN J0 hJ0pos (g Jstar) hgBound
    have hCubeAbs :
        |additiveCube S C a N dirs testList J0 (f Sh.star)| ≤
          |T.cubeTest S C.gap (C.block aStar).1 J0 N (g Jstar)| + eta := by
      rw [hAddCubeEq]
      let U := additiveCube S C a N dirs testList J0 (fun _ => g Jstar)
      let Vcube := T.cubeTest S C.gap (C.block aStar).1 J0 N (g Jstar)
      have hidentity : (U - Vcube) + Vcube = U := sub_add_cancel U Vcube
      calc
        _ = |(U - Vcube) + Vcube| := by rw [hidentity]
        _ ≤ |U - Vcube| + |Vcube| := abs_add_le _ _
        _ ≤ _ := by nlinarith [hCube]
    calc
      _ ≤ CmAdd * |additiveCube S C a N dirs testList J0 (f Sh.star)| + eta := hAdd
      _ ≤ _ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hCubeAbs hCmAdd.le) le_rfl
  have hCombined := hCombine
    |maskedCorrelation S.core.parameters C a N b g|
    |goodRowCorrelation S C a N dirs testList f|
    |T.cubeTest S C.gap (C.block aStar).1 J0 N (g Jstar)|
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    hMaskPower hAddPower
  have hPow :
      |maskedCorrelation S.core.parameters C a N b g| ^ finalPow ≤
        corrCoeff * |T.cubeTest S C.gap (C.block aStar).1 J0 N (g Jstar)| + tau := by
    simpa [finalPow, maskPow, addPow, corrCoeff] using hCombined
  have hn : 0 < finalPow := by dsimp [finalPow, maskPow, addPow]; positivity
  have hroot := c_test2_root_power_bound hn
    |maskedCorrelation S.core.parameters C a N b g|
    |T.cubeTest S C.gap (C.block aStar).1 J0 N (g Jstar)|
    corrCoeff tau ε (abs_nonneg _) (abs_nonneg _) hcorrCoeff hε hPow (by
      dsimp [tau]
      rfl)
  have hpowEq : finalPow = 2 ^ (maskCount m + T.d) := by
    dsimp [finalPow, maskPow, addPow]
    rw [← pow_add]
  have hexp : (1 : ℝ) / (finalPow : ℝ) =
      ((2 : ℝ) ^ (maskCount m + T.d))⁻¹ := by
    rw [hpowEq]
    norm_num
  have hcoeff : (2 * corrCoeff) ^ (1 / (finalPow : ℝ)) = finalCm := by
    rfl
  rw [hcoeff, hexp] at hroot
  exact hroot

end
end HindmanSumsProducts
