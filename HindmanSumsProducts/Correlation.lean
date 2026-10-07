import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.PkgPrime
import HindmanSumsProducts.Correlation.PkgMask
import HindmanSumsProducts.Correlation.PkgRows
import HindmanSumsProducts.Correlation.PkgElim
import HindmanSumsProducts.Correlation.PkgTest

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
  sorry

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
  sorry

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
  sorry

/-! ## Weighted removal of multiplicative masks (Lemma `lem:mask-removal`, 04:128–307) -/

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
  sorry

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
(ii) `M(p) ∣ R_l` on good tuples (04:610–611, 702–704), (iii) eventually every good tuple
satisfies `IntegerDirectionFacts`. -/
def RowDirections.IntegerConclusions {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q)) (B : ℕ) : Prop :=
  ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s), TestsListed Dm ι tests →
  ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
    Tendsto (fun N => gapSlotProbability S C.gap N fun p =>
      ¬ GoodTuple S C.gap N tests dirs.poly p) atTop (𝓝 0) ∧
    (∀ N p, GoodTuple S C.gap N tests dirs.poly p →
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
        (∀ N p, T.Good S C.gap N p → T.modulus S N p ∣ S.core.parameters.H N C.gap) ∧
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
  sorry

end
end HindmanSumsProducts
