import HindmanSumsProducts.Prediction.Tests

/-!
# §4 data used by §5, and chain counts

§3 and §4 are imported, not copied.  §3: master scales (`MasterScales`, `lem_master_scales`),
sampling (`lem_sampling`), product law (`cor_product_law`), rough coprimality
(`rough_coprimality_survives_high_probability_restrictions`), linear forms
(`prop_linear_forms`).  §4 (repaired, `REPAIR-S4.md`): `uniform_correlation_test`
(Proposition `prop:correlation-test`), `maskedCorrelation`, `FunctionsValid`, `CubeTemplate`.

This file only names the data that Proposition `prop:correlation-test` fixes for each `m` and
`J_*` (before any master scales), and defines the chain counts of (eq:weighted-count) and of the
model replacements (05:742–775) as instances of §4's `maskedCorrelation`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace HindmanSumsProducts.Prediction

noncomputable section

variable {K sl m r : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

theorem nonempty_of_two_le_card {J : Finset (Fin m)} (h : 2 ≤ J.card) : J.Nonempty :=
  Finset.card_pos.mp (by omega)

/-- The anchor `d(J) = a(J) = max J` of a nonsingleton `J`. -/
def anchor (J : Finset (Fin m)) (hJ : 2 ≤ J.card) : Fin m :=
  J.max' (nonempty_of_two_le_card hJ)

/-- The cube type that Proposition `prop:correlation-test` attaches to `m` and a nonsingleton
target support `J_*` (§4 `uniform_correlation_test`, `Correlation.lean`). -/
def corrTemplate (m : ℕ) (J : Finset (Fin m)) (hJ : 2 ≤ J.card) : CubeTemplate :=
  (uniform_correlation_test m J (nonempty_of_two_le_card hJ) hJ).choose

/-- The constant `C_m` of Proposition `prop:correlation-test` for `m` and `J_*`. -/
def corrConst (m : ℕ) (J : Finset (Fin m)) (hJ : 2 ≤ J.card) : ℝ :=
  (uniform_correlation_test m J (nonempty_of_two_le_card hJ) hJ).choose_spec.2.2.choose

/-- The exponent `θ = 2^{-(q_mask + d)}` of Proposition `prop:correlation-test`. -/
def corrExponent (m : ℕ) (J : Finset (Fin m)) (hJ : 2 ≤ J.card) : ℝ :=
  ((2 : ℝ) ^ (maskCount m + (corrTemplate m J hJ).d))⁻¹

theorem corrTemplate_d (m : ℕ) (J : Finset (Fin m)) (hJ : 2 ≤ J.card) :
    1 ≤ (corrTemplate m J hJ).d ∧ (corrTemplate m J hJ).d ≤ maskRowBound m - 1 :=
  ⟨(uniform_correlation_test m J (nonempty_of_two_le_card hJ) hJ).choose_spec.1,
    (uniform_correlation_test m J (nonempty_of_two_le_card hJ) hJ).choose_spec.2.1⟩

theorem corrConst_pos (m : ℕ) (J : Finset (Fin m)) (hJ : 2 ≤ J.card) :
    0 < corrConst m J hJ :=
  (uniform_correlation_test m J (nonempty_of_two_le_card hJ) hJ).choose_spec.2.2.choose_spec.1

/-! ### Chain counts -/

/-- The product masks of (eq:product-mask) as functions of `z_U = ∏_{k∈U} z_k`:
`b_U(x) = 1_{χ((∏_{k∈U} c_k) x) = c}`. -/
def countMask (A : Parameters K) (χ : ℕ → Fin r) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (c : Fin r) (U : Finset (Fin m)) (x : ℤ) : ℝ :=
  rationalColorIndicator χ c ((∏ k ∈ U, chainScale A C a N k) * (x : ℚ))

/-- The linear factors of a count: `ν_d` on singletons (the centre weights), and
`G_{B_{d(J)}, a_{d(J)}, c}` on nonsingletons. -/
def countFunctions (A : Parameters K) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    (c : Fin r) (G : Block K → ℚ → Fin r → ℤ → ℝ) (J : Finset (Fin m)) : ℤ → ℝ := by
  classical
  exact if hJ : 2 ≤ J.card then G (C.block (anchor J hJ)) (a (anchor J hJ)) c
    else if hJ1 : J.Nonempty then nu A N (C.block (J.max' hJ1)) else fun _ => 1

/-- The count `E_z U(z) ∏_d ν_d(z_d) ∏_{|J|≥2} G_{d(J)}(L_J(z))`, `z ∼ ⊗_d μ_{i_d}`, as §4's
`maskedCorrelation`.  With `G = ρ` and `a_d = b_{B_d}` it is the weighted count
(eq:weighted-count); with `G = F` or `G = S` it is the count after the replacements of 05:742–767.
-/
def chainCount (A : Parameters K) (χ : ℕ → Fin r) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (c : Fin r) (G : Block K → ℚ → Fin r → ℤ → ℝ) : ℝ :=
  maskedCorrelation A C a N (countMask A χ C a N c) (countFunctions A C a N c G)

end

end HindmanSumsProducts.Prediction
