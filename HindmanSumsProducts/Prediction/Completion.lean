import HindmanSumsProducts.Prediction.Subgroup
import HindmanSumsProducts.Prediction.PkgH

/-!
# Completion of the Prediction Principle (§5.4, `05_prediction.tex` 685–783)

The output is `prediction_principle : HindmanSumsProducts.PredictionPrinciple` (`Framework.lean`),
proved from `prediction_principle_charted`, whose body is `PredictionPrinciple`'s body with
`s := stepOf m`.  The sub-lemmas record the order of choices
`m → s(m)`; `n r χ 𝓑 𝒜 τ η` → `ζ` → `J₀` → `κ(d, J₀, ζ)` → `ε` → master count `K` (energy
selection) → master scales → dense models → selection → restriction to the principal indices.
-/

open scoped BigOperators NNReal Topology
open Filter MeasureTheory

namespace HindmanSumsProducts.Prediction

noncomputable section

variable {K sl r : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

/-! ### Parameters -/

/-- `q_m = 2^m − m − 1`, the number of nonsingleton factors in each count (05:690–691). -/
def nonsingletonCount (m : ℕ) : ℕ := 2 ^ m - m - 1

/-- The order of choices before the master indices (05:694–712): `ζ` with
`C_m(2ζ)^θ < η/(2q_m)` for every target support (finitely many constants and exponents), then
`J₀` with every periodization term `C_d/J₀ < ζ` (`d ≤ K_m − 1`), then `ε` with `0 < ε < η` and
`2ε < κ(d, J₀, ζ)` for every `d ≤ K_m − 1`.  `κ` is any positive function (in the proof, the one of
`subgroup_inverse`). -/
theorem parameter_choice (m : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) (Cd : ℕ → ℝ)
    (κ : ℕ → ℕ → ℝ → ℝ) (hκ : ∀ d J0 γ, 0 < J0 → 0 < γ → 0 < κ d J0 γ) :
    ∃ ζ : ℝ, 0 < ζ ∧
      (∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card),
        corrConst m J hJ * (2 * ζ) ^ corrExponent m J hJ < η / (2 * nonsingletonCount m)) ∧
      ∃ J0 : ℕ, 0 < J0 ∧ (∀ d, d ≤ maskRowBound m - 1 → Cd d / J0 < ζ) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ∀ d, d ≤ maskRowBound m - 1 → 2 * ε < κ d J0 ζ := by
  sorry

/-! ### Restriction to the principal indices (05:713–719) -/

/-- Admissible parameters `A'` on `Fin n` obtained from master parameters `A` by keeping the
principal indices `j_u = prin u` and taking `H_u = R_{k_u}` at the padding indices `pad u`. -/
structure Restriction {n : ℕ} (A : Parameters K) (A' : Parameters n) where
  pad : Fin n → Fin K
  prin : Fin n → Fin K
  pad_lt_prin : ∀ u, pad u < prin u
  prin_lt_pad : ∀ u v, u < v → prin u < pad v
  M_eq : ∀ N, A'.M N = A.M N
  ht_eq : ∀ N u, A'.ht N u = A.ht N (prin u)
  H_eq : ∀ N u, A'.H N u = A.H N (pad u)
  X_eq : ∀ N u, A'.X N u = A.X N (prin u)

theorem Restriction.prin_strictMono {n : ℕ} {A : Parameters K} {A' : Parameters n}
    (R : Restriction A A') : StrictMono R.prin :=
  fun _ _ h => (R.prin_lt_pad _ _ h).trans (R.pad_lt_prin _)

/-- The master block `j(T) ∪ {j_i}` of a block `T ∪ {i}` on the principal indices. -/
def mapBlock {n : ℕ} (prin : Fin n → Fin K) (hprin : StrictMono prin) (B : Block n) :
    Block K :=
  ⟨prin B.1, ⟨B.2.val.map ⟨prin, hprin.injective⟩, B.2.property.1.map, by
    intro j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
    exact hprin (B.2.property.2 j' hj')⟩⟩

/-- Lemma `lem:master-scales` and the padding gaps give admissible parameters on the principal
indices (05:713–719; blueprint P.8b): smoothness, `W^w`-divisibility and the block bounds are
inherited, `ratio` because `prin` preserves the adding-block relation, `M ∣ R_{k_u}`, `R_{k_u}`
dominates powers of `2 + M + ∏_{v<u} X_{j_v}` (a factor of `V_{k_u}`), and `log X_{j_u}` dominates
powers of `R_{j_u} ≥ R_{k_u}`. -/
theorem restrict_parameters {n : ℕ} (MS : MasterScales K As sl Dm) (pad prin : Fin n → Fin K)
    (h1 : ∀ u, pad u < prin u) (h2 : ∀ u v, u < v → prin u < pad v) :
    ∃ (A' : Parameters n) (R : Restriction MS.core.parameters A'), R.pad = pad ∧ R.prin = prin := by
  sorry

/-- A chain on `Fin n` is a master chain on the principal indices with gap the padding index
immediately before its first pivot (05:389–391, 750–752). -/
theorem masterChain_of_restricted {n m : ℕ} {A : Parameters K} {A' : Parameters n}
    (R : Restriction A A') (B' : Fin m → Block n) (hB' : IsBlockChain B') (hm : 0 < m) :
    ∃ C : MasterChain K m, C.gap = R.pad (B' ⟨0, hm⟩).1 ∧
      ∀ d, C.block d = mapBlock R.prin R.prin_strictMono (B' d) := by
  sorry

/-- The selected coarse models assemble into one charted `ModelsSystem` for the restricted
parameters (Definition `def:piecewise-model` with `H_u = R_{k_u}`, 05:717–719): pieces of the
model of `B'` are those of the selected representing family of `mapBlock B'` at gap `pad B'.1`. -/
theorem models_system_of_selection {n s : ℕ} {A : Parameters K} {A' : Parameters n}
    (R : Restriction A A') (vs : Finset ℚ) {Fm : Menu s} {Km : ℝ≥0}
    (Φ : (u : Fin n) → Block K → ℚ → Fin r → RepFamily A (R.pad u) Fm Km) :
    ∃ S : ModelsSystem A' vs r Fm, ∀ N (B' : Block n) (v : ℚ), v ∈ vs → ∀ (c : Fin r) (y : ℤ),
      S.model N B' v c y = (Φ B'.1 (mapBlock R.prin R.prin_strictMono B') v c).eval N y := by
  sorry

/-! ### Counts -/

/-- Telescoping through the nonsingleton factors with Proposition `prop:correlation-test`
(05:250–261 and 05:750–763): if two families `G₁, G₂` and their difference are bounded by
`1 + ν` and, for every nonsingleton `J`, the cube of type `corrTemplate m J` of
`G₁ − G₂` at the anchor block is at most `b_J` in the limit along `L ≤ atTop`, then
`lim_L |count(G₁) − count(G₂)| ≤ ∑_J C_J b_J^{θ_J}`.  The master list must contain every
`corrTemplate m J`'s tests. -/
theorem chainCount_telescope (m : ℕ) (MS : MasterScales K As sl Dm)
    (hlist : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card), Allowed Dm (corrTemplate m J hJ))
    (χ : ℕ → Fin r) (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ k, a k ∈ As) (c : Fin r)
    (L : Filter ℕ) (hL : L ≤ atTop) (J0 : ℕ) (hJ0 : 0 < J0) (G₁ G₂ : BlockFamily K r)
    (hG₁ : ∀ N B b c y, |G₁ N B b c y| ≤ 1 + nu MS.core.parameters N B y)
    (hG₂ : ∀ N B b c y, |G₂ N B b c y| ≤ 1 + nu MS.core.parameters N B y)
    (hG : ∀ N B b c y, |G₁ N B b c y - G₂ N B b c y| ≤ 1 + nu MS.core.parameters N B y)
    (bound : Finset (Fin m) → ℝ)
    (hcube : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card),
      FilterUpperBound L (fun N => |cubeAverage MS (corrTemplate m J hJ) C.gap
        (C.block (anchor J hJ)).1 J0 N (fun y =>
          G₁ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
            G₂ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y)|) (bound J)) :
    FilterUpperBound L
      (fun N => |chainCount MS.core.parameters χ C a N c (G₁ N) -
        chainCount MS.core.parameters χ C a N c (G₂ N)|)
      (∑ J : {J : Finset (Fin m) // 2 ≤ J.card},
        corrConst m J.1 J.2 * (max (bound J.1) 0) ^ corrExponent m J.1 J.2) := by
  sorry

/-- The first consequence of Proposition `prop:dense-model` (05:250–261, 05:742–748): in a
chain count with a valid gap, all nonsingleton colour weights `ρ` can be replaced by the dense
models `F` with total error `o(1)`. -/
theorem count_rho_to_dense (m : ℕ) (MS : MasterScales K As sl Dm)
    (hlist : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card), Allowed Dm (corrTemplate m J hJ))
    (χ : ℕ → Fin r) (F : BlockFamily K r) (hF : IsDenseModel MS χ F)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ k, a k ∈ As) (c : Fin r) :
    Tendsto (fun N => chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
      chainCount MS.core.parameters χ C a N c (F N)) atTop (𝓝 0) := by
  sorry

/-- The weighted count of the Principle (eq:weighted-count, measure form of `Framework.lean`)
for a chain on the principal indices equals the master chain count with `G = ρ` and
`a_d = b_{B_d}`, for all large `N` (blueprint X.4: `Parameters.law` integrals are the §3 weight
sums; the tail and pivot marginals of the restricted law are those of the master law). -/
theorem weightedCount_eq_chainCount {n m : ℕ} {A : Parameters K} {A' : Parameters n}
    (R : Restriction A A') (χ : ℕ → Fin r) (c : Fin r) (b : FrameworkScale n)
    (B' : Fin m → Block n) (hB' : IsBlockChain B') (C : MasterChain K m)
    (hC : ∀ d, C.block d = mapBlock R.prin R.prin_strictMono (B' d))
    (μ : ℕ → Measure (Fin n → ℕ))
    (hμ : ∀ N (hX : ∀ i, 4 * primorial (N + 1) ≤ A'.X N i), μ N = A'.law N hX) :
    ∀ᶠ N in atTop, weightedCountUnder A' (μ N) N χ c b B' =
      chainCount A χ C (fun d => blockScale b (B' d)) N c (rho A χ N) := by
  sorry

/-- The final product-law step (05:768–775, Corollary `cor:product-law`, blueprint P.8f with
X.4): the model integrand mean of the Principle equals, up to `o(1)`, the master chain count with
`G = S` (all factors except the centre weights are bounded by `1`; the chain blocks are
disjoint). -/
theorem modelMean_sub_chainCount {n m s : ℕ} {A : Parameters K} {A' : Parameters n}
    (R : Restriction A A') (vs : Finset ℚ) {Fm : Menu s} (S : ModelsSystem A' vs r Fm)
    (Sm : BlockFamily K r) (hSm : UnitValued Sm)
    (hS : ∀ N (B' : Block n) (v : ℚ), v ∈ vs → ∀ (c : Fin r) (y : ℤ),
      S.model N B' v c y = Sm N (mapBlock R.prin R.prin_strictMono B') v c y)
    (χ : ℕ → Fin r) (c : Fin r) (b : FrameworkScale n) (hb : ∀ B : Block n, blockScale b B ∈ vs)
    (B' : Fin m → Block n) (hB' : IsBlockChain B') (C : MasterChain K m)
    (hC : ∀ d, C.block d = mapBlock R.prin R.prin_strictMono (B' d))
    (μ : ℕ → Measure (Fin n → ℕ))
    (hμ : ∀ N (hX : ∀ i, 4 * primorial (N + 1) ≤ A'.X N i), μ N = A'.law N hX) :
    Tendsto (fun N => modelIntegrandMeanUnder S (μ N) N χ c b B' -
      chainCount A χ C (fun d => blockScale b (B' d)) N c (Sm N)) atTop (𝓝 0) := by
  sorry

/-! ### Calibration -/

/-- Calibration (eq:prediction-calibration), 05:721–740: for a block `B'` of the restricted
parameters whose model is the selected representing family `Φ` at the coarse gap `k_u`, with
`‖P_{j_u,k_u}(F − S)‖ ≤ ε` for the dense model `F`,
`lim_𝒰 P(χ(h_B a t_B) = c, S(t_B) ≤ 2τ) ≤ 3τ + ε`.  Steps: a Lipschitz `ψ` (`1` on `[0,2τ]`,
`0` on `[3τ,1]`); bounded distribution replacement (`cor_product_law`); nilsequence testing for
`ψ(S)` (`RepFamily.comp_exists`); `⟨F − S, ψ(S)⟩ ≤ ‖P(F − S)‖`; `⟨S, ψ(S)⟩ ≤ 3τ`. -/
theorem calibration_from_testing {n s : ℕ} (MS : MasterScales K As sl Dm)
    (h1 : (1 : IntegerPolynomial sl) ∈ Dm) (χ : ℕ → Fin r) (F : BlockFamily K r)
    (hF : IsDenseModel MS χ F) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    {A' : Parameters n} (R : Restriction MS.core.parameters A') (vs : Finset ℚ) (hvs : vs ⊆ As)
    {Fm : Menu s} {Km : ℝ≥0} (S : ModelsSystem A' vs r Fm)
    (Φ : (u : Fin n) → Block K → ℚ → Fin r → RepFamily MS.core.parameters (R.pad u) Fm Km)
    (hS : ∀ N (B' : Block n) (v : ℚ), v ∈ vs → ∀ (c : Fin r) (y : ℤ),
      S.model N B' v c y = (Φ B'.1 (mapBlock R.prin R.prin_strictMono B') v c).eval N y)
    (B' : Block n) (a : ℚ) (ha : a ∈ vs) (c : Fin r) (τ ε : ℝ) (hτ : 0 < τ)
    (hproj : projNorm MS.core.parameters U (R.prin B'.1) (R.pad B'.1) s
      (fun N y => F N (mapBlock R.prin R.prin_strictMono B') a c y -
        (Φ B'.1 (mapBlock R.prin R.prin_strictMono B') a c).eval N y) ≤ ε)
    (μ : ℕ → Measure (Fin n → ℕ))
    (hμ : ∀ N (hX : ∀ i, 4 * primorial (N + 1) ≤ A'.X N i), μ N = A'.law N hX) :
    UltrafilterUpperBound U (fun N => calibrationProbabilityUnder (μ N) S χ N B' a c τ)
      (3 * τ + ε) := by
  sorry

/-! ### The Prediction Principle -/

/-- Principle `pr:prediction` (05:687–783) with `s = s(m) = stepOf m`, in the exact form of the
body of `HindmanSumsProducts.PredictionPrinciple` (charted menus, `Framework.lean`).

Assembly (P.8g): fix `U, n, r, χ, 𝓑, 𝒜 = vs, τ, η`.  `parameter_choice` with `C` of
`periodization`/`subgroup_inverse` and `κ` of `subgroup_inverse` gives `ζ, J₀, ε`;
`energy_selection n r |𝒜| ε` gives `K`; `lem_master_scales K 𝒜` with the master list
`{1} ∪ ⋃_J rename(corrTemplate m J).tests` in `sl = max_J (corrTemplate m J).q` slots;
`bounded_dense_models`; `energy_selection` for `F` (nested gaps from
`MasterScaleGapStage.earlier_gaps_divide`); `restrict_parameters`, `models_system_of_selection`.
Calibration: `calibration_from_testing` with `coarse`.  Counting: for a chain `B'`,
`masterChain_of_restricted`, `weightedCount_eq_chainCount`, `count_rho_to_dense`, then
`chainCount_telescope` with `G₁ = F`, `G₂ = S` and `bound = 2ζ` from `subgroup_inverse`
(`fine` gives `‖P(F − S)‖ ≤ 2ε < κ`), then `modelMean_sub_chainCount`. -/
theorem prediction_principle_charted (m : ℕ) (hm : 2 ≤ m) :
    ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.cofinite →
    ∀ n r (χ : ℕ → Fin r) (bs : Finset (FrameworkScale n)) (vs : Finset ℚ),
      (∀ b ∈ bs, ∀ j, 0 < b j) → (∀ v ∈ vs, 0 < v) → ScaleListsClosed bs vs →
      ∀ τ η : ℝ, 0 < τ → τ < 1/4 → 0 < η →
      ∃ (A : OAI.SourceAdmissible.Parameters n) (F : OAI.SourceChartedMenu.Menu (stepOf m))
        (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F),
        ∀ (μ : ℕ → Measure (Fin n → ℕ)),
          (∀ N (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i), μ N = A.law N hX) →
          (∀ B : FrameworkBlock n, ∀ a : ℚ, a ∈ vs → ∀ c : Fin r,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ N in (U : Filter ℕ),
                calibrationProbabilityUnder (μ N) S χ N B a c τ ≤ 3*τ+η+ε) ∧
          (∀ (B : Fin m → FrameworkBlock n), IsBlockChain B →
            ∀ b : FrameworkScale n, b ∈ bs → ∀ c : Fin r,
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ N in (U : Filter ℕ),
                  |weightedCountUnder A (μ N) N χ c b B -
                      modelIntegrandMeanUnder S (μ N) N χ c b B| ≤ η+ε) := by
  sorry

/-- The Prediction Principle `pr:prediction` (`HindmanSumsProducts.PredictionPrinciple`). -/
theorem prediction_principle : PredictionPrinciple := by
  unfold PredictionPrinciple
  intro m hm
  exact ⟨stepOf m, prediction_principle_charted m hm⟩

end

end HindmanSumsProducts.Prediction
