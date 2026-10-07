import HindmanSumsProducts.Prediction.Subgroup
import HindmanSumsProducts.Prediction.PkgH
import HindmanSumsProducts.Prediction.PkgH2
import HindmanSumsProducts.Prediction.PkgH3

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
  exact calibration_from_testing_helper MS h1 χ F hF U hU
    R.pad R.prin R.prin_strictMono R.pad_lt_prin R.prin_lt_pad R.ht_eq R.X_eq
    vs hvs S Φ hS B' a ha c τ ε hτ hproj μ hμ

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
  intro U hU n r χ bs vs hbs hvs hclosed τ η hτ hτ4 hη
  classical
  obtain ⟨Cd, hsub⟩ := subgroup_inverse
  let κ : ℕ → ℕ → ℝ → ℝ := fun d J0 γ =>
    if hd : 1 ≤ d then
      if hJ0 : 0 < J0 then
        if hγ : 0 < γ then Classical.choose (hsub d J0 hd hJ0 γ hγ) else 1
      else 1
    else 1
  have hκ : ∀ d J0 γ, 0 < J0 → 0 < γ → 0 < κ d J0 γ := by
    intro d J0 γ hJ0 hγ
    by_cases hd : 1 ≤ d
    · simp [κ, hd, hJ0, hγ]
      exact (Classical.choose_spec (hsub d J0 hd hJ0 γ hγ)).1
    · simp [κ, hd]
  obtain ⟨ζ, hζ, hζcorr, J0, hJ0, hperiod, ε₀, hε₀, hε₀η, hκall⟩ :=
    parameter_choice m hm η hη Cd κ hκ
  obtain ⟨sl, Dm, hD, hOne, hlist⟩ := p_h3_master_test_data m
  obtain ⟨K, hK⟩ := energy_selection n r vs.card ε₀ hε₀
  obtain ⟨MS⟩ := HindmanSumsProducts.lem_master_scales K vs hvs sl Dm hD
  obtain ⟨F, hF⟩ := bounded_dense_models MS χ
  have hgapDiv : ∀ N (l l' : Fin K), l ≤ l' → MS.core.parameters.H N l ∣
      MS.core.parameters.H N l' := by
    intro N l l' hll
    rcases eq_or_lt_of_le hll with rfl | hlt
    · exact dvd_rfl
    · exact MS.gapStage.earlier_gaps_divide N l l' hlt
  let E : EnergySelection n (stepOf m) vs MS.core.parameters U F ε₀ :=
    Classical.choice (hK (stepOf m) vs (Nat.le_refl vs.card) MS.core.parameters hgapDiv U F hF.1)
  obtain ⟨A', R, hPad, hPrinEq⟩ :=
    restrict_parameters MS E.pad E.prin E.pad_lt_prin E.prin_lt_pad
  let Φ : (u : Fin n) → Block K → ℚ → Fin r →
      RepFamily MS.core.parameters (R.pad u) E.menu E.lip :=
    fun u B v c => { piece := (E.model u B v c).piece }
  have hΦeval (u : Fin n) (B : Block K) (v : ℚ) (c : Fin r) (N : ℕ) (y : ℤ) :
      (Φ u B v c).eval N y = (E.model u B v c).eval N y := by
    simp [Φ, RepFamily.eval, hPad]
  obtain ⟨S, hSys⟩ := models_system_of_selection (R := R) (vs := vs)
    (Fm := E.menu) (Km := E.lip) Φ
  have hUtop : (U : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hU
  have hEval01 {l : Fin K} {s : ℕ} {Fm : Menu s} {Km : ℝ≥0}
      (Ψ : RepFamily MS.core.parameters l Fm Km) (N : ℕ) (y : ℤ) :
      Ψ.eval N y ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [RepFamily.eval]
    let P := Ψ.piece N (y / (MS.core.parameters.H N l : ℤ))
      (y % (MS.core.parameters.M N : ℤ))
    have hrange := P.range (P.g ^ ((y - y % (MS.core.parameters.M N : ℤ)) /
      (MS.core.parameters.M N : ℤ)) • P.x)
    change P.eval ((y - y % (MS.core.parameters.M N : ℤ)) /
      (MS.core.parameters.M N : ℤ)) ∈ Set.Icc (0 : ℝ) 1
    simpa [OAI.SourceMenuLiteral.CosetPiece.eval] using hrange
  have hPrincipalDiag (B' : Block n) :
      PrincipalBlock R.prin B'.1 B'.1 (mapBlock R.prin R.prin_strictMono B') := by
    change (mapBlock R.prin R.prin_strictMono B').1 = R.prin B'.1 ∧
      ∀ j ∈ (mapBlock R.prin R.prin_strictMono B').2.val,
        ∃ v, v < B'.1 ∧ j = R.prin v
    constructor
    · rfl
    · intro j hj
      dsimp [mapBlock] at hj
      rcases Finset.mem_map.mp hj with ⟨v, hv, hjv⟩
      exact ⟨v, B'.2.property.2 v hv, hjv.symm⟩
  refine ⟨A', E.menu, S, ?_⟩
  intro μ hμ
  constructor
  · intro B a ha c δ hδ
    have hproj : projNorm MS.core.parameters U (R.prin B.1) (R.pad B.1) (stepOf m)
        (fun N y => F N (mapBlock R.prin R.prin_strictMono B) a c y -
          (Φ B.1 (mapBlock R.prin R.prin_strictMono B) a c).eval N y) ≤ ε₀ := by
      simpa [Φ, hPad, hPrinEq, RepFamily.eval, hΦeval] using E.coarse B.1
        (mapBlock R.prin R.prin_strictMono B)
        (by simpa [hPrinEq] using hPrincipalDiag B) a ha c
    have hcal := calibration_from_testing MS hOne χ F hF U hU R vs
      (Finset.Subset.refl vs) S Φ hSys B a ha c τ ε₀ hτ hproj μ hμ
    have hslack : 0 < η - ε₀ + δ := by linarith [hε₀η, hδ]
    have hcal' := hcal (η - ε₀ + δ) hslack
    filter_upwards [hcal'] with N hN
    linarith
  · intro B' hB' b hb c δ hδ
    have hmpos : 0 < m := by omega
    let d₀ : Fin m := ⟨0, hmpos⟩
    have hd₀le (d : Fin m) : d₀ ≤ d := by
      apply Fin.le_iff_val_le_val.mpr
      simp [d₀]
    obtain ⟨C, hCgap, hC⟩ := masterChain_of_restricted R B' hB' (by omega)
    let a : Fin m → ℚ := fun d => blockScale b (B' d)
    have ha : ∀ d, a d ∈ vs := fun d => hclosed b hb (B' d)
    let u₀ : Fin n := (B' d₀).1
    let idx (B : Block K) : Fin n :=
      if h : ∃ u, R.prin u = B.1 then Classical.choose h else u₀
    let Sm : BlockFamily K r := fun N B v c y => (E.model (idx B) B v c).eval N y
    have hidx (B : Block n) : idx (mapBlock R.prin R.prin_strictMono B) = B.1 := by
      dsimp [idx, mapBlock]
      split_ifs with h
      · apply R.prin_strictMono.injective
        exact Classical.choose_spec h
      · exact False.elim (h ⟨B.1, rfl⟩)
    have hSmap (N : ℕ) (B : Block n) (v : ℚ) (hv : v ∈ vs)
        (c : Fin r) (y : ℤ) :
        S.model N B v c y = Sm N (mapBlock R.prin R.prin_strictMono B) v c y := by
      rw [hSys N B v hv c y]
      rw [hΦeval]
      exact congrArg (fun u => (E.model u (mapBlock R.prin R.prin_strictMono B) v c).eval N y)
        (hidx B).symm
    have hSm : UnitValued Sm := by
      intro N B v c y
      exact hEval01 (E.model (idx B) B v c) N y
    have hG₁ : ∀ N B v c y, |F N B v c y| ≤ 1 + nu MS.core.parameters N B y := by
      intro N B v c y
      have hFv := hF.1 N B v c y
      have hν := nu_nonneg MS.core.parameters N B y
      have habs : |F N B v c y| ≤ 1 := abs_le.mpr ⟨by linarith [hFv.1], hFv.2⟩
      linarith
    have hG₂ : ∀ N B v c y, |Sm N B v c y| ≤ 1 + nu MS.core.parameters N B y := by
      intro N B v c y
      have hSv := hSm N B v c y
      have hν := nu_nonneg MS.core.parameters N B y
      have habs : |Sm N B v c y| ≤ 1 := abs_le.mpr ⟨by linarith [hSv.1], hSv.2⟩
      linarith
    have hG : ∀ N B v c y, |F N B v c y - Sm N B v c y| ≤
        1 + nu MS.core.parameters N B y := by
      intro N B v c y
      have hFv := hF.1 N B v c y
      have hSv := hSm N B v c y
      have hν := nu_nonneg MS.core.parameters N B y
      rw [abs_le]
      constructor <;> linarith [hFv.1, hFv.2, hSv.1, hSv.2, hν]
    let 𝒥 := {J : Finset (Fin m) // 2 ≤ J.card}
    have hcard𝒥 : Fintype.card 𝒥 = nonsingletonCount m := by
      simpa [nonsingletonCount] using (p_h3_support_card m)
    have hqpos : 0 < nonsingletonCount m := by
      have hpair : (Finset.univ.filter fun J : Finset (Fin m) => 2 ≤ J.card).Nonempty := by
        let i₀ : Fin m := ⟨0, hmpos⟩
        let i₁ : Fin m := ⟨1, by omega⟩
        have hi : i₀ ≠ i₁ := by
          intro heq
          have hv := congrArg Fin.val heq
          norm_num at hv
        refine ⟨{i₀, i₁}, ?_⟩
        simp [hi]
      have hpos := Finset.card_pos.mpr hpair
      rw [p_h3_nonsingleton_card m] at hpos
      simpa [nonsingletonCount] using hpos
    let Tsum : ℝ := ∑ J : 𝒥,
      corrConst m J.1 J.2 * (max (2 * ζ) 0) ^ corrExponent m J.1 J.2
    have hTsum : Tsum ≤ η / 2 := by
      have hterm (J : 𝒥) : corrConst m J.1 J.2 * (2 * ζ) ^ corrExponent m J.1 J.2 ≤
          η / (2 * nonsingletonCount m) :=
        (hζcorr J.1 J.2).le
      dsimp [Tsum]
      calc
        (∑ J : 𝒥, corrConst m J.1 J.2 * (max (2 * ζ) 0) ^ corrExponent m J.1 J.2)
            ≤ ∑ _J : 𝒥, η / (2 * nonsingletonCount m) := by
              apply Finset.sum_le_sum
              intro J hJ
              simpa [max_eq_left (show 0 ≤ 2 * ζ by positivity)] using hterm J
        _ = (Fintype.card 𝒥 : ℝ) * (η / (2 * nonsingletonCount m)) := by simp
        _ = η / 2 := by
          rw [hcard𝒥]
          have hq : (nonsingletonCount m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
          field_simp [hq] <;> ring
    have hchainTop : Tendsto
        (fun N => chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
          chainCount MS.core.parameters χ C a N c
            (fun B v colour y => F N B v colour y)) atTop (𝓝 0) :=
      count_rho_to_dense m MS hlist χ F hF C a ha c
    have hchainU : Tendsto
        (fun N => chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
          chainCount MS.core.parameters χ C a N c
            (fun B v colour y => F N B v colour y))
        (U : Filter ℕ) (𝓝 0) := hchainTop.mono_left hUtop
    have hmodelTop : Tendsto
        (fun N => modelIntegrandMeanUnder S (μ N) N χ c b B' -
          chainCount MS.core.parameters χ C a N c (Sm N)) atTop (𝓝 0) := by
      apply modelMean_sub_chainCount R vs S Sm hSm hSmap χ c b
        (fun B => hclosed b hb B) B' hB' C hC μ hμ
    have hmodelU : Tendsto
        (fun N => chainCount MS.core.parameters χ C a N c (Sm N) -
          modelIntegrandMeanUnder S (μ N) N χ c b B') (U : Filter ℕ) (𝓝 0) := by
      have hneg := hmodelTop.neg
      simpa using hneg.mono_left hUtop
    have hcountEqTop : ∀ᶠ N in atTop,
        weightedCountUnder A' (μ N) N χ c b B' =
          chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) :=
      weightedCount_eq_chainCount R χ c b B' hB' C hC μ hμ
    have hcountEqU := Filter.Eventually.filter_mono hUtop hcountEqTop
    have hcube : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card),
        FilterUpperBound (U : Filter ℕ)
          (fun N => |cubeAverage MS (corrTemplate m J hJ) C.gap
            (C.block (anchor J hJ)).1 J0 N (fun y =>
              F N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
                Sm N (C.block (anchor J hJ)) (a (anchor J hJ)) c y)|) (2 * ζ) := by
      intro J hJ
      let T := corrTemplate m J hJ
      have hd := corrTemplate_d m J hJ
      have hdstep := (stepOf_spec m T.d hd.2).2
      have hu₀ := C.gap
      let i : Fin K := (C.block (anchor J hJ)).1
      have hPivotLe : (B' d₀).1 ≤ (B' (anchor J hJ)).1 :=
        hB'.2.2.2.monotone (hd₀le (anchor J hJ))
      have hgap : C.gap < i := by
        dsimp [i]
        rw [hCgap, hC (anchor J hJ)]
        change R.pad (B' d₀).1 < R.prin (B' (anchor J hJ)).1
        exact lt_of_lt_of_le (R.pad_lt_prin (B' d₀).1)
          (R.prin_strictMono.monotone hPivotLe)
      have hPrincipalFine : PrincipalBlock R.prin (B' d₀).1
          (B' (anchor J hJ)).1 (mapBlock R.prin R.prin_strictMono (B' (anchor J hJ))) := by
        change (mapBlock R.prin R.prin_strictMono (B' (anchor J hJ))).1 =
            R.prin (B' (anchor J hJ)).1 ∧
          ∀ j ∈ (mapBlock R.prin R.prin_strictMono (B' (anchor J hJ))).2.val,
            ∃ v, v < (B' d₀).1 ∧ j = R.prin v
        constructor
        · rfl
        · intro j hj
          dsimp [mapBlock] at hj
          rcases Finset.mem_map.mp hj with ⟨v, hv, hjv⟩
          exact ⟨v, hB'.2.2.1 (anchor J hJ) d₀ v hv, hjv.symm⟩
      have hprojE : projNorm MS.core.parameters U (E.prin (B' (anchor J hJ)).1)
          (E.pad (B' d₀).1) (stepOf m)
          (fun N y => F N (mapBlock R.prin R.prin_strictMono (B' (anchor J hJ)))
              (a (anchor J hJ)) c y -
            (E.model (B' (anchor J hJ)).1
              (mapBlock R.prin R.prin_strictMono (B' (anchor J hJ)))
              (a (anchor J hJ)) c).eval N y) ≤ 2 * ε₀ := by
        simpa [hPrinEq] using
          E.fine (B' d₀).1 (B' (anchor J hJ)).1
            (mapBlock R.prin R.prin_strictMono (B' (anchor J hJ)))
            (hB'.2.2.2.monotone (hd₀le (anchor J hJ)))
            (by simpa [hPrinEq] using hPrincipalFine)
            (a (anchor J hJ)) (ha (anchor J hJ)) c
      have hindex : i = E.prin (B' (anchor J hJ)).1 := by
        dsimp [i]
        rw [hC (anchor J hJ)]
        simp [mapBlock, hPrinEq]
      have hgapEq : C.gap = E.pad (B' d₀).1 := by
        rw [hCgap, hPad]
      have hproj : projNorm MS.core.parameters U i C.gap (stepOf m)
          (fun N y => F N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
            Sm N (C.block (anchor J hJ)) (a (anchor J hJ)) c y) ≤ 2 * ε₀ := by
        rw [hindex, hgapEq, hC (anchor J hJ)]
        simp only [Sm]
        rw [hidx (B' (anchor J hJ))]
        exact hprojE
      have hκsmall : 2 * ε₀ < κ T.d J0 ζ := hκall T.d hd.2
      have hprojκ : projNorm MS.core.parameters U i C.gap (stepOf m)
          (fun N y => F N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
            Sm N (C.block (anchor J hJ)) (a (anchor J hJ)) c y) < κ T.d J0 ζ :=
        lt_of_le_of_lt hproj hκsmall
      let hsubT := hsub T.d J0 hd.1 hJ0 ζ hζ
      have hκval : κ T.d J0 ζ = Classical.choose hsubT := by
        simp [κ, T, hd.1, hJ0, hζ]
      have hinv := (Classical.choose_spec hsubT).2
        (stepOf m) hdstep MS T (hlist J hJ) rfl i C.gap hgap U hU
        (fun N y => F N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
          Sm N (C.block (anchor J hJ)) (a (anchor J hJ)) c y)
        (by
          intro N y
          have hFv := hF.1 N (C.block (anchor J hJ)) (a (anchor J hJ)) c y
          have hSv := hSm N (C.block (anchor J hJ)) (a (anchor J hJ)) c y
          rw [abs_le]
          constructor <;> linarith [hFv.1, hFv.2, hSv.1, hSv.2])
        (by simpa [hκval] using hprojκ)
      have hperiodJ := hperiod T.d hd.2
      intro δ' hδ'
      have hevent := hinv δ' hδ'
      filter_upwards [hevent] with N hN
      calc
        _ ≤ ζ + Cd T.d / J0 + δ' := by simpa [T, i] using hN
        _ ≤ 2 * ζ + δ' := by linarith [hperiodJ]
    have htel := chainCount_telescope m MS hlist χ C a ha c (U : Filter ℕ) hUtop
      J0 hJ0 F Sm hG₁ hG₂ hG (fun _ => 2 * ζ) hcube
    have htel' : FilterUpperBound (U : Filter ℕ)
        (fun N => |chainCount MS.core.parameters χ C a N c
          (fun B v colour y => F N B v colour y) -
          chainCount MS.core.parameters χ C a N c (Sm N)|) Tsum := by
      simpa [Tsum, max_eq_left (show 0 ≤ 2 * ζ by positivity)] using htel
    have hTelδ := htel' (δ / 2) (by positivity)
    have hRFsmall : ∀ᶠ N in (U : Filter ℕ),
        |chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
          chainCount MS.core.parameters χ C a N c
            (fun B v colour y => F N B v colour y)| ≤ δ / 4 := by
      filter_upwards [hchainU.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < δ / 4))]
        with N hN
      have hh : |(chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
          chainCount MS.core.parameters χ C a N c
            (fun B v colour y => F N B v colour y))| < δ / 4 := by
        simpa [Real.dist_eq] using hN
      exact hh.le
    have hSMsmall : ∀ᶠ N in (U : Filter ℕ),
        |chainCount MS.core.parameters χ C a N c (Sm N) -
          modelIntegrandMeanUnder S (μ N) N χ c b B'| ≤ δ / 4 := by
      filter_upwards [hmodelU.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < δ / 4))]
        with N hN
      have hh : |(chainCount MS.core.parameters χ C a N c (Sm N) -
          modelIntegrandMeanUnder S (μ N) N χ c b B')| < δ / 4 := by
        simpa [Real.dist_eq] using hN
      exact hh.le
    filter_upwards [hcountEqU, hTelδ, hRFsmall, hSMsmall] with N hEq hTel hRF hSM
    have htri : |weightedCountUnder A' (μ N) N χ c b B' -
        modelIntegrandMeanUnder S (μ N) N χ c b B'| ≤
        |chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
          chainCount MS.core.parameters χ C a N c
            (fun B v colour y => F N B v colour y)| +
        |chainCount MS.core.parameters χ C a N c
          (fun B v colour y => F N B v colour y) -
          chainCount MS.core.parameters χ C a N c (Sm N)| +
        |chainCount MS.core.parameters χ C a N c (Sm N) -
          modelIntegrandMeanUnder S (μ N) N χ c b B'| := by
      rw [hEq]
      calc
        |chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
            modelIntegrandMeanUnder S (μ N) N χ c b B'| =
          |(chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
              chainCount MS.core.parameters χ C a N c
                (fun B v colour y => F N B v colour y)) +
            (chainCount MS.core.parameters χ C a N c
              (fun B v colour y => F N B v colour y) -
              chainCount MS.core.parameters χ C a N c (Sm N)) +
            (chainCount MS.core.parameters χ C a N c (Sm N) -
              modelIntegrandMeanUnder S (μ N) N χ c b B')| := by congr 1 <;> ring
        _ ≤ _ := by
          calc
            _ ≤ |(chainCount MS.core.parameters χ C a N c
                  (rho MS.core.parameters χ N) -
                  chainCount MS.core.parameters χ C a N c
                    (fun B v colour y => F N B v colour y)) +
                (chainCount MS.core.parameters χ C a N c
                  (fun B v colour y => F N B v colour y) -
                  chainCount MS.core.parameters χ C a N c (Sm N))| +
                |chainCount MS.core.parameters χ C a N c (Sm N) -
                  modelIntegrandMeanUnder S (μ N) N χ c b B'| := abs_add_le _ _
            _ ≤ _ := by
              gcongr
              exact abs_add_le _ _
    calc
      |weightedCountUnder A' (μ N) N χ c b B' -
          modelIntegrandMeanUnder S (μ N) N χ c b B'| ≤ _ := htri
      _ ≤ δ / 4 + (Tsum + δ / 2) + δ / 4 := by linarith [hTel, hRF, hSM]
      _ ≤ η + δ := by linarith [hTsum, hδ]

/-- The Prediction Principle `pr:prediction` (`HindmanSumsProducts.PredictionPrinciple`). -/
theorem prediction_principle : PredictionPrinciple := by
  unfold PredictionPrinciple
  intro m hm
  exact ⟨stepOf m, prediction_principle_charted m hm⟩

end

end HindmanSumsProducts.Prediction
