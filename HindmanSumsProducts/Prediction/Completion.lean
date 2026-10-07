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
  have hcount : 0 < nonsingletonCount m := by
    have hpow : ∀ k : ℕ, 2 ≤ k → k + 1 < 2 ^ k := by
      intro k
      induction k with
      | zero => intro hk; omega
      | succ k ih =>
          intro hk
          by_cases hk2 : 2 ≤ k
          · have hik := ih hk2
            have hmul := Nat.mul_le_mul_left 2 hik.le
            have hleft : k + 2 ≤ 2 * (k + 1) := by omega
            rw [pow_succ]
            omega
          · have : k = 1 := by omega
            subst k
            norm_num
    unfold nonsingletonCount
    have hk := hpow m hm
    omega
  have hb : 0 < maskRowBound m := by
    have hc : 0 < maskCount m := by
      unfold maskCount
      have hp : 2 ≤ 2 ^ m := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    unfold maskRowBound
    exact Nat.mul_pos hc (pow_pos (by omega) _)
  let q : ℝ := η / (2 * nonsingletonCount m)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hsmall : ∀ᶠ z : ℝ in 𝓝 (0 : ℝ), ∀ J : {J : Finset (Fin m) // 2 ≤ J.card},
      corrConst m J.1 J.2 * (2 * z) ^ corrExponent m J.1 J.2 < q := by
    apply Filter.eventually_all.mpr
    intro J
    let θ := corrExponent m J.1 J.2
    have hθ : 0 < θ := by
      dsimp [θ, corrExponent]
      positivity
    have hpow : ContinuousAt (fun z : ℝ => (2 * z) ^ θ) 0 := by
      have hmul : ContinuousAt (fun z : ℝ => 2 * z) 0 := by fun_prop
      simpa only [Function.comp_def] using
        (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).comp_of_eq hmul (by norm_num)
    have hfun : ContinuousAt (fun z : ℝ =>
        corrConst m J.1 J.2 * (2 * z) ^ θ) 0 :=
      continuousAt_const.mul hpow
    have hval : corrConst m J.1 J.2 * (2 * (0 : ℝ)) ^ θ = 0 := by
      simp [hθ.ne']
    have hnhds : Set.Iio q ∈ 𝓝 (corrConst m J.1 J.2 * (2 * (0 : ℝ)) ^ θ) := by
      rw [hval]
      exact Iio_mem_nhds hq
    filter_upwards [hfun.eventually hnhds] with z hz
    simpa [θ] using hz
  rcases Metric.mem_nhds_iff.mp hsmall with ⟨δ, hδ, hδball⟩
  let ζ : ℝ := δ / 2
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζball : ζ ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [ζ]
    rw [abs_of_pos (by positivity)]
    linarith
  have hζall := hδball hζball
  have hζbound : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card),
      corrConst m J hJ * (2 * ζ) ^ corrExponent m J hJ < q := by
    intro J hJ
    exact hζall ⟨J, hJ⟩
  let Ctot : ℝ := ∑ d ∈ Finset.range (maskRowBound m), max (Cd d) 0
  have hCtot : 0 ≤ Ctot := by
    dsimp [Ctot]
    exact Finset.sum_nonneg fun d hd => le_max_right _ _
  obtain ⟨J0, hJ0large⟩ := exists_nat_gt (Ctot / ζ)
  have hJ0pos : 0 < J0 := by
    have hnonneg : 0 ≤ Ctot / ζ := div_nonneg hCtot hζ.le
    have hJ0R : (0 : ℝ) < J0 := lt_of_le_of_lt hnonneg hJ0large
    exact_mod_cast hJ0R
  have hJ0real : 0 < (J0 : ℝ) := by exact_mod_cast hJ0pos
  have hCratio : Ctot / J0 < ζ := by
    apply (div_lt_iff₀ hJ0real).2
    have hmul : Ctot / ζ < (J0 : ℝ) := hJ0large
    have hmul' := (div_lt_iff₀ hζ).1 hmul
    nlinarith [hmul']
  have hCbound : ∀ d, d ≤ maskRowBound m - 1 → Cd d / J0 < ζ := by
    intro d hd
    have hlt : d < maskRowBound m := by
      exact lt_of_le_of_lt hd (Nat.sub_lt hb (by norm_num))
    have hdm : d ∈ Finset.range (maskRowBound m) := by
      exact Finset.mem_range.mpr hlt
    have hterm : max (Cd d) 0 ≤ Ctot := by
      dsimp [Ctot]
      exact Finset.single_le_sum (fun x hx => le_max_right (Cd x) 0) hdm
    have hCd : Cd d ≤ Ctot := (le_max_left _ _).trans hterm
    have hdiv : Cd d / J0 ≤ Ctot / J0 := div_le_div_of_nonneg_right hCd hJ0real.le
    exact hdiv.trans_lt hCratio
  let κtot : ℝ := ∑ d ∈ Finset.range (maskRowBound m), (κ d J0 ζ)⁻¹
  have hκtot : 0 < κtot := by
    dsimp [κtot]
    apply Finset.sum_pos (fun d hd => inv_pos.mpr (hκ d J0 ζ hJ0pos hζ))
    exact ⟨0, Finset.mem_range.mpr hb⟩
  have hκbound : ∀ d, d ≤ maskRowBound m - 1 → κtot⁻¹ ≤ κ d J0 ζ := by
    intro d hd
    have hlt : d < maskRowBound m := by
      exact lt_of_le_of_lt hd (Nat.sub_lt hb (by norm_num))
    have hdm : d ∈ Finset.range (maskRowBound m) := by
      exact Finset.mem_range.mpr hlt
    have hterm : (κ d J0 ζ)⁻¹ ≤ κtot := by
      dsimp [κtot]
      exact Finset.single_le_sum (fun x hx => inv_nonneg.mpr (le_of_lt (hκ x J0 ζ hJ0pos hζ))) hdm
    have hkpos := hκ d J0 ζ hJ0pos hζ
    have hmul : 1 ≤ κtot * κ d J0 ζ := by
      calc
        1 = (κ d J0 ζ)⁻¹ * κ d J0 ζ := by rw [inv_mul_cancel₀ (ne_of_gt hkpos)]
        _ ≤ κtot * κ d J0 ζ := mul_le_mul_of_nonneg_right hterm hkpos.le
    have hle : (1 : ℝ) / κtot ≤ κ d J0 ζ :=
      (div_le_iff₀ hκtot).2 (by nlinarith [hmul])
    simpa [one_div] using hle
  let ε := min (η / 2) (κtot⁻¹ / 4)
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hεη : ε < η := by
    have : ε ≤ η / 2 := min_le_left _ _
    linarith
  have hεκ : ∀ d, d ≤ maskRowBound m - 1 → 2 * ε < κ d J0 ζ := by
    intro d hd
    have hk := hκbound d hd
    have he : ε ≤ κtot⁻¹ / 4 := min_le_right _ _
    calc
      2 * ε ≤ 2 * (κtot⁻¹ / 4) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ < κtot⁻¹ := by nlinarith [inv_pos.mpr hκtot]
      _ ≤ κ d J0 ζ := hk
  refine ⟨ζ, hζ, ?_, J0, hJ0pos, hCbound, ε, hεpos, hεη, hεκ⟩
  intro J hJ
  simpa [q] using hζbound J hJ

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
  let A := MS.core.parameters
  have hprin : StrictMono prin := fun u v huv => (h2 u v huv).trans (h1 v)
  let e : Fin n ↪ Fin K := ⟨prin, hprin.injective⟩
  have hmapBlock (B : Block n) :
      (mapBlock prin hprin B).set = B.set.map e := by
    simp [mapBlock, OAI.SourceBlocks.Block.set, e]
  have hprev (u : Fin n) (N : ℕ) :
      OAI.SourceAdmissible.previous (fun v => A.X N (prin v)) u ≤
        OAI.SourceAdmissible.previous (A.X N) (pad u) := by
    let s := Finset.univ.filter (fun v : Fin n => v < u)
    let t := Finset.univ.filter (fun i : Fin K => i < pad u)
    have hsubset : s.map e ⊆ t := by
      intro i hi
      rcases Finset.mem_map.mp hi with ⟨v, hv, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact h2 v u (Finset.mem_filter.mp hv).2
    change (∏ v ∈ s, A.X N (prin v)) ≤ ∏ i ∈ t, A.X N i
    calc
      (∏ v ∈ s, A.X N (prin v)) = ∏ i ∈ s.map e, A.X N i :=
        (Finset.prod_map s e (fun i => A.X N i)).symm
      _ ≤ ∏ i ∈ t, A.X N i :=
        Finset.prod_le_prod_of_subset_of_one_le hsubset (by
          intro i hi hni
          exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (A.Xpos N i)))
  have hheight (N : ℕ) (S : Finset (Fin n)) :
      OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (fun u => A.ht N (prin u)) S =
        OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (S.map e) := by
    exact height_map_embedding e (A.ht N) S
  let A' : Parameters n := {
    M := A.M
    ht := fun N u => A.ht N (prin u)
    H := fun N u => A.H N (pad u)
    X := fun N u => A.X N (prin u)
    Mpos := A.Mpos
    htpos := fun N u => A.htpos N (prin u)
    Hpos := fun N u => A.Hpos N (pad u)
    Xpow := fun N u => A.Xpow N (prin u)
    Msmooth := A.Msmooth
    htsmooth := fun N u => A.htsmooth N (prin u)
    Mdiv := A.Mdiv
    htdiv := fun N u => A.htdiv N (prin u)
    singleton_bound := fun N u => A.singleton_bound N (prin u)
    block_bound := by
      intro N B
      change OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (fun u => A.ht N (prin u)) B.set ≤ A.M N
      rw [hheight, ← hmapBlock]
      exact A.block_bound N (mapBlock prin hprin B)
    ratio := by
      intro N B S hS
      have hAdd := added_map_strictMono prin hprin hS
      let BM := mapBlock prin hprin B
      obtain ⟨d, hd⟩ := A.ratio N BM (S.map e) hAdd
      refine ⟨d, ?_⟩
      calc
        OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (fun u => A.ht N (prin u)) S =
          OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height (A.ht N) (S.map e) :=
            hheight N S
        _ = OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
              (A.ht N) BM.set * ((primorial (N + 1) : ℤ) ^ (N + 1) * d) := hd
        _ = OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
              (fun u => A.ht N (prin u)) B.set *
                ((primorial (N + 1) : ℤ) ^ (N + 1) * d) := by
              rw [hheight N B.set, ← hmapBlock B]
    Hdiv := by
      intro N u
      exact A.Hdiv N (pad u)
    Hdom := by
      intro u
      let Pnew : ℕ → ℕ := fun N =>
        OAI.SourceAdmissible.previous (fun v => A.X N (prin v)) u
      let Pold : ℕ → ℕ := fun N =>
        OAI.SourceAdmissible.previous (A.X N) (pad u)
      have hden (N : ℕ) :
          OAI.AdmissibleMicrocellBoundary.earlierScale A.M Pnew N ≤
            OAI.AdmissibleMicrocellBoundary.earlierScale A.M Pold N := by
        unfold OAI.AdmissibleMicrocellBoundary.earlierScale Pnew Pold
        have hp : (OAI.SourceAdmissible.previous (fun v => A.X N (prin v)) u : ℝ) ≤
            OAI.SourceAdmissible.previous (A.X N) (pad u) := Nat.cast_le.mpr (hprev u N)
        linarith
      have hT (N : ℕ) : 0 < OAI.AdmissibleMicrocellBoundary.earlierScale A.M Pnew N :=
        lt_of_lt_of_le (by norm_num) (OAI.AdmissibleMicrocellBoundary.scale_one A.M Pnew N)
      change OAI.MicrocellScale.Dominates (fun N => (A.H N (pad u) : ℝ))
        (fun N => OAI.AdmissibleMicrocellBoundary.earlierScale A.M Pnew N)
      exact dominates_of_le_denominator (A.Hdom (pad u)) hT hden
        (Filter.Eventually.of_forall fun N => by positivity)
    Xdom := by
      intro u
      have hHle (N : ℕ) : (A.H N (pad u) : ℝ) ≤ (A.H N (prin u) : ℝ) := by
        have hdiv : A.H N (pad u) ∣ A.H N (prin u) :=
          MS.gapStage.earlier_gaps_divide N (pad u) (prin u) (h1 u)
        exact_mod_cast Nat.le_of_dvd (A.Hpos N (prin u)) hdiv
      have hXnonneg : ∀ᶠ N in atTop, 0 ≤ Real.log (A.X N (prin u) : ℝ) := by
        filter_upwards [(A.Xtendsto (prin u)).eventually_ge_atTop 1] with N hN
        exact Real.log_nonneg (by exact_mod_cast hN)
      have hT (N : ℕ) : 0 < (A.H N (pad u) : ℝ) := by
        exact_mod_cast A.Hpos N (pad u)
      change OAI.MicrocellScale.Dominates (fun N => Real.log (A.X N (prin u) : ℝ))
        (fun N => (A.H N (pad u) : ℝ))
      exact dominates_of_le_denominator (A.Xdom (prin u)) hT hHle hXnonneg }
  let R : Restriction A A' := {
    pad := pad
    prin := prin
    pad_lt_prin := h1
    prin_lt_pad := h2
    M_eq := by intro N; rfl
    ht_eq := by intro N u; rfl
    H_eq := by intro N u; rfl
    X_eq := by intro N u; rfl }
  exact ⟨A', R, rfl, rfl⟩

/-- A chain on `Fin n` is a master chain on the principal indices with gap the padding index
immediately before its first pivot (05:389–391, 750–752). -/
theorem masterChain_of_restricted {n m : ℕ} {A : Parameters K} {A' : Parameters n}
    (R : Restriction A A') (B' : Fin m → Block n) (hB' : IsBlockChain B') (hm : 0 < m) :
    ∃ C : MasterChain K m, C.gap = R.pad (B' ⟨0, hm⟩).1 ∧
      ∀ d, C.block d = mapBlock R.prin R.prin_strictMono (B' d) := by
  let u₀ : Fin m := ⟨0, hm⟩
  have hchain : IsChain
      (fun d => (mapBlock R.prin R.prin_strictMono (B' d)).2.val)
      (fun d => (mapBlock R.prin R.prin_strictMono (B' d)).1) := by
    change IsChain (fun d => (B' d).2.val) (fun d => (B' d).1) at hB'
    rcases hB' with ⟨hne, htails, htailPivot, hpivots⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d
      obtain ⟨j, hj⟩ := hne d
      exact ⟨R.prin j, Finset.mem_map.mpr ⟨j, hj, rfl⟩⟩
    · intro d d' hdd a ha b hb
      rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_map.mp hb with ⟨b', hb', rfl⟩
      exact R.prin_strictMono (htails d d' hdd a' ha' b' hb')
    · intro d d' a ha
      rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
      exact R.prin_strictMono (htailPivot d d' a' ha')
    · intro d d' hdd
      exact R.prin_strictMono (hpivots hdd)
  let C : MasterChain K m :=
    { gap := R.pad (B' u₀).1
      block := fun d => mapBlock R.prin R.prin_strictMono (B' d)
      tails_before_gap := by
        intro d j hj
        rcases Finset.mem_map.mp hj with ⟨j', hj', rfl⟩
        exact R.prin_lt_pad j' (B' u₀).1 (by
          change IsChain (fun d => (B' d).2.val) (fun d => (B' d).1) at hB'
          exact hB'.2.2.1 d u₀ j' hj')
      tails_ordered := by
        intro u d hud a ha b hb
        exact hchain.2.1 u d hud a ha b hb
      pivots_after_gap := by
        intro d
        have hle : (B' u₀).1 ≤ (B' d).1 := by
          change IsChain (fun d => (B' d).2.val) (fun d => (B' d).1) at hB'
          exact hB'.2.2.2.monotone (Nat.zero_le d)
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact (R.pad_lt_prin (B' u₀).1).trans
            ((R.prin_lt_pad (B' u₀).1 (B' d).1 hlt).trans (R.pad_lt_prin (B' d).1))
        · have heqidx : u₀ = d := by
            have hstrict : StrictMono (fun d => (B' d).1) := by
              change IsChain (fun d => (B' d).2.val) (fun d => (B' d).1) at hB'
              exact hB'.2.2.2
            exact hstrict.injective heq
          subst d
          exact R.pad_lt_prin (B' u₀).1
      pivots_ordered := by
        intro u d hud
        exact R.prin_strictMono (by
          change IsChain (fun d => (B' d).2.val) (fun d => (B' d).1) at hB'
          exact hB'.2.2.2 hud) }
  exact ⟨C, rfl, fun _ => rfl⟩

/-- The selected coarse models assemble into one charted `ModelsSystem` for the restricted
parameters (Definition `def:piecewise-model` with `H_u = R_{k_u}`, 05:717–719): pieces of the
model of `B'` are those of the selected representing family of `mapBlock B'` at gap `pad B'.1`. -/
theorem models_system_of_selection {n s : ℕ} {A : Parameters K} {A' : Parameters n}
    (R : Restriction A A') (vs : Finset ℚ) {Fm : Menu s} {Km : ℝ≥0}
    (Φ : (u : Fin n) → Block K → ℚ → Fin r → RepFamily A (R.pad u) Fm Km) :
    ∃ S : ModelsSystem A' vs r Fm, ∀ N (B' : Block n) (v : ℚ), v ∈ vs → ∀ (c : Fin r) (y : ℤ),
      S.model N B' v c y = (Φ B'.1 (mapBlock R.prin R.prin_strictMono B') v c).eval N y := by
  refine ⟨{
    model := fun N B' v c y =>
      (Φ B'.1 (mapBlock R.prin R.prin_strictMono B') v c).eval N y
    K := Km
    piece := fun N B' v hv c j l =>
      (Φ B'.1 (mapBlock R.prin R.prin_strictMono B') v c).piece N j l
    represents := ?_ }, ?_⟩
  · intro N B' v hv c y
    simp only [R.H_eq, R.M_eq, RepFamily.eval]
  · intro N B' v hv c y
    rfl

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
  exact chainCount_telescope_helper m MS hlist χ C a ha c L hL J0 hJ0 G₁ G₂ hG₁ hG₂ hG bound hcube

/-- The first consequence of Proposition `prop:dense-model` (05:250–261, 05:742–748): in a
chain count with a valid gap, all nonsingleton colour weights `ρ` can be replaced by the dense
models `F` with total error `o(1)`. -/
theorem count_rho_to_dense (m : ℕ) (MS : MasterScales K As sl Dm)
    (hlist : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card), Allowed Dm (corrTemplate m J hJ))
    (χ : ℕ → Fin r) (F : BlockFamily K r) (hF : IsDenseModel MS χ F)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ k, a k ∈ As) (c : Fin r) :
    Tendsto (fun N => chainCount MS.core.parameters χ C a N c (rho MS.core.parameters χ N) -
      chainCount MS.core.parameters χ C a N c (F N)) atTop (𝓝 0) := by
  let A := MS.core.parameters
  let G₁ : BlockFamily K r := fun N B a c y => rho A χ N B a c y
  have hρ (N : ℕ) (B : Block K) (b : ℚ) (c : Fin r) (y : ℤ) :
      0 ≤ rho A χ N B b c y ∧ rho A χ N B b c y ≤ nu A N B y := by
    have hν := pkgH_nu_nonneg A N B y
    have hcolor := rationalColorIndicator_mem_Icc χ c
      (((height (A.ht N) B.set : ℚ) * b * (y : ℚ)))
    change 0 ≤ nu A N B y * rationalColorIndicator χ c
        (((height (A.ht N) B.set : ℚ) * b * (y : ℚ))) ∧
      nu A N B y * rationalColorIndicator χ c
        (((height (A.ht N) B.set : ℚ) * b * (y : ℚ))) ≤ nu A N B y
    constructor
    · exact mul_nonneg hν hcolor.1
    · calc
        nu A N B y * rationalColorIndicator χ c
            (((height (A.ht N) B.set : ℚ) * b * (y : ℚ))) ≤ nu A N B y * 1 :=
          mul_le_mul_of_nonneg_left hcolor.2 hν
        _ = nu A N B y := by ring
  have hdiff (N : ℕ) (B : Block K) (b : ℚ) (c : Fin r) (y : ℤ) :
      |rho A χ N B b c y - F N B b c y| ≤ 1 + nu A N B y := by
    have hρ' := hρ N B b c y
    have hF' := hF.1 N B b c y
    have hν := pkgH_nu_nonneg A N B y
    rw [abs_le]
    constructor
    · have : -F N B b c y ≥ -1 := by linarith [hF'.2]
      linarith [hρ'.1, hν]
    · linarith [hρ'.2, hF'.1]
  have hG₁ : ∀ N B b c y, |G₁ N B b c y| ≤ 1 + nu A N B y := by
    intro N B b c y
    rw [abs_of_nonneg (hρ N B b c y).1]
    linarith [(hρ N B b c y).2]
  have hG₂ : ∀ N B b c y, |F N B b c y| ≤ 1 + nu A N B y := by
    intro N B b c y
    have hν := pkgH_nu_nonneg A N B y
    have hF' := hF.1 N B b c y
    rw [abs_le]
    constructor
    · linarith [hν, hF'.1]
    · linarith [hν, hF'.2]
  have hcube : ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card),
      FilterUpperBound atTop (fun N => |cubeAverage MS (corrTemplate m J hJ) C.gap
        (C.block (anchor J hJ)).1 1 N (fun y =>
          G₁ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
            F N (C.block (anchor J hJ)) (a (anchor J hJ)) c y)|) 0 := by
    intro J hJ ε hε
    have htest := hF.2 (C.block (anchor J hJ)) (a (anchor J hJ))
      (ha (anchor J hJ)) c C.gap (by
        constructor
        · intro j hj
          exact C.tails_before_gap (anchor J hJ) j hj
        · exact C.pivots_after_gap (anchor J hJ))
      (corrTemplate m J hJ) (hlist J hJ) 1 (by norm_num) ε hε
    filter_upwards [htest] with N hN
    let gfun : ℤ → ℝ := fun y =>
      G₁ N (C.block (anchor J hJ)) (a (anchor J hJ)) c y -
        F N (C.block (anchor J hJ)) (a (anchor J hJ)) c y
    let I : DualInput MS (C.block (anchor J hJ)) (corrTemplate m J hJ) N :=
      ⟨fun _ => 1, fun _ _ => gfun,
        fun _ => by norm_num,
        fun _ _ y => hdiff N (C.block (anchor J hJ)) (a (anchor J hJ)) c y⟩
    have hpair := cubeAverage_eq_dualPairing MS (C.block (anchor J hJ))
      (corrTemplate m J hJ) C.gap 1 N gfun
      (fun y => hdiff N (C.block (anchor J hJ)) (a (anchor J hJ)) c y)
    rw [hpair]
    simpa [I, gfun] using hN I
  have htel := chainCount_telescope m MS hlist χ C a ha c atTop le_rfl 1 (by norm_num)
    G₁ F hG₁ hG₂ (fun N B b c y => hdiff N B b c y) (fun _ => 0) hcube
  have hsum : (∑ J : {J : Finset (Fin m) // 2 ≤ J.card},
      corrConst m J.1 J.2 * (max ((fun _ : Finset (Fin m) => 0) J.1) 0) ^
        corrExponent m J.1 J.2) = 0 := by
    apply Finset.sum_eq_zero
    intro J hJ
    simp only [max_self]
    rw [Real.zero_rpow (ne_of_gt (by
      dsimp [corrExponent]
      positivity))]
    ring
  have hbound : FilterUpperBound atTop
      (fun N => |chainCount A χ C a N c (G₁ N) - chainCount A χ C a N c (F N)|) 0 := by
    rw [← hsum]
    exact htel
  exact filterUpperBound_abs_tendsto_zero hbound

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
  classical
  have hXA : ∀ᶠ N in atTop, ∀ j, 4 * primorial (N + 1) ≤ A.X N j := by
    have hall : ∀ᶠ N in atTop, ∀ j ∈ (Finset.univ : Finset (Fin K)),
        4 * primorial (N + 1) ≤ A.X N j := by
      apply (eventually_all_finset (Finset.univ : Finset (Fin K))).2
      intro j hj
      exact A.eventual_X j
    filter_upwards [hall] with N hN
    intro j
    exact hN j (Finset.mem_univ j)
  have hXA' : ∀ᶠ N in atTop, ∀ i, 4 * primorial (N + 1) ≤ A'.X N i := by
    have hall : ∀ᶠ N in atTop, ∀ i ∈ (Finset.univ : Finset (Fin n)),
        4 * primorial (N + 1) ≤ A'.X N i := by
      apply (eventually_all_finset (Finset.univ : Finset (Fin n))).2
      intro i hi
      exact A'.eventual_X i
    filter_upwards [hall] with N hN
    intro i
    exact hN i (Finset.mem_univ i)
  filter_upwards [hXA, hXA'] with N hXA hXA'
  let a : Fin m → ℚ := fun d => blockScale b (B' d)
  let e : Fin n ↪ Fin K := ⟨R.prin, R.prin_strictMono.injective⟩
  have hmapBlock (B : Block n) :
      (mapBlock R.prin R.prin_strictMono B).set = B.set.map e := by
    simp [mapBlock, OAI.SourceBlocks.Block.set, e]
  have hht : A'.ht N = fun i => A.ht N (R.prin i) := by
    funext i
    exact R.ht_eq N i
  have hheight (d : Fin m) :
      OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A'.ht N) (B' d).set =
        OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (C.block d).set := by
    rw [hht, hC d, hmapBlock]
    exact height_map_embedding e (A.ht N) (B' d).set
  have hscale : ∀ d,
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A'.ht N) (B' d).set : ℚ) * blockScale b (B' d) = chainScale A C a N d := by
    intro d
    rw [hheight d]
    rfl
  have hTail : ∀ d, (C.block d).2.val =
      (B' d).2.val.map ⟨R.prin, R.prin_strictMono.injective⟩ := by
    intro d
    rw [hC d]
    rfl
  have hXroot (d : Fin m) : A.X N (C.block d).1 = A'.X N (B' d).1 := by
    rw [hC d]
    exact (R.X_eq N (B' d).1).symm
  have hXfun : (fun d => A'.X N (B' d).1) = (fun d => A.X N (C.block d).1) :=
    funext fun d => (hXroot d).symm
  have hD :
      OAI.ProductExposureLaw.outsideDomain (fun d => A'.X N (B' d).1)
          (primorial (N + 1)) =
        OAI.ProductExposureLaw.outsideDomain (fun d => A.X N (C.block d).1)
          (primorial (N + 1)) := by
    rw [hXfun]
  let F : (Fin m → ℤ) → ℝ := fun z =>
    (∏ U ∈ Finset.univ.filter Finset.Nonempty,
      countMask A χ C a N c U (∏ k ∈ U, z k)) *
    ∏ J ∈ Finset.univ.filter Finset.Nonempty,
      atQ (countFunctions A C a N c (rho A χ N) J)
        (chainForm (chainScale A C a N) J z)
  have hchain : chainCount A χ C a N c (rho A χ N) =
      ∑ t ∈ OAI.ProductExposureLaw.outsideDomain
        (fun d => A.X N (C.block d).1) (primorial (N + 1)),
        (∏ d, harmonicNatLaw (A.X N (C.block d).1) (primorial (N + 1)) (t d)) *
          F (fun d => (t d : ℤ)) := by
    simpa [chainCount, maskedCorrelation, F] using
      (pivotMass_tsum_eq_nat_sum A C N F)
  have hweights (t : Fin m → ℕ) :
      (∏ d, harmonicNatLaw (A'.X N (B' d).1) (primorial (N + 1)) (t d)) =
        ∏ d, harmonicNatLaw (A.X N (C.block d).1) (primorial (N + 1)) (t d) := by
    apply Finset.prod_congr rfl
    intro d hd
    rw [← hXroot d]
  have hterms :
      (∑ t ∈ OAI.ProductExposureLaw.outsideDomain
          (fun d => A'.X N (B' d).1) (primorial (N + 1)),
        (∏ d, harmonicNatLaw (A'.X N (B' d).1) (primorial (N + 1)) (t d)) *
          weightedCountIntegrandUnder A' (A'.law N hXA') N χ c b B' t) =
      ∑ t ∈ OAI.ProductExposureLaw.outsideDomain
          (fun d => A.X N (C.block d).1) (primorial (N + 1)),
        (∏ d, harmonicNatLaw (A.X N (C.block d).1) (primorial (N + 1)) (t d)) *
          F (fun d => (t d : ℤ)) := by
    rw [hD]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hweights t]
    have hterm := weightedCountIntegrandUnder_eq_maskedCorrelationTerm
      A A' N hXA hXA' R.prin R.prin_strictMono.injective (fun i => R.X_eq N i)
      C B' b χ c a hscale hTail t
    rw [hterm]
  calc
    weightedCountUnder A' (μ N) N χ c b B' =
        weightedCountUnder A' (A'.law N hXA') N χ c b B' := by
      rw [hμ N hXA']
    _ =
        ∑ t ∈ OAI.ProductExposureLaw.outsideDomain
          (fun d => A'.X N (B' d).1) (primorial (N + 1)),
          (∏ d, harmonicNatLaw (A'.X N (B' d).1) (primorial (N + 1)) (t d)) *
            weightedCountIntegrandUnder A' (A'.law N hXA') N χ c b B' t := by
      unfold weightedCountUnder
      exact integral_pivotMarginals_eq_sum A' N hXA' B'
        (weightedCountIntegrandUnder A' (A'.law N hXA') N χ c b B')
    _ = chainCount A χ C a N c (rho A χ N) := hterms.trans hchain.symm

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
  classical
  obtain ⟨Aplus, hXplus, hXplusEq⟩ := parameters_allRawCutoffs_eventually_eq A'
  have hXAevent : ∀ᶠ N in atTop, ∀ j,
      4 * primorial (N + 1) ≤ A.X N j := by
    have hall : ∀ᶠ N in atTop, ∀ j ∈ (Finset.univ : Finset (Fin K)),
        4 * primorial (N + 1) ≤ A.X N j := by
      apply (eventually_all_finset (Finset.univ : Finset (Fin K))).2
      intro j hj
      exact A.eventual_X j
    filter_upwards [hall] with N hN
    intro j
    exact hN j (Finset.mem_univ j)
  have hXA'event : ∀ᶠ N in atTop, ∀ i,
      4 * primorial (N + 1) ≤ A'.X N i := by
    have hall : ∀ᶠ N in atTop, ∀ i ∈ (Finset.univ : Finset (Fin n)),
        4 * primorial (N + 1) ≤ A'.X N i := by
      apply (eventually_all_finset (Finset.univ : Finset (Fin n))).2
      intro i hi
      exact A'.eventual_X i
    filter_upwards [hall] with N hN
    intro i
    exact hN i (Finset.mem_univ i)
  let a : Fin m → ℚ := fun d => blockScale b (B' d)
  let V : ℕ → ℕ := fun _ => 1
  have hV : ∀ N, 1 ≤ V N := by intro N; simp [V]
  let productErrorTarget : Fin m → ℕ → ℝ := fun d N =>
    2 + (primorial (N + 1) : ℝ) +
      ((∏ j ∈ (B' d).2.val, (Aplus.X N j) ^ 2 : ℕ) : ℝ) + (V N : ℝ)
  have hdisj : ∀ i j, i ≠ j → Disjoint (B' i).set (B' j).set := by
    change IsChain (fun d => (B' d).2.val) (fun d => (B' d).1) at hB'
    rcases hB' with ⟨hne, htails, htailPivot, hpivots⟩
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hxi' : x = (B' i).1 ∨ x ∈ (B' i).2.val := by
      simpa [OAI.SourceBlocks.Block.set] using hxi
    have hxj' : x = (B' j).1 ∨ x ∈ (B' j).2.val := by
      simpa [OAI.SourceBlocks.Block.set] using hxj
    rcases hxi' with hxiP | hxiT <;> rcases hxj' with hxjP | hxjT
    · exact hij (hpivots.injective (hxiP.symm.trans hxjP))
    · subst x
      exact (Fin.lt_irrefl _ (htailPivot j i _ hxjT))
    · subst x
      exact (Fin.lt_irrefl _ (htailPivot i j _ hxiT))
    · rcases lt_trichotomy i j with hij' | hij' | hji'
      · exact (Fin.lt_irrefl _ (htails i j hij' x hxiT x hxjT))
      · exact hij hij'
      · exact (Fin.lt_irrefl _ (htails j i hji' x hxjT x hxiT))
  have hDom : ∀ d, OAI.MicrocellScale.Dominates
      (fun N => Real.log (Aplus.X N (B' d).1 : ℝ)) (productErrorTarget d) := by
    intro d
    let tailSet : Finset (Fin n) := (B' d).2.val
    let earlier : Finset (Fin n) := Finset.univ.filter (fun j => j < (B' d).1)
    let prevR : ℕ → ℝ := fun N => ∏ j ∈ earlier, (Aplus.X N j : ℝ)
    let Sdom : ℕ → ℝ := fun N => OAI.AdmissibleMicrocellBoundary.earlierScale Aplus.M
      (fun N => OAI.SourceAdmissible.previous (Aplus.X N) (B' d).1) N
    have htailSub : tailSet ⊆ earlier := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (B' d).2.property.2 j hj⟩
    have hprevCast (N : ℕ) :
        (OAI.SourceAdmissible.previous (Aplus.X N) (B' d).1 : ℝ) = prevR N := by
      simp [prevR, earlier, OAI.SourceAdmissible.previous, Nat.cast_prod]
    have hSval (N : ℕ) :
        Sdom N = 2 + (Aplus.M N : ℝ) + prevR N := by
      simp [Sdom, OAI.AdmissibleMicrocellBoundary.earlierScale, hprevCast]
    have htailProd (N : ℕ) :
        (∏ j ∈ tailSet, (Aplus.X N j : ℝ)) ≤ prevR N := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ htailSub
      · intro j hj
        positivity
      · intro j hj hjnot
        exact_mod_cast (Nat.succ_le_of_lt (Aplus.Xpos N j))
    have htailSq (N : ℕ) :
        (∏ j ∈ tailSet, (Aplus.X N j : ℝ) ^ 2) ≤ (prevR N) ^ 2 := by
      rw [Finset.prod_pow]
      nlinarith [htailProd N, show 0 ≤ ∏ j ∈ tailSet, (Aplus.X N j : ℝ) from by positivity]
    have htargetSq (N : ℕ) : productErrorTarget d N ≤ (Sdom N) ^ 2 := by
      have hW : (primorial (N + 1) : ℝ) ≤ (Aplus.M N : ℝ) := by
        exact_mod_cast Aplus.Wle N
      have hM : (1 : ℝ) ≤ (Aplus.M N : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (Aplus.Mpos N))
      have hprevNat : 0 < OAI.SourceAdmissible.previous (Aplus.X N) (B' d).1 := by
        unfold OAI.SourceAdmissible.previous
        apply Finset.prod_pos
        intro j hj
        exact Aplus.Xpos N j
      have hprev : (1 : ℝ) ≤ prevR N := by
        have hn : 1 ≤ OAI.SourceAdmissible.previous (Aplus.X N) (B' d).1 :=
          Nat.succ_le_of_lt hprevNat
        have hnR : (1 : ℝ) ≤
            (OAI.SourceAdmissible.previous (Aplus.X N) (B' d).1 : ℝ) := by
          exact_mod_cast hn
        rw [hprevCast N] at hnR
        exact hnR
      rw [hSval]
      have htailSqCast :
          ((∏ j ∈ tailSet, (Aplus.X N j) ^ 2 : ℕ) : ℝ) ≤ (prevR N) ^ 2 := by
        simpa [Nat.cast_prod, Finset.prod_pow] using htailSq N
      change (2 : ℝ) + (primorial (N + 1) : ℝ) +
          ((∏ j ∈ (B' d).2.val, (Aplus.X N j) ^ 2 : ℕ) : ℝ) + (V N : ℝ) ≤
        (2 + (Aplus.M N : ℝ) + prevR N) ^ 2
      calc
        _ ≤ 3 + (Aplus.M N : ℝ) + (prevR N) ^ 2 := by
          have htailSqCast' :
              ((∏ j ∈ (B' d).2.val, (Aplus.X N j) ^ 2 : ℕ) : ℝ) ≤ (prevR N) ^ 2 := by
            simpa [tailSet] using htailSqCast
          have hVn : (V N : ℝ) = 1 := by simp [V]
          rw [hVn]
          have hsum : (primorial (N + 1) : ℝ) +
              ((∏ j ∈ (B' d).2.val, (Aplus.X N j) ^ 2 : ℕ) : ℝ) ≤
                (Aplus.M N : ℝ) + (prevR N) ^ 2 := add_le_add hW htailSqCast'
          calc
            2 + (primorial (N + 1) : ℝ) +
                ((∏ j ∈ (B' d).2.val, (Aplus.X N j) ^ 2 : ℕ) : ℝ) + 1 =
                3 + ((primorial (N + 1) : ℝ) +
                  ((∏ j ∈ (B' d).2.val, (Aplus.X N j) ^ 2 : ℕ) : ℝ)) := by ring
            _ ≤ 3 + ((Aplus.M N : ℝ) + (prevR N) ^ 2) := by
              have hsum3 := add_le_add_right hsum (3 : ℝ)
              nlinarith [hsum3]
            _ = 3 + (Aplus.M N : ℝ) + (prevR N) ^ 2 := by ring
        _ ≤ (2 + (Aplus.M N : ℝ) + prevR N) ^ 2 := by
          have hMpow : (Aplus.M N : ℝ) ≤ (Aplus.M N : ℝ) ^ 2 := by
            nlinarith [sq_nonneg ((Aplus.M N : ℝ) - 1), hM]
          calc
            3 + (Aplus.M N : ℝ) + (prevR N) ^ 2 ≤
                3 + (Aplus.M N : ℝ) ^ 2 + (prevR N) ^ 2 := by nlinarith [hMpow]
            _ ≤ (2 + (Aplus.M N : ℝ) + prevR N) ^ 2 := by
              nlinarith [hM, hprev]
    have hSpos (N : ℕ) : 0 < Sdom N := by rw [hSval]; positivity
    have hHlarge : ∀ᶠ N in atTop,
        1 ≤ (Aplus.H N (B' d).1 : ℝ) / (Sdom N) ^ (2 : ℝ) := by
      simpa [Sdom] using
        (Aplus.Hdom (B' d).1 2 (by norm_num)).eventually_ge_atTop 1
    have htargetH : ∀ᶠ N in atTop,
        productErrorTarget d N ≤ (Aplus.H N (B' d).1 : ℝ) := by
      filter_upwards [hHlarge] with N hN
      have hSH : (Sdom N) ^ 2 ≤ (Aplus.H N (B' d).1 : ℝ) := by
        have hpow : (Sdom N) ^ (2 : ℝ) = (Sdom N) ^ 2 := Real.rpow_natCast _ _
        have hmul := (le_div_iff₀ (Real.rpow_pos_of_pos (hSpos N) 2)).mp hN
        rw [← hpow]
        simpa only [one_mul] using hmul
      exact (htargetSq N).trans hSH
    have hlog : ∀ᶠ N in atTop,
        0 ≤ Real.log (Aplus.X N (B' d).1 : ℝ) := by
      filter_upwards [(Aplus.Xtendsto (B' d).1).eventually_ge_atTop 1] with N hN
      exact Real.log_nonneg (by exact_mod_cast hN)
    have htargetPos : ∀ᶠ N in atTop, 0 < productErrorTarget d N :=
      Filter.Eventually.of_forall fun N => by positivity
    exact dominates_of_eventually_le_denominator (Aplus.Xdom (B' d).1)
      hlog htargetPos htargetH
  have hcor := cor_product_law Aplus B' hdisj hXplus V hV hDom
  have herr : Tendsto (fun N => arithmeticL1
      (parameterJointBlockProductMass Aplus N B' (hXplus N))
      (weightedPivotTupleMass Aplus N B')) atTop (𝓝 0) := by
    have h := hcor 1 (by norm_num)
    simpa [SuperPolynomialSmall, V] using h
  have hbound : FilterUpperBound atTop
      (fun N => |modelIntegrandMeanUnder S (μ N) N χ c b B' -
        chainCount A χ C a N c (Sm N)|) 0 := by
    have hboundEventually : ∀ᶠ N in atTop,
        |modelIntegrandMeanUnder S (μ N) N χ c b B' -
          chainCount A χ C a N c (Sm N)| ≤
            arithmeticL1 (parameterJointBlockProductMass Aplus N B' (hXplus N))
              (weightedPivotTupleMass Aplus N B') := by
      filter_upwards [hXAevent, hXA'event, hXplusEq] with N hXA hXA' hXplusEqN
      have hmuplus : μ N = Aplus.law N (hXplus N) := by
        calc
          μ N = A'.law N hXA' := hμ N hXA'
          _ = Aplus.law N (hXplus N) := by
            simp [OAI.SourceAdmissible.Parameters.law, hXplusEqN]
      let e : Fin n ↪ Fin K := ⟨R.prin, R.prin_strictMono.injective⟩
      have hmapBlock (B0 : Block n) :
          (mapBlock R.prin R.prin_strictMono B0).set = B0.set.map e := by
        simp [mapBlock, OAI.SourceBlocks.Block.set, e]
      have hht : A'.ht N = fun i => A.ht N (R.prin i) := by
        funext i
        exact R.ht_eq N i
      have hheight (d : Fin m) :
          OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
              (A'.ht N) (B' d).set =
            OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
              (A.ht N) (C.block d).set := by
        rw [hht, hC d, hmapBlock]
        exact height_map_embedding e (A.ht N) (B' d).set
      have hscale : ∀ d,
          (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A'.ht N) (B' d).set : ℚ) * blockScale b (B' d) = chainScale A C a N d := by
        intro d
        rw [hheight d]
        rfl
      have hTail : ∀ d, (C.block d).2.val =
          (B' d).2.val.map ⟨R.prin, R.prin_strictMono.injective⟩ := by
        intro d
        rw [hC d]
        rfl
      have hXroot (d : Fin m) : A.X N (C.block d).1 = A'.X N (B' d).1 := by
        rw [hC d]
        exact (R.X_eq N (B' d).1).symm
      have hXeqPlus (i : Fin n) : Aplus.X N i = A.X N (R.prin i) := by
        rw [hXplusEqN]
        exact R.X_eq N i
      have hnu (d : Fin m) (y : ℤ) :
          nu Aplus N (B' d) y = nu A N (C.block d) y := by
        calc
          nu Aplus N (B' d) y =
              divisorWeightUnder (Aplus.law N (hXplus N)) (B' d) y :=
                (divisorWeightUnder_eq_nu Aplus N (hXplus N) (B' d) y).symm
          _ = nu A N (C.block d) y :=
            divisorWeightUnder_principal A Aplus N R.prin
              R.prin_strictMono.injective hXeqPlus hXA (hXplus N)
              (B' d) (C.block d) (hTail d) y
      have hnuHarmonic (d : Fin m) (y : ℤ) :
          weightedPivotMass Aplus N (B' d) y =
            nu A N (C.block d) y *
              harmonicLaw (A.X N (C.block d).1) (primorial (N + 1)) y := by
        calc
          weightedPivotMass Aplus N (B' d) y =
              nu Aplus N (B' d) y *
                harmonicLaw (Aplus.X N (B' d).1) (primorial (N + 1)) y := rfl
          _ = nu A N (C.block d) y *
                harmonicLaw (A.X N (C.block d).1) (primorial (N + 1)) y := by
            rw [hnu d y, hXplusEqN, hXroot d]
      have hweightTuple (z : Fin m → ℤ) :
          weightedPivotTupleMass Aplus N B' z =
            pivotMass A C N z * ∏ d, nu A N (C.block d) (z d) := by
        calc
          weightedPivotTupleMass Aplus N B' z =
              ∏ d, (nu A N (C.block d) (z d) *
                harmonicLaw (A.X N (C.block d).1) (primorial (N + 1)) (z d)) := by
                  unfold weightedPivotTupleMass
                  apply Finset.prod_congr rfl
                  intro d hd
                  exact hnuHarmonic d (z d)
          _ = (∏ d, nu A N (C.block d) (z d)) *
                ∏ d, harmonicLaw (A.X N (C.block d).1) (primorial (N + 1)) (z d) :=
                  Finset.prod_mul_distrib
          _ = pivotMass A C N z * ∏ d, nu A N (C.block d) (z d) := by
                unfold pivotMass
                ring
      let coeff' : Fin m → ℚ := fun d =>
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A'.ht N) (B' d).set : ℚ) * blockScale b (B' d)
      let coeff : Fin m → ℚ := fun d => chainScale A C a N d
      let zNat (t : Fin n → ℕ) : Fin m → ℕ :=
        fun d => ∏ j ∈ (B' d).set, t j
      let zInt (t : Fin n → ℕ) : Fin m → ℤ := blockProductTuple B' t
      have hcoeff (d : Fin m) : coeff' d = coeff d := hscale d
      have hblockProd (t : Fin n → ℕ) (d : Fin m) :
          zNat t d = tailValue (B' d) t * t (B' d).1 := by
        have hpivotNot : (B' d).1 ∉ (B' d).2.val := by
          intro hj
          exact (Fin.lt_irrefl _) ((B' d).2.property.2 _ hj)
        simp [zNat, tailValue, OAI.SourceBlocks.Block.set, hpivotNot, mul_comm]
      have hArg (t : Fin n → ℕ) (U : Finset (Fin m)) :
          (∏ k ∈ U, coeff' k * (zNat t k : ℚ)) =
            (∏ k ∈ U, coeff k) * ((∏ k ∈ U, zInt t k : ℤ) : ℚ) := by
        calc
          (∏ k ∈ U, coeff' k * (zNat t k : ℚ)) =
              (∏ k ∈ U, coeff' k) * ∏ k ∈ U, (zNat t k : ℚ) := Finset.prod_mul_distrib
          _ = (∏ k ∈ U, coeff k) * ∏ k ∈ U, (zInt t k : ℚ) := by
              have hcoeffProd : (∏ k ∈ U, coeff' k) = ∏ k ∈ U, coeff k := by
                apply Finset.prod_congr rfl
                intro k hk
                exact hcoeff k
              have hzProd : (∏ k ∈ U, (zNat t k : ℚ)) =
                  ∏ k ∈ U, (zInt t k : ℚ) := by
                apply Finset.prod_congr rfl
                intro k hk
                simp [zNat, zInt, blockProductTuple]
              rw [hcoeffProd, hzProd]
          _ = (∏ k ∈ U, coeff k) * ((∏ k ∈ U, zInt t k : ℤ) : ℚ) := by
              congr 1
              simp [Int.cast_prod]
      have hmask (t : Fin n → ℕ) : productMask χ c coeff' (zNat t) =
          ∏ U ∈ Finset.univ.filter Finset.Nonempty,
            countMask A χ C a N c U (∏ k ∈ U, zInt t k) := by
        rw [productMask_eq_filteredProduct]
        apply Finset.prod_congr rfl
        intro U hU
        unfold countMask
        rw [hArg t U]
      let maskFactor : (Fin m → ℤ) → ℝ := fun z =>
        ∏ U ∈ Finset.univ.filter Finset.Nonempty,
          countMask A χ C a N c U (∏ k ∈ U, z k)
      let allFactor : Finset (Fin m) → (Fin m → ℤ) → ℝ := fun J z =>
        atQ (countFunctions A C a N c (Sm N) J) (chainForm coeff J z)
      let modelFactor : NonsingletonSubsets m → (Fin m → ℤ) → ℝ := fun J z =>
        allFactor J.val z
      let g : (Fin m → ℤ) → ℝ := fun z => maskFactor z * ∏ J, modelFactor J z
      have hform (t : Fin n → ℕ) (J : NonsingletonSubsets m)
          (hJ : J.val.Nonempty) :
          sumForm coeff' J.val hJ (zNat t) = chainForm coeff J.val (zInt t) := by
        simp [sumForm, chainForm, hJ, coeff', coeff, hcoeff, zNat, zInt,
          blockProductTuple]
      have hmodelEq (J : NonsingletonSubsets m) (hJ : J.val.Nonempty)
          (t : Fin n → ℕ) :
          rationalModelValue S N (B' (J.val.max' hJ))
            (blockScale b (B' (J.val.max' hJ))) c
            (sumForm coeff' J.val hJ (zNat t)) =
          modelFactor J (zInt t) := by
        let d := J.val.max' hJ
        have hmax : anchor J.val J.property = d := by
          change J.val.max' (nonempty_of_two_le_card J.property) = J.val.max' hJ
          exact congrArg J.val.max' (Subsingleton.elim _ _)
        have hcount : countFunctions A C a N c (Sm N) J.val =
            Sm N (C.block d) (a d) c := by
          have hcard : 2 ≤ J.val.card := J.property
          unfold countFunctions
          rw [dif_pos hcard, hmax]
        have hmodel (y : ℤ) : S.model N (B' d) (blockScale b (B' d)) c y =
            Sm N (C.block d) (a d) c y := by
          calc
            S.model N (B' d) (blockScale b (B' d)) c y =
                Sm N (mapBlock R.prin R.prin_strictMono (B' d))
                  (blockScale b (B' d)) c y := hS N (B' d) _ (hb (B' d)) c y
            _ = Sm N (C.block d) (a d) c y := by rw [hC d]
        rw [rationalModelValue_eq_atQ]
        rw [hform t J hJ]
        dsimp [modelFactor, allFactor]
        rw [hcount]
        congr 1
        funext y
        exact hmodel y
      have hModelPoint (t : Fin n → ℕ) :
          modelIntegrand S N χ c b B' t = g (zInt t) := by
        have hzt : (fun d => tailValue (B' d) t * t (B' d).1) = zNat t := by
          funext d
          exact (hblockProd t d).symm
        calc
          modelIntegrand S N χ c b B' t =
              productMask χ c coeff' (fun d => tailValue (B' d) t * t (B' d).1) *
                (∏ J : NonsingletonSubsets m, by
                  let hJ : J.val.Nonempty := Finset.card_pos.mp
                    (lt_of_lt_of_le (by decide) J.property)
                  let d := J.val.max' hJ
                  exact rationalModelValue S N (B' d) (blockScale b (B' d)) c
                    (sumForm coeff' J.val hJ (fun d => tailValue (B' d) t * t (B' d).1))) := by
              unfold modelIntegrand
              rfl
          _ = productMask χ c coeff' (zNat t) *
                (∏ J : NonsingletonSubsets m, by
                  let hJ : J.val.Nonempty := Finset.card_pos.mp
                    (lt_of_lt_of_le (by decide) J.property)
                  let d := J.val.max' hJ
                  exact rationalModelValue S N (B' d) (blockScale b (B' d)) c
                    (sumForm coeff' J.val hJ (zNat t))) := by
              rw [hzt]
          _ = g (zInt t) := by
              rw [hmask t]
              dsimp [g]
              congr 1
              apply Finset.prod_congr rfl
              intro J hJ
              exact hmodelEq J (Finset.card_pos.mp
                (lt_of_lt_of_le (by decide) J.property)) t
      have hmaskBound (z : Fin m → ℤ) : maskFactor z ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · unfold maskFactor
          exact Finset.prod_nonneg fun U hU =>
            (rationalColorIndicator_mem_Icc χ c _).1
        · unfold maskFactor
          exact Finset.prod_le_one₀
            (fun U hU => (rationalColorIndicator_mem_Icc χ c _).1)
            (fun U hU => (rationalColorIndicator_mem_Icc χ c _).2)
      have hmodelFactorBound (J : NonsingletonSubsets m) (z : Fin m → ℤ) :
          modelFactor J z ∈ Set.Icc (0 : ℝ) 1 := by
        let hJ : J.val.Nonempty := Finset.card_pos.mp
          (lt_of_lt_of_le (by decide) J.property)
        let d := J.val.max' hJ
        have hcard : 2 ≤ J.val.card := J.property
        have hmax : anchor J.val hcard = d := by
          change J.val.max' (nonempty_of_two_le_card hcard) = J.val.max' hJ
          exact congrArg J.val.max' (Subsingleton.elim _ _)
        have hcount : countFunctions A C a N c (Sm N) J.val =
            Sm N (C.block d) (a d) c := by
          unfold countFunctions
          rw [dif_pos hcard, hmax]
        dsimp [modelFactor, allFactor]
        rw [hcount]
        exact atQ_mem_Icc_of_mem
          (fun y => Sm N (C.block d) (a d) c y) (chainForm coeff J.val z)
          (fun y => hSm N (C.block d) (a d) c y)
      have hmodelProdBound (z : Fin m → ℤ) :
          (∏ J, modelFactor J z) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · apply Finset.prod_nonneg
          intro J hJ
          exact (hmodelFactorBound J z).1
        · exact Finset.prod_le_one₀
            (fun J hJ => (hmodelFactorBound J z).1)
            (fun J hJ => (hmodelFactorBound J z).2)
      have hgBound (z : Fin m → ℤ) : g z ∈ Set.Icc (0 : ℝ) 1 := by
        have hm := hmaskBound z
        have hp := hmodelProdBound z
        constructor
        · dsimp [g]
          exact mul_nonneg hm.1 hp.1
        · dsimp [g]
          exact mul_le_one₀ hm.2 hp.1 hp.2
      have hgAbs (z : Fin m → ℤ) : |g z| ≤ 1 := by
        have h := hgBound z
        have hlow : -1 ≤ g z := by
          calc
            (-1 : ℝ) ≤ 0 := by norm_num
            _ ≤ g z := h.1
        exact abs_le.mpr ⟨hlow, h.2⟩
      have hIntegrable : Integrable g
          (Measure.map (blockProductTuple B') (Aplus.law N (hXplus N))) := by
        refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1 ?_
        exact Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact hgAbs z
      have hmean : modelIntegrandMeanUnder S (μ N) N χ c b B' =
          ∑' z, parameterJointBlockProductMass Aplus N B' (hXplus N) z * g z := by
        rw [hmuplus]
        unfold modelIntegrandMeanUnder
        calc
          ∫ t, modelIntegrand S N χ c b B' t ∂Aplus.law N (hXplus N) =
              ∫ t, g (blockProductTuple B' t) ∂Aplus.law N (hXplus N) := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall hModelPoint
          _ = ∑' z, parameterJointBlockProductMass Aplus N B' (hXplus N) z * g z := by
                calc
                  _ = ∑' z, (Measure.map (blockProductTuple B')
                        (Aplus.law N (hXplus N))).real {z} * g z :=
                      integral_eq_tsum_map_real_singleton _ _ (measurable_of_countable _)
                        g hIntegrable
                  _ = ∑' z, parameterJointBlockProductMass Aplus N B' (hXplus N) z * g z := by
                      apply tsum_congr
                      intro z
                      rw [← parameterJointBlockProductMass_eq_map_real]
      have hcolorZero : rationalColorIndicator χ c 0 = 0 := by
        unfold rationalColorIndicator rationalColorHit
        simp
      have hpoint (z : Fin m → ℤ) :
          pivotMass A C N z *
            (maskFactor z * ∏ J ∈ Finset.univ.filter Finset.Nonempty,
              allFactor J z) = weightedPivotTupleMass Aplus N B' z * g z := by
        by_cases hcoeff : ∀ d, chainScale A C a N d ≠ 0
        · have hsingleton (d : Fin m) : allFactor {d} z =
              nu A N (C.block d) (z d) := by
            have hJ : ({d} : Finset (Fin m)).Nonempty :=
              ⟨d, Finset.mem_singleton_self d⟩
            have hmax : ({d} : Finset (Fin m)).max' hJ = d := by simp
            have hformSing : chainForm (chainScale A C a N) ({d} : Finset (Fin m)) z =
                (z d : ℚ) := by
              unfold chainForm
              rw [dif_pos hJ, hmax]
              simp [hcoeff d]
            dsimp [allFactor]
            rw [hformSing]
            simp [countFunctions, atQ]
          have hsplit := prod_nonempty_eq_singleton_nonsingleton (allFactor · z)
          have hsingleprod : (∏ d, allFactor {d} z) =
              ∏ d, nu A N (C.block d) (z d) := by
            apply Finset.prod_congr rfl
            intro d hd
            exact hsingleton d
          rw [hsplit, hsingleprod, hweightTuple z]
          dsimp [g, maskFactor, allFactor]
          ring
        · push_neg at hcoeff
          obtain ⟨d, hd⟩ := hcoeff
          have hmaskZero : maskFactor z = 0 := by
            unfold maskFactor
            let U : Finset (Fin m) := {d}
            have hU : U ∈ Finset.univ.filter Finset.Nonempty := by
              simp [U]
            apply Finset.prod_eq_zero hU
            simp [U, countMask, hd, hcolorZero]
          rw [hmaskZero]
          simp [g, hmaskZero]
      have hchain : chainCount A χ C a N c (Sm N) =
          ∑' z, weightedPivotTupleMass Aplus N B' z * g z := by
        unfold chainCount maskedCorrelation
        apply tsum_congr
        intro z
        exact hpoint z
      have hjointSupport := parameterJointBlockProductMass_support_finite
        Aplus N B' (hXplus N)
      have hpivotSupport := weightedPivotTupleMass_support_finite Aplus N B'
      have hsumBound := abs_tsum_mul_sub_le_tsum_abs_diff
        (parameterJointBlockProductMass Aplus N B' (hXplus N))
        (weightedPivotTupleMass Aplus N B') g hjointSupport hpivotSupport hgAbs
      calc
        |modelIntegrandMeanUnder S (μ N) N χ c b B' -
            chainCount A χ C a N c (Sm N)| =
          |(∑' z, parameterJointBlockProductMass Aplus N B' (hXplus N) z * g z) -
            ∑' z, weightedPivotTupleMass Aplus N B' z * g z| := by
              rw [hmean, hchain]
        _ ≤ arithmeticL1 (parameterJointBlockProductMass Aplus N B' (hXplus N))
            (weightedPivotTupleMass Aplus N B') := by
              simpa [arithmeticL1] using hsumBound
    have herrSmall : ∀ ε > 0, ∀ᶠ N in atTop,
        arithmeticL1 (parameterJointBlockProductMass Aplus N B' (hXplus N))
          (weightedPivotTupleMass Aplus N B') ≤ ε := by
      intro ε hε
      filter_upwards [herr.eventually (Iio_mem_nhds hε)] with N hN
      exact le_of_lt hN
    intro ε hε
    filter_upwards [herrSmall ε hε, hboundEventually] with N hsmall hboundN
    exact hboundN.trans (by simpa using hsmall)
  exact filterUpperBound_abs_tendsto_zero hbound

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
