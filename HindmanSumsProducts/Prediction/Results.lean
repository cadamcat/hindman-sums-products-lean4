import HindmanSumsProducts.Prediction.Outside
import HindmanSumsProducts.CubeCornerCharted
import HindmanSumsProducts.Prediction.PkgB
import HindmanSumsProducts.Prediction.PkgC
import HindmanSumsProducts.Prediction.PkgD

/-!
# Dual-test pseudorandomness, bounded dense models, nilsequence testing (§5.1–§5.2)

`05_prediction.tex` 63–353.  Throughout, `MS : MasterScales K As sl Dm` are §3's master scales and
`A = MS.core.parameters`.  "`o(1)` uniformly over the inputs" is `∀ ε > 0, ∀ᶠ N in atTop, ∀ inputs`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace HindmanSumsProducts.Prediction

noncomputable section

variable {K sl r : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

/-! ### Lemma `lem:dual-pseudorandomness` (05:68–190) -/

/-- `A_* = 2^{2^{d_*} − 1}` (05:76). -/
def dualMomentConstant (dStar : ℕ) : ℝ := (2 : ℝ) ^ (2 ^ dStar - 1)

/-- Integer direction coefficients (05:92–101): for a nonempty `ω ⊆ [d]` there are integers
`a_0, …, a_d` with `a_0 ≠ 0`, `a_0 + ∑_{j∈ω} a_j = 0` and `a_0 + ∑_{j∈ω'} a_j ≠ 0` for `ω' ≠ ω`. -/
theorem direction_integers (d : ℕ) (ω : Finset (Fin d)) (hω : ω.Nonempty) :
    ∃ a : Fin (d + 1) → ℤ, a 0 ≠ 0 ∧ a 0 + ∑ j ∈ ω, a j.succ = 0 ∧
      ∀ ω' : Finset (Fin d), ω' ≠ ω → a 0 + ∑ j ∈ ω', a j.succ ≠ 0 := by
  classical
  let a : Fin (d + 1) → ℤ := Fin.cases (ω.card : ℤ)
    (fun j => if j ∈ ω then -1 else 1)
  refine ⟨a, ?_, ?_, ?_⟩
  · simp only [a, Fin.cases_zero]
    exact_mod_cast (Finset.card_pos.mpr hω).ne'
  · have hωsum : ∑ j ∈ ω, (if j ∈ ω then -1 else 1) =
        -(ω.card : ℤ) := by
      calc
        _ = ∑ _j ∈ ω, (-1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [hj]
        _ = -(ω.card : ℤ) := by simp [Finset.sum_const]
    simpa [a, Fin.cases_succ, hωsum]
  · intro ω' hne
    have hsum : ∑ j ∈ ω', a j.succ =
        -((ω' ∩ ω).card : ℤ) + ((ω' \ ω).card : ℤ) := by
      have hdecomp : ω' = ω' ∩ ω ∪ (ω' \ ω) := by
        ext j
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      have hdisj : Disjoint (ω' ∩ ω) (ω' \ ω) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext j
        simp
      conv_lhs => rw [hdecomp]
      rw [Finset.sum_union hdisj]
      simp only [a, Fin.cases_succ]
      have hleft : ∑ j ∈ ω' ∩ ω, (if j ∈ ω then -1 else 1) =
          -((ω' ∩ ω).card : ℤ) := by
        calc
          _ = ∑ _j ∈ ω' ∩ ω, (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Finset.mem_inter] at hj
            simp [hj.2]
          _ = -((ω' ∩ ω).card : ℤ) := by simp [Finset.sum_const]
      have hright : ∑ j ∈ ω' \ ω, (if j ∈ ω then -1 else 1) =
          ((ω' \ ω).card : ℤ) := by
        calc
          _ = ∑ _j ∈ ω' \ ω, (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Finset.mem_sdiff] at hj
            simp [hj.2]
          _ = ((ω' \ ω).card : ℤ) := by simp [Finset.sum_const]
      rw [hleft, hright]
    have hcard : (ω.card : ℤ) =
        ((ω \ ω').card : ℤ) + ((ω ∩ ω').card : ℤ) := by
      exact_mod_cast (Finset.card_sdiff_add_card_inter ω ω').symm
    have hneZero : ((ω \ ω').card : ℤ) + ((ω' \ ω).card : ℤ) ≠ 0 := by
      intro hz
      have hleft : ((ω \ ω').card : ℤ) = 0 := by nlinarith
      have hright : ((ω' \ ω).card : ℤ) = 0 := by nlinarith
      have hleftN : (ω \ ω').card = 0 := by exact_mod_cast hleft
      have hrightN : (ω' \ ω).card = 0 := by exact_mod_cast hright
      have hωsub : ω ⊆ ω' := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.card_eq_zero.mp hleftN)
      have hω'sub : ω' ⊆ ω := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.card_eq_zero.mp hrightN)
      exact hne (Finset.Subset.antisymm hω'sub hωsub)
    intro hz
    have hz' : (ω.card : ℤ) +
        ∑ j ∈ ω', a j.succ = 0 := by
      change a 0 + ∑ j ∈ ω', a j.succ = 0
      exact hz
    rw [hsum] at hz'
    rw [Finset.inter_comm ω ω'] at hcard
    apply hneZero
    linarith

/-- (eq:prediction-dual-products), 05:68–74 and 129–164: for every fixed `b` and fixed tests at
the same block (possibly different valid gaps, allowed types and `J₀`),
`E_{μ_i}(ν − 1) ∏_{k<b} 𝒟_k = o(1)` uniformly over their inputs. -/
theorem dual_products_orthogonal (MS : MasterScales K As sl Dm) (B : Block K) (b : ℕ)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y)| ≤ ε := by
  sorry

/-- (eq:prediction-dual-moments), 05:74–79 and 166–175: for every fixed `b ≥ 1` and a type of
dimension `≤ d_*`, `E_{μ_i}(1 + ν)|𝒟|^b ≤ 2 A_*^b + o(1)` uniformly over the inputs. -/
theorem dual_moment_bound (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) (hgap : ValidGap B l) (hT : Allowed Dm T) (hJ0 : 0 < J0)
    (dStar : ℕ) (hd : T.d ≤ dStar) (b : ℕ) (hb : 0 < b) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
      Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
        |dualTest MS B T l J0 N I y| ^ b) ≤ 2 * dualMomentConstant dStar ^ b + ε := by
  intro ε hε
  have htwoExp : (1 + b * (2 ^ T.d - 1)) ≤
      1 + b * (2 ^ dStar - 1) := by
    have hpow : 2 ^ T.d ≤ 2 ^ dStar := Nat.pow_le_pow_right (by omega) hd
    have hsub : 2 ^ T.d - 1 ≤ 2 ^ dStar - 1 := Nat.sub_le_sub_right hpow 1
    exact Nat.add_le_add_left (Nat.mul_le_mul_left b hsub) 1
  have hcount : (2 : ℝ) ^ (1 + b * (2 ^ T.d - 1)) ≤
      2 * dualMomentConstant dStar ^ b := by
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) htwoExp
    have hconst : 2 * dualMomentConstant dStar ^ b =
        (2 : ℝ) ^ (1 + b * (2 ^ dStar - 1)) := by
      unfold dualMomentConstant
      calc
        _ = (2 : ℝ) ^ 1 * ((2 : ℝ) ^ (2 ^ dStar - 1)) ^ b := by norm_num
        _ = (2 : ℝ) ^ (1 + (2 ^ dStar - 1) * b) := by
          rw [← pow_mul, ← pow_add]
        _ = _ := by congr 1; rw [Nat.mul_comm]
    exact hpow.trans (le_of_eq hconst.symm)
  have hMoment := pkgB_dualMoment_bound_asymptotic
    MS B l hgap T hT J0 hJ0 b hb ε hε
  filter_upwards [hMoment] with N hN
  intro I
  have hI := hN I
  have hI' : Emu MS.core.parameters N B.1
      (fun y => (1 + nu MS.core.parameters N B y) *
        |dualTest MS B T l J0 N I y| ^ b) ≤
      (2 : ℝ) ^ (1 + b * (2 ^ T.d - 1)) + ε := hI
  linarith [hI', hcount]

/-- Clipping, 05:80–82 and 177–184: for fixed `K > A_*` and fixed `p ≥ 1`,
`E_{μ_i}(1 + ν)|𝒟 − 𝒟^{[K]}|^p = o(1)` uniformly over the inputs. -/
theorem dual_clipping_error (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) (hgap : ValidGap B l) (hT : Allowed Dm T) (hJ0 : 0 < J0)
    (dStar : ℕ) (hd : T.d ≤ dStar) (Kc : ℝ) (hK : dualMomentConstant dStar < Kc)
    (p : ℕ) (hp : 0 < p) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
      Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
        |dualTest MS B T l J0 N I y - clip Kc (dualTest MS B T l J0 N I y)| ^ p) ≤ ε := by
  intro ε hε
  let Astar : ℝ := dualMomentConstant dStar
  have hApos : 0 < Astar := by
    dsimp [Astar, dualMomentConstant]
    positivity
  have hAone : 1 ≤ Astar := by
    dsimp [Astar, dualMomentConstant]
    exact one_le_pow₀ (by norm_num)
  have hKpos : 0 < Kc := lt_trans hApos hK
  have hKone : 1 < Kc := lt_of_le_of_lt hAone hK
  let ratioA : ℝ := Astar / Kc
  let ratioK : ℝ := 1 / Kc
  have hratioA0 : 0 ≤ ratioA := by positivity
  have hratioA1 : ratioA < 1 := (div_lt_one hKpos).2 hK
  have hratioK0 : 0 ≤ ratioK := by positivity
  have hratioK1 : ratioK < 1 := (div_lt_one hKpos).2 hKone
  have hpowA : Tendsto (fun n : ℕ => ratioA ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratioA0 hratioA1
  have hpowK : Tendsto (fun n : ℕ => ratioK ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratioK0 hratioK1
  have hsmall : Tendsto
      (fun n : ℕ => 2 * Astar ^ p * ratioA ^ n + ratioK ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpowA).add hpowK
  let Cseq : ℕ → ℝ := fun n =>
    Kc ^ p * (Kc ^ (p + n))⁻¹ * (2 * Astar ^ (p + n) + 1)
  have hCeq (n : ℕ) :
      Cseq n = 2 * Astar ^ p * ratioA ^ n + ratioK ^ n := by
    dsimp [Cseq, ratioA, ratioK]
    rw [pow_add, pow_add]
    have hcancel : Kc ^ p * (Kc ^ p * Kc ^ n)⁻¹ = (Kc ^ n)⁻¹ := by
      field_simp [ne_of_gt (pow_pos hKpos p), ne_of_gt (pow_pos hKpos n)]
    calc
      Kc ^ p * (Kc ^ p * Kc ^ n)⁻¹ * (2 * (Astar ^ p * Astar ^ n) + 1) =
          (Kc ^ n)⁻¹ * (2 * (Astar ^ p * Astar ^ n) + 1) := by rw [hcancel]
      _ = 2 * Astar ^ p * (Astar ^ n / Kc ^ n) + 1 / Kc ^ n := by
        field_simp [ne_of_gt (pow_pos hKpos n)]
      _ = 2 * Astar ^ p * (Astar / Kc) ^ n + (1 / Kc) ^ n := by
        have h1 : (1 / Kc) ^ n = 1 / Kc ^ n := by
          simpa using (div_pow (1 : ℝ) Kc n)
        calc
          _ = 2 * Astar ^ p * (Astar / Kc) ^ n + 1 / Kc ^ n := by
            rw [← div_pow]
          _ = 2 * Astar ^ p * (Astar / Kc) ^ n + (1 / Kc) ^ n := by
            rw [← h1]
  have hCseq : Tendsto Cseq atTop (𝓝 0) := by
    apply hsmall.congr'
    filter_upwards with n
    exact (hCeq n).symm
  have hevent : ∀ᶠ n : ℕ in atTop, Cseq n < ε :=
    hCseq.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hevent
  have hCsmall : Cseq n < ε := hn n le_rfl
  let b : ℕ := p + n
  have hpb : p ≤ b := by dsimp [b]; omega
  have hb : 0 < b := lt_of_lt_of_le hp hpb
  let Ctail : ℝ := Kc ^ p * (Kc ^ b)⁻¹
  have hCtail : 0 ≤ Ctail := by dsimp [Ctail]; positivity
  have hmoment :=
    dual_moment_bound MS B l T J0 hgap hT hJ0 dStar hd b hb 1 (by norm_num)
  filter_upwards [hmoment] with N hmomentN
  intro I
  let D : ℤ → ℝ := dualTest MS B T l J0 N I
  let w : ℤ → ℝ := fun y => 1 + nu MS.core.parameters N B y
  have hw (y : ℤ) : 0 ≤ w y := by
    have h := I.g_bound (∅ : Finset (Fin T.d)) (fun _ => 0) y
    exact le_trans (abs_nonneg _) h
  have hpoint (y : ℤ) :
      w y * |D y - clip Kc (D y)| ^ p ≤ Ctail * (w y * |D y| ^ b) := by
    have hclip := clip_error_pow_le Kc (D y) hKpos p b hpb hp
    calc
      w y * |D y - clip Kc (D y)| ^ p ≤
          w y * (Ctail * |D y| ^ b) :=
        mul_le_mul_of_nonneg_left hclip (hw y)
      _ = Ctail * (w y * |D y| ^ b) := by ring
  have hresult :
      Emu MS.core.parameters N B.1 (fun y => w y * |D y - clip Kc (D y)| ^ p) < ε := by
   calc
    Emu MS.core.parameters N B.1 (fun y => w y * |D y - clip Kc (D y)| ^ p)
        ≤ Emu MS.core.parameters N B.1 (fun y => Ctail * (w y * |D y| ^ b)) :=
      pkgB_Emu_mono MS.core.parameters N B.1 hpoint
    _ = Ctail * Emu MS.core.parameters N B.1 (fun y => w y * |D y| ^ b) :=
      Emu_mul_left MS.core.parameters N B.1 Ctail (fun y => w y * |D y| ^ b)
    _ ≤ Ctail * (2 * Astar ^ b + 1) :=
      mul_le_mul_of_nonneg_left (hmomentN I) hCtail
    _ < ε := by
      have heq : Ctail * (2 * Astar ^ b + 1) = Cseq n := by
        dsimp [Ctail, Cseq, b]
      rw [heq]
      exact hCsmall
  exact le_of_lt (by simpa [w, D] using hresult)

/-- 05:80–82 and 184–189: (eq:prediction-dual-products) remains true for clipped tests, for a
common clipping bound `K > A_*`. -/
theorem dual_products_orthogonal_clipped (MS : MasterScales K As sl Dm) (B : Block K) (b : ℕ)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (dStar : ℕ) (hd : ∀ k, (T k).d ≤ dStar) (Kc : ℝ) (hK : dualMomentConstant dStar < Kc) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, clip Kc (dualTest MS B (T k) (gap k) (J0 k) N (I k) y))| ≤ ε := by
  intro ε hε
  by_cases hb0 : b = 0
  · subst b
    simpa using
      (dual_products_orthogonal MS B 0 gap T J0 hgap hT hJ0 ε hε)
  · have hb : 0 < b := Nat.pos_of_ne_zero hb0
    let Astar : ℝ := dualMomentConstant dStar
    have hApos : 0 < Astar := by
      dsimp [Astar, dualMomentConstant]
      positivity
    let M : ℝ := 2 * Astar ^ b + 1
    have hMone : 1 ≤ M := by
      dsimp [M]
      nlinarith [pow_nonneg (le_of_lt hApos) b]
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMone
    let theta : ℝ := ε / (4 * (b : ℝ))
    have htheta : 0 < theta := by dsimp [theta]; positivity
    let rtail : ℝ := theta / M ^ b
    have hrtail : 0 < rtail := by dsimp [rtail]; positivity
    let delta : ℝ := rtail ^ b
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    let pRoot : ℝ := 1 / (b : ℝ)
    have hbReal : 0 < (b : ℝ) := by exact_mod_cast hb
    have hpNat : (b : ℝ) * pRoot = 1 := by
      dsimp [pRoot]
      exact mul_one_div_cancel hbReal.ne'
    have hdeltaRoot : delta ^ pRoot = rtail := by
      dsimp [delta, pRoot]
      rw [← Real.rpow_natCast_mul (le_of_lt hrtail), hpNat, Real.rpow_one]
    have horth :=
      dual_products_orthogonal MS B b gap T J0 hgap hT hJ0 (ε / 2) (by positivity)
    have hmomentEach (k : Fin b) :
        ∀ᶠ N in atTop, ∀ Ik : DualInput MS B (T k) N,
          Emu MS.core.parameters N B.1
            (fun y => (1 + nu MS.core.parameters N B y) *
              |dualTest MS B (T k) (gap k) (J0 k) N Ik y| ^ b) ≤ M := by
      have hm := dual_moment_bound MS B (gap k) (T k) (J0 k)
        (hgap k) (hT k) (hJ0 k) dStar (hd k) b hb 1 (by norm_num)
      simpa [M, Astar] using hm
    have hclipEach (k : Fin b) :
        ∀ᶠ N in atTop, ∀ Ik : DualInput MS B (T k) N,
          Emu MS.core.parameters N B.1
            (fun y => (1 + nu MS.core.parameters N B y) *
              |dualTest MS B (T k) (gap k) (J0 k) N Ik y -
                clip Kc (dualTest MS B (T k) (gap k) (J0 k) N Ik y)| ^ b) ≤ delta :=
      dual_clipping_error MS B (gap k) (T k) (J0 k)
        (hgap k) (hT k) (hJ0 k) dStar (hd k) Kc hK b hb delta hdelta
    have hAll : ∀ᶠ N in atTop, ∀ k : Fin b,
        (∀ Ik : DualInput MS B (T k) N,
          Emu MS.core.parameters N B.1
            (fun y => (1 + nu MS.core.parameters N B y) *
              |dualTest MS B (T k) (gap k) (J0 k) N Ik y| ^ b) ≤ M) ∧
        (∀ Ik : DualInput MS B (T k) N,
          Emu MS.core.parameters N B.1
            (fun y => (1 + nu MS.core.parameters N B y) *
              |dualTest MS B (T k) (gap k) (J0 k) N Ik y -
                clip Kc (dualTest MS B (T k) (gap k) (J0 k) N Ik y)| ^ b) ≤ delta) := by
      have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
        (fun k _ => (hmomentEach k).and (hclipEach k))
      simpa using h
    filter_upwards [horth, hAll] with N horthN hAllN
    intro I
    let D : Fin b → ℤ → ℝ := fun k y =>
      dualTest MS B (T k) (gap k) (J0 k) N (I k) y
    let C : Fin b → ℤ → ℝ := fun k y => clip Kc (D k y)
    let w : ℤ → ℝ := fun y => 1 + nu MS.core.parameters N B y
    have hw (y : ℤ) : 0 ≤ w y := by
      dsimp [w]
      exact add_nonneg (by norm_num) (pkgB_nu_nonneg MS.core.parameters N B y)
    have hrootAbs (y : ℤ) :
        |nu MS.core.parameters N B y - 1| ≤ w y := by
      dsimp [w]
      exact abs_sub_one_le_add_one (pkgB_nu_nonneg MS.core.parameters N B y)
    let term : Fin b → ℤ → ℝ := fun i y =>
      |C i y - D i y| *
        ∏ k : Fin b, (if k = i then (1 : ℝ) else |D k y|)
    let F : Fin b → Fin b → ℤ → ℝ := fun i k y =>
      if k = i then D i y - C i y else D k y
    have hFprod (i : Fin b) (y : ℤ) :
        ∏ k : Fin b, |F i k y| = term i y := by
      dsimp [F, term]
      calc
        ∏ k : Fin b, |if k = i then D i y - C i y else D k y| =
            ∏ k : Fin b, if k = i then |D i y - C i y| else |D k y| := by
              apply Finset.prod_congr rfl
              intro k hk
              by_cases hki : k = i <;> simp [hki]
        _ = |D i y - C i y| *
            ∏ k : Fin b, (if k = i then (1 : ℝ) else |D k y|) :=
          prod_ite_factorization (Finset.univ : Finset (Fin b)) i
            (Finset.mem_univ i) _ _
        _ = |C i y - D i y| *
            ∏ k : Fin b, (if k = i then (1 : ℝ) else |D k y|) := by
              rw [abs_sub_comm]
    have htel (y : ℤ) :
        |(∏ k : Fin b, C k y) - ∏ k : Fin b, D k y| ≤
          ∑ k : Fin b, term k y := by
      have hbase := abs_prod_sub_prod_le (Finset.univ : Finset (Fin b))
        (fun k => C k y) (fun k => D k y)
      have hmax (k : Fin b) :
          max (|C k y|) (|D k y|) = |D k y| :=
        max_eq_right (clip_abs_le_abs Kc (D k y) (le_of_lt (lt_trans hApos hK)))
      simpa [term, hmax] using hbase
    letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
    have hholder (i : Fin b) :
        Emu MS.core.parameters N B.1 (fun y => w y * term i y) ≤
          ∏ k : Fin b,
            (Emu MS.core.parameters N B.1
              (fun y => w y * |F i k y| ^ b)) ^ pRoot := by
      calc
        Emu MS.core.parameters N B.1 (fun y => w y * term i y) =
            Emu MS.core.parameters N B.1
              (fun y => w y * ∏ k : Fin b, |F i k y|) := by
                congr 1
                funext y
                rw [hFprod i y]
        _ ≤ ∏ k : Fin b,
              (Emu MS.core.parameters N B.1
                (fun y => w y * |F i k y| ^ (Finset.univ : Finset (Fin b)).card)) ^
                  (1 / ((Finset.univ : Finset (Fin b)).card : ℝ)) :=
          Emu_weighted_holder (Finset.univ : Finset (Fin b)) Finset.univ_nonempty
            MS.core.parameters N B.1 w (F i) hw
        _ = _ := by simp [Finset.card_fin, pRoot]
    have hmomentNonneg (i k : Fin b) :
        0 ≤ Emu MS.core.parameters N B.1
          (fun y => w y * |F i k y| ^ b) :=
      pkgB_Emu_nonneg MS.core.parameters N B.1
        (fun y => mul_nonneg (hw y) (pow_nonneg (abs_nonneg _) _))
    have hmomentRootBound (i k : Fin b) :
        (Emu MS.core.parameters N B.1
          (fun y => w y * |F i k y| ^ b)) ^ pRoot ≤
            if k = i then rtail else M := by
      by_cases hki : k = i
      · subst k
        have herr := (hAllN i).2 (I i)
        have hbound : Emu MS.core.parameters N B.1
            (fun y => w y * |F i i y| ^ b) ≤ delta := by
          simpa [F, D, C, w] using herr
        have hroot : (Emu MS.core.parameters N B.1
            (fun y => w y * |F i i y| ^ b)) ^ pRoot ≤ rtail := by
          calc
            _ ≤ delta ^ pRoot :=
              Real.rpow_le_rpow (hmomentNonneg i i) hbound (by positivity)
            _ = rtail := hdeltaRoot
        simpa using hroot
      · have hbound : Emu MS.core.parameters N B.1
            (fun y => w y * |F i k y| ^ b) ≤ M := by
          simpa [F, hki, D, w] using (hAllN k).1 (I k)
        have hp_le_one : pRoot ≤ 1 := by
          have hbcast : 1 ≤ (b : ℝ) := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hb))
          dsimp [pRoot]
          calc
            1 / (b : ℝ) ≤ 1 / 1 :=
              one_div_le_one_div_of_le (by norm_num) hbcast
            _ = 1 := by norm_num
        have hroot : (Emu MS.core.parameters N B.1
            (fun y => w y * |F i k y| ^ b)) ^ pRoot ≤ M := by
          calc
          _ ≤ M ^ pRoot :=
            Real.rpow_le_rpow (hmomentNonneg i k) hbound (by positivity)
          _ ≤ M := by
            simpa using Real.rpow_le_rpow_of_exponent_le hMone hp_le_one
        simpa [hki] using hroot
    have hrootProd (i : Fin b) :
        ∏ k : Fin b,
            (Emu MS.core.parameters N B.1
              (fun y => w y * |F i k y| ^ b)) ^ pRoot ≤ theta := by
      have hprod :
          ∏ k : Fin b,
            (Emu MS.core.parameters N B.1
              (fun y => w y * |F i k y| ^ b)) ^ pRoot ≤
            ∏ k : Fin b, (if k = i then rtail else M) :=
        Finset.prod_le_prod₀
          (fun k _ => Real.rpow_nonneg (hmomentNonneg i k) _)
          (fun k _ => hmomentRootBound i k)
      have hrest :
          ∏ k ∈ (Finset.univ : Finset (Fin b)),
              (if k = i then (1 : ℝ) else M) ≤ M ^ b := by
        calc
          ∏ k ∈ (Finset.univ : Finset (Fin b)), (if k = i then (1 : ℝ) else M) ≤
              ∏ k ∈ (Finset.univ : Finset (Fin b)), M :=
            Finset.prod_le_prod₀
              (fun k _ => by
                by_cases hk : k = i
                · simp [hk]
                · simp [hk, hMpos.le])
              (fun k _ => by
                by_cases hk : k = i
                · simpa [hk] using hMone
                · simp [hk])
          _ = M ^ b := by simp
      calc
        _ ≤ ∏ k : Fin b, (if k = i then rtail else M) := hprod
        _ = rtail * ∏ k : Fin b, (if k = i then (1 : ℝ) else M) :=
          prod_ite_factorization (Finset.univ : Finset (Fin b)) i
            (Finset.mem_univ i) rtail (fun _ => M)
        _ ≤ rtail * M ^ b :=
          mul_le_mul_of_nonneg_left hrest (le_of_lt hrtail)
        _ = theta := by
          dsimp [rtail]
          field_simp [ne_of_gt (pow_pos hMpos b)]
    have htermBound (i : Fin b) : Emu MS.core.parameters N B.1
        (fun y => w y * term i y) ≤ theta :=
      (hholder i).trans (hrootProd i)
    have hdiffBound :
        Emu MS.core.parameters N B.1
          (fun y => w y *
            |(∏ k : Fin b, C k y) - ∏ k : Fin b, D k y|) ≤
          (b : ℝ) * theta := by
      calc
        _ ≤ Emu MS.core.parameters N B.1
            (fun y => w y * ∑ k : Fin b, term k y) :=
          pkgB_Emu_mono MS.core.parameters N B.1 (fun y =>
            mul_le_mul_of_nonneg_left (htel y) (hw y))
        _ = ∑ k : Fin b, Emu MS.core.parameters N B.1
              (fun y => w y * term k y) := by
          simpa [Finset.mul_sum] using
            Emu_finset_sum MS.core.parameters N B.1
              (Finset.univ : Finset (Fin b)) (fun k y => w y * term k y)
        _ ≤ ∑ _k : Fin b, theta := Finset.sum_le_sum fun k _ => htermBound k
        _ = (b : ℝ) * theta := by simp [Finset.sum_const, Finset.card_fin]
    have hdiffAbs :
        |Emu MS.core.parameters N B.1
          (fun y => (nu MS.core.parameters N B y - 1) *
            ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y))| ≤
          (b : ℝ) * theta := by
      calc
        _ ≤ Emu MS.core.parameters N B.1
            (fun y => |(nu MS.core.parameters N B y - 1) *
              ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y)|) :=
          pkgB_Emu_abs_le MS.core.parameters N B.1 _
        _ ≤ Emu MS.core.parameters N B.1
            (fun y => w y *
              |(∏ k : Fin b, C k y) - ∏ k : Fin b, D k y|) :=
          pkgB_Emu_mono MS.core.parameters N B.1 (fun y => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hrootAbs y) (abs_nonneg _))
        _ ≤ (b : ℝ) * theta := hdiffBound
    have hlinear :
        Emu MS.core.parameters N B.1
            (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, C k y) =
          Emu MS.core.parameters N B.1
            (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, D k y) +
          Emu MS.core.parameters N B.1
            (fun y => (nu MS.core.parameters N B y - 1) *
              ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y)) := by
      calc
        _ = Emu MS.core.parameters N B.1
              (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, D k y +
                (nu MS.core.parameters N B y - 1) *
                  ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y)) := by
            congr 1
            funext y
            ring
        _ = _ := pkgB_Emu_add MS.core.parameters N B.1 _ _
    calc
      |Emu MS.core.parameters N B.1
          (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, C k y)|
          ≤ (ε / 2) + (b : ℝ) * theta := by
              rw [hlinear]
              calc
                _ ≤
                    |Emu MS.core.parameters N B.1
                      (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, D k y)| +
                    |Emu MS.core.parameters N B.1
                      (fun y => (nu MS.core.parameters N B y - 1) *
                        ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y))| :=
                  abs_add_le _ _
                _ ≤ (ε / 2) + (b : ℝ) * theta :=
                  add_le_add (by simpa [D] using horthN I) hdiffAbs
      _ ≤ ε := by
        dsimp [theta]
        have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
        have hbRne : (b : ℝ) ≠ 0 := ne_of_gt hbR
        field_simp [hbRne]
        linarith

/-- Lemma `lem:dual-pseudorandomness` (05:68–83), assembled from its three parts. -/
theorem dual_pseudorandomness (MS : MasterScales K As sl Dm) (B : Block K) (dStar : ℕ) :
    (∀ (b : ℕ) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ),
      (∀ k, ValidGap B (gap k)) → (∀ k, Allowed Dm (T k)) → (∀ k, 0 < J0 k) →
      ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
        |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
          ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y)| ≤ ε) ∧
    (∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ), ValidGap B l → Allowed Dm T → 0 < J0 →
      T.d ≤ dStar → ∀ b : ℕ, 0 < b →
      ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          |dualTest MS B T l J0 N I y| ^ b) ≤ 2 * dualMomentConstant dStar ^ b + ε) ∧
    (∀ Kc : ℝ, dualMomentConstant dStar < Kc →
      (∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ), ValidGap B l → Allowed Dm T → 0 < J0 →
        T.d ≤ dStar → ∀ p : ℕ, 0 < p →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
          Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
            |dualTest MS B T l J0 N I y - clip Kc (dualTest MS B T l J0 N I y)| ^ p) ≤ ε) ∧
      (∀ (b : ℕ) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ),
        (∀ k, ValidGap B (gap k)) → (∀ k, Allowed Dm (T k)) → (∀ k, 0 < J0 k) →
        (∀ k, (T k).d ≤ dStar) →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
          |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (T k) (gap k) (J0 k) N (I k) y))| ≤ ε)) := by
  refine ⟨fun b gap T J0 hgap hT hJ0 => dual_products_orthogonal MS B b gap T J0 hgap hT hJ0,
    fun l T J0 hgap hT hJ0 hd b hb => dual_moment_bound MS B l T J0 hgap hT hJ0 dStar hd b hb,
    fun Kc hK => ⟨fun l T J0 hgap hT hJ0 hd p hp =>
      dual_clipping_error MS B l T J0 hgap hT hJ0 dStar hd Kc hK p hp,
      fun b gap T J0 hgap hT hJ0 hd =>
        dual_products_orthogonal_clipped MS B b gap T J0 hgap hT hJ0 dStar hd Kc hK⟩⟩

/-! ### Proposition `prop:dense-model` (05:199–248) -/

/-- The bounded dense-model property (eq:prediction-dense-approximation): `F` is `[0,1]`-valued
and, for every master block, scale label `a ∈ 𝒜`, colour, valid gap, allowed cube type (any
dimension) and fixed `J₀`, `E_{μ_i}(ρ − F)𝒟 = o(1)` uniformly over the inputs of `𝒟`. -/
def IsDenseModel (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) (F : BlockFamily K r) : Prop :=
  UnitValued F ∧
    ∀ (B : Block K), ∀ a ∈ As, ∀ c : Fin r, ∀ l : Fin K, ValidGap B l →
      ∀ T : CubeTemplate, Allowed Dm T → ∀ J0 : ℕ, 0 < J0 →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
          |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              dualTest MS B T l J0 N I y)| ≤ ε

/-- Finite-dimensional minimax (05:213–226), existence form: on a finite support with weights
`μ ≥ 0`, if `0 ≤ ρ ≤ ν` and `𝒞` is compact convex nonempty, some `F ∈ [0,1]^X` satisfies
`⟨ρ − F, G⟩_μ ≤ sup_{G' ∈ 𝒞} ⟨ν − 1, G'_+⟩_μ` for every `G ∈ 𝒞`. -/
theorem dense_model_minimax {X : Type} [Fintype X] (μ ρ ν : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ ν x) (C : Set (X → ℝ)) (hC : Convex ℝ C) (hCc : IsCompact C)
    (hne : C.Nonempty) :
    ∃ F : X → ℝ, (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ G ∈ C,
      ∑ x, μ x * (ρ x - F x) * G x ≤
        sSup ((fun G' : X → ℝ => ∑ x, μ x * (ν x - 1) * max (G' x) 0) '' C) := by
  sorry

/-- The stage-`Q` test class at a block: valid gap, allowed type of dimension `≤ Q`,
`0 < J₀ ≤ Q`. -/
def StageTest (Dm : Finset (IntegerPolynomial sl)) (B : Block K) (Q : ℕ) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) : Prop :=
  ValidGap B l ∧ Allowed Dm T ∧ T.d ≤ Q ∧ 0 < J0 ∧ J0 ≤ Q

/-- The signed clipped tests of stage `Q` at index `N` (05:213–215). -/
def stageClippedTests (MS : MasterScales K As sl Dm) (B : Block K) (Q : ℕ) (Kc : ℝ) (N : ℕ) :
    Set (ℤ → ℝ) :=
  {G | ∃ (l : Fin K) (T : CubeTemplate) (J0 : ℕ) (I : DualInput MS B T N),
    StageTest Dm B Q l T J0 ∧
      (G = (fun y => clip Kc (dualTest MS B T l J0 N I y)) ∨
        G = (fun y => -clip Kc (dualTest MS B T l J0 N I y)))}

/-- Positive-part bound (05:228–235): for fixed stage `Q`, `K > A_*` (with `d_* = Q`) and
`δ > 0`, `E_{μ_i}(ν − 1) G_+ ≤ 2δ + o(1)` uniformly over the closed convex hull of the signed
clipped stage tests. -/
theorem dense_model_positive_part (MS : MasterScales K As sl Dm) (B : Block K) (Q : ℕ)
    (Kc : ℝ) (hK : dualMomentConstant Q < Kc) (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ G ∈ closure (convexHull ℝ (stageClippedTests MS B Q Kc N)),
      Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) * max (G y) 0) ≤
        2 * δ + ε := by
  sorry

/-- One stage of Proposition `prop:dense-model` (05:209–240): for a fixed stage `Q` there are
`[0,1]`-valued models with error at most `1/(Q+1)` against every stage test, for all large `N`,
uniformly over the finitely many master blocks, scale labels, colours and inputs. -/
theorem dense_model_stage (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) (Q : ℕ) :
    ∃ F : BlockFamily K r, UnitValued F ∧ ∀ᶠ N in atTop,
      ∀ (B : Block K), ∀ a ∈ As, ∀ c : Fin r, ∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ),
        StageTest Dm B Q l T J0 → ∀ I : DualInput MS B T N,
          |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              dualTest MS B T l J0 N I y)| ≤ 1 / ((Q : ℝ) + 1) := by
  sorry

/-- Proposition `prop:dense-model` (05:199–207): bounded dense models exist.  Proof: the stages
`dense_model_stage Q`, diagonalized with `Q = Q(N)` increasing slowly (05:240–247). -/
theorem bounded_dense_models (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) :
    ∃ F : BlockFamily K r, IsDenseModel MS χ F := by
  sorry

/-! ### Lemma `lem:nilsequence-testing` (05:275–353) -/

/-- `y` lies within `width` of an endpoint of its `R`-interval `[kR, (k+1)R)`. -/
def InBoundaryStrip (R width : ℕ) (y : ℤ) : Prop :=
  y % (R : ℤ) ≤ (width : ℤ) ∨ (R : ℤ) ≤ y % (R : ℤ) + (width : ℤ)

/-- Indicator of `InBoundaryStrip`. -/
def boundaryIndicator (R width : ℕ) (y : ℤ) : ℝ := by
  classical
  exact if InBoundaryStrip R width y then 1 else 0

/-- Recipes realized as dual tests (05:287–323): for a fixed menu of step `≤ s`, Lipschitz bound
and accuracy `δ`, there are finitely many scalars `λ_t` (independent of `J₀`, `N` and the
family) such that, for every fixed `J₀` and all large `N`, every representing family at gap `l`
is reconstructed within `δ`, at every root farther than `(s+1)R_l/J₀` from the ends of its
`R_l`-interval, by `∑_t λ_t 𝒟_t` with dual tests of the extra type (dimension `s+1`, modulus `M`),
`e = 1` and inputs bounded by `1`.  Rests on `Charted.cube_corner_recipes`. -/
theorem nilsequence_recipe_tests (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hl : ValidGap B l) {s : ℕ} (Fm : Menu s) (Km : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n₀ : ℕ) (coeff : Fin n₀ → ℝ), ∀ J0 : ℕ, 0 < J0 → ∀ᶠ N in atTop,
      ∀ Φ : RepFamily MS.core.parameters l Fm Km,
        ∃ I : Fin n₀ → DualInput MS B (extraTemplate s) N,
          (∀ t p, (I t).e p = 1) ∧ (∀ t ω p y, |(I t).g ω p y| ≤ 1) ∧
          ∀ y : ℤ,
            ¬ InBoundaryStrip (MS.core.parameters.H N l)
              ((s + 1) * MS.core.parameters.H N l / J0) y →
            |Φ.eval N y - ∑ t, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y| ≤ δ := by
  sorry

/-- (eq:prediction-weighted-boundary), 05:325–342: the boundary strips of relative length
`(s+1)/J₀` carry `(1 + ν_B)μ_i`-mass `O_s(J₀^{-1}) + o(1)`.  The constant depends on `s` only. -/
theorem weighted_boundary (s : ℕ) :
    ∃ C : ℝ, ∀ {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
      (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K), ValidGap B l →
      ∀ J0 : ℕ, 0 < J0 → ∀ ε > 0, ∀ᶠ N in atTop,
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          boundaryIndicator (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J0) y) ≤ C / J0 + ε := by
  sorry

/-- Lemma `lem:nilsequence-testing` (eq:prediction-nilsequence-testing), 05:275–285, 344–353:
for a dense model `F`, a block `B`, a valid gap `l`, and a fixed menu of step `≤ s` with a fixed
Lipschitz bound, `E_{μ_i}(ρ − F) S' = o(1)` uniformly over the representing families `S'` at gap
`l` (bounded real families follow by affine combination with the constant family).  `1 ∈ Dm`
makes the extra type `extraTemplate s` allowed, so that `IsDenseModel` covers it. -/
theorem nilsequence_testing (MS : MasterScales K As sl Dm) (h1 : (1 : IntegerPolynomial sl) ∈ Dm)
    (χ : ℕ → Fin r) (F : BlockFamily K r) (hF : IsDenseModel MS χ F) (B : Block K) (a : ℚ) (ha : a ∈ As) (c : Fin r) (l : Fin K)
    (hl : ValidGap B l) {s : ℕ} (Fm : Menu s) (Km : ℝ≥0) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ Φ : RepFamily MS.core.parameters l Fm Km,
      |Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * Φ.eval N y)| ≤ ε := by
  sorry

end

end HindmanSumsProducts.Prediction
