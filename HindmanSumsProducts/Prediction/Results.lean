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
  sorry

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
      Emu_mono MS.core.parameters N B.1 hpoint
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
      exact add_nonneg (by norm_num) (nu_nonneg MS.core.parameters N B y)
    have hrootAbs (y : ℤ) :
        |nu MS.core.parameters N B y - 1| ≤ w y := by
      dsimp [w]
      exact abs_sub_one_le_add_one (nu_nonneg MS.core.parameters N B y)
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
      Emu_nonneg MS.core.parameters N B.1
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
          Emu_mono MS.core.parameters N B.1 (fun y =>
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
          Emu_abs_le MS.core.parameters N B.1 _
        _ ≤ Emu MS.core.parameters N B.1
            (fun y => w y *
              |(∏ k : Fin b, C k y) - ∏ k : Fin b, D k y|) :=
          Emu_mono MS.core.parameters N B.1 (fun y => by
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
        _ = _ := Emu_add MS.core.parameters N B.1 _ _
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
  exact HindmanSumsProducts.finite_dense_model_minimax μ ρ ν hμ hρ C hC hCc hne

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
  intro ε hε
  classical
  let A := MS.core.parameters
  have hApos : 0 < dualMomentConstant Q := by
    unfold dualMomentConstant
    positivity
  have hKpos : 0 < Kc := hApos.trans hK
  have hcont : ContinuousOn (fun x : ℝ => max x 0) (Set.Icc (-Kc) Kc) :=
    (continuous_id.max continuous_const).continuousOn
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (-Kc) Kc (fun x : ℝ => max x 0) hcont δ hδ
  let coeffMass := HindmanSumsProducts.densePolynomialCoefficientL1 p
  have hcoeffMass : 0 ≤ coeffMass := by
    unfold coeffMass HindmanSumsProducts.densePolynomialCoefficientL1
    exact Finset.sum_nonneg fun n hn => abs_nonneg _
  let ηMass : ℝ := ε / (2 * δ)
  let ηPoly : ℝ := ε / (2 * (coeffMass + 1))
  have hηMass : 0 < ηMass := by
    dsimp [ηMass]
    exact div_pos hε (mul_pos (by norm_num) hδ)
  have hηPoly : 0 < ηPoly := by
    dsimp [ηPoly]
    exact div_pos hε (mul_pos (by norm_num) (by linarith [hcoeffMass]))
  have hmassEvent : ∀ᶠ N in atTop,
      |Emu A N B.1 (fun y => nu A N B y - 1)| ≤ ηMass := by
    have hzero := dual_products_orthogonal MS B 0
      (fun k => Fin.elim0 k) (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
      (by intro k; exact Fin.elim0 k) (by intro k; exact Fin.elim0 k)
      (by intro k; exact Fin.elim0 k)
    filter_upwards [hzero ηMass hηMass] with N hN
    simpa using hN (fun k => Fin.elim0 k)
  let Templates : Type := {T : CubeTemplate // Allowed Dm T ∧ T.d ≤ Q}
  letI : Finite Templates := finite_allowed_cubeTemplates Dm
  letI : Fintype Templates := Fintype.ofFinite Templates
  let StageParams : Type :=
    {p : Fin K × Templates × Fin (Q + 1) // ValidGap B p.1 ∧ 0 < p.2.2.val}
  letI : Fintype StageParams := Fintype.ofFinite StageParams
  let stageGap := fun {b : ℕ} (pt : Fin b → StageParams) (k : Fin b) => (pt k).val.1
  let stageTemplate := fun {b : ℕ} (pt : Fin b → StageParams) (k : Fin b) =>
    ((pt k).val.2.1).val
  let stageJ0 := fun {b : ℕ} (pt : Fin b → StageParams) (k : Fin b) =>
    ((pt k).val.2.2).val
  have hprodUniform (b : ℕ) :
      ∀ᶠ N in atTop, ∀ pt : Fin b → StageParams,
        ∀ I : (k : Fin b) → DualInput MS B (stageTemplate pt k) N,
          |Emu A N B.1 (fun y => (nu A N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (stageTemplate pt k) (stageGap pt k)
              (stageJ0 pt k) N (I k) y))| ≤ ηPoly := by
    have hpt : ∀ pt : Fin b → StageParams, ∀ᶠ N in atTop,
        ∀ I : (k : Fin b) → DualInput MS B (stageTemplate pt k) N,
          |Emu A N B.1 (fun y => (nu A N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (stageTemplate pt k) (stageGap pt k)
              (stageJ0 pt k) N (I k) y))| ≤ ηPoly := by
      intro pt
      have hgap : ∀ k, ValidGap B (stageGap pt k) := fun k => (pt k).property.1
      have hT : ∀ k, Allowed Dm (stageTemplate pt k) :=
        fun k => ((pt k).val.2.1).property.1
      have hd : ∀ k, (stageTemplate pt k).d ≤ Q :=
        fun k => ((pt k).val.2.1).property.2
      have hJ0 : ∀ k, 0 < stageJ0 pt k := fun k => (pt k).property.2
      exact dual_products_orthogonal_clipped MS B b (stageGap pt) (stageTemplate pt)
        (stageJ0 pt) hgap hT hJ0 Q hd Kc hK ηPoly hηPoly
    exact Filter.eventually_all.2 hpt
  have hprodDegree : ∀ᶠ N in atTop,
      ∀ b ≤ p.natDegree, ∀ pt : Fin b → StageParams,
        ∀ I : (k : Fin b) → DualInput MS B (stageTemplate pt k) N,
          |Emu A N B.1 (fun y => (nu A N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (stageTemplate pt k) (stageGap pt k)
              (stageJ0 pt k) N (I k) y))| ≤ ηPoly := by
    have hfinite : ∀ᶠ N in atTop, ∀ b : Fin (p.natDegree + 1),
        ∀ pt : Fin b.val → StageParams,
          ∀ I : (k : Fin b.val) → DualInput MS B (stageTemplate pt k) N,
            |Emu A N B.1 (fun y => (nu A N B y - 1) *
              ∏ k, clip Kc (dualTest MS B (stageTemplate pt k) (stageGap pt k)
                (stageJ0 pt k) N (I k) y))| ≤ ηPoly :=
      Filter.eventually_all.2 (fun b => hprodUniform b.val)
    filter_upwards [hfinite] with N hN
    intro b hb pt I
    exact hN ⟨b, Nat.lt_succ_of_le hb⟩ pt I
  filter_upwards [hmassEvent, hprodDegree] with N hmassN hprodN
  let tests : Set (ℤ → ℝ) := stageClippedTests MS B Q Kc N
  have hHull : ∀ G ∈ convexHull ℝ tests,
      Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + ε := by
    intro G hG
    rcases mem_convexHull_iff_exists_fintype.mp hG with
      ⟨τ, hτ, c, q, hc0, hc1, hqmem, hcomb⟩
    letI : Fintype τ := hτ
    have hcL1 : HindmanSumsProducts.denseCoefficientL1 c = 1 :=
      HindmanSumsProducts.denseCoefficientL1_eq_one_of_nonneg c hc0 hc1
    have hqbound (t : τ) (y : ℤ) : |q t y| ≤ Kc := by
      rcases hqmem t with ⟨l, T, J0, I, hStage, hsign⟩
      rcases hsign with hsign | hsign
      · rw [hsign]
        exact clip_abs_le_of_nonneg hKpos.le
      · rw [hsign]
        simpa only [abs_neg] using clip_abs_le_of_nonneg hKpos.le
    have hcombBound (y : ℤ) :
        |HindmanSumsProducts.denseTestCombination q c y| ≤ Kc := by
      unfold HindmanSumsProducts.denseTestCombination
      calc
        |∑ t, c t * q t y| ≤ ∑ t, |c t * q t y| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ t, c t * |q t y| := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [abs_mul, abs_of_nonneg (hc0 t)]
        _ ≤ ∑ t, c t * Kc := by
          apply Finset.sum_le_sum
          intro t ht
          exact mul_le_mul_of_nonneg_left (hqbound t y) (hc0 t)
        _ = Kc := by
          rw [← Finset.sum_mul, hc1, one_mul]
    have hGval (y : ℤ) : HindmanSumsProducts.denseTestCombination q c y = G y := by
      simpa [HindmanSumsProducts.denseTestCombination, Pi.smul_apply, smul_eq_mul]
        using congrFun hcomb y
    let S := finitePivotSupport A N B.1
    let w : ℤ → ℝ := fun y => mu A N B.1 y
    let f : ℤ → ℝ := fun y => nu A N B y - 1
    have hmono : ∀ (m : ℕ), m ≤ p.natDegree → ∀ s : Fin m → τ,
        |HindmanSumsProducts.denseFinitePairing S w f
          (HindmanSumsProducts.denseTestMonomial q s)| ≤ ηPoly := by
      intro m hm s
      have hmem : ∀ k : Fin m, q (s k) ∈ tests := fun k => hqmem (s k)
      choose l T J0 I hStage hsign using hmem
      let tparam : Fin m → Templates := fun k =>
        ⟨T k, ⟨(hStage k).2.1, (hStage k).2.2.1⟩⟩
      let jparam : Fin m → Fin (Q + 1) := fun k =>
        ⟨J0 k, Nat.lt_succ_of_le (hStage k).2.2.2.2⟩
      let pt : Fin m → StageParams := fun k =>
        ⟨(l k, tparam k, jparam k), ⟨(hStage k).1, (hStage k).2.2.2.1⟩⟩
      have hclip := hprodN m hm pt I
      let clipped : Fin m → ℤ → ℝ := fun k y =>
        clip Kc (dualTest MS B (T k) (l k) (J0 k) N (I k) y)
      let sign : Fin m → ℝ := fun k =>
        if q (s k) = clipped k then 1 else -1
      have hfactor (k : Fin m) (y : ℤ) : q (s k) y = sign k * clipped k y := by
        by_cases hk : q (s k) = clipped k
        · simp [sign, hk]
        · rcases hsign k with hsign | hsign
          · exact False.elim (hk hsign)
          · dsimp [sign]
            rw [if_neg hk]
            rw [hsign]
            ring
      have hsignabs (k : Fin m) : |sign k| = 1 := by
        by_cases hk : q (s k) = clipped k
        · simp [sign, hk]
        · rcases hsign k with hsign | hsign
          · exact False.elim (hk hsign)
          · simp [sign, hk]
      have hsignprod : |∏ k, sign k| = 1 := by
        rw [Finset.abs_prod]
        simp_rw [hsignabs]
        simp
      have hprodEq (y : ℤ) :
          HindmanSumsProducts.denseTestMonomial q s y =
            (∏ k, sign k) * ∏ k, clipped k y := by
        unfold HindmanSumsProducts.denseTestMonomial
        calc
          (∏ k, q (s k) y) = ∏ k, sign k * clipped k y := by
            apply Finset.prod_congr rfl
            intro k hk
            exact hfactor k y
          _ = (∏ k, sign k) * ∏ k, clipped k y := Finset.prod_mul_distrib
      have hraw : |Emu A N B.1 (fun y => f y *
          HindmanSumsProducts.denseTestMonomial q s y)| ≤ ηPoly := by
        have hEq : Emu A N B.1 (fun y => f y *
            HindmanSumsProducts.denseTestMonomial q s y) =
            (∏ k, sign k) * Emu A N B.1 (fun y => f y * ∏ k, clipped k y) := by
          calc
            _ = Emu A N B.1 (fun y => (∏ k, sign k) * (f y * ∏ k, clipped k y)) := by
              apply Emu_congr
              intro y
              rw [hprodEq y]
              ring
            _ = _ := Emu_smul A N B.1 (∏ k, sign k) _
        rw [hEq, abs_mul, hsignprod, one_mul]
        exact hclip
      have hpair : HindmanSumsProducts.denseFinitePairing S w f
          (HindmanSumsProducts.denseTestMonomial q s) =
            Emu A N B.1 (fun y => f y * HindmanSumsProducts.denseTestMonomial q s y) := by
        rw [Emu_eq_sum_finitePivotSupport]
        unfold HindmanSumsProducts.denseFinitePairing S w f
        apply Finset.sum_congr rfl
        intro y hy
        ring
      rw [hpair]
      exact hraw
    have hpolyPair :
        |HindmanSumsProducts.denseFinitePairing S w f
          (fun y => p.eval (HindmanSumsProducts.denseTestCombination q c y))|
            ≤ coeffMass * ηPoly := by
      exact HindmanSumsProducts.denseAbsPolynomialPairing_le S hcL1 hmono
    have hpointErr (y : ℤ) :
        |max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y)| ≤ δ := by
      have hyIcc : HindmanSumsProducts.denseTestCombination q c y ∈ Set.Icc (-Kc) Kc :=
        abs_le.mp (hcombBound y)
      have h := hp _ hyIcc
      calc
        |max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y)| =
            |max (HindmanSumsProducts.denseTestCombination q c y) 0 -
              p.eval (HindmanSumsProducts.denseTestCombination q c y)| := by rw [← hGval y]
        _ = |p.eval (HindmanSumsProducts.denseTestCombination q c y) -
              max (HindmanSumsProducts.denseTestCombination q c y) 0| := abs_sub_comm _ _
        _ ≤ δ := h.le
    have herrorPair :
        |HindmanSumsProducts.denseFinitePairing S w f
          (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y))|
            ≤ δ * ∑ y ∈ S, w y * |f y| := by
      apply HindmanSumsProducts.denseAbsPairing_le_mul_weightedMass S w f
        (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y))
        (fun y hy => harmonicLaw_nonneg A N B.1 y) (fun y => hpointErr y)
    have hmassPoint (y : ℤ) : |f y| ≤ 1 + nu A N B y := by
      have hν := nu_nonneg A N B y
      change |nu A N B y - 1| ≤ 1 + nu A N B y
      rw [abs_le]
      constructor <;> linarith
    have hmassBound : ∑ y ∈ S, w y * |f y| ≤ 2 + ηMass := by
      have hEabs := Emu_mono A N B.1 hmassPoint
      have hEone := Emu_const_one_eq_one MS N B.1
      have hEadd := Emu_add A N B.1 (fun _ => (1 : ℝ)) (fun y => nu A N B y)
      have hEsub := Emu_sub A N B.1 (fun y => nu A N B y) (fun _ => (1 : ℝ))
      have hEadd' : Emu A N B.1 (fun y => 1 + nu A N B y) =
          1 + Emu A N B.1 (fun y => nu A N B y) := by
        rw [hEone] at hEadd
        exact hEadd
      have hEsub' : Emu A N B.1 (fun y => nu A N B y - 1) =
          Emu A N B.1 (fun y => nu A N B y) - 1 := by
        rw [hEone] at hEsub
        exact hEsub
      have hmean : Emu A N B.1 (fun y => 1 + nu A N B y) =
          2 + Emu A N B.1 (fun y => nu A N B y - 1) := by
        linarith [hEadd', hEsub']
      have hνerr : Emu A N B.1 (fun y => nu A N B y - 1) ≤ ηMass :=
        (le_abs_self _).trans hmassN
      have hsumE : (∑ y ∈ S, w y * |f y|) =
          Emu A N B.1 (fun y => |f y|) := by
        rw [Emu_eq_sum_finitePivotSupport]
      rw [hsumE]
      calc
        Emu A N B.1 (fun y => |f y|) ≤ Emu A N B.1 (fun y => 1 + nu A N B y) := hEabs
        _ = 2 + Emu A N B.1 (fun y => nu A N B y - 1) := hmean
        _ ≤ 2 + ηMass := by linarith
    have hsplit :
        HindmanSumsProducts.denseFinitePairing S w f (fun y => max (G y) 0) =
          HindmanSumsProducts.denseFinitePairing S w f
              (fun y => p.eval (HindmanSumsProducts.denseTestCombination q c y)) +
            HindmanSumsProducts.denseFinitePairing S w f
              (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y)) := by
      unfold HindmanSumsProducts.denseFinitePairing
      calc
        (∑ y ∈ S, w y * f y * max (G y) 0) =
            ∑ y ∈ S, (w y * f y * p.eval (HindmanSumsProducts.denseTestCombination q c y) +
              w y * f y * (max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y))) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = _ := Finset.sum_add_distrib
    have hpolyLe : HindmanSumsProducts.denseFinitePairing S w f
        (fun y => p.eval (HindmanSumsProducts.denseTestCombination q c y)) ≤ coeffMass * ηPoly :=
      (le_abs_self _).trans hpolyPair
    have herrLe : HindmanSumsProducts.denseFinitePairing S w f
        (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y)) ≤
          δ * (2 + ηMass) := by
      calc
        _ ≤ |HindmanSumsProducts.denseFinitePairing S w f
          (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y))| := le_abs_self _
        _ ≤ δ * ∑ y ∈ S, w y * |f y| := herrorPair
        _ ≤ δ * (2 + ηMass) := mul_le_mul_of_nonneg_left hmassBound (le_of_lt hδ)
    have hcoeffBound : coeffMass * ηPoly ≤ ε / 2 := by
      dsimp [ηPoly]
      have hden : 0 < 2 * (coeffMass + 1) := by positivity
      field_simp [ne_of_gt hden]
      have hc0 : 0 ≤ coeffMass := hcoeffMass
      nlinarith [hε]
    have herrBound : δ * (2 + ηMass) ≤ 2 * δ + ε / 2 := by
      dsimp [ηMass]
      field_simp [ne_of_gt hδ] <;> norm_num
    have hpairBound : HindmanSumsProducts.denseFinitePairing S w f
        (fun y => max (G y) 0) ≤ 2 * δ + ε := by
      rw [hsplit]
      linarith [hpolyLe, herrLe, hcoeffBound, herrBound]
    have hEmuPair : Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) =
        HindmanSumsProducts.denseFinitePairing S w f (fun y => max (G y) 0) := by
      rw [Emu_eq_sum_finitePivotSupport]
      unfold HindmanSumsProducts.denseFinitePairing S w f
      apply Finset.sum_congr rfl
      intro y hy
      ring
    rw [hEmuPair]
    exact hpairBound
  have hcont : Continuous (fun G : ℤ → ℝ =>
      Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0)) := by
    have heq : (fun G : ℤ → ℝ =>
        Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0)) =
        fun G => ∑ y ∈ finitePivotSupport A N B.1,
          mu A N B.1 y * ((nu A N B y - 1) * max (G y) 0) := by
      funext G
      rw [Emu_eq_sum_finitePivotSupport]
    rw [heq]
    fun_prop
  let good : Set (ℤ → ℝ) := {G | Emu A N B.1
    (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + ε}
  have hgoodClosed : IsClosed good := isClosed_Iic.preimage hcont
  have hHullSubset : convexHull ℝ (stageClippedTests MS B Q Kc N) ⊆ good := hHull
  have hclosure := closure_minimal hHullSubset hgoodClosed
  intro G hG
  exact hclosure hG

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
  classical
  let A := MS.core.parameters
  let Kc := dualMomentConstant Q + 1
  have hK : dualMomentConstant Q < Kc := by dsimp [Kc]; linarith
  have hKpos : 0 < Kc := by
    have hA : 0 < dualMomentConstant Q := by
      unfold dualMomentConstant
      positivity
    dsimp [Kc]
    linarith
  let targetErr : ℝ := 1 / ((Q : ℝ) + 1)
  let δ : ℝ := targetErr / 8
  let εpos : ℝ := targetErr / 4
  let εclip : ℝ := targetErr / 2
  have hTargetErr : 0 < targetErr := by dsimp [targetErr]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hεpos : 0 < εpos := by dsimp [εpos]; positivity
  have hεclip : 0 < εclip := by dsimp [εclip]; positivity
  have herrorSplit : 2 * δ + εpos + εclip = targetErr := by
    dsimp [targetErr, δ, εpos, εclip]
    ring
  let stageTests (N : ℕ) (B : Block K) : Set (ℤ → ℝ) :=
    stageClippedTests MS B Q Kc N
  let Support (N : ℕ) (B : Block K) := finitePivotSupport A N B.1
  letI (N : ℕ) (B : Block K) : Fintype (Support N B) :=
    Finset.fintypeCoeSort (finitePivotSupport A N B.1)
  let restrict (N : ℕ) (B : Block K) :
      (ℤ → ℝ) →ₗ[ℝ] (Support N B → ℝ) :=
    { toFun := fun (G : ℤ → ℝ) (x : Support N B) => G (x : ℤ)
      map_add' := by
        intro G H
        funext x
        rfl
      map_smul' := by
        intro a G
        funext x
        rfl }
  let restrictedTests (N : ℕ) (B : Block K) : Set (Support N B → ℝ) :=
    restrict N B '' stageTests N B
  let stageClass (N : ℕ) (B : Block K) : Set (Support N B → ℝ) :=
    closure (convexHull ℝ (restrictedTests N B))
  let stagePositive (N : ℕ) (B : Block K) (G : Support N B → ℝ) : ℝ :=
    ∑ x : Support N B, mu A N B.1 x * (nu A N B x - 1) * max (G x) 0
  let templates : Type := {T : CubeTemplate // Allowed Dm T ∧ T.d ≤ Q}
  letI : Finite templates := finite_allowed_cubeTemplates Dm
  letI : Fintype templates := Fintype.ofFinite templates
  let StageParam (B : Block K) : Type :=
    {p : Fin K × templates × Fin (Q + 1) // ValidGap B p.1 ∧ 0 < p.2.2.val}
  letI (B : Block K) : Fintype (StageParam B) := Fintype.ofFinite (StageParam B)
  letI : Fintype (Block K) := inferInstance
  let AllStageParams : Type := Σ B : Block K, StageParam B
  letI : Fintype (AllStageParams) := inferInstance
  have hposAll : ∀ᶠ N in atTop, ∀ B : Block K, ∀ G ∈ closure (convexHull ℝ (stageTests N B)),
      Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + εpos := by
    apply Filter.eventually_all.2
    intro B
    exact dense_model_positive_part MS B Q Kc hK δ hδ εpos hεpos
  let allGap := fun p : AllStageParams => p.2.val.1
  let allTemplate := fun p : AllStageParams => p.2.val.2.1.val
  let allJ0 := fun p : AllStageParams => p.2.val.2.2.val
  have hclipEach (p : AllStageParams) : ∀ᶠ N in atTop,
      ∀ I : DualInput MS p.1 (allTemplate p) N,
        Emu A N p.1.1 (fun y => (1 + nu A N p.1 y) *
          |dualTest MS p.1 (allTemplate p) (allGap p) (allJ0 p) N I y -
            clip Kc (dualTest MS p.1 (allTemplate p) (allGap p) (allJ0 p) N I y)| ^ 1) ≤ εclip := by
    let B := p.1
    let P := p.2
    exact dual_clipping_error MS B (allGap p) (allTemplate p) (allJ0 p)
      P.property.1 P.val.2.1.property.1 P.property.2 Q P.val.2.1.property.2
      Kc hK 1 (by norm_num) εclip hεclip
  have hclipAll : ∀ᶠ N in atTop, ∀ p : AllStageParams,
      ∀ I : DualInput MS p.1 (allTemplate p) N,
        Emu A N p.1.1 (fun y => (1 + nu A N p.1 y) *
          |dualTest MS p.1 (allTemplate p) (allGap p) (allJ0 p) N I y -
            clip Kc (dualTest MS p.1 (allTemplate p) (allGap p) (allJ0 p) N I y)| ^ 1) ≤ εclip := by
    exact Filter.eventually_all.2 hclipEach
  let stagePsiEq (N : ℕ) (B : Block K) (G : ℤ → ℝ) :
      Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) =
        stagePositive N B (restrict N B G) := by
    rw [Emu_eq_sum_finitePivotSupportSort]
    unfold stagePositive
    apply Fintype.sum_congr
    intro x
    dsimp [restrict]
    ring
  have hstageClassPos {N : ℕ} {B : Block K}
      (hpos : ∀ G ∈ closure (convexHull ℝ (stageTests N B)),
        Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + εpos) :
      ∀ G ∈ stageClass N B, stagePositive N B G ≤ 2 * δ + εpos := by
    have hcont : Continuous (stagePositive N B) := by
      unfold stagePositive
      simpa using continuous_finsetSum (Finset.univ : Finset (Support N B))
        (fun x hx => by fun_prop)
    let good : Set (Support N B → ℝ) := {G | stagePositive N B G ≤ 2 * δ + εpos}
    have hgoodClosed : IsClosed good := isClosed_Iic.preimage hcont
    have himage : restrict N B '' convexHull ℝ (stageTests N B) =
        convexHull ℝ (restrictedTests N B) :=
      (restrict N B).image_convexHull (stageTests N B)
    have hsub : convexHull ℝ (restrictedTests N B) ⊆ good := by
      intro G hG
      rw [← himage] at hG
      rcases hG with ⟨G0, hG0, rfl⟩
      have hG0' : G0 ∈ closure (convexHull ℝ (stageTests N B)) := subset_closure hG0
      change stagePositive N B (restrict N B G0) ≤ 2 * δ + εpos
      rw [← stagePsiEq N B G0]
      exact hpos G0 hG0'
    have hclosure := closure_minimal hsub hgoodClosed
    exact hclosure
  have hmodelExists (N : ℕ) (B : Block K) (a : ℚ) (c : Fin r) :
      ∃ F0 : ℤ → ℝ, (∀ y, F0 y ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ G ∈ stageTests N B,
          Emu A N B.1 (fun y => (rho MS.core.parameters χ N B a c y - F0 y) * G y) ≤
            sSup ((stagePositive N B) '' (stageClass N B)) := by
    classical
    let S := stageTests N B
    let C := stageClass N B
    by_cases hS : S.Nonempty
    · have hboxConv : Convex ℝ (Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc)) :=
        convex_Icc _ _
      have hboxClosed : IsClosed (Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc)) :=
        isClosed_Icc
      have hboxCompact : IsCompact (Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc)) :=
        isCompact_Icc
      have hrestrictedAbs (G0 : ℤ → ℝ) (hG0 : G0 ∈ stageTests N B)
          (x : Support N B) : |(restrict N B G0) x| ≤ Kc := by
        rcases hG0 with ⟨l, T, J0, I, hStage, hsign | hsign⟩
        · have hb : |clip Kc (dualTest MS B T l J0 N I (x : ℤ))| ≤ Kc :=
            clip_abs_le_of_nonneg hKpos.le
          dsimp [restrict]
          rw [hsign]
          exact hb
        · have hb : |clip Kc (dualTest MS B T l J0 N I (x : ℤ))| ≤ Kc :=
            clip_abs_le_of_nonneg hKpos.le
          dsimp [restrict]
          rw [hsign]
          simpa only [abs_neg] using hb
      have htestBound : restrictedTests N B ⊆
          Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc) := by
        rintro G ⟨G0, hG0, rfl⟩
        refine Set.mem_Icc.mpr ⟨?_, ?_⟩
        · intro x
          exact (abs_le.mp (hrestrictedAbs G0 hG0 x)).1
        · intro x
          exact (abs_le.mp (hrestrictedAbs G0 hG0 x)).2
      have hCsub : C ⊆ Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc) :=
        closure_minimal
          (hboxConv.convexHull_subset_iff.mpr htestBound) hboxClosed
      have hCcompact : IsCompact C :=
        hboxCompact.of_isClosed_subset isClosed_closure hCsub
      have hCconv : Convex ℝ C :=
        (convex_convexHull ℝ (restrictedTests N B)).closure
      have hCnonempty : C.Nonempty := by
        rcases hS with ⟨G, hG⟩
        exact ⟨restrict N B G,
          subset_closure (subset_convexHull ℝ _ ⟨G, hG, rfl⟩)⟩
      obtain ⟨F0, hF0, hF0ineq⟩ := finitePivot_minimax A N B.1
        (fun y => rho MS.core.parameters χ N B a c y) (fun y => nu A N B y)
        (fun y => rho_bounds A χ N B a c y) C hCconv hCcompact hCnonempty
      refine ⟨F0, hF0, ?_⟩
      intro G hG
      have hGmem : restrict N B G ∈ C :=
        subset_closure (subset_convexHull ℝ _ ⟨G, hG, rfl⟩)
      have hmin := hF0ineq (restrict N B G) hGmem
      have hpair : Emu A N B.1
          (fun y => (rho MS.core.parameters χ N B a c y - F0 y) * G y) =
            ∑ x : Support N B, mu A N B.1 (x : ℤ) *
              (rho MS.core.parameters χ N B a c (x : ℤ) - F0 (x : ℤ)) *
                (restrict N B G) x := by
        rw [Emu_eq_sum_finitePivotSupportSort]
        apply Fintype.sum_congr
        intro x
        dsimp [restrict]
        ring
      rw [hpair]
      exact hmin
    · refine ⟨fun _ => 0, ?_, ?_⟩
      · intro y
        exact ⟨le_rfl, zero_le_one⟩
      · intro G hG
        exact False.elim (hS ⟨G, hG⟩)
  let model : ℕ → Block K → ℚ → Fin r → ℤ → ℝ :=
    fun N B a c => Classical.choose (hmodelExists N B a c)
  have hmodelSpec (N : ℕ) (B : Block K) (a : ℚ) (c : Fin r) :=
    Classical.choose_spec (hmodelExists N B a c)
  let F : BlockFamily K r := model
  have hFunit : UnitValued F := by
    intro N B a c y
    exact (hmodelSpec N B a c).1 y
  have hposEvent : ∀ᶠ N in atTop, ∀ B : Block K,
      ∀ G ∈ closure (convexHull ℝ (stageTests N B)),
        Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + εpos :=
    hposAll
  have hclipEvent := hclipAll
  refine ⟨F, hFunit, ?_⟩
  filter_upwards [hposEvent, hclipEvent] with N hposN hclipN
  intro B a ha c l T J0 hStage I
  let hDual : ℤ → ℝ := dualTest MS B T l J0 N I
  let hClip : ℤ → ℝ := fun y => clip Kc (hDual y)
  have hClipMem : hClip ∈ stageTests N B :=
    ⟨l, T, J0, I, hStage, Or.inl rfl⟩
  have hNegClipMem : (fun y => -hClip y) ∈ stageTests N B :=
    ⟨l, T, J0, I, hStage, Or.inr rfl⟩
  have hclassBound := hstageClassPos (N := N) (B := B) (hposN B)
  have hCbound : ∀ G ∈ stageClass N B, stagePositive N B G ≤ 2 * δ + εpos :=
    hclassBound
  have hCnonempty : (stageClass N B).Nonempty := by
    exact ⟨restrict N B hClip,
      subset_closure (subset_convexHull ℝ _ ⟨hClip, hClipMem, rfl⟩)⟩
  have hValuesNonempty : ((stagePositive N B) '' (stageClass N B)).Nonempty :=
    hCnonempty.image _
  have hsupBound : sSup ((stagePositive N B) '' (stageClass N B)) ≤ 2 * δ + εpos := by
    apply csSup_le hValuesNonempty
    rintro v ⟨G, hG, rfl⟩
    exact hCbound G hG
  have hplusBound : Emu A N B.1
      (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) ≤
        2 * δ + εpos := by
    exact ((hmodelSpec N B a c).2 hClip hClipMem).trans hsupBound
  have hnegEq : Emu A N B.1
      (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * (-hClip y)) =
        -Emu A N B.1
          (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) := by
    calc
      _ = Emu A N B.1 (fun y => (-1 : ℝ) *
          ((rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y)) := by
        apply Emu_congr
        intro y
        ring
      _ = (-1 : ℝ) * Emu A N B.1
          (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) :=
        Emu_smul A N B.1 (-1) _
      _ = _ := by ring
  have hnegBound : -Emu A N B.1
      (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) ≤
        2 * δ + εpos := by
    rw [← hnegEq]
    exact ((hmodelSpec N B a c).2 (fun y => -hClip y) hNegClipMem).trans hsupBound
  have hclipCorrelation : |Emu A N B.1
      (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y)| ≤
        2 * δ + εpos := by
    rw [abs_le]
    constructor
    · linarith [hnegBound]
    · exact hplusBound
  let tparam : templates := ⟨T, ⟨hStage.2.1, hStage.2.2.1⟩⟩
  let jparam : Fin (Q + 1) := ⟨J0, Nat.lt_succ_of_le hStage.2.2.2.2⟩
  let param : StageParam B :=
    ⟨(l, tparam, jparam), ⟨hStage.1, hStage.2.2.2.1⟩⟩
  let allParam : AllStageParams := ⟨B, param⟩
  have hclipError : Emu A N B.1 (fun y => (1 + nu A N B y) *
      |hDual y - hClip y|) ≤ εclip := by
    have h := hclipN allParam (by
      simpa [allParam, param, tparam, allTemplate] using I)
    simpa [allParam, param, tparam, jparam, allGap, allTemplate, allJ0,
      hDual, hClip, pow_one] using h
  have hrhoF (y : ℤ) :
      |rho MS.core.parameters χ N B a c y - F N B a c y| ≤ 1 + nu A N B y := by
    have hr := rho_bounds A χ N B a c y
    have hν := nu_nonneg A N B y
    have hFv := hFunit N B a c y
    rw [abs_le]
    constructor <;> rcases Set.mem_Icc.mp hFv with ⟨hF0, hF1⟩ <;> linarith
  have herrAbs : |Emu A N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y))| ≤
        Emu A N B.1 (fun y => (1 + nu A N B y) * |hDual y - hClip y|) := by
    calc
      _ ≤ Emu A N B.1 (fun y => |(rho MS.core.parameters χ N B a c y - F N B a c y) *
          (hDual y - hClip y)|) := Emu_abs_le A N B.1 _
      _ ≤ Emu A N B.1 (fun y => (1 + nu A N B y) * |hDual y - hClip y|) := by
        apply Emu_mono A N B.1
        intro y
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hrhoF y) (abs_nonneg _)
  have herrBound : |Emu A N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y))| ≤ εclip :=
    herrAbs.trans hclipError
  have hsplit : Emu A N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * hDual y) =
      Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) +
      Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y)) := by
    rw [← Emu_add]
    congr 1
    funext y
    ring
  calc
    |Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * hDual y)| =
      |Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) +
       Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y))| := by rw [hsplit]
    _ ≤ |Emu A N B.1 (fun y =>
          (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y)| +
        |Emu A N B.1 (fun y =>
          (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y))| := abs_add_le _ _
    _ ≤ (2 * δ + εpos) + εclip := add_le_add hclipCorrelation herrBound
    _ = targetErr := herrorSplit

/-- Proposition `prop:dense-model` (05:199–207): bounded dense models exist.  Proof: the stages
`dense_model_stage Q`, diagonalized with `Q = Q(N)` increasing slowly (05:240–247). -/
theorem bounded_dense_models (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) :
    ∃ F : BlockFamily K r, IsDenseModel MS χ F := by
  classical
  let stageFamily : ℕ → BlockFamily K r := fun q =>
    Classical.choose (dense_model_stage MS χ q)
  have stageSpec (q : ℕ) := Classical.choose_spec (dense_model_stage MS χ q)
  let cutoff : ℕ → ℕ := fun q =>
    Classical.choose (Filter.eventually_atTop.1 (stageSpec q).2)
  have cutoffSpec (q : ℕ) (N : ℕ) (hN : cutoff q ≤ N) :=
    Classical.choose_spec (Filter.eventually_atTop.1 (stageSpec q).2) N hN
  let candidates (N : ℕ) : Finset ℕ :=
    insert 0 ((Finset.range (N + 1)).filter (fun q => cutoff q ≤ N))
  let slow (N : ℕ) : ℕ := (candidates N).max' (by simp [candidates])
  let F : BlockFamily K r := fun N B a c y => stageFamily (slow N) N B a c y
  have hUnit : UnitValued F := by
    intro N B a c y
    exact (stageSpec (slow N)).1 N B a c y
  refine ⟨F, ?_⟩
  change UnitValued F ∧ _
  refine ⟨hUnit, ?_⟩
  intro B a ha c l hl T hT J0 hJ0 ε hε
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / ε)
  have hRerr : 1 / ((R : ℝ) + 1) ≤ ε := by
    have hmul := mul_lt_mul_of_pos_left hR hε
    have hεR : 1 < ε * (R : ℝ) := by
      simpa [hε.ne', mul_comm] using hmul
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) + 1)]
    nlinarith [hεR]
  let qmin : ℕ := max (max T.d J0) R
  have hJ0le : J0 ≤ qmin := by
    dsimp [qmin]
    exact (Nat.le_max_right T.d J0).trans (Nat.le_max_left _ _)
  have hqminPos : 0 < qmin := lt_of_lt_of_le hJ0 hJ0le
  have hlarge : ∀ᶠ N in atTop, max qmin (cutoff qmin) ≤ N := by
    exact Filter.eventually_atTop.2 ⟨max qmin (cutoff qmin), fun _ hN => hN⟩
  have hslowLarge : ∀ᶠ N in atTop,
      qmin ≤ slow N ∧ cutoff (slow N) ≤ N := by
    filter_upwards [hlarge] with N hN
    have hqminN : qmin ≤ N := (Nat.le_max_left _ _).trans hN
    have hcutminN : cutoff qmin ≤ N := (Nat.le_max_right _ _).trans hN
    have hqminRange : qmin ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hqminN)
    have hqminCandidate : qmin ∈ candidates N :=
      Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hqminRange, hcutminN⟩)
    have hge : qmin ≤ slow N := (candidates N).le_max' qmin hqminCandidate
    have hqPos : 0 < slow N := lt_of_lt_of_le hqminPos hge
    have hmaxMem : slow N ∈ candidates N :=
      (candidates N).max'_mem (by simp [candidates])
    rcases Finset.mem_insert.mp hmaxMem with hzero | hfiltered
    · omega
    · exact ⟨hge, (Finset.mem_filter.mp hfiltered).2⟩
  filter_upwards [hslowLarge] with N hN
  intro I
  have hmodel := cutoffSpec (slow N) N hN.2
  have hdim : T.d ≤ slow N := by
    dsimp [qmin] at hN
    exact (Nat.le_max_left T.d J0).trans ((Nat.le_max_left _ _).trans hN.1)
  have hJ0slow : J0 ≤ slow N := by
    exact hJ0le.trans hN.1
  have hJ0Q : J0 ≤ slow N := hJ0slow
  have hStage : StageTest Dm B (slow N) l T J0 :=
    ⟨hl, hT, hdim, hJ0, hJ0Q⟩
  have hbound := hmodel B a ha c l T J0 hStage
  have hRle : R ≤ slow N := by
    dsimp [qmin] at hN
    exact (Nat.le_max_right (max T.d J0) R).trans hN.1
  have hden : (R : ℝ) + 1 ≤ (slow N : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hRle
  have hsmall : 1 / ((slow N : ℝ) + 1) ≤ ε :=
    (one_div_le_one_div_of_le (by positivity) hden).trans hRerr
  exact (hbound I).trans hsmall

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
