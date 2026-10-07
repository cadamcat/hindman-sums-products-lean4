import HindmanSumsProducts.Prediction.Outside
import Mathlib.Topology.Sion

/-! Helper lemmas for the §5 proof package S5-C (owned by its proof lane). -/

namespace HindmanSumsProducts

open scoped BigOperators

open Polynomial

noncomputable section

def denseFinitePairing {α : Type} (S : Finset α) (w f g : α → ℝ) : ℝ :=
  ∑ x ∈ S, w x * f x * g x

noncomputable def denseLinearFunctional {α : Type} [Fintype α]
    (a : α → ℝ) : (α → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ x ∈ (Finset.univ : Finset α), a x * f x
  map_add' f g := by
    simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ x ∈ (Finset.univ : Finset α), a x * (r * f x)) =
          ∑ x ∈ (Finset.univ : Finset α), r * (a x * f x) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = r * ∑ x ∈ (Finset.univ : Finset α), a x * f x := by
        rw [Finset.mul_sum]

def denseTestCombination {α τ : Type} [Fintype τ]
    (q : τ → α → ℝ) (c : τ → ℝ) (x : α) : ℝ :=
  ∑ t, c t * q t x

def denseTestMonomial {α τ : Type} (q : τ → α → ℝ) {m : ℕ}
    (s : Fin m → τ) (x : α) : ℝ :=
  ∏ i, q (s i) x

def denseCoefficientL1 {τ : Type} [Fintype τ] (c : τ → ℝ) : ℝ :=
  ∑ t, |c t|

def densePolynomialCoefficientL1 (p : ℝ[X]) : ℝ :=
  ∑ n ∈ p.support, |p.coeff n|

theorem denseCoefficientL1_eq_one_of_nonneg {τ : Type} [Fintype τ]
    (c : τ → ℝ) (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∑ t, c t = 1) :
    denseCoefficientL1 c = 1 := by
  unfold denseCoefficientL1
  calc
    (∑ t, |c t|) = ∑ t, c t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact abs_of_nonneg (hc0 t)
    _ = 1 := hc1

theorem denseTestCombination_pow {α τ : Type} [Fintype τ]
    (q : τ → α → ℝ) (c : τ → ℝ) (m : ℕ) (x : α) :
    denseTestCombination q c x ^ m =
      ∑ s : Fin m → τ, (∏ i, c (s i)) * denseTestMonomial q s x := by
  classical
  rw [denseTestCombination, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro s
  rw [Finset.prod_mul_distrib]
  rfl

theorem densePolynomial_eval_combination {α τ : Type} [Fintype τ]
    (p : ℝ[X]) (q : τ → α → ℝ) (c : τ → ℝ) (x : α) :
    p.eval (denseTestCombination q c x) =
      ∑ n ∈ p.support, ∑ s : Fin n → τ,
        (p.coeff n * ∏ i, c (s i)) * denseTestMonomial q s x := by
  classical
  rw [Polynomial.eval_eq_sum]
  change ∑ n ∈ p.support,
      p.coeff n * denseTestCombination q c x ^ n = _
  apply Finset.sum_congr rfl
  intro n hn
  rw [denseTestCombination_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem denseFinitePairing_finset_sum_right {α ι : Type}
    (S : Finset α) (w f : α → ℝ) (s : Finset ι) (q : ι → α → ℝ) :
    denseFinitePairing S w f (fun x => ∑ i ∈ s, q i x) =
      ∑ i ∈ s, denseFinitePairing S w f (q i) := by
  classical
  unfold denseFinitePairing
  calc
    (∑ x ∈ S, w x * f x * ∑ i ∈ s, q i x) =
        ∑ x ∈ S, ∑ i ∈ s, w x * f x * q i x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ x ∈ S, w x * f x * q i x := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ s, denseFinitePairing S w f (q i) := rfl

theorem denseFinitePairing_fintype_sum_right {α ι : Type} [Fintype ι]
    (S : Finset α) (w f : α → ℝ) (q : ι → α → ℝ) :
    denseFinitePairing S w f (fun x => ∑ i, q i x) =
      ∑ i, denseFinitePairing S w f (q i) := by
  simpa using denseFinitePairing_finset_sum_right S w f (Finset.univ : Finset ι) q

theorem denseFinitePairing_polynomial_eval_combination {α τ : Type}
    [Fintype τ] (S : Finset α) (w f : α → ℝ) (p : ℝ[X]) (q : τ → α → ℝ) (c : τ → ℝ) :
    denseFinitePairing S w f (fun x => p.eval (denseTestCombination q c x)) =
      ∑ n ∈ p.support, ∑ s : Fin n → τ,
        (p.coeff n * ∏ i, c (s i)) *
          denseFinitePairing S w f (denseTestMonomial q s) := by
  classical
  have heval : (fun x => p.eval (denseTestCombination q c x)) =
      fun x => ∑ n ∈ p.support, ∑ s : Fin n → τ,
        (p.coeff n * ∏ i, c (s i)) * denseTestMonomial q s x := by
    funext x
    exact densePolynomial_eval_combination p q c x
  rw [heval, denseFinitePairing_finset_sum_right S]
  apply Finset.sum_congr rfl
  intro n hn
  rw [denseFinitePairing_fintype_sum_right S]
  apply Finset.sum_congr rfl
  intro s hs
  unfold denseFinitePairing
  calc
    (∑ x ∈ S,
        w x * f x * ((p.coeff n * ∏ i, c (s i)) * denseTestMonomial q s x)) =
      ∑ x ∈ S,
        (p.coeff n * ∏ i, c (s i)) *
          (w x * f x * denseTestMonomial q s x) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
    _ = (p.coeff n * ∏ i, c (s i)) *
        ∑ x ∈ S,
          w x * f x * denseTestMonomial q s x := by
        exact (Finset.mul_sum S
          (fun x => w x * f x * denseTestMonomial q s x)
          (p.coeff n * ∏ i, c (s i))).symm

theorem denseCoefficientL1_monomial_sum {τ : Type} [Fintype τ]
    (c : τ → ℝ) (m : ℕ) :
    (∑ s : Fin m → τ, |∏ i, c (s i)|) = denseCoefficientL1 c ^ m := by
  classical
  unfold denseCoefficientL1
  rw [Fintype.sum_pow]
  apply Fintype.sum_congr
  intro s
  rw [Finset.abs_prod]

theorem denseAbsPairing_le_mul_weightedMass {α : Type}
    (S : Finset α) (w f e : α → ℝ) (hw : ∀ x ∈ S, 0 ≤ w x) {δ : ℝ}
    (he : ∀ x, |e x| ≤ δ) :
    |denseFinitePairing S w f e| ≤ δ * ∑ x ∈ S, w x * |f x| := by
  classical
  unfold denseFinitePairing
  calc
    |∑ x ∈ S, w x * f x * e x| ≤ ∑ x ∈ S, |w x * f x * e x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S, δ * (w x * |f x|) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul, abs_mul, abs_of_nonneg (hw x hx)]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left (he x) (mul_nonneg (hw x hx) (abs_nonneg _))
    _ = δ * ∑ x ∈ S, w x * |f x| := by rw [Finset.mul_sum]

theorem denseAbsPolynomialPairing_le {α τ : Type} [Fintype τ]
    (S : Finset α) {w f : α → ℝ} {p : ℝ[X]} {q : τ → α → ℝ} {c : τ → ℝ}
    (hc : denseCoefficientL1 c = 1) {η : ℝ}
    (hmono : ∀ (m : ℕ), m ≤ p.natDegree → ∀ s : Fin m → τ,
      |denseFinitePairing S w f (denseTestMonomial q s)| ≤ η) :
    |denseFinitePairing S w f (fun x => p.eval (denseTestCombination q c x))| ≤
      densePolynomialCoefficientL1 p * η := by
  classical
  rw [denseFinitePairing_polynomial_eval_combination S]
  calc
    |∑ n ∈ p.support, ∑ s : Fin n → τ,
        (p.coeff n * ∏ i, c (s i)) *
          denseFinitePairing S w f (denseTestMonomial q s)| ≤
      ∑ n ∈ p.support, |∑ s : Fin n → τ,
        (p.coeff n * ∏ i, c (s i)) *
          denseFinitePairing S w f (denseTestMonomial q s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support, |p.coeff n| * η := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        |∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              denseFinitePairing S w f (denseTestMonomial q s)| ≤
          ∑ s : Fin n → τ,
            |(p.coeff n * ∏ i, c (s i)) *
              denseFinitePairing S w f (denseTestMonomial q s)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s : Fin n → τ, |p.coeff n| * |∏ i, c (s i)| * η := by
          apply Finset.sum_le_sum
          intro s hs
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left
            (hmono n (Polynomial.le_natDegree_of_mem_supp n hn) s)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |p.coeff n| *
              (∑ s : Fin n → τ, |∏ i, c (s i)|) * η := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = |p.coeff n| * η := by
          rw [denseCoefficientL1_monomial_sum, hc, one_pow, mul_one]
    _ = densePolynomialCoefficientL1 p * η := by
      rw [densePolynomialCoefficientL1, Finset.sum_mul]

/-- The finite-dimensional minimax inequality used by the dense-model argument. -/
theorem finite_dense_model_minimax {X : Type} [Fintype X]
    (μ ρ ν : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ ν x)
    (C : Set (X → ℝ)) (hC : Convex ℝ C) (hCc : IsCompact C) (hne : C.Nonempty) :
    ∃ F : X → ℝ, (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ G ∈ C,
      ∑ x, μ x * (ρ x - F x) * G x ≤
        sSup ((fun G' : X → ℝ => ∑ x, μ x * (ν x - 1) * max (G' x) 0) '' C) := by
  classical
  let U : Set (X → ℝ) := Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)
  let payoff : (X → ℝ) → (X → ℝ) → ℝ := fun F G =>
    ∑ x, μ x * (ρ x - F x) * G x
  have hUconv : Convex ℝ U := by
    exact convex_Icc _ _
  have hUcompact : IsCompact U := by
    exact isCompact_Icc
  have hUne : U.Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    exact ⟨fun _ => le_rfl, fun _ => zero_le_one⟩
  have hCcFun : Continuous (fun G : X → ℝ =>
      ∑ x, μ x * (ν x - 1) * max (G x) 0) := by
    fun_prop
  have hsup : BddAbove
      ((fun G : X → ℝ => ∑ x, μ x * (ν x - 1) * max (G x) 0) '' C) :=
    (hCc.image hCcFun).bddAbove
  have hfy : ∀ G ∈ C, LowerSemicontinuousOn (fun F => payoff F G) U := by
    intro G hG
    have hcont : Continuous (fun F : X → ℝ => payoff F G) := by
      dsimp [payoff]
      fun_prop
    exact hcont.continuousOn.lowerSemicontinuousOn
  have hfy' : ∀ G ∈ C, QuasiconvexOn ℝ U (fun F => payoff F G) := by
    intro G hG
    let L := denseLinearFunctional (fun x => -(μ x * G x))
    have hrepr : (fun F : X → ℝ => payoff F G) =
        (fun F => L F +
          (∑ x ∈ (Finset.univ : Finset X), μ x * ρ x * G x)) := by
      funext F
      change (∑ x ∈ (Finset.univ : Finset X), μ x * (ρ x - F x) * G x) =
        (∑ x ∈ (Finset.univ : Finset X), -(μ x * G x) * F x) +
          ∑ x ∈ (Finset.univ : Finset X), μ x * ρ x * G x
      calc
        (∑ x ∈ (Finset.univ : Finset X), μ x * (ρ x - F x) * G x) =
            ∑ x ∈ (Finset.univ : Finset X),
              (μ x * ρ x * G x - μ x * G x * F x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = (∑ x ∈ (Finset.univ : Finset X), μ x * ρ x * G x) -
            ∑ x ∈ (Finset.univ : Finset X), μ x * G x * F x := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ x ∈ (Finset.univ : Finset X), -(μ x * G x) * F x) +
            ∑ x ∈ (Finset.univ : Finset X), μ x * ρ x * G x := by
          have hneg :
              (∑ x ∈ (Finset.univ : Finset X), -(μ x * G x) * F x) =
                -(∑ x ∈ (Finset.univ : Finset X), μ x * G x * F x) := by
            calc
              _ = ∑ x ∈ (Finset.univ : Finset X), -(μ x * G x * F x) := by
                apply Finset.sum_congr rfl
                intro x hx
                ring
              _ = -(∑ x ∈ (Finset.univ : Finset X), μ x * G x * F x) := by
                rw [Finset.sum_neg_distrib]
          rw [hneg]
          ring
    rw [hrepr]
    have hconv : ConvexOn ℝ U (fun F => L F) :=
      L.convexOn hUconv
    exact (hconv.add_const _).quasiconvexOn
  have hfx : ∀ F ∈ U, UpperSemicontinuousOn (fun G => payoff F G) C := by
    intro F hF
    have hcont : Continuous (fun G : X → ℝ => payoff F G) := by
      dsimp [payoff]
      fun_prop
    exact hcont.continuousOn.upperSemicontinuousOn
  have hfx' : ∀ F ∈ U, QuasiconcaveOn ℝ C (fun G => payoff F G) := by
    intro F hF
    let L := denseLinearFunctional (fun x => μ x * (ρ x - F x))
    have hrepr : (fun G : X → ℝ => payoff F G) = L := by
      funext G
      change (∑ x ∈ (Finset.univ : Finset X), μ x * (ρ x - F x) * G x) = _
      rfl
    rw [hrepr]
    exact (L.concaveOn hC).quasiconcaveOn
  obtain ⟨F, hF, G, hG, hsad⟩ :=
    Sion.exists_isSaddlePointOn hUne hUconv hUcompact hfy hfy' hC hne hCc hfx hfx'
  refine ⟨F, ?_, ?_⟩
  · intro x
    rcases Set.mem_Icc.mp hF with ⟨h0, h1⟩
    exact ⟨h0 x, h1 x⟩
  · intro G' hG'
    let F₀ : X → ℝ := fun x => if 0 ≤ G x then 1 else 0
    have hF₀ : F₀ ∈ U := by
      change (∀ x, 0 ≤ F₀ x) ∧ ∀ x, F₀ x ≤ 1
      constructor <;> intro x <;> dsimp [F₀] <;> split_ifs <;> norm_num
    have hsad' := hsad F₀ hF₀ G' hG'
    have hpoint : payoff F₀ G ≤
        ∑ x, μ x * (ν x - 1) * max (G x) 0 := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hxG : 0 ≤ G x
      · simp [F₀, hxG, max_eq_left hxG]
        have hρν := (hρ x).2
        have hterm := mul_le_mul_of_nonneg_right
          (sub_le_sub_right hρν 1) hxG
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hterm (hμ x)
      · have hxG' : G x ≤ 0 := le_of_not_ge hxG
        have hρ0 := (hρ x).1
        simp [F₀, hxG, max_eq_right hxG']
        have hprod : ρ x * G x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ0 hxG'
        simpa [mul_assoc] using mul_nonpos_of_nonneg_of_nonpos (hμ x) hprod
    have hGbound :
        (∑ x, μ x * (ν x - 1) * max (G x) 0) ≤
          sSup ((fun G' : X → ℝ => ∑ x, μ x * (ν x - 1) * max (G' x) 0) '' C) := by
      exact le_csSup hsup ⟨G, hG, rfl⟩
    calc
      payoff F G' ≤ payoff F₀ G := hsad'
      _ ≤ ∑ x, μ x * (ν x - 1) * max (G x) 0 := hpoint
      _ ≤ sSup ((fun G' : X → ℝ => ∑ x, μ x * (ν x - 1) * max (G' x) 0) '' C) := hGbound

end

namespace Prediction

theorem clip_abs_le_of_nonneg {K x : ℝ} (hK : 0 ≤ K) : |clip K x| ≤ K := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

def denseHarmonicNatSupport (X W : ℕ) : Finset ℕ :=
  (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)

def denseHarmonicIntSupport (X W : ℕ) : Finset ℤ :=
  (denseHarmonicNatSupport X W).image (fun n : ℕ => (n : ℤ))

theorem harmonicLaw_zero_of_not_mem_denseHarmonicIntSupport (X W : ℕ) (y : ℤ)
    (hy : y ∉ denseHarmonicIntSupport X W) : harmonicLaw X W y = 0 := by
  unfold harmonicLaw
  split
  · next h =>
    exfalso
    apply hy
    apply Finset.mem_image.mpr
    refine ⟨y.toNat, ?_, Int.toNat_of_nonneg h.1⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩
  · rfl

/-- A finite interval containing the support of the pivot harmonic law. -/
def finitePivotSupport {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n) : Finset ℤ :=
  Finset.Icc 0 ((A.X N i : ℕ) ^ 2 : ℤ)

theorem harmonicLaw_zero_of_not_mem_finitePivotSupport {n : ℕ}
    (A : Parameters n) (N : ℕ) (i : Fin n) (y : ℤ)
    (hy : y ∉ finitePivotSupport A N i) :
    harmonicLaw (A.X N i) (primorial (N + 1)) y = 0 := by
  unfold finitePivotSupport at hy
  unfold harmonicLaw
  split
  · next h =>
    exfalso
    apply hy
    rw [Finset.mem_Icc]
    constructor
    · exact h.1
    · have hycast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg h.1
      rw [← hycast]
      exact_mod_cast (le_of_lt h.2.2.1)
  · rfl

theorem Emu_eq_sum_finitePivotSupport {n : ℕ} (A : Parameters n) (N : ℕ)
    (i : Fin n) (f : ℤ → ℝ) :
    Emu A N i f = ∑ y ∈ finitePivotSupport A N i, mu A N i y * f y := by
  classical
  unfold Emu
  rw [tsum_eq_sum (s := finitePivotSupport A N i) (fun y hy => by
    rw [mu, harmonicLaw_zero_of_not_mem_finitePivotSupport A N i y hy]
    simp)]

theorem Emu_eq_sum_finitePivotSupportSort {n : ℕ} (A : Parameters n) (N : ℕ)
    (i : Fin n) (f : ℤ → ℝ) :
    Emu A N i f = ∑ y : finitePivotSupport A N i, mu A N i y * f y := by
  classical
  rw [Emu_eq_sum_finitePivotSupport]
  let S := finitePivotSupport A N i
  calc
    (∑ y ∈ S, mu A N i y * f y) =
        ∑ y ∈ S.attach, mu A N i y.1 * f y.1 := by
      exact (Finset.sum_attach S (fun y => mu A N i y * f y)).symm
    _ = ∑ y : S, mu A N i y * f y := by
      rw [← Finset.univ_eq_attach]

theorem Emu_add {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (f g : ℤ → ℝ) :
    Emu A N i (fun y => f y + g y) = Emu A N i f + Emu A N i g := by
  rw [Emu_eq_sum_finitePivotSupport A N i (fun y => f y + g y),
    Emu_eq_sum_finitePivotSupport A N i f, Emu_eq_sum_finitePivotSupport A N i g]
  simp [Finset.sum_add_distrib, mul_add]

theorem Emu_sub {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (f g : ℤ → ℝ) :
    Emu A N i (fun y => f y - g y) = Emu A N i f - Emu A N i g := by
  rw [Emu_eq_sum_finitePivotSupport A N i (fun y => f y - g y),
    Emu_eq_sum_finitePivotSupport A N i f, Emu_eq_sum_finitePivotSupport A N i g]
  simp [Finset.sum_sub_distrib, mul_sub]

theorem Emu_smul {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (a : ℝ) (f : ℤ → ℝ) :
    Emu A N i (fun y => a * f y) = a * Emu A N i f := by
  rw [Emu_eq_sum_finitePivotSupport A N i (fun y => a * f y),
    Emu_eq_sum_finitePivotSupport A N i f]
  calc
    (∑ y ∈ finitePivotSupport A N i, mu A N i y * (a * f y)) =
        ∑ y ∈ finitePivotSupport A N i, a * (mu A N i y * f y) := by
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = a * ∑ y ∈ finitePivotSupport A N i, mu A N i y * f y := by
      rw [Finset.mul_sum]

theorem Emu_congr {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    {f g : ℤ → ℝ} (hfg : ∀ y, f y = g y) : Emu A N i f = Emu A N i g := by
  rw [Emu_eq_sum_finitePivotSupport A N i f, Emu_eq_sum_finitePivotSupport A N i g]
  apply Finset.sum_congr rfl
  intro y hy
  rw [hfg y]

theorem Emu_const_one_eq_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (N : ℕ) (i : Fin K) :
    Emu MS.core.parameters N i (fun _ => (1 : ℝ)) = 1 := by
  classical
  let A := MS.core.parameters
  let X := A.X N i
  let W := primorial (N + 1)
  let S := denseHarmonicNatSupport X W
  have hW : 0 < W := primorial_pos _
  have hX : 4 * W ≤ X := MS.gapStage.valid_raw_cutoffs N i
  have hXpos : 0 < X := by omega
  have hnorm : 0 < harmonicNormalizer X W := by
    have h := OAI.RawHarmonicProbability.mass_pos X W hW hX
    simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, one_div, Nat.coprime_comm] using h
  have hzero : ∀ y ∉ denseHarmonicIntSupport X W,
      mu A N i y * (1 : ℝ) = 0 := by
    intro y hy
    rw [mu, harmonicLaw_zero_of_not_mem_denseHarmonicIntSupport X W y hy]
    simp
  rw [show Emu A N i (fun _ => (1 : ℝ)) =
      ∑ y ∈ denseHarmonicIntSupport X W, mu A N i y * 1 by
        unfold Emu
        rw [tsum_eq_sum (s := denseHarmonicIntSupport X W) hzero]]
  simp only [mu]
  simp only [A, X, W, mul_one]
  rw [show (∑ y ∈ denseHarmonicIntSupport X W, harmonicLaw X W y) =
      ∑ n ∈ S, harmonicLaw X W (n : ℤ) by
        unfold denseHarmonicIntSupport
        exact Finset.sum_image (s := S) (g := fun n : ℕ => (n : ℤ))
          (f := fun y : ℤ => harmonicLaw X W y)
          (by
            intro a ha b hb hab
            exact Int.ofNat_injective hab)]
  have hpoint : ∀ n ∈ S,
      harmonicLaw X W (n : ℤ) = (1 / (n : ℝ)) * (harmonicNormalizer X W)⁻¹ := by
    intro n hn
    have hnIco : n ∈ Finset.Ico X (X ^ 2) := (Finset.mem_filter.mp hn).1
    have hnrange := Finset.mem_Ico.mp hnIco
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le hXpos hnrange.1)
    have hcond : 0 ≤ (n : ℤ) ∧ X ≤ (n : ℤ).toNat ∧
        (n : ℤ).toNat < X ^ 2 ∧ Nat.Coprime n W := by
      refine ⟨by positivity, ?_, ?_, (Finset.mem_filter.mp hn).2⟩
      · simpa using hnrange.1
      · simpa using hnrange.2
    have hcond' : 0 ≤ (n : ℤ) ∧ X ≤ (n : ℤ).toNat ∧
        (n : ℤ).toNat < X ^ 2 ∧ Nat.Coprime (n : ℤ).toNat W := by
      simpa using hcond
    have hreal : ((↑((n : ℤ).toNat) : ℝ)) = (n : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hcond.1)
    rw [harmonicLaw, if_pos hcond']
    rw [hreal]
    field_simp [ne_of_gt hnpos, ne_of_gt hnorm]
  calc
    (∑ n ∈ S, harmonicLaw X W (n : ℤ)) =
        (∑ n ∈ S, (1 / (n : ℝ))) * (harmonicNormalizer X W)⁻¹ := by
      calc
        (∑ n ∈ S, harmonicLaw X W (n : ℤ)) =
            ∑ n ∈ S, (1 / (n : ℝ)) * (harmonicNormalizer X W)⁻¹ := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hpoint n hn
        _ = (∑ n ∈ S, 1 / (n : ℝ)) * (harmonicNormalizer X W)⁻¹ := by
          rw [Finset.sum_mul]
    _ = harmonicNormalizer X W * (harmonicNormalizer X W)⁻¹ := by
      rfl
    _ = 1 := by field_simp [ne_of_gt hnorm]

theorem harmonicNormalizer_nonneg (X W : ℕ) : 0 ≤ harmonicNormalizer X W := by
  unfold harmonicNormalizer
  apply Finset.sum_nonneg
  intro n hn
  positivity

theorem harmonicNatLaw_nonneg (X W y : ℕ) : 0 ≤ harmonicNatLaw X W y := by
  unfold harmonicNatLaw
  split_ifs with h
  · exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (harmonicNormalizer_nonneg X W))
  · exact le_rfl

theorem parameterTailProductLaw_nonneg {n : ℕ} (A : Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (σ : ℕ) : 0 ≤ parameterTailProductLaw A N T σ := by
  unfold parameterTailProductLaw
  apply tsum_nonneg
  intro t
  apply mul_nonneg
  · split_ifs <;> positivity
  · exact Finset.prod_nonneg fun j hj => harmonicNatLaw_nonneg _ _ _

theorem nu_nonneg {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) (y : ℤ) : 0 ≤ nu A N B y := by
  unfold nu nuB
  apply tsum_nonneg
  intro σ
  apply mul_nonneg
  · exact mul_nonneg (parameterTailProductLaw_nonneg A N B.2.val σ) (Nat.cast_nonneg _)
  · split_ifs <;> positivity

theorem harmonicLaw_nonneg {n : ℕ} (A : Parameters n) (N : ℕ)
    (i : Fin n) (y : ℤ) : 0 ≤ mu A N i y := by
  unfold mu harmonicLaw
  split_ifs with h
  · exact div_nonneg zero_le_one
      (mul_nonneg (Nat.cast_nonneg _) (harmonicNormalizer_nonneg _ _))
  · exact le_rfl

theorem Emu_mono {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    {f g : ℤ → ℝ} (hfg : ∀ y, f y ≤ g y) : Emu A N i f ≤ Emu A N i g := by
  rw [Emu_eq_sum_finitePivotSupport A N i f, Emu_eq_sum_finitePivotSupport A N i g]
  apply Finset.sum_le_sum
  intro y hy
  exact mul_le_mul_of_nonneg_left (hfg y) (harmonicLaw_nonneg A N i y)

theorem Emu_abs_le {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (f : ℤ → ℝ) : |Emu A N i f| ≤ Emu A N i (fun y => |f y|) := by
  rw [Emu_eq_sum_finitePivotSupport A N i f,
    Emu_eq_sum_finitePivotSupport A N i (fun y => |f y|)]
  calc
    |∑ y ∈ finitePivotSupport A N i, mu A N i y * f y| ≤
        ∑ y ∈ finitePivotSupport A N i, |mu A N i y * f y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y ∈ finitePivotSupport A N i, mu A N i y * |f y| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [abs_mul, abs_of_nonneg (harmonicLaw_nonneg A N i y)]

theorem rho_bounds {n r : ℕ} (A : Parameters n) (χ : ℕ → Fin r) (N : ℕ)
    (B : Block n) (a : ℚ) (c : Fin r) (y : ℤ) :
    0 ≤ rho A χ N B a c y ∧ rho A χ N B a c y ≤ nu A N B y := by
  unfold rho colorFactor
  have hν := nu_nonneg A N B y
  have hc := rationalColorIndicator_mem_Icc χ c
    ((height (A.ht N) B.set : ℚ) * a * (y : ℚ))
  constructor
  · exact mul_nonneg hν hc.1
  · simpa using mul_le_mul_of_nonneg_left hc.2 hν

theorem finitePivot_minimax {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (ρ ν : ℤ → ℝ) (hρ : ∀ y, 0 ≤ ρ y ∧ ρ y ≤ ν y)
    (C : Set (finitePivotSupport A N i → ℝ)) (hC : Convex ℝ C)
    (hCc : IsCompact C) (hne : C.Nonempty) :
    ∃ F : ℤ → ℝ,
      (∀ y, F y ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ G ∈ C,
        ∑ x : finitePivotSupport A N i,
          mu A N i x * (ρ x - F x) * G x ≤
          sSup ((fun G' : finitePivotSupport A N i → ℝ =>
            ∑ x : finitePivotSupport A N i,
              mu A N i x * (ν x - 1) * max (G' x) 0) '' C) := by
  classical
  let X := finitePivotSupport A N i
  letI : Fintype X := Finset.fintypeCoeSort X
  obtain ⟨M, hM, hMineq⟩ := finite_dense_model_minimax
    (fun x : X => mu A N i x) (fun x => ρ x) (fun x => ν x)
    (fun x => harmonicLaw_nonneg A N i x) (fun x => hρ x)
    C hC hCc hne
  let F : ℤ → ℝ := fun y => if hy : y ∈ X then M ⟨y, hy⟩ else 0
  refine ⟨F, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ X
    · simpa [F, hy] using hM ⟨y, hy⟩
    · simp [F, hy]
  · intro G hG
    have hsum := hMineq G hG
    simpa [F, X] using hsum

private abbrev DenseAllowedPolynomial {q sl : ℕ}
    (Dm : Finset (IntegerPolynomial sl)) (ι : Fin q ↪ Fin sl) :=
  {P : IntegerPolynomial q // MvPolynomial.rename ι P ∈ Dm}

private theorem finite_denseAllowedPolynomial {q sl : ℕ}
    (Dm : Finset (IntegerPolynomial sl)) (ι : Fin q ↪ Fin sl) :
    Finite (DenseAllowedPolynomial Dm ι) := by
  let embedding : DenseAllowedPolynomial Dm ι → {P : IntegerPolynomial sl // P ∈ Dm} :=
    fun P => ⟨MvPolynomial.rename ι P.1, P.2⟩
  apply Finite.of_injective embedding
  intro P P' h
  apply Subtype.ext
  exact MvPolynomial.rename_injective ι ι.injective (congrArg Subtype.val h)

private abbrev DenseTemplateCode (sl Q : ℕ) (Dm : Finset (IntegerPolynomial sl)) :=
  Σ q : Fin (sl + 1), Σ d : Fin (Q + 1), Σ ι : Fin q.val ↪ Fin sl,
    Σ D : DenseAllowedPolynomial Dm ι,
      {tests : Finset (DenseAllowedPolynomial Dm ι) //
        D ∈ tests ∧ ∀ P ∈ tests, P.1 ≠ 0}

private theorem cubeTemplate_ext {T U : CubeTemplate}
    (hq : T.q = U.q) (hd : T.d = U.d) (hD : HEq T.D U.D)
    (htests : HEq T.tests U.tests) : T = U := by
  cases T with
  | mk q d D tests hmem hne =>
    cases U with
    | mk q' d' D' tests' hmem' hne' =>
      cases hq
      cases hd
      cases hD
      cases htests
      rfl

private noncomputable def decodeDenseTemplate {sl Q : ℕ}
    {Dm : Finset (IntegerPolynomial sl)}
    (c : DenseTemplateCode sl Q Dm) : CubeTemplate where
  q := c.1.val
  d := c.2.1.val
  D := c.2.2.2.1.1
  tests := c.2.2.2.2.1.image Subtype.val
  D_mem := by
    classical
    apply Finset.mem_image.mpr
    exact ⟨c.2.2.2.1, c.2.2.2.2.2.1, rfl⟩
  tests_ne_zero := by
    classical
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨P', hP', rfl⟩
    exact c.2.2.2.2.2.2 P' hP'

private noncomputable def encodeDenseTemplate {sl Q : ℕ}
    (Dm : Finset (IntegerPolynomial sl)) (T : CubeTemplate)
    (ι : Fin T.q ↪ Fin sl) (hlisted : TestsListed Dm ι T.tests)
    (hd : T.d ≤ Q) : DenseTemplateCode sl Q Dm := by
  classical
  have hqCard : Fintype.card (Fin T.q) ≤ Fintype.card (Fin sl) :=
    Fintype.card_le_of_injective ι ι.injective
  have hq : T.q ≤ sl := by simpa using hqCard
  let D : DenseAllowedPolynomial Dm ι := ⟨T.D, hlisted T.D T.D_mem⟩
  let tests : Finset (DenseAllowedPolynomial Dm ι) :=
    T.tests.attach.image (fun P => ⟨P.1, hlisted P.1 P.2⟩)
  have hD : D ∈ tests := by
    apply Finset.mem_image.mpr
    refine ⟨⟨T.D, T.D_mem⟩, ?_, ?_⟩
    · simp
    · apply Subtype.ext
      rfl
  have htests : ∀ P ∈ tests, P.1 ≠ 0 := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨P', hP', rfl⟩
    exact T.tests_ne_zero P'.1 P'.2
  exact ⟨⟨T.q, by omega⟩, ⟨⟨T.d, by omega⟩, ⟨ι, ⟨D, ⟨tests, hD, htests⟩⟩⟩⟩⟩

private theorem decode_encodeDenseTemplate {sl Q : ℕ}
    (Dm : Finset (IntegerPolynomial sl)) (T : CubeTemplate)
    (ι : Fin T.q ↪ Fin sl) (hlisted : TestsListed Dm ι T.tests) (hd : T.d ≤ Q) :
    decodeDenseTemplate (sl := sl) (Q := Q) (Dm := Dm)
      (encodeDenseTemplate (sl := sl) (Q := Q) Dm T ι hlisted hd) = T := by
  classical
  cases T with
  | mk q d D tests hD htests =>
    apply cubeTemplate_ext
    · dsimp [decodeDenseTemplate, encodeDenseTemplate]
    · dsimp [decodeDenseTemplate, encodeDenseTemplate]
    · dsimp [decodeDenseTemplate, encodeDenseTemplate, DenseAllowedPolynomial]
      exact HEq.rfl
    · apply heq_of_eq
      dsimp [decodeDenseTemplate, encodeDenseTemplate, DenseAllowedPolynomial]
      rw [Finset.image_image]
      change tests.attach.image (fun P : {P // P ∈ tests} => P.1) = tests
      exact Finset.attach_image_val

theorem finite_allowed_cubeTemplates {sl Q : ℕ} (Dm : Finset (IntegerPolynomial sl)) :
    Finite {T : CubeTemplate // Allowed Dm T ∧ T.d ≤ Q} := by
  classical
  letI (q : Fin (sl + 1)) :
      Fintype (Fin q.val ↪ Fin sl) := by
    letI : Fintype (Fin q.val → Fin sl) := inferInstance
    letI : Finite (Fin q.val ↪ Fin sl) :=
      Finite.of_injective (fun e : Fin q.val ↪ Fin sl => (e : Fin q.val → Fin sl))
        (by
          intro e e' he
          exact DFunLike.coe_injective he)
    exact Fintype.ofFinite _
  letI (q : Fin (sl + 1)) (ι : Fin q.val ↪ Fin sl) :
      Fintype (DenseAllowedPolynomial Dm ι) := by
    letI : Finite (DenseAllowedPolynomial Dm ι) := finite_denseAllowedPolynomial Dm ι
    exact Fintype.ofFinite _
  letI (q : Fin (sl + 1)) (ι : Fin q.val ↪ Fin sl)
      (D : DenseAllowedPolynomial Dm ι) :
      Fintype {tests : Finset (DenseAllowedPolynomial Dm ι) //
        D ∈ tests ∧ ∀ P ∈ tests, P.1 ≠ 0} := by
    letI : Finite (DenseAllowedPolynomial Dm ι) := finite_denseAllowedPolynomial Dm ι
    letI : Fintype (DenseAllowedPolynomial Dm ι) := Fintype.ofFinite _
    letI : Fintype (Finset (DenseAllowedPolynomial Dm ι)) := inferInstance
    letI : Finite {tests : Finset (DenseAllowedPolynomial Dm ι) //
        D ∈ tests ∧ ∀ P ∈ tests, P.1 ≠ 0} :=
      Finite.of_injective Subtype.val Subtype.val_injective
    exact Fintype.ofFinite _
  letI (q : Fin (sl + 1)) (ι : Fin q.val ↪ Fin sl) :
      Fintype (Σ D : DenseAllowedPolynomial Dm ι,
        {tests : Finset (DenseAllowedPolynomial Dm ι) //
          D ∈ tests ∧ ∀ P ∈ tests, P.1 ≠ 0}) := inferInstance
  letI (q : Fin (sl + 1)) :
      Fintype (Σ ι : Fin q.val ↪ Fin sl,
        Σ D : DenseAllowedPolynomial Dm ι,
          {tests : Finset (DenseAllowedPolynomial Dm ι) //
            D ∈ tests ∧ ∀ P ∈ tests, P.1 ≠ 0}) := inferInstance
  letI (q : Fin (sl + 1)) :
      Fintype (Σ d : Fin (Q + 1), Σ ι : Fin q.val ↪ Fin sl,
        Σ D : DenseAllowedPolynomial Dm ι,
          {tests : Finset (DenseAllowedPolynomial Dm ι) //
            D ∈ tests ∧ ∀ P ∈ tests, P.1 ≠ 0}) := inferInstance
  letI : Fintype (DenseTemplateCode sl Q Dm) := by
    unfold DenseTemplateCode
    infer_instance
  letI : Finite (DenseTemplateCode sl Q Dm) := by
    infer_instance
  let decode := decodeDenseTemplate (sl := sl) (Q := Q) (Dm := Dm)
  have hrange : (Set.range decode).Finite := Set.finite_range _
  have hsub : {T : CubeTemplate | Allowed Dm T ∧ T.d ≤ Q} ⊆
      Set.range decode := by
    intro T hT
    obtain ⟨ι, hlisted⟩ := hT.1
    refine ⟨encodeDenseTemplate (sl := sl) (Q := Q) Dm T ι hlisted hT.2, ?_⟩
    simpa [decode] using decode_encodeDenseTemplate Dm T ι hlisted hT.2
  exact (hrange.subset hsub).to_subtype

end Prediction

end HindmanSumsProducts
