import HindmanSumsProducts.Prediction.PkgB2
import HindmanSumsProducts.Prediction.PkgD
import HindmanSumsProducts.Prediction.PkgB

/-!
# Helpers for `dual_products_orthogonal`

Shared definitions for the part lemmas stated above `dual_products_orthogonal` in `Results.lean`,
built on the `PkgB2` state machinery (replicated prime slots, occurrence rows, mixed base law):

* `opus_dpo_average`: the normalized joint average of `pkgB2_stateAverage`, for an arbitrary
  integrand (joint good prime event, `pkgB2_baseMass`).
* `opus_dpo_prefactor`: the Cauchy–Schwarz prefactor `E Ω`, `Ω = ∏_{copies of row s} (1 + ν)`.
* `opus_dpo_zeroTranslations`, `opus_dpo_untranslatedAverage`: the stage-`∅` state with every
  translation coordinate set to zero (the replica expansion of the original pairing).
* `opus_dpo_iterate`: the finite iteration of `|a_j|² ≤ C_j |a_{j+1}|`.
-/

namespace HindmanSumsProducts
namespace Prediction

open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

noncomputable section

/-- Normalized joint average over the replica prime law, conditioned on the joint good event, and
the mixed base-coordinate law `pkgB2_baseMass`, of an arbitrary integrand `F p x`.  This is the
averaging operator of `pkgB2_stateAverage`. -/
def opus_dpo_average {K sl b : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (F : (Fin (b * sl) → ℕ) → (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) → ℝ) : ℝ :=
  (independentPrimePoolProbability
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
    (pkgB2_goodPrimeEvent MS gap T hT N))⁻¹ *
  ∑' p : Fin (b * sl) → ℕ,
    independentPrimePoolMass
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p *
      (if pkgB2_goodPrimeEvent MS gap T hT N p then
        ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
          pkgB2_baseMass MS B T J0 gap hT N p x * F p x
       else 0)

/-- The Cauchy–Schwarz prefactor at stage `E` for the direction of the nonroot row `s`:
the normalized average of `Ω = ∏_{copies o of row s} (1 + ν(L_o))`.  It does not involve the
inputs. -/
def opus_dpo_prefactor {K sl b : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (s : pkgB2_Nonroot T) (N : ℕ) : ℝ :=
  opus_dpo_average MS B gap T J0 hT N fun p x =>
    ∏ o ∈ (Finset.univ.filter fun o : Fin (Fintype.card (pkgB2_Occurrence T E)) =>
        (pkgB2_occurrenceEnum T E o).1 = Sum.inr s),
      (1 + nu MS.core.parameters N B
        (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x))

/-- Set every translation coordinate (the `inr` part of `pkgB2_Coord`) to zero. -/
def opus_dpo_zeroTranslations {b : ℕ} (T : Fin b → CubeTemplate)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    Fin (Fintype.card (pkgB2_Coord T)) → ℤ :=
  fun i => Sum.elim (fun _ => x i) (fun _ => 0) (pkgB2_coordEnum T i)

/-- The stage-`∅` state before the translations are inserted: the integrand of
`pkgB2_stateAverage … ∅` evaluated with all translation coordinates zero. -/
def opus_dpo_untranslatedAverage {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) : ℝ :=
  opus_dpo_average MS B gap T J0 hT N fun p x =>
    pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p (opus_dpo_zeroTranslations T x)

/-- `pkgB2_stateAverage` is `opus_dpo_average` of the stage integrand. -/
theorem opus_dpo_stateAverage_eq {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (I : ∀ k, DualInput MS B (T k) N) :
    pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 E N I =
      opus_dpo_average MS B gap T J0 hT N
        (pkgB2_stateIntegrand MS B gap T hT J0 direction E N I) := by
  unfold pkgB2_stateAverage opus_dpo_average
  congr 1

/-- Downward iteration of `|a_j|² ≤ C_j |a_{j+1}|` from a uniformly small last term. -/
theorem opus_dpo_iterate {X : ℕ → Type*} (n : ℕ) (a : ℕ → (N : ℕ) → X N → ℝ)
    (hstep : ∀ j < n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ x : X N, |a j N x| ^ 2 ≤ C * |a (j + 1) N x|)
    (hlast : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x : X N, |a n N x| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x : X N, |a 0 N x| ≤ ε := by
  -- Downward induction: the claim at `n - m` for `m ≤ n`.
  suffices h : ∀ m ≤ n, ∀ ε > 0, ∀ᶠ N in atTop, ∀ x : X N, |a (n - m) N x| ≤ ε by
    simpa using h n le_rfl
  intro m
  induction m with
  | zero => intro _; simpa using hlast
  | succ m ih =>
    intro hm ε hε
    have hj : n - (m + 1) < n := by omega
    obtain ⟨C, hC, hCstep⟩ := hstep (n - (m + 1)) hj
    have hsucc : n - (m + 1) + 1 = n - m := by omega
    have hδ : 0 < ε ^ 2 / (C + 1) := by positivity
    filter_upwards [hCstep, ih (by omega) _ hδ] with N hN hsmall x
    have h1 := hN x
    rw [hsucc] at h1
    have h2 : C * |a (n - m) N x| ≤ C * (ε ^ 2 / (C + 1)) :=
      mul_le_mul_of_nonneg_left (hsmall x) hC
    have h3 : C * (ε ^ 2 / (C + 1)) ≤ ε ^ 2 := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg ε]
    have h4 : |a (n - (m + 1)) N x| ^ 2 ≤ ε ^ 2 := h1.trans (h2.trans h3)
    have h5 := sq_le_sq.mp h4
    simpa [abs_abs, abs_of_pos hε] using h5


/-! ### Translation insertion: generic finite product-law translation bounds -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinates other than `a`. -/
abbrev opus_dpo_PiExcept (a : ι) := {i : ι // i ∈ (Finset.univ : Finset ι).erase a}

/-- Split a coordinate vector into its value at `a` and the other coordinates. -/
def opus_dpo_piSplitAt (a : ι) : (ι → ℤ) ≃ ((opus_dpo_PiExcept a → ℤ) × ℤ) where
  toFun x := (fun i => x i.1, x a)
  invFun z i := if h : i = a then z.2 else
    z.1 ⟨i, Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩⟩
  left_inv := by
    intro x
    funext i
    by_cases h : i = a
    · subst h; simp
    · simp [h]
  right_inv := by
    intro z
    apply Prod.ext
    · funext i
      have hne : i.1 ≠ a := (Finset.mem_erase.mp i.2).1
      simp [hne]
    · simp

theorem opus_dpo_piSplitAt_symm_self (a : ι) (xr : opus_dpo_PiExcept a → ℤ) (z : ℤ) :
    (opus_dpo_piSplitAt a).symm (xr, z) a = z := by
  simp [opus_dpo_piSplitAt]

theorem opus_dpo_piSplitAt_symm_ne (a : ι) (xr : opus_dpo_PiExcept a → ℤ) (z : ℤ)
    (i : ι) (hi : i ≠ a) :
    (opus_dpo_piSplitAt a).symm (xr, z) i =
      xr ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩ := by
  simp [opus_dpo_piSplitAt, hi]

theorem opus_dpo_update_piSplitAt_symm (a : ι) (xr : opus_dpo_PiExcept a → ℤ) (z w : ℤ) :
    Function.update ((opus_dpo_piSplitAt a).symm (xr, z)) a w =
      (opus_dpo_piSplitAt a).symm (xr, w) := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp [opus_dpo_piSplitAt_symm_self]
  · rw [Function.update_of_ne hi, opus_dpo_piSplitAt_symm_ne a xr z i hi,
      opus_dpo_piSplitAt_symm_ne a xr w i hi]

/-- Isolate one coordinate of a finitely supported independent product law. -/
theorem opus_dpo_productLaw_tsum_splitAt (a : ι) (law : ι → ℤ → ℝ) (win : ι → Finset ℤ)
    (hzero : ∀ i z, z ∉ win i → law i z = 0) (F : (ι → ℤ) → ℝ) :
    (∑' x : ι → ℤ, (∏ i, law i (x i)) * F x) =
      ∑' xr : opus_dpo_PiExcept a → ℤ,
        (∏ i : opus_dpo_PiExcept a, law i.1 (xr i)) *
          ∑' z : ℤ, law a z * F ((opus_dpo_piSplitAt a).symm (xr, z)) := by
  classical
  let e := opus_dpo_piSplitAt a
  let full (x : ι → ℤ) : ℝ := (∏ i, law i (x i)) * F x
  let rest (xr : opus_dpo_PiExcept a → ℤ) : ℝ :=
    ∏ i : opus_dpo_PiExcept a, law i.1 (xr i)
  have hprod (x : ι → ℤ) : (∏ i, law i (x i)) = rest (e x).1 * law a (e x).2 := by
    change (∏ i, law i (x i)) = rest (fun i => x i.1) * law a (x a)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    congr 1
    exact Finset.prod_subtype ((Finset.univ : Finset ι).erase a)
      (by intro i; rfl) (fun i => law i (x i))
  have hfullzero (x : ι → ℤ) (hx : x ∉ Fintype.piFinset win) : full x = 0 := by
    have hnot : ¬∀ i, x i ∈ win i := by
      intro hall
      exact hx (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hw : (∏ j, law j (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hzero i (x i) hi)
    simp [full, hw]
  have hs : Summable full := summable_of_ne_finset_zero hfullzero
  have hs' : Summable (fun z : (opus_dpo_PiExcept a → ℤ) × ℤ => full (e.symm z)) :=
    hs.comp_injective e.symm.injective
  calc
    _ = ∑' z : (opus_dpo_PiExcept a → ℤ) × ℤ, full (e.symm z) :=
      (e.symm.tsum_eq full).symm
    _ = ∑' xr : opus_dpo_PiExcept a → ℤ, ∑' z : ℤ, full (e.symm (xr, z)) := hs'.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro xr
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      dsimp [full]
      rw [hprod]
      simp only [e.apply_symm_apply, mul_assoc]
      rfl

/-- Translating one coordinate by an amount independent of that coordinate changes a bounded
expectation under a product law by at most the bound times the coordinate's translation error. -/
theorem opus_dpo_single_translate (law : ι → ℤ → ℝ) (win : ι → Finset ℤ)
    (hzero : ∀ i z, z ∉ win i → law i z = 0) (hnonneg : ∀ i z, 0 ≤ law i z)
    (hsum : ∀ i, ∑ z ∈ win i, law i z = 1)
    (a : ι) (t : (ι → ℤ) → ℤ) (ht : ∀ x z, t (Function.update x a z) = t x)
    (G : (ι → ℤ) → ℝ) (Bd : ℝ) (hG : ∀ x, |G x| ≤ Bd)
    (η : ℝ) (hη : ∀ x, (∀ i, i ≠ a → x i ∈ win i) →
      ∑' z, |law a (z - t x) - law a z| ≤ η) :
    |(∑' x : ι → ℤ, (∏ i, law i (x i)) * G (Function.update x a (x a + t x))) -
      ∑' x : ι → ℤ, (∏ i, law i (x i)) * G x| ≤ Bd * η := by
  classical
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hG 0)
  let e := opus_dpo_piSplitAt a
  rw [opus_dpo_productLaw_tsum_splitAt a law win hzero,
    opus_dpo_productLaw_tsum_splitAt a law win hzero]
  let Wr : Finset (opus_dpo_PiExcept a → ℤ) := Fintype.piFinset fun i => win i.1
  let R : (opus_dpo_PiExcept a → ℤ) → ℝ := fun xr => ∏ i : opus_dpo_PiExcept a, law i.1 (xr i)
  have hRzero : ∀ xr ∉ Wr, R xr = 0 := by
    intro xr hxr
    have hnot : ¬∀ i, xr i ∈ win i.1 := by
      intro hall
      exact hxr (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero i.1 (xr i) hi)
  have hRnonneg : ∀ xr, 0 ≤ R xr := fun xr =>
    Finset.prod_nonneg fun i _ => hnonneg i.1 (xr i)
  have hRsum : ∑ xr ∈ Wr, R xr = 1 := by
    have h := (Finset.prod_univ_sum (fun i : opus_dpo_PiExcept a => win i.1)
      (fun i z => law i.1 z)).symm
    rw [h]
    exact Finset.prod_eq_one fun i _ => hsum i.1
  -- the translated inner integral
  have hupd (xr : opus_dpo_PiExcept a → ℤ) (z : ℤ) :
      Function.update (e.symm (xr, z)) a (e.symm (xr, z) a + t (e.symm (xr, z))) =
        e.symm (xr, z + t (e.symm (xr, 0))) := by
    have hz : e.symm (xr, z) = Function.update (e.symm (xr, 0)) a z :=
      (opus_dpo_update_piSplitAt_symm a xr 0 z).symm
    have htz : t (e.symm (xr, z)) = t (e.symm (xr, 0)) := by rw [hz, ht]
    rw [htz, opus_dpo_piSplitAt_symm_self, opus_dpo_update_piSplitAt_symm]
  have hinner (xr : opus_dpo_PiExcept a → ℤ) (hxr : xr ∈ Wr) :
      |(∑' z : ℤ, law a z * G (Function.update (e.symm (xr, z)) a
          (e.symm (xr, z) a + t (e.symm (xr, z))))) -
        ∑' z : ℤ, law a z * G (e.symm (xr, z))| ≤ Bd * η := by
    simp_rw [hupd]
    set t' := t (e.symm (xr, 0)) with ht'
    set g : ℤ → ℝ := fun w => G (e.symm (xr, w)) with hg
    have hshift : (∑' z : ℤ, law a z * g (z + t')) = ∑' z : ℤ, law a (z - t') * g z := by
      rw [← (Equiv.subRight t').tsum_eq (fun z => law a z * g (z + t'))]
      apply tsum_congr
      intro z
      simp
    change |(∑' z : ℤ, law a z * g (z + t')) - ∑' z : ℤ, law a z * g z| ≤ Bd * η
    rw [hshift]
    let S : Finset ℤ := win a ∪ (win a).image (· + t')
    have hS1 : ∀ z ∉ S, law a (z - t') = 0 := by
      intro z hz
      apply hzero
      intro hm
      apply hz
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z - t', hm, by ring⟩)
    have hS2 : ∀ z ∉ S, law a z = 0 := by
      intro z hz
      apply hzero
      intro hm
      exact hz (Finset.mem_union_left _ hm)
    rw [tsum_eq_sum (s := S) (fun z hz => by rw [hS1 z hz, zero_mul]),
      tsum_eq_sum (s := S) (fun z hz => by rw [hS2 z hz, zero_mul]),
      ← Finset.sum_sub_distrib]
    have hηx := hη (e.symm (xr, 0)) (by
      intro i hi
      rw [opus_dpo_piSplitAt_symm_ne a xr 0 i hi]
      exact Fintype.mem_piFinset.mp hxr ⟨i, _⟩)
    rw [← ht', tsum_eq_sum (s := S) (fun z hz => by rw [hS1 z hz, hS2 z hz]; simp)] at hηx
    calc
      |∑ z ∈ S, (law a (z - t') * g z - law a z * g z)| ≤
          ∑ z ∈ S, |law a (z - t') * g z - law a z * g z| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ z ∈ S, |law a (z - t') - law a z| * |g z| := by
        apply Finset.sum_congr rfl
        intro z _
        rw [← sub_mul, abs_mul]
      _ ≤ ∑ z ∈ S, |law a (z - t') - law a z| * Bd := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (hG _) (abs_nonneg _)
      _ = (∑ z ∈ S, |law a (z - t') - law a z|) * Bd := by rw [Finset.sum_mul]
      _ ≤ η * Bd := mul_le_mul_of_nonneg_right hηx hBd
      _ = Bd * η := by ring
  rw [tsum_eq_sum (s := Wr) (fun xr hxr => by
      change R xr * _ = 0
      rw [hRzero xr hxr, zero_mul]),
    tsum_eq_sum (s := Wr) (fun xr hxr => by
      change R xr * _ = 0
      rw [hRzero xr hxr, zero_mul]),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ xr ∈ Wr, |R xr * (∑' z : ℤ, law a z * G (Function.update (e.symm (xr, z)) a
          (e.symm (xr, z) a + t (e.symm (xr, z))))) -
          R xr * ∑' z : ℤ, law a z * G (e.symm (xr, z))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ xr ∈ Wr, R xr * |(∑' z : ℤ, law a z * G (Function.update (e.symm (xr, z)) a
          (e.symm (xr, z) a + t (e.symm (xr, z))))) -
          ∑' z : ℤ, law a z * G (e.symm (xr, z))| := by
      apply Finset.sum_congr rfl
      intro xr _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hRnonneg xr)]
    _ ≤ ∑ xr ∈ Wr, R xr * (Bd * η) := by
      apply Finset.sum_le_sum
      intro xr hxr
      exact mul_le_mul_of_nonneg_left (hinner xr hxr) (hRnonneg xr)
    _ = Bd * η := by rw [← Finset.sum_mul, hRsum, one_mul]

/-- Translating every coordinate by amounts depending only on a set `Tr` of untranslated
coordinates changes a bounded product-law expectation by at most the bound times the sum of the
coordinate translation errors. -/
theorem opus_dpo_hybrid_translate (law : ι → ℤ → ℝ) (win : ι → Finset ℤ)
    (hzero : ∀ i z, z ∉ win i → law i z = 0) (hnonneg : ∀ i z, 0 ≤ law i z)
    (hsum : ∀ i, ∑ z ∈ win i, law i z = 1)
    (Tr : Finset ι) (δ : (ι → ℤ) → (ι → ℤ))
    (hδTr : ∀ x i, i ∈ Tr → δ x i = 0)
    (hδdep : ∀ x x', (∀ i ∈ Tr, x i = x' i) → δ x = δ x')
    (G : (ι → ℤ) → ℝ) (Bd : ℝ) (hG : ∀ x, |G x| ≤ Bd)
    (η : ℝ) (hη0 : 0 ≤ η)
    (hη : ∀ x c, (∀ i ∈ Tr, x i ∈ win i) → ∑' z, |law c (z - δ x c) - law c z| ≤ η) :
    |(∑' x : ι → ℤ, (∏ i, law i (x i)) * G (x + δ x)) -
      ∑' x : ι → ℤ, (∏ i, law i (x i)) * G x| ≤ Bd * (Fintype.card ι * η) := by
  classical
  let δS : Finset ι → (ι → ℤ) → (ι → ℤ) := fun S x i => if i ∈ S then δ x i else 0
  suffices h : ∀ S : Finset ι,
      |(∑' x : ι → ℤ, (∏ i, law i (x i)) * G (x + δS S x)) -
        ∑' x : ι → ℤ, (∏ i, law i (x i)) * G x| ≤ Bd * (S.card * η) by
    have hu := h Finset.univ
    have hδuniv : ∀ x, δS Finset.univ x = δ x := by
      intro x
      funext i
      simp [δS]
    simp only [hδuniv, Finset.card_univ] at hu
    exact hu
  intro S
  induction S using Finset.induction_on with
  | empty =>
    have h0 : ∀ x, x + δS ∅ x = x := by
      intro x
      funext i
      simp [δS]
    simp [h0]
  | insert c S hc ih =>
    let H : (ι → ℤ) → ℝ := fun y => G (y + δS S y)
    have hkey : ∀ x, G (x + δS (insert c S) x) = H (Function.update x c (x c + δ x c)) := by
      intro x
      by_cases hcT : c ∈ Tr
      · have h0 : δ x c = 0 := hδTr x c hcT
        simp only [H, h0, add_zero, Function.update_eq_self]
        congr 1
        funext i
        by_cases hi : i = c
        · subst hi
          simp [δS, h0]
        · simp [δS, hi]
      · have hdep : δ (Function.update x c (x c + δ x c)) = δ x := by
          apply hδdep
          intro i hi
          have hne : i ≠ c := by
            rintro rfl
            exact hcT hi
          rw [Function.update_of_ne hne]
        simp only [H]
        congr 1
        funext i
        by_cases hi : i = c
        · subst hi
          simp [δS, hc, hdep]
        · simp [δS, hi, Function.update_of_ne hi, hdep]
    have ht : ∀ x z, (fun y => δ y c) (Function.update x c z) = (fun y => δ y c) x := by
      intro x z
      by_cases hcT : c ∈ Tr
      · simp [hδTr _ c hcT]
      · simp only
        rw [hδdep (Function.update x c z) x]
        intro i hi
        have hne : i ≠ c := by
          rintro rfl
          exact hcT hi
        rw [Function.update_of_ne hne]
    have hη' : ∀ x, (∀ i, i ≠ c → x i ∈ win i) →
        ∑' z, |law c (z - (fun y => δ y c) x) - law c z| ≤ η := by
      intro x hx
      by_cases hcT : c ∈ Tr
      · simp [hδTr x c hcT, hη0]
      · apply hη x c
        intro i hi
        apply hx
        rintro rfl
        exact hcT hi
    have hsingle := opus_dpo_single_translate law win hzero hnonneg hsum c
      (fun y => δ y c) ht H Bd (fun y => hG _) η hη'
    have hsplit :
        (∑' x : ι → ℤ, (∏ i, law i (x i)) * G (x + δS (insert c S) x)) -
          ∑' x : ι → ℤ, (∏ i, law i (x i)) * G x =
        ((∑' x : ι → ℤ, (∏ i, law i (x i)) *
            H (Function.update x c (x c + (fun y => δ y c) x))) -
          ∑' x : ι → ℤ, (∏ i, law i (x i)) * H x) +
        ((∑' x : ι → ℤ, (∏ i, law i (x i)) * G (x + δS S x)) -
          ∑' x : ι → ℤ, (∏ i, law i (x i)) * G x) := by
      simp only [hkey]
      ring
    rw [hsplit]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ Bd * η + Bd * (S.card * η) := add_le_add hsingle ih
      _ = Bd * ((insert c S).card * η) := by
        rw [Finset.card_insert_of_notMem hc]
        push_cast
        ring

end Generic

/-! ### Translation insertion: bounds on the stage integrand -/

theorem opus_dpo_nu_le {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (N : ℕ) (y : ℤ) :
    nu MS.core.parameters N B y ≤ (pkgB2_blockScale MS.core.parameters B N : ℝ) := by
  classical
  have hNorm (j : Fin K) :
      0 < harmonicNormalizer (MS.core.parameters.X N j) (primorial (N + 1)) :=
    harmonicNormalizer_pos (MS.core.parameters.X N j) (primorial (N + 1)) (primorial_pos _)
      (MS.gapStage.valid_raw_cutoffs N j)
  let Bound : ℕ := ∏ j ∈ B.2.val, (MS.core.parameters.X N j) ^ 2
  let Sig : Finset ℕ := Finset.range (Bound + 1)
  have hTailZero (σ : ℕ) (hσ : σ ∉ Sig) :
      parameterTailProductLaw MS.core.parameters N B.2.val σ = 0 := by
    apply parameterTailProductLaw_zero_of_gt MS.core.parameters N B.2.val σ
    have hnot : ¬ σ < Bound + 1 := by simpa [Sig, Finset.mem_range] using hσ
    change Bound < σ
    omega
  have hTailNonneg (σ : ℕ) : 0 ≤ parameterTailProductLaw MS.core.parameters N B.2.val σ :=
    pkgD_parameterTailProductLaw_nonneg MS.core.parameters N B.2.val (fun j => hNorm j) σ
  have hTailSum : ∑ σ ∈ Sig, parameterTailProductLaw MS.core.parameters N B.2.val σ = 1 := by
    have htotal := parameterTailProductLaw_tsum_one MS.core.parameters N B.2.val
      (fun j => MS.core.parameters.Xpos N j) (fun j => hNorm j)
    rw [tsum_eq_sum (s := Sig) (fun σ hσ => hTailZero σ hσ)] at htotal
    exact htotal
  unfold nu nuB
  rw [tsum_eq_sum (s := Sig) (fun σ hσ => by rw [hTailZero σ hσ]; ring)]
  have hBoundle : (Bound : ℝ) ≤ (pkgB2_blockScale MS.core.parameters B N : ℝ) := by
    have : Bound ≤ pkgB2_blockScale MS.core.parameters B N := by
      dsimp [pkgB2_blockScale, Bound]
      omega
    exact_mod_cast this
  calc
    _ ≤ ∑ σ ∈ Sig, parameterTailProductLaw MS.core.parameters N B.2.val σ * (Bound : ℝ) := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hσB : (σ : ℝ) ≤ Bound := by
        have : σ < Bound + 1 := Finset.mem_range.mp hσ
        exact_mod_cast (by omega : σ ≤ Bound)
      have hL := hTailNonneg σ
      split_ifs
      · rw [mul_one]
        exact mul_le_mul_of_nonneg_left hσB hL
      · rw [mul_zero]
        exact mul_nonneg hL (Nat.cast_nonneg _)
    _ = (Bound : ℝ) := by rw [← Finset.sum_mul, hTailSum, one_mul]
    _ ≤ _ := hBoundle

theorem opus_dpo_stateFactor_abs_le {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ)
    (o : Fin (Fintype.card (pkgB2_Occurrence T E))) :
    |pkgB2_stateFactor MS B gap T hT J0 direction E N I p x o| ≤
      1 + (pkgB2_blockScale MS.core.parameters B N : ℝ) := by
  classical
  have hnu0 := fun y => pkgB_nu_nonneg MS.core.parameters N B y
  have hnuV := fun y => opus_dpo_nu_le MS B N y
  simp only [pkgB2_stateFactor]
  split
  · rename_i y _
    apply abs_le.mpr
    constructor
    · linarith [hnu0 (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x),
        hnuV (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x)]
    · linarith [hnu0 (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x),
        hnuV (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x)]
  · split_ifs
    · rw [abs_of_nonneg (by linarith [hnu0 (pkgB2_stateRowValue MS T hT J0 gap direction
          E N p o x)])]
      linarith [hnuV (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x)]
    · rename_i r _ _
      exact ((I r.1).g_bound _ _ _).trans (by
        linarith [hnuV (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x)])

theorem opus_dpo_stateIntegrand_abs_le {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    |pkgB2_stateIntegrand MS B gap T hT J0 direction E N I p x| ≤
      (1 + (pkgB2_blockScale MS.core.parameters B N : ℝ)) ^
        Fintype.card (Fin (Fintype.card (pkgB2_Occurrence T E))) := by
  classical
  unfold pkgB2_stateIntegrand
  rw [abs_mul]
  have he : |(if E = ∅ then ∏ k : Fin b, (I k).e (pkgB2_repPrimeProject hT p k) else 1)| ≤ 1 := by
    split_ifs
    · rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _k : Fin b, (1 : ℝ) :=
          Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) (fun k _ => (I k).e_bound _)
        _ = 1 := Finset.prod_const_one
    · simp
  have hprod : |∏ o, pkgB2_stateFactor MS B gap T hT J0 direction E N I p x o| ≤
      (1 + (pkgB2_blockScale MS.core.parameters B N : ℝ)) ^
        Fintype.card (Fin (Fintype.card (pkgB2_Occurrence T E))) := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _o : Fin (Fintype.card (pkgB2_Occurrence T E)),
          (1 + (pkgB2_blockScale MS.core.parameters B N : ℝ)) :=
        Finset.prod_le_prod₀ (fun o _ => abs_nonneg _)
          (fun o _ => opus_dpo_stateFactor_abs_le MS B gap T hT J0 direction E N I p x o)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  calc
    _ ≤ 1 * (1 + (pkgB2_blockScale MS.core.parameters B N : ℝ)) ^
        Fintype.card (Fin (Fintype.card (pkgB2_Occurrence T E))) :=
      mul_le_mul he hprod (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Comparison of two normalized averages from an inner bound on good prime tuples. -/
theorem opus_dpo_average_sub_le {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (F F' : (Fin (b * sl) → ℕ) → (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ p, pkgB2_goodPrimeEvent MS gap T hT N p →
      |(∑' x, pkgB2_baseMass MS B T J0 gap hT N p x * F p x) -
        ∑' x, pkgB2_baseMass MS B T J0 gap hT N p x * F' p x| ≤ δ) :
    |opus_dpo_average MS B gap T J0 hT N F - opus_dpo_average MS B gap T J0 hT N F'| ≤ δ := by
  classical
  let lo : Fin (b * sl) → ℕ := fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin (b * sl) → ℕ := fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let Good := pkgB2_goodPrimeEvent MS gap T hT N
  let m : (Fin (b * sl) → ℕ) → ℝ := independentPrimePoolMass lo hi
  let Pset : Finset (Fin (b * sl) → ℕ) := Fintype.piFinset fun i => Finset.range (hi i)
  have hm0 : ∀ p, 0 ≤ m p := by
    intro p
    apply Finset.prod_nonneg
    intro i _
    unfold primePoolLaw
    split_ifs
    · apply div_nonneg (by positivity)
      unfold primePoolMass
      exact Finset.sum_nonneg fun q _ => by positivity
    · exact le_refl 0
  have hmzero : ∀ p ∉ Pset, m p = 0 := by
    intro p hp
    have hnot : ¬∀ i, p i ∈ Finset.range (hi i) := by
      intro hall
      exact hp (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi'⟩ := not_forall.mp hnot
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold primePoolLaw
    rw [if_neg]
    intro hc
    exact hi' (Finset.mem_range.mpr hc.2.1)
  let IF : (Fin (b * sl) → ℕ) → ℝ := fun p =>
    ∑' x, pkgB2_baseMass MS B T J0 gap hT N p x * F p x
  let IF' : (Fin (b * sl) → ℕ) → ℝ := fun p =>
    ∑' x, pkgB2_baseMass MS B T J0 gap hT N p x * F' p x
  have hP : independentPrimePoolProbability lo hi Good =
      ∑ p ∈ Pset, m p * (if Good p then 1 else 0) := by
    unfold independentPrimePoolProbability
    rw [tsum_eq_sum (s := Pset) (fun p hp => by
      change m p * _ = 0
      rw [hmzero p hp, zero_mul])]
  have hP0 : 0 ≤ independentPrimePoolProbability lo hi Good := by
    rw [hP]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hm0 p) (by split_ifs <;> norm_num)
  have hA (G' : (Fin (b * sl) → ℕ) → ℝ) :
      (∑' p : Fin (b * sl) → ℕ, independentPrimePoolMass lo hi p *
        (if pkgB2_goodPrimeEvent MS gap T hT N p then G' p else 0)) =
      ∑ p ∈ Pset, m p * (if Good p then G' p else 0) := by
    rw [tsum_eq_sum (s := Pset) (fun p hp => by
      change m p * _ = 0
      rw [hmzero p hp, zero_mul])]
  unfold opus_dpo_average
  change |(independentPrimePoolProbability lo hi Good)⁻¹ *
      (∑' p : Fin (b * sl) → ℕ, independentPrimePoolMass lo hi p *
        (if pkgB2_goodPrimeEvent MS gap T hT N p then IF p else 0)) -
    (independentPrimePoolProbability lo hi Good)⁻¹ *
      (∑' p : Fin (b * sl) → ℕ, independentPrimePoolMass lo hi p *
        (if pkgB2_goodPrimeEvent MS gap T hT N p then IF' p else 0))| ≤ δ
  rw [hA IF, hA IF', ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hP0)]
  have hsum : |∑ p ∈ Pset, (m p * (if Good p then IF p else 0) -
      m p * (if Good p then IF' p else 0))| ≤
      δ * independentPrimePoolProbability lo hi Good := by
    rw [hP, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro p _
    by_cases hg : Good p
    · simp only [hg, if_true, mul_one]
      rw [← mul_sub, abs_mul, abs_of_nonneg (hm0 p), mul_comm δ]
      exact mul_le_mul_of_nonneg_left (h p hg) (hm0 p)
    · simp [hg]
  by_cases hPz : independentPrimePoolProbability lo hi Good = 0
  · rw [hPz, inv_zero, zero_mul]
    exact hδ
  · calc
      _ ≤ (independentPrimePoolProbability lo hi Good)⁻¹ *
          (δ * independentPrimePoolProbability lo hi Good) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hP0)
      _ = δ := by field_simp


/-! ### Translation insertion: the inserted translations as a coordinate shift -/

/-- The displacement of the pivot and of the upper original shifts produced by the inserted
translations, as a function of the structured coordinates (only the side-`0` translation
coordinates are read). -/
def opus_dpo_shiftS {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (X : pkgB2_Coord T → ℤ) : pkgB2_Coord T → ℤ :=
  Sum.elim
    (Sum.elim
      (fun _ => ∑ r : pkgB2_Nonroot T,
        pkgB2_directionLift (T r.1).d (direction r) 0 * (M r.1 : ℤ) * X (.inr (r, 0)))
      (fun kjs => if kjs.2.2 = 1 then
        ∑ r : pkgB2_Nonroot T, (if r.1 = kjs.1 then
          pkgB2_directionLift (T r.1).d (direction r) (kjs.2.1.val + 1) else 0) *
            X (.inr (r, 0))
        else 0))
    (fun _ => 0)

/-- The same displacement on enumerated coordinate vectors. -/
def opus_dpo_shift {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) : Fin (Fintype.card (pkgB2_Coord T)) → ℤ :=
  fun i => opus_dpo_shiftS T M direction (fun c => x ((pkgB2_coordEnum T).symm c))
    (pkgB2_coordEnum T i)

theorem opus_dpo_sum_coord {b : ℕ} (T : Fin b → CubeTemplate) (f : pkgB2_Coord T → ℤ) :
    ∑ c, f c = (∑ old : pkgB2_OldCoord T, f (.inl old)) +
      ∑ tr : pkgB2_Nonroot T × Fin 2, f (.inr tr) := by
  rw [← Fintype.sum_sum_type]
  refine Finset.sum_congr ?_ (fun c _ => by cases c <;> rfl)
  ext c
  simp only [Finset.mem_univ]

theorem opus_dpo_oldCoeff_same {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (s : pkgB2_Nonroot T) (j : Fin (T s.1).d) (side : Fin 2) :
    pkgB2_oldCoefficient T M (.inr s) (.inr ⟨s.1, (j, side)⟩) =
      if j ∈ s.2.1 then (if side.val = 0 then -M s.1 else M s.1) else 0 := by
  unfold pkgB2_oldCoefficient
  exact dif_pos rfl

theorem opus_dpo_oldCoeff_ne {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (s : pkgB2_Nonroot T) (k : Fin b) (hk : k ≠ s.1) (j : Fin (T k).d) (side : Fin 2) :
    pkgB2_oldCoefficient T M (.inr s) (.inr ⟨k, (j, side)⟩) = 0 := by
  unfold pkgB2_oldCoefficient
  exact dif_neg hk

/-- The inserted translations act on every stage-`∅` row as the coordinate shift. -/
theorem opus_dpo_coeff_shift {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (o : pkgB2_Occurrence T ∅) (X : pkgB2_Coord T → ℤ) :
    ∑ c, pkgB2_occurrenceCoefficientInt T M direction ∅ o c * X c =
      ∑ c, pkgB2_occurrenceCoefficientInt T M direction ∅ o c *
        Sum.elim (fun old => X (.inl old) + opus_dpo_shiftS T M direction X (.inl old))
          (fun _ => 0) c := by
  classical
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h1v : (1 : Fin 2).val ≠ 0 := by decide
  have hcoeffT (r : pkgB2_Nonroot T) (side : Fin 2) :
      pkgB2_occurrenceCoefficientInt T M direction ∅ o (.inr (r, side)) =
        if side = 0 then pkgB2_response T (fun k => (M k : ℤ)) r
          (pkgB2_directionLift (T r.1).d (direction r)) o.1 else 0 := by
    simp [pkgB2_occurrenceCoefficientInt, pkgB2_copyCoeffInt]
  have hcoeffO (old : pkgB2_OldCoord T) :
      pkgB2_occurrenceCoefficientInt T M direction ∅ o (.inl old) =
        pkgB2_oldCoefficient T (fun k => (M k : ℤ)) o.1 old := by
    simp [pkgB2_occurrenceCoefficientInt, pkgB2_copyCoeffInt]
  rw [opus_dpo_sum_coord, opus_dpo_sum_coord]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero, mul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, hcoeffT, hcoeffO, if_pos rfl, h01.symm, if_false, zero_mul,
    add_zero]
  rcases o with ⟨t, η⟩
  cases t with
  | inl u =>
    simp [pkgB2_oldCoefficient, opus_dpo_shiftS, pkgB2_response, mul_comm, mul_left_comm,
      mul_assoc]
  | inr s =>
    change ∑ r : pkgB2_Nonroot T, pkgB2_response T (fun k => (M k : ℤ)) r
        (pkgB2_directionLift (T r.1).d (direction r)) (.inr s) * X (.inr (r, 0)) =
      ∑ old : pkgB2_OldCoord T, pkgB2_oldCoefficient T (fun k => (M k : ℤ)) (.inr s) old *
        opus_dpo_shiftS T M direction X (.inl old)
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    rw [Finset.sum_eq_single s.1 (fun k _ hk => by
      apply Finset.sum_eq_zero
      intro js _
      rw [opus_dpo_oldCoeff_ne T _ s k hk js.1 js.2, zero_mul]) (by simp)]
    have hU : (∑ u : Unit, pkgB2_oldCoefficient T (fun k => (M k : ℤ)) (.inr s) (.inl u) *
        opus_dpo_shiftS T M direction X (.inl (.inl u))) =
        ∑ r : pkgB2_Nonroot T,
          pkgB2_directionLift (T r.1).d (direction r) 0 * (M r.1 : ℤ) * X (.inr (r, 0)) := by
      simp [pkgB2_oldCoefficient, opus_dpo_shiftS]
    have hJ : (∑ js : Fin (T s.1).d × Fin 2,
        pkgB2_oldCoefficient T (fun k => (M k : ℤ)) (.inr s) (.inr ⟨s.1, js⟩) *
          opus_dpo_shiftS T M direction X (.inl (.inr ⟨s.1, js⟩))) =
        ∑ r : pkgB2_Nonroot T, (if r.1 = s.1 then (M s.1 : ℤ) *
          ∑ j ∈ s.2.1, pkgB2_directionLift (T r.1).d (direction r) (j.val + 1) else 0) *
            X (.inr (r, 0)) := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two, opus_dpo_oldCoeff_same, opus_dpo_shiftS, Sum.elim_inl,
        Sum.elim_inr, Fin.val_zero, h01, h1v, if_false, mul_zero, zero_add, if_true, eq_self_iff_true]
      have hj (j : Fin (T s.1).d) :
          (if j ∈ s.2.1 then (M s.1 : ℤ) else 0) *
            ∑ r : pkgB2_Nonroot T, (if r.1 = s.1 then
              pkgB2_directionLift (T r.1).d (direction r) (j.val + 1) else 0) *
                X (.inr (r, 0)) =
          ∑ r : pkgB2_Nonroot T, (if j ∈ s.2.1 then (if r.1 = s.1 then (M s.1 : ℤ) *
              pkgB2_directionLift (T r.1).d (direction r) (j.val + 1) else 0) else 0) *
                X (.inr (r, 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        by_cases hjm : j ∈ s.2.1 <;> by_cases hr : r.1 = s.1 <;> simp [hjm, hr, mul_assoc]
      simp only [hj]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_mul]
      congr 1
      by_cases hr : r.1 = s.1
      · simp [hr, Finset.mul_sum]
      · simp [hr]
    rw [hU, hJ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← add_mul]
    congr 1
    by_cases hr : r.1 = s.1
    · have hM : (M r.1 : ℤ) = M s.1 := by rw [hr]
      simp only [pkgB2_response, dif_pos hr.symm, if_pos hr, hM]
      rw [pkgB2_directionLift_zero]
      ring
    · have hr' : ¬ s.1 = r.1 := fun h => hr h.symm
      simp only [pkgB2_response, dif_neg hr', if_neg hr, add_zero]


/-- Stage-`∅` row values are unchanged when the inserted translations are replaced by the
coordinate shift and the translation coordinates are set to zero. -/
theorem opus_dpo_rowValue_shift {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ)
    (p : Fin (b * sl) → ℕ) (o : Fin (Fintype.card (pkgB2_Occurrence T ∅)))
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    pkgB2_stateRowValue MS T hT J0 gap direction ∅ N p o x =
      pkgB2_stateRowValue MS T hT J0 gap direction ∅ N p o
        (opus_dpo_zeroTranslations T (x + opus_dpo_shift T
          (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
            direction x)) := by
  classical
  set M : Fin b → ℕ := fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k)
    with hM
  set e := pkgB2_coordEnum T
  set cI := pkgB2_occurrenceCoefficientInt T M direction ∅ (pkgB2_occurrenceEnum T ∅ o)
  unfold pkgB2_stateRowValue
  congr 1
  unfold linearRowValue pkgB2_rowCoefficientArray pkgB2_occurrenceCoefficient
  have hre (y : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
      (∑ j, ((cI (e j) : ℤ) : ℚ) * (y j : ℚ)) = ((∑ c, cI c * y (e.symm c) : ℤ) : ℚ) := by
    rw [← e.sum_comp (fun c => cI c * y (e.symm c))]
    push_cast
    simp
  change (∑ j, ((cI (e j) : ℤ) : ℚ) * (x j : ℚ)) =
    ∑ j, ((cI (e j) : ℤ) : ℚ) *
      ((opus_dpo_zeroTranslations T (x + opus_dpo_shift T M direction x) j : ℤ) : ℚ)
  rw [hre, hre]
  congr 1
  rw [opus_dpo_coeff_shift T M direction (pkgB2_occurrenceEnum T ∅ o)
    (fun c => x (e.symm c))]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  cases c with
  | inl old =>
    simp [opus_dpo_zeroTranslations, opus_dpo_shift, e]
  | inr tr =>
    simp [opus_dpo_zeroTranslations, e]

theorem opus_dpo_stateIntegrand_shift {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p x =
      pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
        (opus_dpo_zeroTranslations T (x + opus_dpo_shift T
          (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
            direction x)) := by
  unfold pkgB2_stateIntegrand
  congr 1
  apply Finset.prod_congr rfl
  intro o _
  simp only [pkgB2_stateFactor]
  rw [← opus_dpo_rowValue_shift MS T hT J0 gap direction N p o x]


/-! ### Translation insertion: the inner bound at a regular prime tuple -/

/-- Sum of the absolute values of the fixed direction integers. -/
def opus_dpo_dirConst {b : ℕ} (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) : ℕ :=
  ∑ r : pkgB2_Nonroot T, ∑ m : Fin ((T r.1).d + 1), (direction r m).natAbs

theorem opus_dpo_lift_abs_le {b : ℕ} (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (r : pkgB2_Nonroot T)
    (m : ℕ) :
    |pkgB2_directionLift (T r.1).d (direction r) m| ≤ (opus_dpo_dirConst T direction : ℤ) := by
  rw [Int.abs_eq_natAbs]
  have h : (pkgB2_directionLift (T r.1).d (direction r) m).natAbs ≤
      opus_dpo_dirConst T direction := by
    unfold pkgB2_directionLift
    split_ifs with hm
    · calc
        (direction r ⟨m, by omega⟩).natAbs ≤
            ∑ m' : Fin ((T r.1).d + 1), (direction r m').natAbs :=
          Finset.single_le_sum (f := fun m' => (direction r m').natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        _ ≤ opus_dpo_dirConst T direction :=
          Finset.single_le_sum (f := fun r' : pkgB2_Nonroot T =>
              ∑ m' : Fin ((T r'.1).d + 1), (direction r' m').natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    · simp
  exact_mod_cast h

/-- A prime-independent bound for the pivot displacement. -/
def opus_dpo_harmBound {K sl b : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ) : ℕ :=
  Fintype.card (pkgB2_Nonroot T) * opus_dpo_dirConst T direction *
    (MS.core.parameters.H N B.1) ^ 2

/-- A prime-independent bound for every coordinate translation error. -/
def opus_dpo_eta {K sl b : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ) : ℝ :=
  harmonicTranslationUniformError (MS.core.parameters.X N B.1) (primorial (N + 1))
      (opus_dpo_harmBound MS B T direction N) +
    ∑ k : Fin b, 2 * ((Fintype.card (pkgB2_Nonroot T) * opus_dpo_dirConst T direction : ℕ) : ℝ) /
      max 1 (pkgB2_translationLength MS T J0 gap k N : ℝ)

/-- The total insertion error bound. -/
def opus_dpo_insertError {K sl b : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ) : ℝ :=
  (1 + (pkgB2_blockScale MS.core.parameters B N : ℝ)) ^
      Fintype.card (Fin (Fintype.card (pkgB2_Occurrence T ∅))) *
    (Fintype.card (Fin (Fintype.card (pkgB2_Coord T))) * opus_dpo_eta MS B gap T J0 direction N)

theorem opus_dpo_shiftS_congr {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (X X' : pkgB2_Coord T → ℤ) (h : ∀ r, X (.inr (r, 0)) = X' (.inr (r, 0))) :
    opus_dpo_shiftS T M direction X = opus_dpo_shiftS T M direction X' := by
  funext c
  rcases c with (u | kjs) | rs <;> simp [opus_dpo_shiftS, h]

/-- At a regular prime tuple, the untranslated and translated stage-`∅` inner integrals differ by
at most `opus_dpo_insertError`. -/
theorem opus_dpo_inner_translation {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (N : ℕ) (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (hreg : pkgB2_baseRegular MS B T J0 gap hT N p)
    (hX2 : 2 ≤ MS.core.parameters.X N B.1)
    (hlog : Real.log (MS.core.parameters.X N B.1 : ℝ) >
      (primorial (N + 1) : ℝ) / (MS.core.parameters.X N B.1 : ℝ)) :
    |(∑' x, pkgB2_baseMass MS B T J0 gap hT N p x *
        pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
          (opus_dpo_zeroTranslations T x)) -
      ∑' x, pkgB2_baseMass MS B T J0 gap hT N p x *
        pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p x| ≤
      opus_dpo_insertError MS B gap T J0 direction N := by
  classical
  set A := MS.core.parameters with hA
  set e := pkgB2_coordEnum T with he
  set M : Fin b → ℕ := fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k)
    with hM
  set W := primorial (N + 1) with hW
  set Hi := A.H N B.1 with hHi
  set cC : ℕ := Fintype.card (pkgB2_Nonroot T) * opus_dpo_dirConst T direction with hcC
  set Cd : ℕ := opus_dpo_dirConst T direction with hCd
  let law : Fin (Fintype.card (pkgB2_Coord T)) → ℤ → ℝ := fun i =>
    pkgB2_baseCoordinateLaw MS B T J0 gap hT N p (e i)
  let win : Fin (Fintype.card (pkgB2_Coord T)) → Finset ℤ := fun i =>
    Sum.elim (fun _ => pkgB2_baseWindow MS B T J0 gap hT N p)
      (fun rs => Finset.Ico (0 : ℤ) (pkgB2_translationLength MS T J0 gap rs.1.1 N : ℤ)) (e i)
  let Tr : Finset (Fin (Fintype.card (pkgB2_Coord T))) :=
    Finset.univ.filter fun i => (e i).isRight
  let δ := opus_dpo_shift T M direction
  let Φ := pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
  let G : (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) → ℝ := fun w =>
    Φ (opus_dpo_zeroTranslations T w)
  set Bd : ℝ := (1 + (pkgB2_blockScale A B N : ℝ)) ^
    Fintype.card (Fin (Fintype.card (pkgB2_Occurrence T ∅))) with hBd
  set η := opus_dpo_eta MS B gap T J0 direction N with hη
  -- regularity consequences
  have hLpos (k : Fin b) : 0 < pkgB2_shiftLength MS T J0 gap hT N p k := hreg.2.1 k
  have hApos (k : Fin b) : 0 < pkgB2_translationLength MS T J0 gap k N := hreg.2.2 k
  have hLdef (k : Fin b) : pkgB2_shiftLength MS T J0 gap hT N p k =
      A.H N (gap k) / (J0 k * M k) := rfl
  have hGapLe (k : Fin b) : A.H N (gap k) ≤ Hi :=
    Nat.le_of_dvd (A.Hpos N B.1) (MS.gapStage.earlier_gaps_divide N (gap k) B.1 (hgap k).2)
  have hMle (k : Fin b) : M k ≤ Hi := by
    have hJM : J0 k * M k ≤ A.H N (gap k) := by
      by_contra hcon
      have h0 : A.H N (gap k) / (J0 k * M k) = 0 := Nat.div_eq_of_lt (lt_of_not_ge hcon)
      have := hLpos k
      rw [hLdef k, h0] at this
      exact lt_irrefl 0 this
    have hMJ : M k ≤ J0 k * M k := Nat.le_mul_of_pos_left (M k) (hJ0 k)
    exact hMJ.trans (hJM.trans (hGapLe k))
  have hA2L (k : Fin b) :
      pkgB2_translationLength MS T J0 gap k N ^ 2 ≤ pkgB2_shiftLength MS T J0 gap hT N p k := by
    have h1 := pkgB2_shiftLengthFloor_le_actual MS T J0 gap hJ0 N
      (fun k => pkgB2_repPrimeProject hT p k) hreg.1 k
    have h2 : pkgB2_translationLength MS T J0 gap k N ^ 2 ≤ _ := Nat.sqrt_le' _
    exact h2.trans h1
  have hAle (k : Fin b) : pkgB2_translationLength MS T J0 gap k N ≤ Hi := by
    have h1 : pkgB2_translationLength MS T J0 gap k N ≤
        pkgB2_translationLength MS T J0 gap k N ^ 2 := by
      rcases Nat.eq_zero_or_pos (pkgB2_translationLength MS T J0 gap k N) with h | h
      · rw [h]; simp
      · nlinarith
    have h2 : pkgB2_shiftLength MS T J0 gap hT N p k ≤ A.H N (gap k) := by
      rw [hLdef k]
      exact Nat.div_le_self _ _
    exact h1.trans ((hA2L k).trans (h2.trans (hGapLe k)))
  have hWM (k : Fin b) : (W : ℤ) ∣ (M k : ℤ) := by
    have : W ∣ M k := by
      show primorial (N + 1) ∣ (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k)
      unfold CubeTemplate.modulus directionModulus
      exact Dvd.dvd.mul_right (MS.core.parameters.Wdiv N) _
    exact_mod_cast this
  -- the product law
  have hbase : ∀ x, pkgB2_baseMass MS B T J0 gap hT N p x = ∏ i, law i (x i) := by
    intro x
    simp only [pkgB2_baseMass, dif_pos hreg]
    rfl
  have hzero : ∀ i z, z ∉ win i → law i z = 0 := by
    intro i z hz
    simp only [law]
    simp only [win] at hz
    rcases hc : e i with old | ⟨r, side⟩
    · rw [hc] at hz
      exact pkgB2_baseCoordinateLaw_zero_outside MS B T J0 gap hT N p (.inl old) z hz
    · rw [hc] at hz
      simp only [Sum.elim_inr, Finset.mem_Ico, not_and_or, not_le, not_lt] at hz
      simp only [pkgB2_baseCoordinateLaw, FromArithmetic.uniformIntegerIntervalLaw]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      rcases hz with h | h <;> omega
  have hnonneg : ∀ i z, 0 ≤ law i z := fun i z =>
    pkgB2_baseCoordinateLaw_nonneg MS B T J0 gap hT N p (e i) z
  have hsum : ∀ i, ∑ z ∈ win i, law i z = 1 := by
    intro i
    exact (tsum_eq_sum (s := win i) (fun z hz => hzero i z hz)).symm.trans
      (pkgB2_baseCoordinateLaw_tsum_one MS B T J0 gap hT N p hreg (e i))
  have hTr (r : pkgB2_Nonroot T) : e.symm (.inr (r, 0)) ∈ Tr := by
    simp [Tr]
  have hδTr : ∀ x i, i ∈ Tr → δ x i = 0 := by
    intro x i hi
    have hright : (e i).isRight := (Finset.mem_filter.mp hi).2
    rcases hc : e i with old | rs
    · rw [hc] at hright
      simp at hright
    · simp [δ, opus_dpo_shift, opus_dpo_shiftS, ← he, hc]
  have hδdep : ∀ x x', (∀ i ∈ Tr, x i = x' i) → δ x = δ x' := by
    intro x x' hxx
    funext i
    simp only [δ, opus_dpo_shift]
    rw [opus_dpo_shiftS_congr T M direction _ (fun c => x' (e.symm c))
      (fun r => hxx _ (hTr r))]
  have hG : ∀ w, |G w| ≤ Bd := fun w =>
    opus_dpo_stateIntegrand_abs_le MS B gap T hT J0 direction ∅ N I p _
  -- nonnegativity of the error terms
  have hXpos : (0 : ℝ) < (A.X N B.1 : ℝ) := by exact_mod_cast (A.Xpos N B.1)
  have hD : 0 < (A.X N B.1 : ℝ) * (Real.log (A.X N B.1 : ℝ) - (W : ℝ) / (A.X N B.1 : ℝ)) :=
    mul_pos hXpos (sub_pos.mpr hlog)
  have hharm0 : 0 ≤ harmonicTranslationUniformError (A.X N B.1) W
      (opus_dpo_harmBound MS B T direction N) := by
    unfold harmonicTranslationUniformError
    exact le_min (by norm_num) (div_nonneg (by positivity) hD.le)
  have hterm0 (k : Fin b) : 0 ≤ 2 * ((cC : ℕ) : ℝ) /
      max 1 (pkgB2_translationLength MS T J0 gap k N : ℝ) := by positivity
  have hη0 : 0 ≤ η := by
    simp only [hη, opus_dpo_eta]
    exact add_nonneg hharm0 (Finset.sum_nonneg fun k _ => hterm0 k)
  -- translation errors of single coordinates
  have hcoord : ∀ x c, (∀ i ∈ Tr, x i ∈ win i) →
      ∑' z, |law c (z - δ x c) - law c z| ≤ η := by
    intro x c hx
    have hXr (r : pkgB2_Nonroot T) : 0 ≤ x (e.symm (.inr (r, 0))) ∧
        x (e.symm (.inr (r, 0))) < (pkgB2_translationLength MS T J0 gap r.1 N : ℤ) := by
      have h := hx _ (hTr r)
      simp only [win, Equiv.apply_symm_apply, Sum.elim_inr, Finset.mem_Ico] at h
      exact h
    rcases hc : e c with (u | ⟨k, ⟨j, side⟩⟩) | rs
    · -- the pivot
      have hδc : δ x c = ∑ r : pkgB2_Nonroot T,
          pkgB2_directionLift (T r.1).d (direction r) 0 * (M r.1 : ℤ) *
            x (e.symm (.inr (r, 0))) := by
        simp [δ, opus_dpo_shift, opus_dpo_shiftS, ← he, hc]
      have hlaw : law c = harmonicLaw (A.X N B.1) W := by
        funext z
        simp [law, hc, pkgB2_baseCoordinateLaw, hA, hW]
      set h0 := δ x c with hh0
      have hdiv : ∃ m : ℤ, h0 = (W : ℤ) * m := by
        rw [hδc]
        apply Finset.dvd_sum
        intro r _
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hWM r.1) _) _
      have hbound : |h0| ≤ (opus_dpo_harmBound MS B T direction N : ℤ) := by
        rw [hδc]
        calc
          _ ≤ ∑ r : pkgB2_Nonroot T, |pkgB2_directionLift (T r.1).d (direction r) 0 *
              (M r.1 : ℤ) * x (e.symm (.inr (r, 0)))| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _r : pkgB2_Nonroot T, (Cd : ℤ) * (Hi : ℤ) * (Hi : ℤ) := by
            apply Finset.sum_le_sum
            intro r _
            rw [abs_mul, abs_mul]
            have h1 := opus_dpo_lift_abs_le T direction r 0
            have h2 : |(M r.1 : ℤ)| ≤ (Hi : ℤ) := by
              rw [abs_of_nonneg (by positivity)]
              exact_mod_cast hMle r.1
            have h3 : |x (e.symm (.inr (r, 0)))| ≤ (Hi : ℤ) := by
              rw [abs_of_nonneg (hXr r).1]
              have := (hXr r).2
              have h4 : (pkgB2_translationLength MS T J0 gap r.1 N : ℤ) ≤ Hi := by
                exact_mod_cast hAle r.1
              omega
            exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3
              (abs_nonneg _) (by positivity)
          _ = (opus_dpo_harmBound MS B T direction N : ℤ) := by
            simp [opus_dpo_harmBound, Finset.sum_const, Finset.card_univ, hHi, hA]
            ring
      have hS := sampling_pointwise_claim (A.X N B.1) W (primorial_pos _) hX2 hlog
      have htr := hS.translation hX2 hlog h0 hdiv
      rw [hlaw]
      have hbR : |(h0 : ℝ)| ≤ (opus_dpo_harmBound MS B T direction N : ℝ) := by
        have := hbound
        rw [← Int.cast_abs]
        exact_mod_cast this
      calc
        _ = arithmeticL1 (translatedLaw (harmonicLaw (A.X N B.1) W) h0)
            (harmonicLaw (A.X N B.1) W) := rfl
        _ ≤ min 2 (2 * |(h0 : ℝ)| / ((A.X N B.1 : ℝ) *
            (Real.log (A.X N B.1) - (W : ℝ) / (A.X N B.1)))) := htr
        _ ≤ harmonicTranslationUniformError (A.X N B.1) W
            (opus_dpo_harmBound MS B T direction N) := by
          unfold harmonicTranslationUniformError
          apply min_le_min_left
          apply div_le_div_of_nonneg_right _ hD.le
          linarith
        _ ≤ η := by
          simp only [hη, opus_dpo_eta]
          linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hterm0 k]
    · -- an original shift coordinate
      have hlaw : law c = FromArithmetic.uniformIntegerIntervalLaw 0
          (pkgB2_shiftLength MS T J0 gap hT N p k) := by
        funext z
        simp [law, hc, pkgB2_baseCoordinateLaw]
      have hδc : δ x c = if side = 1 then ∑ r : pkgB2_Nonroot T, (if r.1 = k then
          pkgB2_directionLift (T r.1).d (direction r) (j.val + 1) else 0) *
            x (e.symm (.inr (r, 0))) else 0 := by
        simp [δ, opus_dpo_shift, opus_dpo_shiftS, ← he, hc]
      set hk := δ x c with hhk
      have hbound : |hk| ≤ (cC : ℤ) * (pkgB2_translationLength MS T J0 gap k N : ℤ) := by
        rw [hδc]
        split_ifs
        · calc
            _ ≤ ∑ r : pkgB2_Nonroot T, |(if r.1 = k then
                pkgB2_directionLift (T r.1).d (direction r) (j.val + 1) else 0) *
                  x (e.symm (.inr (r, 0)))| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _r : pkgB2_Nonroot T,
                (Cd : ℤ) * (pkgB2_translationLength MS T J0 gap k N : ℤ) := by
              apply Finset.sum_le_sum
              intro r _
              by_cases hr : r.1 = k
              · rw [if_pos hr, abs_mul]
                have h1 := opus_dpo_lift_abs_le T direction r (j.val + 1)
                have h3 : |x (e.symm (.inr (r, 0)))| ≤
                    (pkgB2_translationLength MS T J0 gap k N : ℤ) := by
                  rw [abs_of_nonneg (hXr r).1]
                  have := (hXr r).2
                  rw [hr] at this
                  omega
                exact mul_le_mul h1 h3 (abs_nonneg _) (by positivity)
              · rw [if_neg hr, zero_mul, abs_zero]
                positivity
            _ = (cC : ℤ) * (pkgB2_translationLength MS T J0 gap k N : ℤ) := by
              simp [Finset.sum_const, Finset.card_univ, hcC, hCd]
              ring
        · simp only [abs_zero]
          positivity
      have hL := hLpos k
      have hint := FromArithmetic.uniform_interval_translation_bound 0 hk
        (pkgB2_shiftLength MS T J0 gap hT N p k) hL
      rw [hlaw]
      have hAk := hApos k
      have hAkR : (1 : ℝ) ≤ (pkgB2_translationLength MS T J0 gap k N : ℝ) := by
        exact_mod_cast hAk
      have hLR : (pkgB2_translationLength MS T J0 gap k N : ℝ) ^ 2 ≤
          (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ) := by exact_mod_cast hA2L k
      have hbR : |(hk : ℝ)| ≤ (cC : ℝ) * (pkgB2_translationLength MS T J0 gap k N : ℝ) := by
        rw [← Int.cast_abs]
        exact_mod_cast hbound
      have hmax : max 1 (pkgB2_translationLength MS T J0 gap k N : ℝ) =
          (pkgB2_translationLength MS T J0 gap k N : ℝ) := max_eq_right hAkR
      calc
        _ = arithmeticL1 (translatedLaw (FromArithmetic.uniformIntegerIntervalLaw 0
            (pkgB2_shiftLength MS T J0 gap hT N p k)) hk)
            (FromArithmetic.uniformIntegerIntervalLaw 0
              (pkgB2_shiftLength MS T J0 gap hT N p k)) := rfl
        _ ≤ 2 * min 1 (|(hk : ℝ)| / (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ)) := by
          rw [Int.cast_abs] at hint
          exact hint
        _ ≤ 2 * (|(hk : ℝ)| / (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ)) := by
          gcongr
          exact min_le_right _ _
        _ ≤ 2 * ((cC : ℝ) * (pkgB2_translationLength MS T J0 gap k N : ℝ) /
            (pkgB2_translationLength MS T J0 gap k N : ℝ) ^ 2) := by
          gcongr
          all_goals first | positivity | exact hbR
        _ = 2 * ((cC : ℕ) : ℝ) / max 1 (pkgB2_translationLength MS T J0 gap k N : ℝ) := by
          rw [hmax]
          field_simp
        _ ≤ ∑ k' : Fin b, 2 * ((cC : ℕ) : ℝ) /
            max 1 (pkgB2_translationLength MS T J0 gap k' N : ℝ) :=
          Finset.single_le_sum (f := fun k' : Fin b => 2 * ((cC : ℕ) : ℝ) /
            max 1 (pkgB2_translationLength MS T J0 gap k' N : ℝ))
            (fun k' _ => hterm0 k') (Finset.mem_univ k)
        _ ≤ η := by
          simp only [hη, opus_dpo_eta, ← hcC]
          linarith
    · -- a translation coordinate
      have hδc : δ x c = 0 := hδTr x c (by simp [Tr, hc])
      rw [hδc]
      simp only [sub_zero, sub_self, abs_zero, tsum_zero]
      exact hη0
  -- apply the hybrid translation bound
  have hhyb := opus_dpo_hybrid_translate law win hzero hnonneg hsum Tr δ hδTr hδdep G Bd hG
    η hη0 hcoord
  have hshiftEq : ∀ x, G (x + δ x) = Φ x := by
    intro x
    exact (opus_dpo_stateIntegrand_shift MS B gap T hT J0 direction N I p x).symm
  simp only [hshiftEq] at hhyb
  have hL : (∑' x, pkgB2_baseMass MS B T J0 gap hT N p x *
        pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
          (opus_dpo_zeroTranslations T x)) = ∑' x, (∏ i, law i (x i)) * G x := by
    apply tsum_congr
    intro x
    rw [hbase]
  have hR : (∑' x, pkgB2_baseMass MS B T J0 gap hT N p x *
        pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p x) =
      ∑' x, (∏ i, law i (x i)) * Φ x := by
    apply tsum_congr
    intro x
    rw [hbase]
  rw [hL, hR, abs_sub_comm]
  calc
    _ ≤ Bd * (Fintype.card (Fin (Fintype.card (pkgB2_Coord T))) * η) := hhyb
    _ = opus_dpo_insertError MS B gap T J0 direction N := by
      simp only [opus_dpo_insertError, hBd, hη, hA]


/-! ### Translation insertion: decay and the part lemma -/

/-- Harmonic translation errors decay superpolynomially when the
logarithmic cutoff
separates every fixed power of a scale dominating the displacement and block scale. -/
theorem opus_dpo_harmonicTranslation_superPolynomial
    (X W H V S : ℕ → ℕ) (q : ℕ)
    (hX : ∀ N, 1 ≤ X N) (hS : ∀ N, 1 ≤ S N)
    (hStendsto : Tendsto (fun N => (S N : ℝ)) atTop atTop)
    (hWle : ∀ᶠ N in atTop, W N ≤ S N)
    (hVle : ∀ᶠ N in atTop, V N ≤ S N)
    (hHle : ∀ᶠ N in atTop, H N ≤ S N ^ q)
    (hlog : OAI.MicrocellScale.Dominates (fun N => Real.log (X N : ℝ))
      (fun N => (S N : ℝ))) :
    SuperPolynomialSmall (fun N => harmonicTranslationUniformError (X N) (W N) (H N))
      (fun N => (V N : ℝ)) := by
  intro C hC
  let m : ℕ := Nat.ceil ((q : ℝ) + C + 1)
  have hm : (q : ℝ) + C + 1 ≤ (m : ℝ) := Nat.le_ceil _
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hSpos (N : ℕ) : (0 : ℝ) < (S N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hS N))
  have hSone (N : ℕ) : (1 : ℝ) ≤ (S N : ℝ) := by exact_mod_cast hS N
  have hlargeLog : ∀ᶠ N in atTop, 2 * (S N : ℝ) ≤ Real.log (X N : ℝ) := by
    filter_upwards [(hlog 1 (by norm_num)).eventually_ge_atTop 2] with N hN
    have hN' : (2 : ℝ) ≤ Real.log (X N : ℝ) / (S N : ℝ) := by simpa using hN
    exact (le_div_iff₀ (hSpos N)).mp hN'
  have hpowerLog : ∀ᶠ N in atTop, (S N : ℝ) ^ (m : ℝ) ≤ Real.log (X N : ℝ) := by
    filter_upwards [(hlog m hmpos).eventually_ge_atTop 1] with N hN
    simpa using (le_div_iff₀ (Real.rpow_pos_of_pos (hSpos N) _)).mp hN
  have hbound : ∀ᶠ N in atTop,
      harmonicTranslationUniformError (X N) (W N) (H N) * (V N : ℝ) ^ C ≤
        4 / (S N : ℝ) := by
    filter_upwards [hWle, hVle, hHle, hlargeLog, hpowerLog]
      with N hW hV hH hlogLarge hlogPower
    let L := Real.log (X N : ℝ)
    let D := (X N : ℝ) * (L - (W N : ℝ) / (X N : ℝ))
    have hXone : (1 : ℝ) ≤ (X N : ℝ) := by exact_mod_cast hX N
    have hXpos : (0 : ℝ) < (X N : ℝ) := by positivity
    have hWreal : (W N : ℝ) ≤ (S N : ℝ) := by exact_mod_cast hW
    have hVreal : (V N : ℝ) ≤ (S N : ℝ) := by exact_mod_cast hV
    have hHreal : (H N : ℝ) ≤ (S N : ℝ) ^ q := by exact_mod_cast hH
    have hLpos : 0 < L := by dsimp [L]; nlinarith [hSpos N]
    have hFrac : (W N : ℝ) / (X N : ℝ) ≤ (S N : ℝ) := by
      apply (div_le_iff₀ hXpos).mpr
      exact hWreal.trans (by nlinarith [hSpos N])
    have hDen : L / 2 ≤ L - (W N : ℝ) / (X N : ℝ) := by dsimp [L] at *; linarith
    have hD : L ≤ 2 * D := by
      dsimp [D]
      have hhalfpos : 0 ≤ L / 2 := by positivity
      have hmul := mul_le_mul hXone hDen hhalfpos (by positivity : (0 : ℝ) ≤ X N)
      nlinarith
    have hDpos : 0 < D := by linarith
    have herror : harmonicTranslationUniformError (X N) (W N) (H N) ≤ 4 * (H N : ℝ) / L := by
      calc
        _ ≤ 2 * (H N : ℝ) / D := min_le_right _ _
        _ ≤ _ := by
          apply (div_le_div_iff₀ hDpos hLpos).mpr
          nlinarith [Nat.cast_nonneg (α := ℝ) (H N)]
    have hpowV : (V N : ℝ) ^ C ≤ (S N : ℝ) ^ C :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hVreal hC.le
    have hpower : (H N : ℝ) * (V N : ℝ) ^ C * (S N : ℝ) ≤ L := by
      calc
        _ ≤ (S N : ℝ) ^ q * (S N : ℝ) ^ C * (S N : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hHreal hpowV (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))
            (Nat.cast_nonneg _)
        _ = (S N : ℝ) ^ ((q : ℝ) + C + 1) := by
          calc
            _ = (S N : ℝ) ^ ((q : ℝ) + C) * (S N : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_add (hSpos N)]
            _ = (S N : ℝ) ^ ((q : ℝ) + C) * (S N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := (Real.rpow_add (hSpos N) _ _).symm
        _ ≤ (S N : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le (hSone N) hm
        _ ≤ L := hlogPower
    calc
      _ ≤ (4 * (H N : ℝ) / L) * (V N : ℝ) ^ C :=
        mul_le_mul_of_nonneg_right herror (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = 4 * ((H N : ℝ) * (V N : ℝ) ^ C) / L := by ring
      _ ≤ 4 / (S N : ℝ) := by
        apply (div_le_div_iff₀ hLpos (hSpos N)).mpr
        nlinarith
  have hupper : Tendsto (fun N => 4 / (S N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hStendsto).const_mul 4
  have hnonneg : ∀ᶠ N in atTop,
      0 ≤ harmonicTranslationUniformError (X N) (W N) (H N) * (V N : ℝ) ^ C := by
    filter_upwards [hWle, hlargeLog] with N hW hlogLarge
    have hXone : (1 : ℝ) ≤ (X N : ℝ) := by exact_mod_cast hX N
    have hWreal : (W N : ℝ) ≤ (S N : ℝ) := by exact_mod_cast hW
    have hFrac : (W N : ℝ) / (X N : ℝ) ≤ (S N : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < X N)).mpr
      exact hWreal.trans (by nlinarith [hSpos N])
    unfold harmonicTranslationUniformError
    apply mul_nonneg
    · apply le_min (by norm_num)
      apply div_nonneg (by positivity)
      apply mul_nonneg (by positivity)
      nlinarith [hSpos N]
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact squeeze_zero' hnonneg hbound hupper

/-- Every good joint prime tuple is eventually regular (copy of the private
`pkgB2_baseRegular_of_allGood_eventually`, from public PkgB2 lemmas). -/
theorem opus_dpo_regular_eventually {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Fin (b * sl) → ℕ,
      pkgB2_goodPrimeEvent MS gap T hT N p → pkgB2_baseRegular MS B T J0 gap hT N p := by
  have hshiftAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
        (pkgB2_translationLength MS T J0 gap k N) ^ 2 := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => pkgB2_translationLength_ge_blockScale_pow MS B T J0 gap hgap hJ0 k 1)
    filter_upwards [h] with N hN k
    have hk : pkgB2_blockScale MS.core.parameters B N ^ 1 ≤
        pkgB2_translationLength MS T J0 gap k N := hN k (Finset.mem_univ k)
    calc
      _ ≤ pkgB2_translationLength MS T J0 gap k N := hk
      _ ≤ _ := by
        rcases Nat.eq_zero_or_pos (pkgB2_translationLength MS T J0 gap k N) with h0 | h0
        · rw [h0]; simp
        · nlinarith
  filter_upwards [hshiftAll] with N hN
  intro p hpGood
  have hV : 1 ≤ pkgB2_blockScale MS.core.parameters B N := by
    dsimp [pkgB2_blockScale]
    omega
  refine ⟨hpGood, ?_, ?_⟩
  · intro k
    have hactual := pkgB2_shiftLengthFloor_le_actual MS T J0 gap hJ0 N
      (fun k => pkgB2_repPrimeProject hT p k) hpGood k
    have h2 : pkgB2_translationLength MS T J0 gap k N ^ 2 ≤ _ := Nat.sqrt_le' _
    have hk := hN k
    change 0 < (T k).length (corrScales MS) (gap k) (J0 k) N (pkgB2_repPrimeProject hT p k)
    rw [pow_one] at hk
    omega
  · intro k
    have hk := hN k
    rw [pow_one] at hk
    by_contra h0
    push_neg at h0
    have : pkgB2_translationLength MS T J0 gap k N = 0 := by omega
    rw [this] at hk
    simp at hk
    omega

theorem opus_dpo_blockScale_ge {K : ℕ} (A : Parameters K) (B : Block K) (N : ℕ) :
    N ≤ pkgB2_blockScale A B N := by
  dsimp [pkgB2_blockScale]
  have h1 : N + 1 ≤ primorial (N + 1) := le_primorial_self
  have h2 := A.Wle N
  omega

/-- The insertion error bound tends to zero. -/
theorem opus_dpo_insertError_tendsto {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) :
    Tendsto (opus_dpo_insertError MS B gap T J0 direction) atTop (𝓝 0) := by
  classical
  set A := MS.core.parameters with hA
  let V : ℕ → ℕ := pkgB2_blockScale A B
  let Hi : ℕ → ℕ := fun N => A.H N B.1
  let m : ℕ := Fintype.card (Fin (Fintype.card (pkgB2_Occurrence T ∅)))
  let n : ℕ := Fintype.card (Fin (Fintype.card (pkgB2_Coord T)))
  let cC : ℕ := Fintype.card (pkgB2_Nonroot T) * opus_dpo_dirConst T direction
  let harm : ℕ → ℝ := fun N => harmonicTranslationUniformError (A.X N B.1) (primorial (N + 1))
    (opus_dpo_harmBound MS B T direction N)
  let tk : Fin b → ℕ → ℝ := fun k N => 2 * (cC : ℝ) /
    max 1 (pkgB2_translationLength MS T J0 gap k N : ℝ)
  have hVge (N : ℕ) : N ≤ V N := opus_dpo_blockScale_ge A B N
  have hVone (N : ℕ) : 1 ≤ V N := by
    dsimp [V, pkgB2_blockScale]
    omega
  have hVtend : Tendsto (fun N => (V N : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    rw [tendsto_atTop]
    intro a
    filter_upwards [eventually_ge_atTop a] with N hN
    exact hN.trans (hVge N)
  have hMH (N : ℕ) : A.M N ≤ Hi N := Nat.le_of_dvd (A.Hpos N B.1) (A.Hdiv N B.1)
  have hWH (N : ℕ) : primorial (N + 1) ≤ Hi N := (A.Wle N).trans (hMH N)
  have hHge (N : ℕ) : N ≤ Hi N := by
    have h1 : N + 1 ≤ primorial (N + 1) := le_primorial_self
    have := hWH N
    omega
  have hHtend : Tendsto (fun N => (Hi N : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    rw [tendsto_atTop]
    intro a
    filter_upwards [eventually_ge_atTop a] with N hN
    exact hN.trans (hHge N)
  -- V ≤ H_i eventually, from the domination of the earlier scale
  have hVH : ∀ᶠ N in atTop, V N ≤ Hi N := by
    have hdom := A.Hdom B.1 2 (by norm_num)
    filter_upwards [hdom.eventually_ge_atTop 1] with N hN
    set P : ℕ := OAI.SourceAdmissible.previous (A.X N) B.1 with hP
    have hS : (0 : ℝ) < OAI.AdmissibleMicrocellBoundary.earlierScale A.M
        (fun N => OAI.SourceAdmissible.previous (A.X N) B.1) N := by
      unfold OAI.AdmissibleMicrocellBoundary.earlierScale
      positivity
    have hS2 := (le_div_iff₀ (Real.rpow_pos_of_pos hS 2)).mp hN
    rw [one_mul, Real.rpow_two] at hS2
    have hscale : (OAI.AdmissibleMicrocellBoundary.earlierScale A.M
        (fun N => OAI.SourceAdmissible.previous (A.X N) B.1) N) = 2 + (A.M N : ℝ) + P := by
      rfl
    rw [hscale] at hS2
    have htail : ∏ j ∈ B.2.val, (A.X N j) ^ 2 ≤ P ^ 2 := by
      rw [hP, OAI.SourceAdmissible.previous, ← Finset.prod_pow]
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, B.2.property.2 j hj⟩
      · intro j _ _
        exact Nat.one_le_pow _ _ (A.Xpos N j)
    have hVR : (V N : ℝ) ≤ 2 + (A.M N : ℝ) + (P : ℝ) ^ 2 := by
      have : V N ≤ 2 + A.M N + P ^ 2 := by
        dsimp [V, pkgB2_blockScale]
        omega
      exact_mod_cast this
    have hsq : 2 + (A.M N : ℝ) + (P : ℝ) ^ 2 ≤ (2 + (A.M N : ℝ) + P) ^ 2 := by
      have hM0 : (0 : ℝ) ≤ A.M N := Nat.cast_nonneg _
      have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast hVR.trans (hsq.trans hS2)
  have hHb : ∀ᶠ N in atTop, opus_dpo_harmBound MS B T direction N ≤ Hi N ^ 3 := by
    have hbig : ∀ᶠ N in atTop, cC ≤ Hi N := by
      filter_upwards [eventually_ge_atTop cC] with N hN
      exact hN.trans (hHge N)
    filter_upwards [hbig] with N hN
    dsimp [opus_dpo_harmBound]
    calc
      Fintype.card (pkgB2_Nonroot T) * opus_dpo_dirConst T direction * A.H N B.1 ^ 2 =
          cC * Hi N ^ 2 := rfl
      _ ≤ Hi N * Hi N ^ 2 := Nat.mul_le_mul_right _ hN
      _ = Hi N ^ 3 := by ring
  have hharm := opus_dpo_harmonicTranslation_superPolynomial (fun N => A.X N B.1)
    (fun N => primorial (N + 1)) (fun N => opus_dpo_harmBound MS B T direction N) V Hi 3
    (fun N => A.Xpos N B.1) (fun N => A.Hpos N B.1) hHtend
    (Eventually.of_forall hWH) hVH hHb (A.Xdom B.1)
  -- each term times any power of V tends to zero
  have hharmPow : Tendsto (fun N => (V N : ℝ) ^ m * harm N) atTop (𝓝 0) := by
    have h := hharm ((m : ℝ) + 1) (by positivity)
    have hle : ∀ᶠ N in atTop, |(V N : ℝ) ^ m * harm N| ≤
        |harm N * (V N : ℝ) ^ ((m : ℝ) + 1)| := by
      filter_upwards with N
      have hV1 : (1 : ℝ) ≤ V N := by exact_mod_cast hVone N
      rw [abs_mul, abs_mul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), Real.rpow_add_one
        (by positivity), Real.rpow_natCast]
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ V N) m]
    exact squeeze_zero_norm' hle (by simpa using h.abs)
  have htkPow (k : Fin b) : Tendsto (fun N => (V N : ℝ) ^ m * tk k N) atTop (𝓝 0) := by
    have hfloor := pkgB2_translationLength_ge_blockScale_pow MS B T J0 gap hgap hJ0 k (m + 1)
    have hupper : Tendsto (fun N => 2 * (cC : ℝ) / (V N : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hVtend).const_mul (2 * (cC : ℝ))
    apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hupper
    filter_upwards [hfloor] with N hN
    have hN' : (V N : ℝ) ^ (m + 1) ≤ (pkgB2_translationLength MS T J0 gap k N : ℝ) := by
      exact_mod_cast hN
    have hV1 : (1 : ℝ) ≤ V N := by exact_mod_cast hVone N
    have hVpos : (0 : ℝ) < V N := by linarith
    have hApos : (0 : ℝ) < (pkgB2_translationLength MS T J0 gap k N : ℝ) :=
      lt_of_lt_of_le (by positivity) hN'
    have hmax : max 1 (pkgB2_translationLength MS T J0 gap k N : ℝ) =
        (pkgB2_translationLength MS T J0 gap k N : ℝ) := by
      apply max_eq_right
      exact le_trans (one_le_pow₀ hV1) hN'
    dsimp [tk]
    rw [hmax]
    rw [mul_div_assoc', div_le_div_iff₀ hApos hVpos]
    calc
      (V N : ℝ) ^ m * (2 * cC) * V N = 2 * cC * (V N : ℝ) ^ (m + 1) := by ring
      _ ≤ 2 * cC * (pkgB2_translationLength MS T J0 gap k N : ℝ) :=
        mul_le_mul_of_nonneg_left hN' (by positivity)
  -- assemble
  have hsum : Tendsto (fun N => (2 : ℝ) ^ m * n * ((V N : ℝ) ^ m * harm N +
      ∑ k : Fin b, (V N : ℝ) ^ m * tk k N)) atTop (𝓝 0) := by
    have h := (hharmPow.add (tendsto_finset_sum (Finset.univ : Finset (Fin b))
      fun k _ => htkPow k)).const_mul
      ((2 : ℝ) ^ m * n)
    simpa using h
  have hharm0 : ∀ᶠ N in atTop, 0 ≤ harm N := by
    filter_upwards [pivotSamplingEventually MS B.1] with N hN
    rcases hN with ⟨hX2, hlog⟩
    have hXpos : (0 : ℝ) < (A.X N B.1 : ℝ) := by exact_mod_cast (A.Xpos N B.1)
    dsimp [harm]
    unfold harmonicTranslationUniformError
    exact le_min (by norm_num) (div_nonneg (by positivity)
      (mul_nonneg hXpos.le (sub_pos.mpr hlog).le))
  apply squeeze_zero' _ _ hsum
  · filter_upwards [hharm0] with N hN
    unfold opus_dpo_insertError opus_dpo_eta
    apply mul_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    exact add_nonneg hN (Finset.sum_nonneg fun k _ => by positivity)
  · filter_upwards [hharm0] with N hN
    have hV1 : (1 : ℝ) ≤ V N := by exact_mod_cast hVone N
    have hpow : (1 + (V N : ℝ)) ^ m ≤ (2 : ℝ) ^ m * (V N : ℝ) ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have hη0 : 0 ≤ harm N + ∑ k : Fin b, tk k N :=
      add_nonneg hN (Finset.sum_nonneg fun k _ => by positivity)
    unfold opus_dpo_insertError opus_dpo_eta
    change (1 + (V N : ℝ)) ^ m * ((n : ℝ) * (harm N + ∑ k : Fin b, tk k N)) ≤ _
    calc
      (1 + (V N : ℝ)) ^ m * ((n : ℝ) * (harm N + ∑ k : Fin b, tk k N)) ≤
          (2 : ℝ) ^ m * (V N : ℝ) ^ m * ((n : ℝ) * (harm N + ∑ k : Fin b, tk k N)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (2 : ℝ) ^ m * n * ((V N : ℝ) ^ m * harm N +
          ∑ k : Fin b, (V N : ℝ) ^ m * tk k N) := by
        rw [← Finset.mul_sum]
        ring

/-- Proof of the part `opus_dpo_translation_error`. -/
theorem opus_dpo_translation_error_proof {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |opus_dpo_untranslatedAverage MS B gap T J0 hT direction N I -
        pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 ∅ N I| ≤ ε := by
  intro ε hε
  have hdecay := opus_dpo_insertError_tendsto MS B gap T J0 hgap hJ0 direction
  filter_upwards [hdecay.eventually (Iic_mem_nhds hε),
    opus_dpo_regular_eventually MS B gap T J0 hgap hT hJ0,
    pivotSamplingEventually MS B.1] with N hsmall hreg hsamp I
  rcases hsamp with ⟨hX2, hlog⟩
  rw [opus_dpo_stateAverage_eq]
  unfold opus_dpo_untranslatedAverage
  have hinner := fun p (hp : pkgB2_goodPrimeEvent MS gap T hT N p) =>
    opus_dpo_inner_translation MS B gap T J0 hgap hT hJ0 direction N I p (hreg p hp) hX2 hlog
  have hδ : 0 ≤ opus_dpo_insertError MS B gap T J0 direction N := by
    have hXpos : (0 : ℝ) < (MS.core.parameters.X N B.1 : ℝ) := by
      exact_mod_cast (MS.core.parameters.Xpos N B.1)
    unfold opus_dpo_insertError opus_dpo_eta
    apply mul_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    apply add_nonneg
    · unfold harmonicTranslationUniformError
      exact le_min (by norm_num) (div_nonneg (by positivity)
        (mul_nonneg hXpos.le (sub_pos.mpr hlog).le))
    · exact Finset.sum_nonneg fun k _ => by positivity
  exact (opus_dpo_average_sub_le MS B gap T J0 hT N _ _ _ hδ hinner).trans hsmall


/-! ### Terminal state (copy of PkgB2's terminal chain without `0 < sl`) -/

theorem opus_dpo_repGoodProbability_eq_product {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (hpool : ∀ k, 0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
      (MS.primeStage.pool N (gap k)).upper) :
    independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) =
      ∏ k, gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
  classical
  let lo : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let loBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).lower
  let hiBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).upper
  let G : ∀ k : Fin b, (Fin sl → ℕ) → Prop := fun k q =>
    (T k).Good (corrScales MS) (gap k) N
      (fun j => q ((Classical.choose (hT k)) j))
  have hlo : ∀ k j, lo (pkgB2_replicaEmbedding k j) = loBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).lower = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  have hhi : ∀ k j, hi (pkgB2_replicaEmbedding k j) = hiBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).upper = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  let M := (∑ i : Fin (b * sl), hi i) + ∑ k : Fin b, hiBlock k
  have hboundFull : ∀ i, hi i ≤ M := by
    intro i
    dsimp [M]
    exact (Finset.single_le_sum (fun j hj => Nat.zero_le (hi j)) (Finset.mem_univ i)).trans
      (Nat.le_add_right _ _)
  have hboundBlock : ∀ k, hiBlock k ≤ M := by
    intro k
    dsimp [M]
    exact (Finset.single_le_sum (fun j hj => Nat.zero_le (hiBlock j)) (Finset.mem_univ k)).trans
      (Nat.le_add_left _ _)
  have hproject (p : Fin (b * sl) → ℕ) (k : Fin b) :
      pkgB2_repPrimeProject hT p k =
        fun j => p (pkgB2_replicaEmbedding k ((Classical.choose (hT k)) j)) := by
    funext j
    rfl
  have hfullEvent :
      (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
        (pkgB2_repPrimeProject hT p k)) =
      (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) := by
    funext p
    apply propext
    apply forall_congr'
    intro k
    rw [hproject p k]
  have hfactor := pkgB2_independentPrimePoolProbability_blockFactor
    lo hi loBlock hiBlock hlo hhi ⟨hboundFull, hboundBlock⟩ G
  have hmarginal (k : Fin b) :
      independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (G k) =
        gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N) := by
    have h := independentPrimePoolProbability_iid_marginal
      (loBlock k) (hiBlock k) (hpool k) (Classical.choose (hT k))
      ((T k).Good (corrScales MS) (gap k) N)
    simpa [G, loBlock, hiBlock, gapSlotProbability, corrScales] using h.symm
  calc
    independentPrimePoolProbability lo hi
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) =
      independentPrimePoolProbability lo hi
        (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) := by
          rw [hfullEvent]
    _ = ∏ k, independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (G k) := hfactor
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k hk
      exact hmarginal k

theorem opus_dpo_repGoodProbability_lower_eventually {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) :
    ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) ^ b ≤ independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) := by
  have hgood (k : Fin b) : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) < gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
    have hlim := good_probability_tendsto_one MS (T k) (hT k) (gap k)
    exact hlim.eventually (Ioi_mem_nhds (by norm_num))
  have hpoolPos (k : Fin b) : ∀ᶠ N : ℕ in atTop,
      0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
        (MS.primeStage.pool N (gap k)).upper := by
    have hratio := MS.primeStage.pool_harmonic_mass_dominates (gap k) 1 (by norm_num)
    have hlarge : ∀ᶠ N : ℕ in atTop,
        1 ≤ primePoolMass (MS.primeStage.pool N (gap k)).lower
          (MS.primeStage.pool N (gap k)).upper /
            (masterScaleV MS.core.parameters N (gap k) : ℝ) := by
      simpa [pow_one] using hratio.eventually_ge_atTop (1 : ℝ)
    filter_upwards [hlarge] with N hN
    have hVpos : 0 < (masterScaleV MS.core.parameters N (gap k) : ℝ) := by
      unfold masterScaleV
      positivity
    have hmass := (le_div_iff₀ hVpos).mp hN
    have hmassPos :
        0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
          (MS.primeStage.pool N (gap k)).upper := by
      linarith
    exact hmassPos
  have hgoodAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      (1 / 2 : ℝ) < gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => hgood k)
    simpa using h
  have hpoolAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
        (MS.primeStage.pool N (gap k)).upper := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => hpoolPos k)
    simpa using h
  filter_upwards [hgoodAll, hpoolAll] with N hgoodN hpoolN
  have hfactor := opus_dpo_repGoodProbability_eq_product MS gap T hT N hpoolN
  rw [hfactor]
  calc
    (1 / 2 : ℝ) ^ b = ∏ k : Fin b, (1 / 2 : ℝ) := by simp
    _ ≤ ∏ k : Fin b, gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N) := by
        apply Finset.prod_le_prod₀
        · intro k hk
          norm_num
        · intro k hk
          exact le_of_lt (hgoodN k)

theorem opus_dpo_weightedGoodMonomial_tendsto_one {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T))
    (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E)))) :
    Tendsto
      (fun N : ℕ =>
        weightedLinearFormsAverage
            (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
              direction hdir k0 E U) N
            (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
              (pkgB2_repPrimeProject hT p k)) /
          weightedLinearFormsEventProbability
            (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
              direction hdir k0 E U) N
            (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
              (pkgB2_repPrimeProject hT p k)))
      atTop (𝓝 1) := by
  classical
  let D := pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
    direction hdir k0 E U
  let good (N : ℕ) (p : Fin (b * sl) → ℕ) : Prop :=
    ∀ k, (T k).Good (corrScales MS) (gap k) N (pkgB2_repPrimeProject hT p k)
  let prob (N : ℕ) : ℝ := weightedLinearFormsEventProbability D N (good N)
  let average (N : ℕ) : ℝ := weightedLinearFormsAverage D N (good N)
  let c : ℝ := (1 / 2 : ℝ) ^ b
  have hc : 0 < c := by dsimp [c]; positivity
  have hgoodDomain : ∀ᶠ N : ℕ in atTop, ∀ p : Fin (b * sl) → ℕ,
      good N p → D.goodDomain N p := by
    have hreg := opus_dpo_regular_eventually MS B gap T J0 hgap hT hJ0
    have hN0 : ∀ᶠ N : ℕ in atTop,
        pkgB2_directionConstantBound T direction + 1 ≤ N :=
      eventually_ge_atTop _
    filter_upwards [hreg, hN0] with N hregN hN0 p hp
    change pkgB2_directionConstantBound T direction + 1 ≤ N ∧
      pkgB2_baseRegular MS B T J0 gap hT N p
    exact ⟨hN0, hregN p hp⟩
  obtain ⟨C, hC, hlinear⟩ := prop_linear_forms D
  have herr : Tendsto
      (fun N : ℕ => C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^
        Fintype.card (pkgB2_Occurrence T E) * (D.epsilonBase N + D.epsilonCRT N)))
      atTop (𝓝 0) := by
    have hCconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    simpa using hCconst.mul (weighted_linear_forms_error_tends_zero D)
  have hlinearEventually : ∀ᶠ N : ℕ in atTop,
      |average N - prob N| ≤
        C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^
          Fintype.card (pkgB2_Occurrence T E) * (D.epsilonBase N + D.epsilonCRT N)) := by
    filter_upwards [hgoodDomain] with N hN
    exact hlinear N (good N) (fun p hp => hN p hp)
  have habs : Tendsto (fun N => |average N - prob N|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _)
      hlinearEventually herr
  have hrepLower : ∀ᶠ N : ℕ in atTop, c ≤
      independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) (good N) :=
    opus_dpo_repGoodProbability_lower_eventually MS gap T hT
  have hprobEq (N : ℕ) : prob N =
      independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) (good N) := by
    simp [prob, good, weightedLinearFormsEventProbability, D,
      pkgB2_weightedLinearFormsData, pkgB2_repScales, pkgB2_repScalesOfFacts]
  have hprobLower : ∀ᶠ N : ℕ in atTop, c ≤ prob N := by
    filter_upwards [hrepLower] with N hN
    rw [hprobEq]
    exact hN
  have hratioBound (N : ℕ) (hP : c ≤ prob N) :
      |average N / prob N - 1| ≤ |average N - prob N| / c := by
    have hPpos : 0 < prob N := lt_of_lt_of_le hc hP
    have heq : average N / prob N - 1 = (average N - prob N) / prob N := by
      field_simp [ne_of_gt hPpos]
    rw [heq, abs_div, abs_of_pos hPpos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc hP
  have hratioError : Tendsto (fun N => |average N - prob N| / c) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using habs.mul_const c⁻¹
  have hratio : Tendsto (fun N => |average N / prob N - 1|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _)
      (Filter.Eventually.mono hprobLower (fun N hP => hratioBound N hP)) hratioError
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa [Real.norm_eq_abs, average, prob, D, good] using hratio

theorem opus_dpo_terminal_proof {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (hNonroot : Nonempty (pkgB2_Nonroot T)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 Finset.univ N I| ≤ ε := by
  classical
  let plus := pkgB2_nonrootOccurrenceSet (T := T) Finset.univ
  let minus := pkgB2_rootOccurrenceSet (T := T) Finset.univ
  let q := Fintype.card (pkgB2_Occurrence T Finset.univ)
  let C : ℝ := (2 : ℝ) ^ (plus.card + minus.card)
  have hC : 0 < C := by dsimp [C]; positivity
  have hdisj : Disjoint plus minus := by
    rw [Finset.disjoint_left]
    intro o ho hm
    exact (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp ho).2
  have hminus : minus.Nonempty := by
    simpa [minus] using pkgB2_rootOccurrenceSet_nonempty T
  have hclose (U : Finset (Fin q)) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ N : ℕ in atTop,
        |pkgB2_stateMonomialAverage MS B gap T J0 hT Finset.univ direction N U - 1| ≤ ε := by
    have hlim := opus_dpo_weightedGoodMonomial_tendsto_one MS B gap T J0
      hgap hT hJ0 direction hdir k0 Finset.univ U
    have hlimState :
        Tendsto (fun N => pkgB2_stateMonomialAverage MS B gap T J0 hT
          Finset.univ direction N U) atTop (𝓝 1) := by
      have hEq : (fun N =>
          weightedLinearFormsAverage
              (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
                direction hdir k0 Finset.univ U) N
              (fun p => pkgB2_goodPrimeEvent MS gap T hT N p) /
            weightedLinearFormsEventProbability
              (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
                direction hdir k0 Finset.univ U) N
              (pkgB2_goodPrimeEvent MS gap T hT N)) =ᶠ[atTop]
          fun N => pkgB2_stateMonomialAverage MS B gap T J0 hT Finset.univ direction N U := by
        filter_upwards with N
        exact (pkgB2_stateMonomialAverage_eq_wlf MS B gap T J0 hgap hT hJ0
          direction hdir k0 Finset.univ U N).symm
      exact hlim.congr' hEq
    have hdist : Tendsto
        (fun N => |pkgB2_stateMonomialAverage MS B gap T J0 hT Finset.univ direction N U - 1|)
        atTop (𝓝 0) := by
      simpa [Real.norm_eq_abs] using (tendsto_iff_norm_sub_tendsto_zero).1 hlimState
    filter_upwards [hdist.eventually (Iio_mem_nhds hε)] with N hN
    exact le_of_lt hN
  have hcloseForP (ε : ℝ) (hε : 0 < ε)
      (P : Finset (Fin q)) : ∀ᶠ N : ℕ in atTop,
        ∀ M ∈ minus.powerset,
          |pkgB2_stateMonomialAverage MS B gap T J0 hT Finset.univ direction N (P ∪ M) - 1| ≤ ε := by
    have h := (eventually_all_finset minus.powerset).2
      (fun M hM => hclose (P ∪ M) ε hε)
    exact h
  have hclosePairs (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
      ∀ P ∈ plus.powerset, ∀ M ∈ minus.powerset,
        |pkgB2_stateMonomialAverage MS B gap T J0 hT Finset.univ direction N (P ∪ M) - 1| ≤ ε := by
    have h := (eventually_all_finset plus.powerset).2
      (fun P hP => hcloseForP ε hε P)
    exact h
  have hbound (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
      ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0
          Finset.univ N I| ≤ C * ε := by
    filter_upwards [hclosePairs ε hε] with N hcloseN I
    have hPartition : plus ∪ minus = Finset.univ := by
      ext o
      simp only [Finset.mem_union, Finset.mem_univ]
      constructor
      · intro h
        trivial
      · intro _
        by_cases hn : pkgB2_occurrenceIsNonroot (T := T) Finset.univ o
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    have hmain : ∀ U : Finset (Fin q),
        |pkgB2_stateMonomialAverage MS B gap T J0 hT Finset.univ direction N U - 1| ≤ ε := by
      intro U
      let P := U ∩ plus
      let M := U ∩ minus
      have hP : P ∈ plus.powerset := Finset.mem_powerset.mpr (by
        intro o ho
        exact (Finset.mem_inter.mp ho).2)
      have hM : M ∈ minus.powerset := Finset.mem_powerset.mpr (by
        intro o ho
        exact (Finset.mem_inter.mp ho).2)
      have hU : U = P ∪ M := by
        ext o
        constructor
        · intro hoU
          have hsplit : o ∈ plus ∨ o ∈ minus := by
            have : o ∈ plus ∪ minus := by rw [hPartition]; exact Finset.mem_univ o
            simpa using this
          rcases hsplit with hplus | hminus
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hoU, hplus⟩))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hoU, hminus⟩))
        · intro h
          rcases Finset.mem_union.mp h with hP | hM
          · exact (Finset.mem_inter.mp hP).1
          · exact (Finset.mem_inter.mp hM).1
      rw [hU]
      exact hcloseN P hP M hM
    have hexpand := pkgB2_terminalStateAverage_expansion MS B gap T J0 hgap hT hJ0
      direction hdir k0 N I hNonroot
    rw [hexpand]
    have herr := pkgB2_signedMomentError_bound plus minus 1
      (pkgB2_stateMonomialAverage MS B gap T J0 hT Finset.univ direction N)
      ε (le_of_lt hε) hmain hminus
    simpa [C, plus, minus] using herr
  intro ε hε
  let δ := ε / (2 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hbound δ hδ] with N hN I
  have hCδ : C * δ ≤ ε := by
    dsimp [δ]
    have hC0 : C ≠ 0 := ne_of_gt hC
    field_simp [hC0]
    nlinarith
  exact (hN I).trans hCδ


/-! ### Replica identity: the base-coordinate sum at a regular prime tuple -/

/-- Structured coordinates: the pivot, the original shifts of each replica, and the translation
coordinates. -/
abbrev opus_dpo_Y {b : ℕ} (T : Fin b → CubeTemplate) :=
  ℤ × ((k : Fin b) → Fin (T k).d → Fin 2 → ℤ) × (pkgB2_Nonroot T × Fin 2 → ℤ)

def opus_dpo_coordY {b : ℕ} (T : Fin b → CubeTemplate) :
    (pkgB2_Coord T → ℤ) ≃ opus_dpo_Y T where
  toFun X := (X (.inl (.inl ())), fun k j s => X (.inl (.inr ⟨k, (j, s)⟩)),
    fun tr => X (.inr tr))
  invFun w c := match c with
    | .inl (.inl _) => w.1
    | .inl (.inr ⟨k, (j, s)⟩) => w.2.1 k j s
    | .inr tr => w.2.2 tr
  left_inv := by
    intro X
    funext c
    rcases c with (⟨⟩ | ⟨k, j, s⟩) | tr <;> rfl
  right_inv := by
    intro w
    rfl

/-- The enumerated coordinate vectors in structured form. -/
def opus_dpo_coordE {b : ℕ} (T : Fin b → CubeTemplate) :
    (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) ≃ opus_dpo_Y T :=
  (Equiv.arrowCongr (pkgB2_coordEnum T) (Equiv.refl ℤ)).trans (opus_dpo_coordY T)

theorem opus_dpo_coordE_symm_apply {b : ℕ} (T : Fin b → CubeTemplate) (w : opus_dpo_Y T)
    (i : Fin (Fintype.card (pkgB2_Coord T))) :
    (opus_dpo_coordE T).symm w i = (opus_dpo_coordY T).symm w (pkgB2_coordEnum T i) := by
  simp [opus_dpo_coordE, Equiv.arrowCongr]

theorem opus_dpo_prod_coord {b : ℕ} (T : Fin b → CubeTemplate) (f : pkgB2_Coord T → ℝ) :
    ∏ c, f c = f (.inl (.inl ())) *
      (∏ k : Fin b, ∏ j : Fin (T k).d, ∏ s : Fin 2, f (.inl (.inr ⟨k, (j, s)⟩))) *
        ∏ tr : pkgB2_Nonroot T × Fin 2, f (.inr tr) := by
  classical
  have h1 : ∏ c, f c = (∏ old : pkgB2_OldCoord T, f (.inl old)) *
      ∏ tr : pkgB2_Nonroot T × Fin 2, f (.inr tr) := by
    rw [← Fintype.prod_sum_type]
    exact Finset.prod_congr (by ext; simp) (fun c _ => by cases c <;> rfl)
  rw [h1, Fintype.prod_sum_type, Fintype.prod_sigma]
  simp only [Finset.univ_unique, Finset.prod_singleton, Fintype.prod_prod_type]

theorem opus_dpo_prod_baseRow {b : ℕ} (T : Fin b → CubeTemplate) (F : pkgB2_BaseRow T → ℝ) :
    ∏ t, F t = F (.inl ()) * ∏ r : pkgB2_Nonroot T, F (.inr r) := by
  classical
  have h : F (.inl ()) = ∏ u : Unit, F (.inl u) := by simp
  rw [h, ← Fintype.prod_sum_type]
  exact Finset.prod_congr (by ext; simp) (fun c _ => by cases c <;> rfl)

theorem opus_dpo_prod_nonroot {b : ℕ} (T : Fin b → CubeTemplate) (F : pkgB2_Nonroot T → ℝ) :
    ∏ r, F r = ∏ k : Fin b, ∏ ω ∈ (Finset.univ : Finset (Finset (Fin (T k).d))).erase ∅,
      (if h : ω.Nonempty then F ⟨k, ⟨ω, h⟩⟩ else 1) := by
  classical
  have h1 : ∏ r, F r = ∏ k : Fin b, ∏ ω : {ω : Finset (Fin (T k).d) // ω.Nonempty},
      F ⟨k, ω⟩ := by
    rw [← Fintype.prod_sigma]
    exact Finset.prod_congr (by ext; simp) (fun _ _ => rfl)
  rw [h1]
  apply Finset.prod_congr rfl
  intro k _
  rw [Finset.prod_subtype ((Finset.univ : Finset (Finset (Fin (T k).d))).erase ∅)
    (p := fun ω : Finset (Fin (T k).d) => ω.Nonempty)
    (fun ω => by simp [Finset.nonempty_iff_ne_empty])]
  apply Finset.prod_congr rfl
  intro ω _
  rw [dif_pos ω.2]

/-- The stage-`∅` occurrences are the base rows. -/
def opus_dpo_occEmptyEquiv {b : ℕ} (T : Fin b → CubeTemplate) :
    pkgB2_Occurrence T ∅ ≃ pkgB2_BaseRow T where
  toFun o := o.1
  invFun t := ⟨t, fun j => (Finset.notMem_empty _ j.2.1).elim⟩
  left_inv := by
    intro o
    rcases o with ⟨t, η⟩
    have hη : (fun j : {j // j ∈ (∅ : Finset (pkgB2_Nonroot T)) ∧ pkgB2_activeRow T t j} =>
        ((Finset.notMem_empty _ j.2.1).elim : Fin 2)) = η := by
      funext j
      exact (Finset.notMem_empty _ j.2.1).elim
    simp only [hη]
  right_inv := by
    intro t
    rfl

theorem opus_dpo_prod_occEmpty {b : ℕ} (T : Fin b → CubeTemplate) (F : pkgB2_BaseRow T → ℝ) :
    ∏ o : Fin (Fintype.card (pkgB2_Occurrence T ∅)), F (pkgB2_occurrenceEnum T ∅ o).1 =
      ∏ t, F t := by
  rw [(pkgB2_occurrenceEnum T ∅).prod_comp (fun o => F o.1)]
  exact (opus_dpo_occEmptyEquiv T).prod_comp F

theorem opus_dpo_oldSum_root {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (X : pkgB2_OldCoord T → ℤ) :
    ∑ old, pkgB2_oldCoefficient T M (.inl ()) old * X old = X (.inl ()) := by
  rw [Fintype.sum_sum_type]
  simp [pkgB2_oldCoefficient]

theorem opus_dpo_oldSum_row {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (s : pkgB2_Nonroot T) (X : pkgB2_OldCoord T → ℤ) :
    ∑ old, pkgB2_oldCoefficient T M (.inr s) old * X old =
      X (.inl ()) + M s.1 * ∑ j ∈ s.2.1,
        (X (.inr ⟨s.1, (j, 1)⟩) - X (.inr ⟨s.1, (j, 0)⟩)) := by
  classical
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h1v : (1 : Fin 2).val ≠ 0 := by decide
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  rw [Finset.sum_eq_single s.1 (fun k _ hk => by
    apply Finset.sum_eq_zero
    intro js _
    rw [opus_dpo_oldCoeff_ne T _ s k hk js.1 js.2, zero_mul]) (by simp)]
  congr 1
  · simp [pkgB2_oldCoefficient]
  · rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, opus_dpo_oldCoeff_same, Fin.val_zero, h1v, if_true, if_false]
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => j ∈ s.2.1)]
    have hfil : Finset.univ.filter (fun j => j ∈ s.2.1) = s.2.1 := by ext; simp
    rw [hfil, Finset.sum_eq_zero (s := Finset.univ.filter (fun j => ¬ j ∈ s.2.1))
      (fun j hj => by simp [(Finset.mem_filter.mp hj).2]), add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hj, if_true]
    ring

/-- The stage-`∅` row values with all translations zero. -/
theorem opus_dpo_rowValue_zero {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ)
    (p : Fin (b * sl) → ℕ) (o : Fin (Fintype.card (pkgB2_Occurrence T ∅)))
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    pkgB2_stateRowValue MS T hT J0 gap direction ∅ N p o (opus_dpo_zeroTranslations T x) =
      ∑ old, pkgB2_oldCoefficient T
        (fun k => ((T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) : ℤ))
        (pkgB2_occurrenceEnum T ∅ o).1 old * x ((pkgB2_coordEnum T).symm (.inl old)) := by
  classical
  set M : Fin b → ℕ := fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k)
    with hM
  set e := pkgB2_coordEnum T
  set cI := pkgB2_occurrenceCoefficientInt T M direction ∅ (pkgB2_occurrenceEnum T ∅ o)
  unfold pkgB2_stateRowValue
  have hre (y : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
      (∑ j, ((cI (e j) : ℤ) : ℚ) * (y j : ℚ)) = ((∑ c, cI c * y (e.symm c) : ℤ) : ℚ) := by
    rw [← e.sum_comp (fun c => cI c * y (e.symm c))]
    push_cast
    simp
  have hlin : linearRowValue (pkgB2_rowCoefficientArray MS T hT J0 gap direction ∅) N p o
      (opus_dpo_zeroTranslations T x) =
      ((∑ c, cI c * opus_dpo_zeroTranslations T x (e.symm c) : ℤ) : ℚ) := by
    unfold linearRowValue pkgB2_rowCoefficientArray pkgB2_occurrenceCoefficient
    exact hre _
  rw [hlin, Rat.num_intCast, opus_dpo_sum_coord]
  have hcoeffO (old : pkgB2_OldCoord T) :
      cI (.inl old) = pkgB2_oldCoefficient T (fun k => (M k : ℤ))
        (pkgB2_occurrenceEnum T ∅ o).1 old := by
    simp [cI, pkgB2_occurrenceCoefficientInt, pkgB2_copyCoeffInt]
  have hz (tr : pkgB2_Nonroot T × Fin 2) :
      opus_dpo_zeroTranslations T x (e.symm (.inr tr)) = 0 := by
    simp [opus_dpo_zeroTranslations, e]
  have hz' (old : pkgB2_OldCoord T) :
      opus_dpo_zeroTranslations T x (e.symm (.inl old)) = x (e.symm (.inl old)) := by
    simp [opus_dpo_zeroTranslations, e]
  simp only [hz, mul_zero, Finset.sum_const_zero, add_zero, hz', hcoeffO]
  rfl

/-- The block function of replica `k`: the product of its nonroot inputs. -/
def opus_dpo_block {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (T : CubeTemplate) (N : ℕ)
    (I : DualInput MS B T N) (q : Fin T.q → ℕ) (y : ℤ) (u : Fin T.d → Fin 2 → ℤ) : ℝ :=
  ∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅,
    I.g ω q (y + (T.modulus (corrScales MS) N q : ℤ) * ∑ j ∈ ω, (u j 1 - u j 0))

/-- The stage-`∅` integrand with zero translations in structured coordinates. -/
theorem opus_dpo_integrand_zero {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ) (w : opus_dpo_Y T) :
    pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
        (opus_dpo_zeroTranslations T ((opus_dpo_coordE T).symm w)) =
      (∏ k, (I k).e (pkgB2_repPrimeProject hT p k)) *
        ((nu MS.core.parameters N B w.1 - 1) *
          ∏ k, opus_dpo_block MS B (T k) N (I k) (pkgB2_repPrimeProject hT p k) w.1 (w.2.1 k)) := by
  classical
  set M : Fin b → ℤ := fun k =>
    ((T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) : ℤ) with hM
  let x := (opus_dpo_coordE T).symm w
  have hxold (old : pkgB2_OldCoord T) :
      x ((pkgB2_coordEnum T).symm (.inl old)) = (opus_dpo_coordY T).symm w (.inl old) := by
    simp [x, opus_dpo_coordE_symm_apply]
  let F : pkgB2_BaseRow T → ℝ := fun t => match t with
    | .inl _ => nu MS.core.parameters N B w.1 - 1
    | .inr r => (I r.1).g r.2.1 (pkgB2_repPrimeProject hT p r.1)
        (w.1 + M r.1 * ∑ j ∈ r.2.1, (w.2.1 r.1 j 1 - w.2.1 r.1 j 0))
  have hfactor (o : Fin (Fintype.card (pkgB2_Occurrence T ∅))) :
      pkgB2_stateFactor MS B gap T hT J0 direction ∅ N I p (opus_dpo_zeroTranslations T x) o =
        F (pkgB2_occurrenceEnum T ∅ o).1 := by
    have hrv := opus_dpo_rowValue_zero MS T hT J0 gap direction N p o x
    simp only [hxold] at hrv
    simp only [pkgB2_stateFactor]
    rcases ht : (pkgB2_occurrenceEnum T ∅ o).1 with u | r
    · rw [ht] at hrv
      rw [opus_dpo_oldSum_root] at hrv
      simp only [F, hrv]
      rfl
    · rw [ht] at hrv
      rw [opus_dpo_oldSum_row] at hrv
      simp only [F, Finset.notMem_empty, if_false, hrv]
      rfl
  unfold pkgB2_stateIntegrand
  simp only [if_true]
  rw [Finset.prod_congr rfl (fun o _ => hfactor o)]
  rw [opus_dpo_prod_occEmpty T F, opus_dpo_prod_baseRow, opus_dpo_prod_nonroot]
  congr 2
  apply Finset.prod_congr rfl
  intro k _
  unfold opus_dpo_block
  apply Finset.prod_congr rfl
  intro ω hω
  have hne : ω.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact (Finset.mem_erase.mp hω).1
  rw [dif_pos hne]


theorem opus_dpo_unif_zero (L : ℕ) (z : ℤ) (hz : z ∉ Finset.Ico (0 : ℤ) L) :
    FromArithmetic.uniformIntegerIntervalLaw 0 L z = 0 := by
  unfold FromArithmetic.uniformIntegerIntervalLaw
  rw [if_neg]
  intro h
  apply hz
  rw [Finset.mem_Ico]
  constructor <;> linarith [h.1, h.2]

theorem opus_dpo_unif_sum (L : ℕ) (hL : 0 < L) :
    ∑ z ∈ Finset.Ico (0 : ℤ) L, FromArithmetic.uniformIntegerIntervalLaw 0 L z = 1 := by
  have hterm : ∀ z ∈ Finset.Ico (0 : ℤ) L,
      FromArithmetic.uniformIntegerIntervalLaw 0 L z = 1 / (L : ℝ) := by
    intro z hz
    rw [Finset.mem_Ico] at hz
    unfold FromArithmetic.uniformIntegerIntervalLaw
    rw [if_pos]
    constructor <;> linarith [hz.1, hz.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Int.card_Ico, sub_zero, Int.toNat_natCast,
    nsmul_eq_mul]
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

/-- A uniform shift box on `ℤ` is the natural-number shift average. -/
theorem opus_dpo_shiftSum (d L : ℕ) (G : (Fin d → Fin 2 → ℤ) → ℝ) :
    ∑ u ∈ Fintype.piFinset (fun _ : Fin d => Fintype.piFinset
        (fun _ : Fin 2 => Finset.Ico (0 : ℤ) L)),
      (∏ j, ∏ s, FromArithmetic.uniformIntegerIntervalLaw 0 L (u j s)) * G u =
      shiftAverage (Fin d) L (fun u => G (fun j s => (u j s : ℤ))) := by
  classical
  rw [shiftAverage_eq_uniformIntervalSum]
  symm
  apply Finset.sum_nbij' (fun u j s => ((u j s : ℕ) : ℤ)) (fun u j s => (u j s).toNat)
  · intro u hu
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_Ico] at hu ⊢
    intro j s
    have := hu j s
    omega
  · intro u hu
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_Ico] at hu ⊢
    intro j s
    have := hu j s
    omega
  · intro u _
    funext j s
    simp
  · intro u hu
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico] at hu
    funext j s
    exact Int.toNat_of_nonneg (hu j s).1
  · intro u _
    rfl

/-- The untranslated stage-`∅` inner integral at a regular prime tuple, in the form of the dual
tests: pivot average of `(ν − 1)` times the product over replicas of `e` and the shift average. -/
theorem opus_dpo_inner_replica {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (hreg : pkgB2_baseRegular MS B T J0 gap hT N p) :
    (∑' x, pkgB2_baseMass MS B T J0 gap hT N p x *
        pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
          (opus_dpo_zeroTranslations T x)) =
      ∑' y : ℤ, harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1)) y *
        ((nu MS.core.parameters N B y - 1) *
          ∏ k, ((I k).e (pkgB2_repPrimeProject hT p k) *
            shiftAverage (Fin (T k).d) (pkgB2_shiftLength MS T J0 gap hT N p k) (fun u =>
              opus_dpo_block MS B (T k) N (I k) (pkgB2_repPrimeProject hT p k) y
                (fun j s => (u j s : ℤ))))) := by
  classical
  let law := pkgB2_baseCoordinateLaw MS B T J0 gap hT N p
  let harm := harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))
  let L : Fin b → ℕ := pkgB2_shiftLength MS T J0 gap hT N p
  let A : Fin b → ℕ := fun k => pkgB2_translationLength MS T J0 gap k N
  let unif := FromArithmetic.uniformIntegerIntervalLaw 0
  let eP : ℝ := ∏ k, (I k).e (pkgB2_repPrimeProject hT p k)
  let Bk : (k : Fin b) → ℤ → (Fin (T k).d → Fin 2 → ℤ) → ℝ := fun k y u =>
    opus_dpo_block MS B (T k) N (I k) (pkgB2_repPrimeProject hT p k) y u
  let Ulaw : ((k : Fin b) → Fin (T k).d → Fin 2 → ℤ) → ℝ := fun u =>
    ∏ k, ∏ j, ∏ s, unif (L k) (u k j s)
  let Vlaw : (pkgB2_Nonroot T × Fin 2 → ℤ) → ℝ := fun v =>
    ∏ tr, unif (A tr.1.1) (v tr)
  let Wy : Finset ℤ := pkgB2_baseWindow MS B T J0 gap hT N p
  let Ufin : Finset ((k : Fin b) → Fin (T k).d → Fin 2 → ℤ) :=
    Fintype.piFinset fun k => Fintype.piFinset fun _ : Fin (T k).d =>
      Fintype.piFinset fun _ : Fin 2 => Finset.Ico (0 : ℤ) (L k)
  let Vfin : Finset (pkgB2_Nonroot T × Fin 2 → ℤ) :=
    Fintype.piFinset fun tr => Finset.Ico (0 : ℤ) (A tr.1.1)
  let Sfin : Finset (opus_dpo_Y T) := Wy ×ˢ (Ufin ×ˢ Vfin)
  let Ψ : opus_dpo_Y T → ℝ := fun w =>
    eP * ((nu MS.core.parameters N B w.1 - 1) * ∏ k, Bk k w.1 (w.2.1 k))
  have hharm (y : ℤ) : law (.inl (.inl ())) y = harm y := rfl
  have hbaseY (w : opus_dpo_Y T) :
      pkgB2_baseMass MS B T J0 gap hT N p ((opus_dpo_coordE T).symm w) =
        harm w.1 * Ulaw w.2.1 * Vlaw w.2.2 := by
    simp only [pkgB2_baseMass, dif_pos hreg]
    have h1 : (∏ i, pkgB2_baseCoordinateLaw MS B T J0 gap hT N p (pkgB2_coordEnum T i)
        ((opus_dpo_coordE T).symm w i)) =
        ∏ c, law c ((opus_dpo_coordY T).symm w c) := by
      rw [← (pkgB2_coordEnum T).prod_comp (fun c => law c ((opus_dpo_coordY T).symm w c))]
      apply Finset.prod_congr rfl
      intro i _
      rw [opus_dpo_coordE_symm_apply]
    rw [h1, opus_dpo_prod_coord]
    congr 1
  have hint (w : opus_dpo_Y T) :
      pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
        (opus_dpo_zeroTranslations T ((opus_dpo_coordE T).symm w)) = Ψ w :=
    opus_dpo_integrand_zero MS B gap T hT J0 direction N I p w
  have hstep1 : (∑' x, pkgB2_baseMass MS B T J0 gap hT N p x *
        pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
          (opus_dpo_zeroTranslations T x)) =
      ∑' w : opus_dpo_Y T, harm w.1 * Ulaw w.2.1 * Vlaw w.2.2 * Ψ w := by
    rw [← (opus_dpo_coordE T).symm.tsum_eq]
    apply tsum_congr
    intro w
    rw [hbaseY, hint]
  have hzeroY : ∀ w ∉ Sfin, harm w.1 * Ulaw w.2.1 * Vlaw w.2.2 * Ψ w = 0 := by
    intro w hw
    rcases w with ⟨y, u, v⟩
    simp only [Sfin, Finset.mem_product, not_and_or] at hw
    rcases hw with hy | hu | hv
    · have : harm y = 0 := by
        rw [← hharm]
        exact pkgB2_baseCoordinateLaw_zero_outside MS B T J0 gap hT N p _ y hy
      simp [this]
    · have : Ulaw u = 0 := by
        simp only [Ufin, Fintype.mem_piFinset, not_forall] at hu
        obtain ⟨k, j, s, hks⟩ := hu
        exact Finset.prod_eq_zero (Finset.mem_univ k) (Finset.prod_eq_zero (Finset.mem_univ j)
          (Finset.prod_eq_zero (Finset.mem_univ s) (opus_dpo_unif_zero _ _ hks)))
      simp [this]
    · have : Vlaw v = 0 := by
        simp only [Vfin, Fintype.mem_piFinset, not_forall] at hv
        obtain ⟨tr, htr⟩ := hv
        exact Finset.prod_eq_zero (Finset.mem_univ tr) (opus_dpo_unif_zero _ _ htr)
      simp [this]
  have hVsum : ∑ v ∈ Vfin, Vlaw v = 1 := by
    simp only [Vfin, Vlaw]
    rw [← Finset.prod_univ_sum]
    exact Finset.prod_eq_one fun tr _ => opus_dpo_unif_sum _ (hreg.2.2 tr.1.1)
  have hUsum (y : ℤ) : ∑ u ∈ Ufin, Ulaw u * ∏ k, Bk k y (u k) =
      ∏ k, shiftAverage (Fin (T k).d) (L k) (fun u => Bk k y (fun j s => (u j s : ℤ))) := by
    have h := (Finset.prod_univ_sum (fun k => Fintype.piFinset fun _ : Fin (T k).d =>
      Fintype.piFinset fun _ : Fin 2 => Finset.Ico (0 : ℤ) (L k))
      (fun k uk => (∏ j, ∏ s, unif (L k) (uk j s)) * Bk k y uk))
    simp only [Ufin, Ulaw]
    calc
      _ = ∑ u ∈ Fintype.piFinset (fun k => Fintype.piFinset fun _ : Fin (T k).d =>
            Fintype.piFinset fun _ : Fin 2 => Finset.Ico (0 : ℤ) (L k)),
          ∏ k, ((∏ j, ∏ s, unif (L k) (u k j s)) * Bk k y (u k)) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.prod_mul_distrib]
      _ = ∏ k, ∑ uk ∈ Fintype.piFinset (fun _ : Fin (T k).d =>
            Fintype.piFinset fun _ : Fin 2 => Finset.Ico (0 : ℤ) (L k)),
          (∏ j, ∏ s, unif (L k) (uk j s)) * Bk k y uk := h.symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro k _
        exact opus_dpo_shiftSum (T k).d (L k) (Bk k y)
  rw [hstep1, tsum_eq_sum (s := Sfin) hzeroY]
  rw [tsum_eq_sum (s := Wy) (fun y hy => by
    have : harm y = 0 := by
      rw [← hharm]
      exact pkgB2_baseCoordinateLaw_zero_outside MS B T J0 gap hT N p _ y hy
    change harm y * _ = 0
    rw [this, zero_mul])]
  simp only [Sfin, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y _
  have hinner : ∀ u, ∑ v ∈ Vfin, harm y * Ulaw u * Vlaw v * Ψ (y, u, v) =
      harm y * Ulaw u * Ψ (y, u, (fun _ => 0)) := by
    intro u
    calc
      _ = ∑ v ∈ Vfin, (harm y * Ulaw u * Ψ (y, u, v)) * Vlaw v := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ v ∈ Vfin, (harm y * Ulaw u * Ψ (y, u, (fun _ => 0))) * Vlaw v := by
        apply Finset.sum_congr rfl
        intro v _
        rfl
      _ = harm y * Ulaw u * Ψ (y, u, (fun _ => 0)) := by
        rw [← Finset.mul_sum, hVsum, mul_one]
  simp only [hinner]
  calc
    _ = harm y * (eP * (nu MS.core.parameters N B y - 1)) *
        ∑ u ∈ Ufin, Ulaw u * ∏ k, Bk k y (u k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      simp only [Ψ]
      ring
    _ = _ := by
      rw [hUsum y, Finset.prod_mul_distrib]
      simp only [eP, Bk]
      ring


/-! ### Replica identity: prime-slot factorization -/

private noncomputable def opus_dpo_rep_blockTupleEquiv {b sl M : ℕ} :
    (Fin (b * sl) → Fin M) ≃ (Fin b → Fin sl → Fin M) where
  toFun p k j := p (pkgB2_replicaEmbedding k j)
  invFun p i := p ((finProdFinEquiv (m := b) (n := sl)).symm i).1
      ((finProdFinEquiv (m := b) (n := sl)).symm i).2
  left_inv := by
    intro p
    funext i
    exact congrArg p ((finProdFinEquiv (m := b) (n := sl)).apply_symm_apply i)
  right_inv := by
    intro p
    funext k j
    exact congrArg (fun z : Fin b × Fin sl => p z.1 z.2)
      ((finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j))

private noncomputable def opus_dpo_rep_poolRangeTupleEquiv {m M : ℕ} :
    {p : Fin m → ℕ // p ∈ Fintype.piFinset (fun _ : Fin m => Finset.range M)} ≃
      (Fin m → Fin M) where
  toFun p i := ⟨p.1 i, by
    have hi := Fintype.mem_piFinset.mp p.2 i
    exact Finset.mem_range.mp hi⟩
  invFun p := ⟨fun i => (p i).val, Fintype.mem_piFinset.mpr (fun i =>
    Finset.mem_range.mpr (p i).isLt)⟩
  left_inv := by
    intro p
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    intro p
    funext i
    apply Fin.ext
    rfl

private def opus_dpo_rep_allGood {b sl : ℕ}
    (G : ∀ k : Fin b, (Fin sl → ℕ) → Prop)
    (p : Fin (b * sl) → ℕ) : Prop :=
  ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))

private theorem opus_dpo_rep_primePoolExpectation_finite {m : ℕ}
    (lo hi : Fin m → ℕ) (M : ℕ) (hhi : ∀ i, hi i ≤ M)
    (E : (Fin m → ℕ) → Prop) [DecidablePred E] (F : (Fin m → ℕ) → ℝ) :
    ∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p *
        (if E p then F p else 0) =
      ∑ p : Fin m → Fin M,
        (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if E (fun i => (p i).val) then F (fun i => (p i).val) else 0) := by
  classical
  let S : Finset (Fin m → ℕ) := Fintype.piFinset
    (fun _ : Fin m => Finset.range M)
  have htermZero (p : Fin m → ℕ) (hp : p ∉ S) :
      independentPrimePoolMass lo hi p * (if E p then F p else 0) = 0 := by
    have hnot : ¬ ∀ i : Fin m, p i ∈ Finset.range M := by
      intro hall
      apply hp
      simpa [S, Fintype.mem_piFinset] using hall
    obtain ⟨i, hiMem⟩ := not_forall.mp hnot
    have hmass : independentPrimePoolMass lo hi p = 0 := by
      unfold independentPrimePoolMass
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      unfold primePoolLaw
      split_ifs with h
      · exact False.elim (hiMem (Finset.mem_range.mpr
          (lt_of_lt_of_le h.2.1 (hhi i))))
      · rfl
    simp [hmass]
  have hsum :
      ∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p *
          (if E p then F p else 0) =
        ∑ p ∈ S, independentPrimePoolMass lo hi p * (if E p then F p else 0) :=
    tsum_eq_sum (s := S) htermZero
  have hattach :
      (∑ p ∈ S, independentPrimePoolMass lo hi p * (if E p then F p else 0)) =
        ∑ p : {p : Fin m → ℕ // p ∈ S},
          independentPrimePoolMass lo hi p.1 * (if E p.1 then F p.1 else 0) := by
    rw [← Finset.sum_attach]
    simp
  calc
    _ = ∑ p : {p : Fin m → ℕ // p ∈ S},
          independentPrimePoolMass lo hi p.1 * (if E p.1 then F p.1 else 0) := by
            rw [hsum, hattach]
    _ = ∑ p : Fin m → Fin M,
          (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
            (if E (fun i => (p i).val) then F (fun i => (p i).val) else 0) := by
          apply Fintype.sum_equiv (opus_dpo_rep_poolRangeTupleEquiv (m := m) (M := M))
          intro p
          have hval :
              (fun i => ((opus_dpo_rep_poolRangeTupleEquiv (m := m) (M := M) p) i).val) = p.1 := by
            funext i
            rfl
          simp only [independentPrimePoolMass]
          rw [← hval]

private theorem opus_dpo_rep_blockExpectation_factor {b sl M : ℕ}
    (lo hi : Fin (b * sl) → ℕ) (loBlock hiBlock : Fin b → ℕ)
    (hlo : ∀ k j, lo (pkgB2_replicaEmbedding k j) = loBlock k)
    (hhi : ∀ k j, hi (pkgB2_replicaEmbedding k j) = hiBlock k)
    (hbound : (∀ i, hi i ≤ M) ∧ ∀ k, hiBlock k ≤ M)
    (G : ∀ k : Fin b, (Fin sl → ℕ) → Prop)
    (F : ∀ k : Fin b, (Fin sl → ℕ) → ℝ) :
    ∑' p : Fin (b * sl) → ℕ,
        independentPrimePoolMass lo hi p *
          (if opus_dpo_rep_allGood G p then
            ∏ k, F k (fun j => p (pkgB2_replicaEmbedding k j)) else 0) =
      ∏ k, ∑' q : Fin sl → ℕ,
        independentPrimePoolMass (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) q * (if G k q then F k q else 0) := by
  classical
  let Btuple := opus_dpo_rep_blockTupleEquiv (b := b) (sl := sl) (M := M)
  let term : ∀ k, (Fin sl → Fin M) → ℝ := fun k q =>
    (∏ j, primePoolLaw (loBlock k) (hiBlock k) (q j).val) *
      (if G k (fun j => (q j).val) then F k (fun j => (q j).val) else 0)
  have hmass (p : Fin (b * sl) → Fin M) :
      independentPrimePoolMass lo hi (fun i => (p i).val) =
        ∏ k, ∏ j, primePoolLaw (loBlock k) (hiBlock k)
          (p (pkgB2_replicaEmbedding k j)).val := by
    unfold independentPrimePoolMass
    calc
      ∏ i : Fin (b * sl), primePoolLaw (lo i) (hi i) (p i).val =
          ∏ z : Fin b × Fin sl,
            primePoolLaw (lo (finProdFinEquiv (m := b) (n := sl) z))
              (hi (finProdFinEquiv (m := b) (n := sl) z))
              (p (finProdFinEquiv (m := b) (n := sl) z)).val := by
                symm
                exact Fintype.prod_equiv (finProdFinEquiv (m := b) (n := sl))
                  (fun z => primePoolLaw (lo (finProdFinEquiv (m := b) (n := sl) z))
                    (hi (finProdFinEquiv (m := b) (n := sl) z))
                    (p (finProdFinEquiv (m := b) (n := sl) z)).val)
                  (fun i => primePoolLaw (lo i) (hi i) (p i).val) (by intro z; rfl)
      _ = ∏ k : Fin b, ∏ j : Fin sl,
            primePoolLaw (loBlock k) (hiBlock k)
              (p (pkgB2_replicaEmbedding k j)).val := by
                rw [Fintype.prod_prod_type]
                apply Finset.prod_congr rfl
                intro k hk
                apply Finset.prod_congr rfl
                intro j hj
                have hlo' : lo (finProdFinEquiv (m := b) (n := sl) (k, j)) = loBlock k := by
                  have he : pkgB2_replicaEmbedding k j =
                      finProdFinEquiv (m := b) (n := sl) (k, j) := rfl
                  rw [← he]
                  exact hlo k j
                have hhi' : hi (finProdFinEquiv (m := b) (n := sl) (k, j)) = hiBlock k := by
                  have he : pkgB2_replicaEmbedding k j =
                      finProdFinEquiv (m := b) (n := sl) (k, j) := rfl
                  rw [← he]
                  exact hhi k j
                rw [hlo', hhi']
                rfl
  have hterm (p : Fin (b * sl) → Fin M) :
      (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if opus_dpo_rep_allGood G (fun i => (p i).val) then
            ∏ k, F k (fun j => (p (pkgB2_replicaEmbedding k j)).val) else 0) =
        ∏ k, term k (fun j => p (pkgB2_replicaEmbedding k j)) := by
    have hEvent :
        (if opus_dpo_rep_allGood G (fun i => (p i).val) then
            (∏ k, F k (fun j => (p (pkgB2_replicaEmbedding k j)).val)) else 0) =
          ∏ k, if G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then
            F k (fun j => (p (pkgB2_replicaEmbedding k j)).val) else 0 := by
      by_cases hall : ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val)
      · simp [opus_dpo_rep_allGood, hall]
      · obtain ⟨k, hk⟩ := not_forall.mp hall
        have hzero : ∏ k' : Fin b,
            (if G k' (fun j => (p (pkgB2_replicaEmbedding k' j)).val) then
              F k' (fun j => (p (pkgB2_replicaEmbedding k' j)).val) else 0) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
        simpa [opus_dpo_rep_allGood, hall] using hzero.symm
    calc
      _ = independentPrimePoolMass lo hi (fun i => (p i).val) *
            (if opus_dpo_rep_allGood G (fun i => (p i).val) then
              ∏ k, F k (fun j => (p (pkgB2_replicaEmbedding k j)).val) else 0) := by rfl
      _ = (∏ k, ∏ j, primePoolLaw (loBlock k) (hiBlock k)
              (p (pkgB2_replicaEmbedding k j)).val) *
            (∏ k, if G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then
              F k (fun j => (p (pkgB2_replicaEmbedding k j)).val) else 0) := by
                rw [hmass p, hEvent]
      _ = ∏ k, term k (fun j => p (pkgB2_replicaEmbedding k j)) := by
                simp only [term]
                rw [← Finset.prod_mul_distrib]
  have hfactor :
      (∑ p : Fin (b * sl) → Fin M,
        (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if opus_dpo_rep_allGood G (fun i => (p i).val) then
            ∏ k, F k (fun j => (p (pkgB2_replicaEmbedding k j)).val) else 0)) =
        ∏ k, ∑ q : Fin sl → Fin M, term k q := by
    calc
      _ = ∑ q : Fin b → Fin sl → Fin M, ∏ k, term k (q k) := by
        apply Fintype.sum_equiv Btuple
        intro p
        have hB (k : Fin b) : Btuple p k =
            fun j => p (pkgB2_replicaEmbedding k j) := rfl
        simpa only [hB] using hterm p
      _ = ∏ k, ∑ q : Fin sl → Fin M, term k q := by
        symm
        exact Fintype.prod_sum (fun k q => term k q)
  have hglobal := opus_dpo_rep_primePoolExpectation_finite lo hi M hbound.1
    (fun p => opus_dpo_rep_allGood G p)
    (fun p => ∏ k, F k (fun j => p (pkgB2_replicaEmbedding k j)))
  have hlocal (k : Fin b) := opus_dpo_rep_primePoolExpectation_finite
    (fun _ : Fin sl => loBlock k) (fun _ => hiBlock k) M (fun _ => hbound.2 k)
    (G k) (F k)
  calc
    _ = ∑ p : Fin (b * sl) → Fin M,
          (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
            (if opus_dpo_rep_allGood G (fun i => (p i).val) then
              ∏ k, F k (fun j => (p (pkgB2_replicaEmbedding k j)).val) else 0) := hglobal
    _ = ∏ k, ∑ q : Fin sl → Fin M, term k q := hfactor
    _ = ∏ k, ∑' q : Fin sl → ℕ,
          independentPrimePoolMass (fun _ : Fin sl => loBlock k)
            (fun _ => hiBlock k) q * (if G k q then F k q else 0) := by
          apply Finset.prod_congr rfl
          intro k hk
          symm
          exact hlocal k

private theorem opus_dpo_rep_repGoodProbability_eq_product {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (hpool : ∀ k, 0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
      (MS.primeStage.pool N (gap k)).upper) :
    independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (pkgB2_goodPrimeEvent MS gap T hT N) =
      ∏ k, gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
  classical
  let lo : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let loBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).lower
  let hiBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).upper
  let M : ℕ := ∑ k : Fin b, hiBlock k
  let G : ∀ k : Fin b, (Fin sl → ℕ) → Prop := fun k q =>
    (T k).Good (corrScales MS) (gap k) N
      (fun j => q ((Classical.choose (hT k)) j))
  have hlo : ∀ k j, lo (pkgB2_replicaEmbedding k j) = loBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).lower = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  have hhi : ∀ k j, hi (pkgB2_replicaEmbedding k j) = hiBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).upper = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  have hboundFull : ∀ i, hi i ≤ M := by
    intro i
    let k := (finProdFinEquiv (m := b) (n := sl)).symm i |>.1
    let j := (finProdFinEquiv (m := b) (n := sl)).symm i |>.2
    have he : pkgB2_replicaEmbedding k j = i := by
      dsimp [pkgB2_replicaEmbedding, k, j]
      exact (finProdFinEquiv (m := b) (n := sl)).apply_symm_apply i
    rw [← he, hhi]
    dsimp [M, hiBlock]
    exact Finset.single_le_sum (f := fun k' => hiBlock k')
      (fun k' _ => Nat.zero_le _) (Finset.mem_univ k)
  have hboundBlock : ∀ k, hiBlock k ≤ M := by
    intro k
    dsimp [M]
    exact Finset.single_le_sum (f := fun k' => hiBlock k')
      (fun k' _ => Nat.zero_le _) (Finset.mem_univ k)
  have hproject (p : Fin (b * sl) → ℕ) (k : Fin b) :
      pkgB2_repPrimeProject hT p k =
        fun j => p (pkgB2_replicaEmbedding k ((Classical.choose (hT k)) j)) := by
    funext j
    rfl
  have hfullEvent :
      (pkgB2_goodPrimeEvent MS gap T hT N) =
        (fun p => opus_dpo_rep_allGood G p) := by
    funext p
    apply propext
    apply forall_congr'
    intro k
    rw [hproject p k]
  have hfactor := opus_dpo_rep_blockExpectation_factor lo hi loBlock hiBlock hlo hhi
    ⟨hboundFull, hboundBlock⟩ G (fun _ _ => 1)
  calc
    independentPrimePoolProbability lo hi (pkgB2_goodPrimeEvent MS gap T hT N) =
        independentPrimePoolProbability lo hi (fun p => opus_dpo_rep_allGood G p) := by
            rw [hfullEvent]
    _ = ∏ k, independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (G k) := by
            simpa [independentPrimePoolProbability] using hfactor
    _ = ∏ k, gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N) := by
            apply Finset.prod_congr rfl
            intro k hk
            have hmarginal := independentPrimePoolProbability_iid_marginal
              (loBlock k) (hiBlock k) (hpool k) (Classical.choose (hT k))
              ((T k).Good (corrScales MS) (gap k) N)
            simpa [G, gapSlotProbability, loBlock, hiBlock, corrScales] using hmarginal.symm

private abbrev opus_dpo_rep_EmbeddingComplement {q m : ℕ} (ι : Fin q ↪ Fin m) :=
  {j : Fin m // j ∉ Finset.univ.image ι}

private noncomputable def opus_dpo_rep_embeddingIndexEquiv {q m : ℕ} (ι : Fin q ↪ Fin m) :
    Fin q ⊕ opus_dpo_rep_EmbeddingComplement ι ≃ Fin m := by
  classical
  let R : Finset (Fin m) := Finset.univ.image ι
  refine
    { toFun := fun x => match x with
        | .inl i => ι i
        | .inr j => j.1
      invFun := fun j => if hj : j ∈ R then
        Sum.inl (Classical.choose (Finset.mem_image.mp hj))
      else Sum.inr ⟨j, hj⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    cases x with
    | inl i =>
        have hmem : ι i ∈ R := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        simp only [dif_pos hmem]
        congr 1
        apply ι.injective
        exact (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    | inr j => simp [R, j.2]
  · intro j
    by_cases hmem : j ∈ R
    · simp only [dif_pos hmem]
      exact (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    · simp [hmem]

private noncomputable def opus_dpo_rep_embeddingTupleEquiv {q m : ℕ} (ι : Fin q ↪ Fin m) :
    (Fin m → ℕ) ≃ ((Fin q → ℕ) × (opus_dpo_rep_EmbeddingComplement ι → ℕ)) :=
  ((opus_dpo_rep_embeddingIndexEquiv ι).arrowCongr (Equiv.refl ℕ)).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin q) (opus_dpo_rep_EmbeddingComplement ι) ℕ)

private theorem opus_dpo_rep_embeddingTupleEquiv_apply_left {q m : ℕ}
    (ι : Fin q ↪ Fin m) (p : Fin m → ℕ) (i : Fin q) :
    (opus_dpo_rep_embeddingTupleEquiv ι p).1 i = p (ι i) := by
  simp [opus_dpo_rep_embeddingTupleEquiv, Equiv.trans_apply, opus_dpo_rep_embeddingIndexEquiv]

private theorem opus_dpo_rep_embeddingTupleEquiv_apply_right {q m : ℕ}
    (ι : Fin q ↪ Fin m) (p : Fin m → ℕ) (i : opus_dpo_rep_EmbeddingComplement ι) :
    (opus_dpo_rep_embeddingTupleEquiv ι p).2 i = p i.1 := by
  simp [opus_dpo_rep_embeddingTupleEquiv, Equiv.trans_apply, opus_dpo_rep_embeddingIndexEquiv]

private theorem opus_dpo_rep_embeddingMass_split {q m : ℕ}
    (ι : Fin q ↪ Fin m) (lo hi : ℕ) (p : Fin m → ℕ) :
    independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p =
      independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi)
          (opus_dpo_rep_embeddingTupleEquiv ι p).1 *
        (∏ j : opus_dpo_rep_EmbeddingComplement ι,
          primePoolLaw lo hi ((opus_dpo_rep_embeddingTupleEquiv ι p).2 j)) := by
  classical
  unfold independentPrimePoolMass
  calc
    (∏ j : Fin m, primePoolLaw lo hi (p j)) =
        ∏ z : Fin q ⊕ opus_dpo_rep_EmbeddingComplement ι,
          primePoolLaw lo hi (p (opus_dpo_rep_embeddingIndexEquiv ι z)) := by
      symm
      exact Fintype.prod_equiv (opus_dpo_rep_embeddingIndexEquiv ι)
        (fun z => primePoolLaw lo hi (p (opus_dpo_rep_embeddingIndexEquiv ι z)))
        (fun j => primePoolLaw lo hi (p j)) (by intro z; rfl)
    _ = (∏ i : Fin q, primePoolLaw lo hi
          ((opus_dpo_rep_embeddingTupleEquiv ι p).1 i)) *
        ∏ j : opus_dpo_rep_EmbeddingComplement ι, primePoolLaw lo hi
          ((opus_dpo_rep_embeddingTupleEquiv ι p).2 j) := by
      rw [Fintype.prod_sum_type]
      simp [opus_dpo_rep_embeddingTupleEquiv_apply_left,
        opus_dpo_rep_embeddingTupleEquiv_apply_right, opus_dpo_rep_embeddingIndexEquiv]

private theorem opus_dpo_rep_primeTupleMass_zero_of_not_mem {ι : Type*} [Fintype ι]
    (lo hi : ι → ℕ) (p : ι → ℕ)
    (hp : p ∉ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))) :
    (∏ i, primePoolLaw (lo i) (hi i) (p i)) = 0 := by
  classical
  have hnot : ¬ ∀ i, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    exact hp (Fintype.mem_piFinset.mpr hall)
  obtain ⟨i, hi'⟩ := not_forall.mp hnot
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi' (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private theorem opus_dpo_rep_primePoolLaw_tsum_one {lo hi : ℕ}
    (hMass : 0 < primePoolMass lo hi) :
    ∑' p : ℕ, primePoolLaw lo hi p = 1 := by
  classical
  have hzero : ∀ p ∉ Finset.Ico lo hi, primePoolLaw lo hi p = 0 := by
    intro p hp
    have hp' : ¬ (lo ≤ p ∧ p < hi) := by
      simpa only [Finset.mem_Ico] using hp
    simp only [primePoolLaw]
    split_ifs with h
    · exact False.elim (hp' ⟨h.1, h.2.1⟩)
    · rfl
  calc
    _ = ∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p :=
      tsum_eq_sum (s := Finset.Ico lo hi) hzero
    _ = ∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
          (1 / (p : ℝ)) / primePoolMass lo hi := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro p hp
          simp [primePoolLaw, Finset.mem_Ico.mp hp]
    _ = (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime, 1 / (p : ℝ)) /
          primePoolMass lo hi := by rw [Finset.sum_div]
    _ = 1 := by
          rw [show (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime, 1 / (p : ℝ)) =
            primePoolMass lo hi by rfl]
          exact div_self (ne_of_gt hMass)

private theorem opus_dpo_rep_productPrimeLaw_tsum_one {ι : Type*} [Fintype ι]
    (lo hi : ℕ) (hMass : 0 < primePoolMass lo hi) :
    ∑' p : ι → ℕ, ∏ i, primePoolLaw lo hi (p i) = 1 := by
  classical
  let S : Finset (ι → ℕ) := Fintype.piFinset fun _ : ι => Finset.Ico lo hi
  have hzero (p : ι → ℕ) (hp : p ∉ S) :
      (∏ i, primePoolLaw lo hi (p i)) = 0 := by
    exact opus_dpo_rep_primeTupleMass_zero_of_not_mem (fun _ : ι => lo) (fun _ => hi) p
      (by simpa [S] using hp)
  have hfactor :
      (∑ p ∈ S, ∏ i, primePoolLaw lo hi (p i)) =
        ∏ i : ι, ∑ n ∈ Finset.Ico lo hi, primePoolLaw lo hi n := by
    simpa [S] using
      (Finset.prod_univ_sum (fun _ : ι => Finset.Ico lo hi)
        (fun _ n => primePoolLaw lo hi n)).symm
  have hzeroOne : ∀ n ∉ Finset.Ico lo hi, primePoolLaw lo hi n = 0 := by
    intro n hn
    have hn' : ¬ (lo ≤ n ∧ n < hi) := by
      simpa only [Finset.mem_Ico] using hn
    simp only [primePoolLaw]
    split_ifs with h
    · exact False.elim (hn' ⟨h.1, h.2.1⟩)
    · rfl
  have hlocal : ∑ n ∈ Finset.Ico lo hi, primePoolLaw lo hi n = 1 := by
    calc
      _ = ∑' n : ℕ, primePoolLaw lo hi n := (tsum_eq_sum (s := Finset.Ico lo hi) hzeroOne).symm
      _ = 1 := opus_dpo_rep_primePoolLaw_tsum_one hMass
  calc
    _ = ∑ p ∈ S, ∏ i, primePoolLaw lo hi (p i) := tsum_eq_sum (s := S) hzero
    _ = ∏ i : ι, ∑ n ∈ Finset.Ico lo hi, primePoolLaw lo hi n := hfactor
    _ = 1 := by simp [hlocal]

private theorem opus_dpo_rep_primePoolExpectation_embedding {q m : ℕ}
    (ι : Fin q ↪ Fin m) (lo hi : ℕ) (hMass : 0 < primePoolMass lo hi)
    (Good : (Fin q → ℕ) → Prop) (F : (Fin q → ℕ) → ℝ) :
    ∑' p : Fin m → ℕ,
        independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
          (if Good (fun i => p (ι i)) then F (fun i => p (ι i)) else 0) =
      ∑' p : Fin q → ℕ,
        independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
          (if Good p then F p else 0) := by
  classical
  let C := opus_dpo_rep_EmbeddingComplement ι
  let e := opus_dpo_rep_embeddingTupleEquiv ι
  let Sm : Finset (Fin m → ℕ) := Fintype.piFinset fun _ : Fin m => Finset.Ico lo hi
  let Sq : Finset (Fin q → ℕ) := Fintype.piFinset fun _ : Fin q => Finset.Ico lo hi
  let Sc : Finset (C → ℕ) := Fintype.piFinset fun _ : C => Finset.Ico lo hi
  let St : Finset ((Fin q → ℕ) × (C → ℕ)) := Sq ×ˢ Sc
  have hmem (p : Fin m → ℕ) : p ∈ Sm ↔ e p ∈ St := by
    simp only [Sm, Sq, Sc, St, Finset.mem_product, Fintype.mem_piFinset]
    constructor
    · intro hp
      constructor
      · intro i
        simpa only [e, opus_dpo_rep_embeddingTupleEquiv_apply_left] using hp (ι i)
      · intro j
        simpa only [e, opus_dpo_rep_embeddingTupleEquiv_apply_right] using hp j.1
    · rintro ⟨hpq, hpc⟩ j
      obtain ⟨z, rfl⟩ := (opus_dpo_rep_embeddingIndexEquiv ι).surjective j
      cases z with
      | inl i =>
          simpa [e, opus_dpo_rep_embeddingTupleEquiv_apply_left,
            opus_dpo_rep_embeddingIndexEquiv] using hpq i
      | inr c =>
          simpa [e, opus_dpo_rep_embeddingTupleEquiv_apply_right,
            opus_dpo_rep_embeddingIndexEquiv] using hpc c
  have hcompZero (c : C → ℕ) (hc : c ∉ Sc) :
      (∏ j : C, primePoolLaw lo hi (c j)) = 0 := by
    exact opus_dpo_rep_primeTupleMass_zero_of_not_mem (fun _ : C => lo) (fun _ => hi) c
      (by simpa [Sc] using hc)
  have hcompSum :
      ∑ c ∈ Sc, ∏ j : C, primePoolLaw lo hi (c j) = 1 := by
    calc
      _ = ∑' c : C → ℕ, ∏ j : C, primePoolLaw lo hi (c j) :=
        (tsum_eq_sum (s := Sc) hcompZero).symm
      _ = 1 := opus_dpo_rep_productPrimeLaw_tsum_one (ι := C) lo hi hMass
  have hglobalZero (p : Fin m → ℕ) (hp : p ∉ Sm) :
      independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        (if Good (fun i => p (ι i)) then F (fun i => p (ι i)) else 0) = 0 := by
    have hm : independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p = 0 := by
      unfold independentPrimePoolMass
      exact opus_dpo_rep_primeTupleMass_zero_of_not_mem (fun _ : Fin m => lo)
        (fun _ => hi) p (by simpa [Sm] using hp)
    rw [hm]
    ring
  have hqZero (p : Fin q → ℕ) (hp : p ∉ Sq) :
      independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        (if Good p then F p else 0) = 0 := by
    have hm : independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi) p = 0 := by
      unfold independentPrimePoolMass
      exact opus_dpo_rep_primeTupleMass_zero_of_not_mem (fun _ : Fin q => lo)
        (fun _ => hi) p (by simpa [Sq] using hp)
    rw [hm]
    ring
  have hsum :
      (∑ p ∈ Sm, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        (if Good (fun i => p (ι i)) then F (fun i => p (ι i)) else 0)) =
      ∑ rc ∈ St,
        (independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi) rc.1 *
          (∏ j : C, primePoolLaw lo hi (rc.2 j))) *
          (if Good rc.1 then F rc.1 else 0) := by
    apply Finset.sum_equiv e hmem
    intro p hp
    have hrestrict : (fun i : Fin q => p (ι i)) = (e p).1 := by
      funext i
      exact (opus_dpo_rep_embeddingTupleEquiv_apply_left ι p i).symm
    rw [opus_dpo_rep_embeddingMass_split, hrestrict]
  calc
    _ = ∑ p ∈ Sm, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
          (if Good (fun i => p (ι i)) then F (fun i => p (ι i)) else 0) :=
      tsum_eq_sum (s := Sm) hglobalZero
    _ = ∑ rc ∈ St,
          (independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi) rc.1 *
            (∏ j : C, primePoolLaw lo hi (rc.2 j))) *
            (if Good rc.1 then F rc.1 else 0) := hsum
    _ = ∑ p ∈ Sq, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
          (if Good p then F p else 0) := by
          rw [Finset.sum_product]
          apply Finset.sum_congr rfl
          intro p hp
          calc
            (∑ c ∈ Sc,
                (independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi) p *
                  (∏ j : C, primePoolLaw lo hi (c j))) *
                  (if Good p then F p else 0)) =
                (independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi) p *
                  (if Good p then F p else 0)) *
                  (∑ c ∈ Sc, ∏ j : C, primePoolLaw lo hi (c j)) := by
                calc
                  _ = ∑ c ∈ Sc,
                    (independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi) p *
                      (if Good p then F p else 0)) *
                      (∏ j : C, primePoolLaw lo hi (c j)) := by
                        apply Finset.sum_congr rfl
                        intro c hc
                        ring
                  _ = _ := by rw [← Finset.mul_sum]
            _ = independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
                  (if Good p then F p else 0) := by rw [hcompSum, mul_one]
    _ = ∑' p : Fin q → ℕ,
          independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
            (if Good p then F p else 0) := (tsum_eq_sum (s := Sq) hqZero).symm

private theorem opus_dpo_rep_replicaGoodAverage_product {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (hpool : ∀ k, 0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
      (MS.primeStage.pool N (gap k)).upper)
    (hgood : ∀ k, 0 < gapSlotProbability (corrScales MS) (gap k) N
      ((T k).Good (corrScales MS) (gap k) N))
    (F : ∀ k : Fin b, (Fin (T k).q → ℕ) → ℝ) :
    (independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (pkgB2_goodPrimeEvent MS gap T hT N))⁻¹ *
      ∑' p : Fin (b * sl) → ℕ,
        independentPrimePoolMass
          (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
          (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p *
          (if pkgB2_goodPrimeEvent MS gap T hT N p then
            ∏ k, F k (pkgB2_repPrimeProject hT p k) else 0) =
      ∏ k, (gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N))⁻¹ *
        ∑' q : Fin (T k).q → ℕ,
          gapSlotMass (corrScales MS) (gap k) N q *
            (if (T k).Good (corrScales MS) (gap k) N q then F k q else 0) := by
  classical
  let lo : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let loBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).lower
  let hiBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).upper
  let M : ℕ := ∑ k : Fin b, hiBlock k
  let G : ∀ k : Fin b, (Fin sl → ℕ) → Prop := fun k q =>
    (T k).Good (corrScales MS) (gap k) N
      (fun j => q ((Classical.choose (hT k)) j))
  let Ffull : ∀ k : Fin b, (Fin sl → ℕ) → ℝ := fun k q =>
    F k (fun j => q ((Classical.choose (hT k)) j))
  have hlo : ∀ k j, lo (pkgB2_replicaEmbedding k j) = loBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).lower = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  have hhi : ∀ k j, hi (pkgB2_replicaEmbedding k j) = hiBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).upper = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  have hboundFull : ∀ i, hi i ≤ M := by
    intro i
    let k := (finProdFinEquiv (m := b) (n := sl)).symm i |>.1
    let j := (finProdFinEquiv (m := b) (n := sl)).symm i |>.2
    have he : pkgB2_replicaEmbedding k j = i := by
      dsimp [pkgB2_replicaEmbedding, k, j]
      exact (finProdFinEquiv (m := b) (n := sl)).apply_symm_apply i
    rw [← he, hhi]
    dsimp [M, hiBlock]
    exact Finset.single_le_sum (f := fun k' => hiBlock k')
      (fun k' _ => Nat.zero_le _) (Finset.mem_univ k)
  have hboundBlock : ∀ k, hiBlock k ≤ M := by
    intro k
    dsimp [M]
    exact Finset.single_le_sum (f := fun k' => hiBlock k')
      (fun k' _ => Nat.zero_le _) (Finset.mem_univ k)
  have hproject (p : Fin (b * sl) → ℕ) (k : Fin b) :
      pkgB2_repPrimeProject hT p k =
        fun j => p (pkgB2_replicaEmbedding k ((Classical.choose (hT k)) j)) := by
    funext j
    rfl
  have hfullEvent (p : Fin (b * sl) → ℕ) :
      pkgB2_goodPrimeEvent MS gap T hT N p = opus_dpo_rep_allGood G p := by
    apply propext
    apply forall_congr'
    intro k
    rw [hproject p k]
  have hprob := opus_dpo_rep_repGoodProbability_eq_product MS gap T hT N hpool
  have hnum := opus_dpo_rep_blockExpectation_factor lo hi loBlock hiBlock hlo hhi
    ⟨hboundFull, hboundBlock⟩ G Ffull
  have hnumMarginal (k : Fin b) :
      ∑' q : Fin sl → ℕ,
        independentPrimePoolMass (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) q * (if G k q then Ffull k q else 0) =
      ∑' q : Fin (T k).q → ℕ,
        independentPrimePoolMass (fun _ => loBlock k) (fun _ => hiBlock k) q *
          (if (T k).Good (corrScales MS) (gap k) N q then F k q else 0) := by
    simpa [G, Ffull, gapSlotMass, loBlock, hiBlock, corrScales] using
      (opus_dpo_rep_primePoolExpectation_embedding (Classical.choose (hT k))
        (loBlock k) (hiBlock k) (hpool k)
        ((T k).Good (corrScales MS) (gap k) N) (F k))
  have hFproject (p : Fin (b * sl) → ℕ) :
      ∏ k, F k (pkgB2_repPrimeProject hT p k) =
        ∏ k, Ffull k (fun j => p (pkgB2_replicaEmbedding k j)) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [hproject p k]
  have hprobPos : 0 < independentPrimePoolProbability lo hi
      (pkgB2_goodPrimeEvent MS gap T hT N) := by
    rw [hprob]
    exact Finset.prod_pos fun k hk => hgood k
  have hnum' :
      ∑' p : Fin (b * sl) → ℕ,
        independentPrimePoolMass lo hi p *
          (if pkgB2_goodPrimeEvent MS gap T hT N p then
            ∏ k, F k (pkgB2_repPrimeProject hT p k) else 0) =
        ∏ k, ∑' q : Fin sl → ℕ,
          independentPrimePoolMass (fun _ : Fin sl => loBlock k)
            (fun _ => hiBlock k) q * (if G k q then Ffull k q else 0) := by
    calc
      _ = ∑' p : Fin (b * sl) → ℕ,
            independentPrimePoolMass lo hi p *
              (if opus_dpo_rep_allGood G p then
                ∏ k, Ffull k (fun j => p (pkgB2_replicaEmbedding k j)) else 0) := by
              apply tsum_congr
              intro p
              rw [hfullEvent p]
              rw [hFproject p]
      _ = _ := hnum
  calc
    _ = (∏ k, gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N))⁻¹ *
        ∏ k, ∑' q : Fin sl → ℕ,
          independentPrimePoolMass (fun _ : Fin sl => loBlock k)
            (fun _ => hiBlock k) q * (if G k q then Ffull k q else 0) := by
          rw [hprob]
          exact congrArg
            (fun z : ℝ =>
              (∏ k, gapSlotProbability (corrScales MS) (gap k) N
                ((T k).Good (corrScales MS) (gap k) N))⁻¹ * z) hnum'
    _ = (∏ k, (gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N))⁻¹) *
        ∏ k, ∑' q : Fin sl → ℕ,
          independentPrimePoolMass (fun _ : Fin sl => loBlock k)
            (fun _ => hiBlock k) q * (if G k q then Ffull k q else 0) := by
          rw [Finset.prod_inv_distrib]
    _ = ∏ k, (gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N))⁻¹ *
        ∑' q : Fin sl → ℕ,
          independentPrimePoolMass (fun _ : Fin sl => loBlock k)
            (fun _ => hiBlock k) q * (if G k q then Ffull k q else 0) := by
          rw [← Finset.prod_mul_distrib]
    _ = ∏ k, (gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N))⁻¹ *
        ∑' q : Fin (T k).q → ℕ,
          independentPrimePoolMass (fun _ => loBlock k) (fun _ => hiBlock k) q *
            (if (T k).Good (corrScales MS) (gap k) N q then F k q else 0) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [hnumMarginal k]
    _ = ∏ k, (gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N))⁻¹ *
        ∑' q : Fin (T k).q → ℕ,
          gapSlotMass (corrScales MS) (gap k) N q *
            (if (T k).Good (corrScales MS) (gap k) N q then F k q else 0) := by
          apply Finset.prod_congr rfl
          intro k hk
          simp [gapSlotMass, loBlock, hiBlock, corrScales]



/-! ### Replica identity: assembly -/

theorem opus_dpo_harm_zero (X W : ℕ) (z : ℤ) (hz : z ∉ Finset.Ico (0 : ℤ) ((X ^ 2 : ℕ) : ℤ)) :
    harmonicLaw X W z = 0 := by
  unfold harmonicLaw
  rw [if_neg]
  rintro ⟨h0, -, h2, -⟩
  apply hz
  rw [Finset.mem_Ico]
  refine ⟨h0, ?_⟩
  have : ((z.toNat : ℕ) : ℤ) < ((X ^ 2 : ℕ) : ℤ) := by exact_mod_cast h2
  rwa [Int.toNat_of_nonneg h0] at this

/-- Proof of the part `opus_dpo_replica_identity`. -/
theorem opus_dpo_replica_identity_proof {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ) :
    ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y) =
      opus_dpo_untranslatedAverage MS B gap T J0 hT direction N I := by
  classical
  have hpoolAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
        (MS.primeStage.pool N (gap k)).upper := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => pkgB2_poolMass_pos_eventually MS (gap k))
    simpa using h
  have hgoodAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      0 < gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => (good_probability_tendsto_one MS (T k) (hT k) (gap k)).eventually
        (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)))
    simpa using h
  filter_upwards [hpoolAll, hgoodAll, opus_dpo_regular_eventually MS B gap T J0 hgap hT hJ0]
    with N hpool hgood hreg I
  set A := MS.core.parameters with hA
  let lo : Fin (b * sl) → ℕ := fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin (b * sl) → ℕ := fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let Good := pkgB2_goodPrimeEvent MS gap T hT N
  let m : (Fin (b * sl) → ℕ) → ℝ := independentPrimePoolMass lo hi
  let P := independentPrimePoolProbability lo hi Good
  let Pset : Finset (Fin (b * sl) → ℕ) := Fintype.piFinset fun i => Finset.range (hi i)
  let harm := harmonicLaw (A.X N B.1) (primorial (N + 1))
  let Wy : Finset ℤ := Finset.Ico (0 : ℤ) (((A.X N B.1) ^ 2 : ℕ) : ℤ)
  let Fk : (y : ℤ) → (k : Fin b) → (Fin (T k).q → ℕ) → ℝ := fun y k q =>
    (I k).e q * shiftAverage (Fin (T k).d) ((T k).length (corrScales MS) (gap k) (J0 k) N q)
      (fun u => opus_dpo_block MS B (T k) N (I k) q y (fun j s => (u j s : ℤ)))
  have hmzero : ∀ p ∉ Pset, m p = 0 := by
    intro p hp
    have hnot : ¬∀ i, p i ∈ Finset.range (hi i) := by
      intro hall
      exact hp (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi'⟩ := not_forall.mp hnot
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold primePoolLaw
    rw [if_neg]
    intro hc
    exact hi' (Finset.mem_range.mpr hc.2.1)
  have hharmzero : ∀ y ∉ Wy, harm y = 0 := fun y hy => opus_dpo_harm_zero _ _ y hy
  -- the right side as a finite double sum
  have hR : opus_dpo_untranslatedAverage MS B gap T J0 hT direction N I =
      ∑ y ∈ Wy, harm y * ((nu A N B y - 1) *
        (P⁻¹ * ∑ p ∈ Pset, m p * (if Good p then ∏ k, Fk y k (pkgB2_repPrimeProject hT p k)
          else 0))) := by
    unfold opus_dpo_untranslatedAverage opus_dpo_average
    change P⁻¹ * ∑' p : Fin (b * sl) → ℕ, m p * (if Good p then ∑' x,
        pkgB2_baseMass MS B T J0 gap hT N p x *
          pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
            (opus_dpo_zeroTranslations T x) else 0) = _
    have hinner (p : Fin (b * sl) → ℕ) :
        m p * (if Good p then ∑' x, pkgB2_baseMass MS B T J0 gap hT N p x *
          pkgB2_stateIntegrand MS B gap T hT J0 direction ∅ N I p
            (opus_dpo_zeroTranslations T x) else 0) =
        ∑ y ∈ Wy, harm y * ((nu A N B y - 1) *
          (m p * (if Good p then ∏ k, Fk y k (pkgB2_repPrimeProject hT p k) else 0))) := by
      by_cases hg : Good p
      · rw [if_pos hg, opus_dpo_inner_replica MS B gap T hT J0 direction N I p (hreg p hg),
          tsum_eq_sum (s := Wy) (fun y hy => by
            change harm y * _ = 0
            rw [hharmzero y hy, zero_mul]),
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        simp only [if_pos hg, Fk, harm, hA, pkgB2_shiftLength]
        ring
      · simp [hg]
    rw [tsum_eq_sum (s := Pset) (fun p hp => by rw [hmzero p hp, zero_mul])]
    simp only [hinner]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hL : Emu A N B.1 (fun y => (nu A N B y - 1) *
      ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y) =
      ∑ y ∈ Wy, harm y * ((nu A N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y) := by
    unfold Emu mu
    exact tsum_eq_sum (s := Wy) (fun y hy => by
      change harm y * _ = 0
      rw [hharmzero y hy, zero_mul])
  rw [hL, hR]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  have hprod := opus_dpo_rep_replicaGoodAverage_product MS gap T hT N hpool hgood (Fk y)
  have hsumP : (∑' p : Fin (b * sl) → ℕ, independentPrimePoolMass
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p *
      (if pkgB2_goodPrimeEvent MS gap T hT N p then
        ∏ k, Fk y k (pkgB2_repPrimeProject hT p k) else 0)) =
      ∑ p ∈ Pset, m p * (if Good p then ∏ k, Fk y k (pkgB2_repPrimeProject hT p k) else 0) :=
    tsum_eq_sum (s := Pset) (fun p hp => by
      change m p * _ = 0
      rw [hmzero p hp, zero_mul])
  rw [hsumP] at hprod
  change P⁻¹ * _ = _ at hprod
  rw [hprod]
  apply Finset.prod_congr rfl
  intro k _
  rfl


/-! ### Cauchy–Schwarz elimination step -/

section OpusDpoS


theorem opus_dpo_s_direction_integers (d : ℕ) (ω : Finset (Fin d)) (hω : ω.Nonempty) :
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

def opus_dpo_s_blockScale {K : ℕ} (A : Parameters K) (B : Block K) (N : ℕ) : ℕ :=
  2 + A.M N + ∏ j ∈ B.2.val, (A.X N j) ^ 2

theorem opus_dpo_s_blockScale_le_masterScaleV {K : ℕ} (A : Parameters K) (B : Block K)
    (l : Fin K) (h : ∀ j ∈ B.2.val, j < l) (N : ℕ) :
    opus_dpo_s_blockScale A B N ≤ masterScaleV A N l := by
  unfold opus_dpo_s_blockScale masterScaleV
  apply Nat.add_le_add_left
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h j hj⟩
  · intro j _ _
    exact Nat.one_le_pow _ _ (A.Xpos N j)

def opus_dpo_s_direction (d : ℕ) (ω : Finset (Fin d)) (hω : ω.Nonempty) : Fin (d + 1) → ℤ :=
  Classical.choose (opus_dpo_s_direction_integers d ω hω)

theorem opus_dpo_s_direction_spec (d : ℕ) (ω : Finset (Fin d)) (hω : ω.Nonempty) :
    opus_dpo_s_direction d ω hω 0 ≠ 0 ∧
    opus_dpo_s_direction d ω hω 0 + ∑ j ∈ ω, opus_dpo_s_direction d ω hω j.succ = 0 ∧
    ∀ ω' : Finset (Fin d), ω' ≠ ω →
      opus_dpo_s_direction d ω hω 0 + ∑ j ∈ ω', opus_dpo_s_direction d ω hω j.succ ≠ 0 :=
  Classical.choose_spec (opus_dpo_s_direction_integers d ω hω)

theorem opus_dpo_s_direction_response_zero_iff (d : ℕ) (ω : Finset (Fin d))
    (hω : ω.Nonempty) (ω' : Finset (Fin d)) :
    opus_dpo_s_direction d ω hω 0 + ∑ j ∈ ω', opus_dpo_s_direction d ω hω j.succ = 0 ↔ ω' = ω := by
  constructor
  · intro hz
    by_contra hne
    exact (opus_dpo_s_direction_spec d ω hω).2.2 ω' hne hz
  · intro h
    rw [h]
    exact (opus_dpo_s_direction_spec d ω hω).2.1

theorem opus_dpo_s_scaled_direction_response_ne_zero (d : ℕ) (ω : Finset (Fin d))
    (hω : ω.Nonempty) (ω' : Finset (Fin d)) (hne : ω' ≠ ω)
    (M : ℤ) (hM : M ≠ 0) :
    M * (opus_dpo_s_direction d ω hω 0 + ∑ j ∈ ω', opus_dpo_s_direction d ω hω j.succ) ≠ 0 :=
  mul_ne_zero hM ((opus_dpo_s_direction_spec d ω hω).2.2 ω' hne)

section Copies

variable {R J C F : Type*} [Field F]

/-- The support predicate is fixed before reducing responses modulo a prime. -/
abbrev opus_dpo_s_Copy (active : R → J → Prop) (E : Finset J) :=
  Σ r : R, ({j : J // j ∈ E ∧ active r j} → Fin 2)

def opus_dpo_s_copyCoeff (c : R → C → F) (ρ : R → J → F)
    (active : R → J → Prop) (E : Finset J)
    (o : opus_dpo_s_Copy active E) : C ⊕ (J × Fin 2) → F := by
  classical
  exact Sum.elim (c o.1) fun js =>
    if h : js.1 ∈ E ∧ active o.1 js.1 then
      if o.2 ⟨js.1, h⟩ = js.2 then ρ o.1 js.1 else 0
    else if js.2 = 0 then ρ o.1 js.1 else 0

theorem opus_dpo_s_copyCoeff_anchor (c : R → C → F) (ρ : R → J → F)
    (active : R → J → Prop) (E : Finset J)
    (a : C) (ha : ∀ r, c r a = 1) (o : opus_dpo_s_Copy active E) :
    opus_dpo_s_copyCoeff c ρ active E o (.inl a) = 1 := ha o.1

/-- Different base rows separate on an old column; different copies separate
on a branch column. Taking the anchor as the other column gives a minor. -/
theorem opus_dpo_s_copies_pairwise_minor (c : R → C → F) (ρ : R → J → F)
    (active : R → J → Prop) (E : Finset J)
    (a : C) (ha : ∀ r, c r a = 1)
    (hsep : ∀ r s, r ≠ s → ∃ j, c r j ≠ c s j)
    (hresp : ∀ r j, active r j → ρ r j ≠ 0)
    (o v : opus_dpo_s_Copy active E) (hne : o ≠ v) :
    ∃ j : C ⊕ (J × Fin 2),
      opus_dpo_s_copyCoeff c ρ active E o (.inl a) * opus_dpo_s_copyCoeff c ρ active E v j ≠
        opus_dpo_s_copyCoeff c ρ active E o j * opus_dpo_s_copyCoeff c ρ active E v (.inl a) := by
  classical
  simp only [opus_dpo_s_copyCoeff_anchor c ρ active E a ha, one_mul, mul_one]
  by_cases hrs : o.1 = v.1
  · rcases o with ⟨r, f⟩
    rcases v with ⟨s, g⟩
    simp only at hrs
    subst s
    have hfg : f ≠ g := by
      intro h
      subst g
      exact hne rfl
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hfg
    refine ⟨.inr (j.1, f j), ?_⟩
    have hgf : g j ≠ f j := Ne.symm hj
    simpa [opus_dpo_s_copyCoeff, j.2, hgf] using (hresp r j.1 j.2.2).symm
  · obtain ⟨j, hj⟩ := hsep o.1 v.1 hrs
    exact ⟨.inl j, hj.symm⟩

end Copies


theorem opus_dpo_s_finite_weighted_cauchy {α : Type*} [Fintype α]
    (μ Ω H₀ H₁ : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hΩ : ∀ x, 0 ≤ Ω x)
    (h₀ : ∀ x, |H₀ x| ≤ Ω x) :
    |∑ x : α, μ x * (H₀ x * H₁ x)| ^ 2 ≤
      (∑ x, μ x * Ω x) * ∑ x, μ x * (Ω x * H₁ x ^ 2) := by
  classical
  let w : α → ℝ := fun x => μ x * Ω x
  have hw (x : α) : 0 ≤ w x := mul_nonneg (hμ x) (hΩ x)
  have hcsWeighted (f : α → ℝ) :
      |∑ x : α, w x * f x| ^ 2 ≤ (∑ x, w x) * ∑ x, w x * f x ^ 2 := by
    let u : α → ℝ := fun x => Real.sqrt (w x)
    let v : α → ℝ := fun x => Real.sqrt (w x) * f x
    have hsumuv : (∑ x : α, u x * v x) = ∑ x, w x * f x := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [u, v]
      calc
        Real.sqrt (w x) * (Real.sqrt (w x) * f x) =
            (Real.sqrt (w x) ^ 2) * f x := by ring
        _ = w x * f x := by rw [Real.sq_sqrt (hw x)]
    have hsumu : (∑ x : α, u x ^ 2) = ∑ x, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [u]
      exact Real.sq_sqrt (hw x)
    have hsumv : (∑ x : α, v x ^ 2) = ∑ x, w x * f x ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [v]
      rw [mul_pow, Real.sq_sqrt (hw x)]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α) u v
    rw [hsumuv, hsumu, hsumv] at hcs
    simpa only [sq_abs] using hcs
  have hdom : |∑ x : α, μ x * (H₀ x * H₁ x)| ≤
      ∑ x : α, w x * |H₁ x| := by
    calc
      _ ≤ ∑ x : α, |μ x * (H₀ x * H₁ x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : α, w x * |H₁ x| := by
        apply Finset.sum_le_sum
        intro x hx
        rw [abs_mul, abs_mul, abs_of_nonneg (hμ x)]
        calc
          μ x * (|H₀ x| * |H₁ x|) = (μ x * |H₀ x|) * |H₁ x| := by ring
          _ ≤ (μ x * Ω x) * |H₁ x| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h₀ x) (hμ x))
              (abs_nonneg _)
          _ = w x * |H₁ x| := by rfl
  have hsumNonneg : 0 ≤ ∑ x : α, w x * |H₁ x| :=
    Finset.sum_nonneg fun x hx => mul_nonneg (hw x) (abs_nonneg _)
  have hcs := hcsWeighted (fun x => |H₁ x|)
  have hcs' : (∑ x : α, w x * |H₁ x|) ^ 2 ≤
      (∑ x : α, w x) * ∑ x : α, w x * |H₁ x| ^ 2 := by
    have habs : |(∑ x : α, w x * |H₁ x|)| = ∑ x : α, w x * |H₁ x| :=
      abs_of_nonneg hsumNonneg
    rw [habs] at hcs
    exact hcs
  calc
    |∑ x : α, μ x * (H₀ x * H₁ x)| ^ 2 ≤
        (∑ x : α, w x * |H₁ x|) ^ 2 := by
          have hleft : 0 ≤ |∑ x : α, μ x * (H₀ x * H₁ x)| := abs_nonneg _
          nlinarith [hdom, hsumNonneg, hleft]
    _ ≤ (∑ x : α, w x) * ∑ x : α, w x * |H₁ x| ^ 2 := hcs'
    _ = (∑ x : α, μ x * Ω x) * ∑ x : α, μ x * (Ω x * H₁ x ^ 2) := by
      have hsumW : (∑ x : α, w x) = ∑ x, μ x * Ω x := by simp [w]
      have hsumWH : (∑ x : α, w x * |H₁ x| ^ 2) =
          ∑ x, μ x * (Ω x * H₁ x ^ 2) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [w, sq_abs]
        ring
      rw [hsumW, hsumWH]


/-- Iterate a finite family of weighted square inequalities without requiring signed states
at intermediate stages to be nonnegative. -/
theorem opus_dpo_s_iterate_abs_cauchy {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α → ℝ) (C : ℝ) (hC : 0 < C)
    (hstep : ∀ E r, r ∉ E → |F E| ^ 2 ≤ C * |F (insert r E)|) :
    |F ∅| ^ (2 ^ Fintype.card α) ≤
      C ^ (2 ^ Fintype.card α - 1) * |F Finset.univ| := by
  simpa only [abs_abs] using c_elim2_iterate_box_cauchy
    (fun E => |F E|) C hC (fun E _ r _ hr => by simpa using hstep E r hr)
    (fun E _ => abs_nonneg (F E))

/-- Uniform smallness of the terminal state propagates back through finitely many
weighted square inequalities with a fixed bound on their prefactors. -/
theorem opus_dpo_s_uniform_initial_small {α : Type*} [Fintype α] [DecidableEq α]
    {Input : ℕ → Type*} (F : (N : ℕ) → Input N → Finset α → ℝ)
    (C : ℝ) (hC : 0 < C)
    (hstep : ∀ᶠ N in atTop, ∀ I : Input N, ∀ E r, r ∉ E →
      |F N I E| ^ 2 ≤ C * |F N I (insert r E)|)
    (hterminal : ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : Input N,
      |F N I Finset.univ| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : Input N, |F N I ∅| ≤ ε := by
  intro ε hε
  let n := 2 ^ Fintype.card α
  let A := C ^ (n - 1)
  have hn : n ≠ 0 := by dsimp [n]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  let δ := ε ^ n / A
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hstep, hterminal δ hδ] with N hN ht I
  have hp := opus_dpo_s_iterate_abs_cauchy (F N I) C hC (hN I)
  have hpow : |F N I ∅| ^ n ≤ ε ^ n := by
    calc
      _ ≤ A * |F N I Finset.univ| := hp
      _ ≤ A * δ := mul_le_mul_of_nonneg_left (ht I) (le_of_lt hA)
      _ = ε ^ n := by dsimp [δ]; field_simp
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (le_of_lt hε) hn).mp hpow

/-- The inserted average and original pairing need only be uniformly close; no fixed
moment prebound is needed after the initial state itself has been shown to be small. -/
theorem opus_dpo_s_uniform_transfer {Input : ℕ → Type*}
    (f g : (N : ℕ) → Input N → ℝ)
    (hf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : Input N, |f N I| ≤ ε)
    (hclose : ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : Input N, |g N I - f N I| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : Input N, |g N I| ≤ ε := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hclose (ε / 2) (by positivity)]
    with N hfN hcN I
  calc
    |g N I| = |(g N I - f N I) + f N I| := by congr 1; ring
    _ ≤ |g N I - f N I| + |f N I| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hcN I) (hfN I)
    _ = ε := by ring

/-- A weighted square step for an arbitrary finite outside law and arbitrary selected
coordinate laws. Each replica may use a different translation interval. -/
theorem opus_dpo_s_weighted_coordinate_step {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (σ : α → β → ℝ) (H₀ Ω : α → ℝ) (H : α → β → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hΩ : ∀ x, 0 ≤ Ω x)
    (hH₀ : ∀ x, |H₀ x| ≤ Ω x) :
    |∑ x, μ x * (H₀ x * ∑ z, σ x z * H x z)| ^ 2 ≤
      (∑ x, μ x * Ω x) *
        ∑ x, μ x * (Ω x * ∑ z₀, ∑ z₁,
          σ x z₀ * σ x z₁ * (H x z₀ * H x z₁)) := by
  have hsq (x : α) : (∑ z, σ x z * H x z) ^ 2 =
      ∑ z₀, ∑ z₁, σ x z₀ * σ x z₁ * (H x z₀ * H x z₁) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro z₀ _
    apply Finset.sum_congr rfl
    intro z₁ _
    ring
  simpa only [hsq] using opus_dpo_s_finite_weighted_cauchy μ Ω H₀
    (fun x => ∑ z, σ x z * H x z) hμ hΩ hH₀

/-- Restrict the branch bits after adding one direction. -/
def opus_dpo_s_branchRestrict {R J : Type*} (active : R → J → Prop)
    (E : Finset J) (r : J) (t : R)
    (η : {j : J // j ∈ insert r E ∧ active t j} → Fin 2) :
    {j : J // j ∈ E ∧ active t j} → Fin 2 :=
  fun j => η ⟨j.1, Finset.mem_insert_of_mem j.2.1, j.2.2⟩

noncomputable def opus_dpo_s_branchExtend {R J : Type*} (active : R → J → Prop)
    (E : Finset J) (r : J) (t : R)
    (η : {j : J // j ∈ E ∧ active t j} → Fin 2) (bit : Fin 2) :
    {j : J // j ∈ insert r E ∧ active t j} → Fin 2 := by
  classical
  exact fun j => if h : j.1 = r then bit else
    η ⟨j.1, (Finset.mem_insert.mp j.2.1).resolve_left h, j.2.2⟩

/-- A responding row acquires exactly one independent bit at a square step. -/
noncomputable def opus_dpo_s_branchInsertEquiv {R J : Type*}
    (active : R → J → Prop) (E : Finset J) (r : J) (hr : r ∉ E)
    (t : R) (hact : active t r) :
    ({j : J // j ∈ insert r E ∧ active t j} → Fin 2) ≃
      (({j : J // j ∈ E ∧ active t j} → Fin 2) × Fin 2) where
  toFun η := (opus_dpo_s_branchRestrict active E r t η,
    η ⟨r, Finset.mem_insert_self r E, hact⟩)
  invFun z := opus_dpo_s_branchExtend active E r t z.1 z.2
  left_inv η := by
    classical
    funext j
    by_cases h : j.1 = r
    · simp only [opus_dpo_s_branchExtend, dif_pos h]
      exact congrArg η (Subtype.ext h.symm)
    · simp [opus_dpo_s_branchExtend, opus_dpo_s_branchRestrict, h]
  right_inv z := by
    classical
    apply Prod.ext
    · funext j
      have h : j.1 ≠ r := by intro h; exact hr (h ▸ j.2.1)
      simp [opus_dpo_s_branchRestrict, opus_dpo_s_branchExtend, h]
    · simp [opus_dpo_s_branchExtend]

/-- A nonresponding row acquires no bit. In particular, its own direction cannot
create two identical occurrences in the weighted linear forms system. -/
noncomputable def opus_dpo_s_branchInsertInactiveEquiv {R J : Type*}
    (active : R → J → Prop) (E : Finset J) (r : J)
    (t : R) (hact : ¬active t r) :
    ({j : J // j ∈ insert r E ∧ active t j} → Fin 2) ≃
      ({j : J // j ∈ E ∧ active t j} → Fin 2) where
  toFun := opus_dpo_s_branchRestrict active E r t
  invFun η j := η ⟨j.1, (Finset.mem_insert.mp j.2.1).resolve_left
    (fun h => hact (h ▸ j.2.2)), j.2.2⟩
  left_inv η := by funext j; rfl
  right_inv η := by funext j; rfl

/-- Product factorization over the exact branch support of a responding row. -/
theorem opus_dpo_s_branchProduct_insert {R J : Type*} [Fintype J]
    (active : R → J → Prop) (E : Finset J) (r : J) (hr : r ∉ E)
    (t : R) (hact : active t r)
    (f : ({j : J // j ∈ insert r E ∧ active t j} → Fin 2) → ℝ) :
    ∏ η, f η = ∏ η, (f (opus_dpo_s_branchExtend active E r t η 0) *
      f (opus_dpo_s_branchExtend active E r t η 1)) := by
  classical
  let e := opus_dpo_s_branchInsertEquiv active E r hr t hact
  calc
    _ = ∏ z : (({j : J // j ∈ E ∧ active t j} → Fin 2) × Fin 2),
        f (e.symm z) := by
      exact Fintype.prod_equiv e _ _ (fun _ => by simp)
    _ = _ := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro η _
      rw [Fin.prod_univ_two]
      rfl

theorem opus_dpo_s_intervalError_superPolynomial {q : ℕ}
    (V L : ℕ → ℕ) (hVtendsto : Tendsto (fun N => (V N : ℝ)) atTop atTop)
    (hVone : ∀ N, 1 ≤ V N)
    (hFloor : ∀ m : ℕ, ∀ᶠ N : ℕ in atTop, V N ^ m ≤ max 1 (L N)) :
    SuperPolynomialSmall
      (fun N => 2 * ((V N) ^ q : ℝ) / (max 1 (L N) : ℝ))
      (fun N => (V N : ℝ)) := by
  intro C hC
  let S : ℕ → ℝ := fun N => (V N : ℝ)
  let Aexp : ℝ := (q : ℝ) + C
  let m : ℕ := Nat.ceil (Aexp + 1)
  have hApos : 0 < Aexp := by dsimp [Aexp]; positivity
  have hm : Aexp + 1 ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil (Aexp + 1)
  have hS : Tendsto S atTop atTop := hVtendsto
  have hSpos (N : ℕ) : 0 < S N := by
    change (0 : ℝ) < (V N : ℝ)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hVone N))
  have hSone (N : ℕ) : 1 ≤ S N := by
    change (1 : ℝ) ≤ (V N : ℝ)
    exact_mod_cast hVone N
  have hFloorLower : ∀ᶠ N : ℕ in atTop,
      S N ^ (m : ℝ) ≤ (max 1 (L N) : ℝ) := by
    filter_upwards [hFloor m] with N hN
    have hcast : ((V N) ^ m : ℝ) = S N ^ (m : ℝ) := by
      dsimp [S]
      exact (Real.rpow_natCast (V N : ℝ) m).symm
    rw [← hcast]
    exact_mod_cast hN
  have hProduct (N : ℕ) :
      ((V N : ℝ) ^ q) * (V N : ℝ) ^ C ≤ S N ^ Aexp := by
    calc
      _ = S N ^ (q : ℝ) * S N ^ C := by
        simp [S, Real.rpow_natCast]
      _ = S N ^ ((q : ℝ) + C) := (Real.rpow_add (hSpos N) _ _).symm
      _ ≤ S N ^ Aexp := by
        change S N ^ ((q : ℝ) + C) ≤ S N ^ ((q : ℝ) + C)
        exact le_rfl
  have hSmallBound : ∀ᶠ N : ℕ in atTop,
      (2 * ((V N) ^ q : ℝ) / (max 1 (L N) : ℝ)) * (V N : ℝ) ^ C ≤ 2 / S N := by
    filter_upwards [hFloorLower] with N hfloor
    have hDenPos : 0 < (max 1 (L N) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (L N)))
    have hratio : S N ^ Aexp / (max 1 (L N) : ℝ) ≤ 1 / S N := by
      apply (div_le_div_iff₀ hDenPos (hSpos N)).2
      calc
        S N ^ Aexp * S N = S N ^ (Aexp + 1) := by
          calc
            _ = S N ^ Aexp * S N ^ (1 : ℝ) := by simp
            _ = _ := (Real.rpow_add (hSpos N) Aexp 1).symm
        _ ≤ S N ^ (m : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (hSone N) hm
        _ ≤ (max 1 (L N) : ℝ) := hfloor
        _ = 1 * (max 1 (L N) : ℝ) := by ring
    calc
      _ = 2 * ((((V N : ℝ) ^ q) * (V N : ℝ) ^ C) /
          (max 1 (L N) : ℝ)) := by ring
      _ ≤ 2 * (S N ^ Aexp / (max 1 (L N) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_right (hProduct N) (by positivity)
      _ ≤ 2 / S N := by
        have hmul := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)
        simpa [div_eq_mul_inv, mul_assoc] using hmul
  have hInv : Tendsto (fun N : ℕ => (S N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hS
  have hTop : Tendsto (fun N : ℕ => 2 / S N) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hInv
  have hnonneg (N : ℕ) :
      0 ≤ (2 * ((V N) ^ q : ℝ) / (max 1 (L N) : ℝ)) * (V N : ℝ) ^ C := by
    positivity
  exact squeeze_zero' (Eventually.of_forall hnonneg) hSmallBound hTop

noncomputable def opus_dpo_s_copyCoeffInt {R J C : Type*}
    (c : R → C → ℤ) (ρ : R → J → ℤ)
    (active : R → J → Prop) (E : Finset J)
    (o : opus_dpo_s_Copy active E) : C ⊕ (J × Fin 2) → ℤ := by
  classical
  exact Sum.elim (c o.1) fun js =>
    if h : js.1 ∈ E ∧ active o.1 js.1 then
      if o.2 ⟨js.1, h⟩ = js.2 then ρ o.1 js.1 else 0
    else if js.2 = 0 then ρ o.1 js.1 else 0

/-- The two columns for a direction contribute exactly its selected endpoint. -/
theorem opus_dpo_s_copyEvaluation {R J C : Type*} [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ)
    (active : R → J → Prop) (E : Finset J)
    (o : opus_dpo_s_Copy active E) (x : C ⊕ (J × Fin 2) → ℤ) :
    (∑ a, opus_dpo_s_copyCoeffInt c ρ active E o a * x a) =
      (∑ a : C, c o.1 a * x (.inl a)) +
        ∑ j : J, ρ o.1 j * x (.inr (j,
          if h : j ∈ E ∧ active o.1 j then o.2 ⟨j, h⟩ else 0)) := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_two]
  by_cases h : j ∈ E ∧ active o.1 j
  · by_cases hb : o.2 ⟨j, h⟩ = 0
    · simp [opus_dpo_s_copyCoeffInt, h, hb]
    · have hb' : o.2 ⟨j, h⟩ = 1 := by
        have hv := (o.2 ⟨j, h⟩).isLt
        apply Fin.ext
        have h0 : (o.2 ⟨j, h⟩).val ≠ 0 := by
          intro hzero
          exact hb (Fin.ext hzero)
        change (o.2 ⟨j, h⟩).val = 1
        omega
      simp [opus_dpo_s_copyCoeffInt, h, hb', hb]
  · simp [opus_dpo_s_copyCoeffInt, h]

/-- The square-root insertion scale has a uniformly controlled relative size. -/
theorem opus_dpo_s_sqrt_ratio_le (F : ℕ) :
    (Nat.sqrt F : ℝ) / (max 1 F : ℝ) ≤ 1 / (max 1 (Nat.sqrt F) : ℝ) := by
  by_cases h : Nat.sqrt F = 0
  · simp [h]
  have hA : 0 < Nat.sqrt F := Nat.pos_of_ne_zero h
  have hmax : max 1 (Nat.sqrt F) = Nat.sqrt F :=
    max_eq_right (Nat.one_le_iff_ne_zero.mpr h)
  have hmaxReal : max (1 : ℝ) (Nat.sqrt F : ℝ) = (Nat.sqrt F : ℝ) :=
    max_eq_right (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
  rw [hmaxReal]
  have hsq : (Nat.sqrt F : ℝ) ^ 2 ≤ (max 1 F : ℝ) := by
    exact_mod_cast (Nat.sqrt_le' F).trans (Nat.le_max_right 1 F)
  have hFpos : (0 : ℝ) < max (1 : ℝ) (F : ℝ) := by positivity
  have hApos : (0 : ℝ) < (Nat.sqrt F : ℝ) := by exact_mod_cast hA
  apply (div_le_div_iff₀ hFpos hApos).2
  nlinarith

/-- The interval insertion error decays faster than every fixed power of the block scale. -/
theorem opus_dpo_s_sqrt_ratio_superPolynomial
    (V F : ℕ → ℕ) (hVtendsto : Tendsto (fun N => (V N : ℝ)) atTop atTop)
    (hVone : ∀ N, 1 ≤ V N)
    (hFloor : ∀ m : ℕ, ∀ᶠ N : ℕ in atTop, V N ^ m ≤ max 1 (Nat.sqrt (F N))) :
    SuperPolynomialSmall
      (fun N => 2 * (Nat.sqrt (F N) : ℝ) / (max 1 (F N) : ℝ))
      (fun N => (V N : ℝ)) := by
  have hsmall := opus_dpo_s_intervalError_superPolynomial (q := 0) V
    (fun N => Nat.sqrt (F N)) hVtendsto hVone hFloor
  intro C hC
  have hbound (N : ℕ) :
      (2 * (Nat.sqrt (F N) : ℝ) / (max 1 (F N) : ℝ)) * (V N : ℝ) ^ C ≤
        (2 * ((V N) ^ 0 : ℝ) / (max 1 (Nat.sqrt (F N)) : ℝ)) * (V N : ℝ) ^ C := by
    have hratio := mul_le_mul_of_nonneg_left (opus_dpo_s_sqrt_ratio_le (F N))
      (by norm_num : (0 : ℝ) ≤ 2)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    simpa only [pow_zero, mul_one, one_mul, div_eq_mul_inv, mul_assoc] using hratio
  exact squeeze_zero' (Eventually.of_forall (fun N => by positivity))
    (Eventually.of_forall hbound) (hsmall C hC)
/-- The newly duplicated branch is the old form evaluated at its chosen endpoint. -/
theorem opus_dpo_s_copyEvaluation_insert {R J C : Type*} [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ)
    (active : R → J → Prop) (E : Finset J) (r : J) (hr : r ∉ E)
    (t : R) (hact : active t r)
    (η : {j : J // j ∈ E ∧ active t j} → Fin 2) (bit : Fin 2)
    (x : C ⊕ (J × Fin 2) → ℤ) :
    (∑ a, opus_dpo_s_copyCoeffInt c ρ active (insert r E)
      ⟨t, opus_dpo_s_branchExtend active E r t η bit⟩ a * x a) =
    ∑ a, opus_dpo_s_copyCoeffInt c ρ active E ⟨t, η⟩ a *
      (Function.update x (.inr (r, 0)) (x (.inr (r, bit)))) a := by
  classical
  rw [opus_dpo_s_copyEvaluation, opus_dpo_s_copyEvaluation]
  apply congrArg₂ (fun a b : ℤ => a + b)
  · apply Finset.sum_congr rfl
    intro a _
    simp
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = r
    · subst j
      simp [hr, hact, opus_dpo_s_branchExtend]
    · have hne (s : Fin 2) : (Sum.inr (j, s) : C ⊕ (J × Fin 2)) ≠ .inr (r, 0) := by
        intro he
        exact hj (congrArg Prod.fst (Sum.inr.inj he))
      rw [Function.update_of_ne (hne _)]
      have hmem : j ∈ insert r E ↔ j ∈ E := by simp [hj]
      by_cases he : j ∈ E ∧ active t j
      · have he' : j ∈ insert r E ∧ active t j := ⟨Finset.mem_insert_of_mem he.1, he.2⟩
        simp [he, he', opus_dpo_s_branchExtend, hj]
      · have he' : ¬(j ∈ insert r E ∧ active t j) := by simpa only [hmem] using he
        simp [he, he', hj]

/-- Adding a nonresponding direction preserves the corresponding row exactly. -/
theorem opus_dpo_s_copyEvaluation_insert_inactive {R J C : Type*}
    [Fintype J] [Fintype C] (c : R → C → ℤ) (ρ : R → J → ℤ)
    (active : R → J → Prop) (E : Finset J) (r : J)
    (t : R) (hact : ¬active t r) (hρ : ρ t r = 0)
    (η : {j : J // j ∈ E ∧ active t j} → Fin 2)
    (x : C ⊕ (J × Fin 2) → ℤ) :
    (∑ a, opus_dpo_s_copyCoeffInt c ρ active (insert r E)
      ⟨t, (opus_dpo_s_branchInsertInactiveEquiv active E r t hact).symm η⟩ a * x a) =
    ∑ a, opus_dpo_s_copyCoeffInt c ρ active E ⟨t, η⟩ a * x a := by
  classical
  rw [opus_dpo_s_copyEvaluation, opus_dpo_s_copyEvaluation]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = r
  · subst j
    simp [hρ]
  · have hmem : j ∈ insert r E ↔ j ∈ E := by simp [hj]
    by_cases he : j ∈ E ∧ active t j
    · have he' : j ∈ insert r E ∧ active t j := ⟨Finset.mem_insert_of_mem he.1, he.2⟩
      simp [he, he', opus_dpo_s_branchInsertInactiveEquiv]
    · have he' : ¬(j ∈ insert r E ∧ active t j) := by simpa only [hmem] using he
      simp [he, he', hj]
/-- Arbitrary input sequences suffice to establish a uniform bound: choose a violating
input at every index where one exists. -/
theorem opus_dpo_s_uniform_small_of_all_sequences {Input : ℕ → Type*}
    [∀ N, Nonempty (Input N)] (f : (N : ℕ) → Input N → ℝ)
    (h : ∀ I : (N : ℕ) → Input N, Tendsto (fun N => f N (I N)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : Input N, |f N I| ≤ ε := by
  classical
  intro ε hε
  let I : (N : ℕ) → Input N := fun N =>
    if hN : ∃ x : Input N, ε < |f N x| then Classical.choose hN
    else Classical.choice (inferInstance : Nonempty (Input N))
  have hlim : Tendsto (fun N => |f N (I N)|) atTop (𝓝 0) := by
    simpa using (h I).abs
  have hevent := hlim.eventually (Iio_mem_nhds hε)
  filter_upwards [hevent] with N hN x
  by_contra hx
  have hex : ∃ x : Input N, ε < |f N x| := ⟨x, lt_of_not_ge hx⟩
  have hchoose : ε < |f N (I N)| := by
    dsimp [I]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact (not_lt_of_ge (le_of_lt hchoose)) hN
noncomputable def opus_dpo_s_rowProduct {R J C : Type*} [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ) (active : R → J → Prop)
    (E : Finset J) (t : R) (f : ℤ → ℝ) (x : C ⊕ (J × Fin 2) → ℤ) : ℝ :=
  ∏ η : {j : J // j ∈ E ∧ active t j} → Fin 2,
    f (∑ a, opus_dpo_s_copyCoeffInt c ρ active E ⟨t, η⟩ a * x a)

/-- Every responding row contributes its two endpoint products at a square step. -/
theorem opus_dpo_s_rowProduct_insert {R J C : Type*} [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ)
    (active : R → J → Prop) (E : Finset J) (r : J) (hr : r ∉ E)
    (t : R) (hact : active t r) (f : ℤ → ℝ)
    (x : C ⊕ (J × Fin 2) → ℤ) :
    opus_dpo_s_rowProduct c ρ active (insert r E) t f x =
      opus_dpo_s_rowProduct c ρ active E t f x *
        opus_dpo_s_rowProduct c ρ active E t f
          (Function.update x (.inr (r, 0)) (x (.inr (r, 1)))) := by
  classical
  unfold opus_dpo_s_rowProduct
  rw [opus_dpo_s_branchProduct_insert active E r hr t hact]
  simp_rw [opus_dpo_s_copyEvaluation_insert c ρ active E r hr t hact]
  simp only [Function.update_eq_self]
  exact Finset.prod_mul_distrib

/-- The row removed at a square step retains a single product of weight factors. -/
theorem opus_dpo_s_rowProduct_insert_inactive {R J C : Type*}
    [Fintype J] [Fintype C] (c : R → C → ℤ) (ρ : R → J → ℤ)
    (active : R → J → Prop) (E : Finset J) (r : J)
    (t : R) (hact : ¬active t r) (hρ : ρ t r = 0) (f : ℤ → ℝ)
    (x : C ⊕ (J × Fin 2) → ℤ) :
    opus_dpo_s_rowProduct c ρ active (insert r E) t f x =
      opus_dpo_s_rowProduct c ρ active E t f x := by
  classical
  unfold opus_dpo_s_rowProduct
  let e := opus_dpo_s_branchInsertInactiveEquiv active E r t hact
  calc
    _ = ∏ η : {j : J // j ∈ E ∧ active t j} → Fin 2,
        f (∑ a, opus_dpo_s_copyCoeffInt c ρ active (insert r E)
          ⟨t, e.symm η⟩ a * x a) :=
      Fintype.prod_equiv e _ _ (fun _ => by simp)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro η _
      rw [opus_dpo_s_copyEvaluation_insert_inactive c ρ active E r t hact hρ η x]

/-- Factor the next occurrence state into the selected row's weight and the two products
of complementary rows, evaluated at the two newly independent endpoints. -/
theorem opus_dpo_s_occurrenceProduct_insert {R J C : Type*}
    [Fintype R] [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ) (selected : J → R)
    (E : Finset J) (r : J) (hr : r ∉ E)
    (hρ : ρ (selected r) r = 0)
    (f : Finset J → R → ℤ → ℝ)
    (hstable : ∀ t, t ≠ selected r → f (insert r E) t = f E t)
    (x : C ⊕ (J × Fin 2) → ℤ) :
    (∏ t : R, opus_dpo_s_rowProduct c ρ (fun t j => t ≠ selected j)
      (insert r E) t (f (insert r E) t) x) =
      opus_dpo_s_rowProduct c ρ (fun t j => t ≠ selected j) E
        (selected r) (f (insert r E) (selected r)) x *
      (∏ t ∈ Finset.univ.erase (selected r),
        opus_dpo_s_rowProduct c ρ (fun t j => t ≠ selected j) E t (f E t) x) *
      (∏ t ∈ Finset.univ.erase (selected r),
        opus_dpo_s_rowProduct c ρ (fun t j => t ≠ selected j) E t (f E t)
          (Function.update x (.inr (r, 0)) (x (.inr (r, 1))))) := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (selected r))]
  rw [opus_dpo_s_rowProduct_insert_inactive c ρ (fun t j => t ≠ selected j)
    E r (selected r) (by simp) hρ]
  have hrest :
      (∏ t ∈ Finset.univ.erase (selected r),
        opus_dpo_s_rowProduct c ρ (fun t j => t ≠ selected j) (insert r E) t
          (f (insert r E) t) x) =
      (∏ t ∈ Finset.univ.erase (selected r),
        opus_dpo_s_rowProduct c ρ (fun t j => t ≠ selected j) E t (f E t) x) *
      (∏ t ∈ Finset.univ.erase (selected r),
        opus_dpo_s_rowProduct c ρ (fun t j => t ≠ selected j) E t (f E t)
          (Function.update x (.inr (r, 0)) (x (.inr (r, 1))))) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t ht
    have hne := (Finset.mem_erase.mp ht).1
    rw [hstable t hne]
    exact opus_dpo_s_rowProduct_insert c ρ (fun t j => t ≠ selected j) E r hr t hne _ x
  rw [hrest]
  ring
/-- The square of a finite-support expectation is its independent two-copy expectation. -/
theorem opus_dpo_s_tsum_square {β : Type*} (σ H : β → ℝ) (S : Finset β)
    (hzero : ∀ z, z ∉ S → σ z = 0) :
    (∑' z, σ z * H z) ^ 2 =
      ∑' z₀, ∑' z₁, σ z₀ * σ z₁ * (H z₀ * H z₁) := by
  classical
  have havg : (∑' z, σ z * H z) = ∑ z ∈ S, σ z * H z :=
    tsum_eq_sum (fun z hz => by simp [hzero z hz])
  have houter : (∑' z₀, ∑' z₁, σ z₀ * σ z₁ * (H z₀ * H z₁)) =
      ∑ z₀ ∈ S, ∑ z₁ ∈ S, σ z₀ * σ z₁ * (H z₀ * H z₁) := by
    rw [tsum_eq_sum (s := S) (fun z hz => by simp [hzero z hz])]
    apply Finset.sum_congr rfl
    intro z _
    exact tsum_eq_sum (fun z' hz' => by simp [hzero z' hz'])
  rw [havg, houter, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro z₀ _
  apply Finset.sum_congr rfl
  intro z₁ _
  ring

/-- Weighted Cauchy–Schwarz for an arbitrary finitely supported outside law. -/
theorem opus_dpo_s_finiteSupport_weighted_cauchy {α : Type*}
    (μ Ω H₀ H₁ : α → ℝ) (S : Finset α)
    (hzero : ∀ x, x ∉ S → μ x = 0)
    (hμ : ∀ x, 0 ≤ μ x) (hΩ : ∀ x, 0 ≤ Ω x)
    (h₀ : ∀ x, |H₀ x| ≤ Ω x) :
    |∑' x, μ x * (H₀ x * H₁ x)| ^ 2 ≤
      (∑' x, μ x * Ω x) * ∑' x, μ x * (Ω x * H₁ x ^ 2) := by
  classical
  have hcs := opus_dpo_s_finite_weighted_cauchy
    (fun x : {x : α // x ∈ S} => μ x.1)
    (fun x => Ω x.1) (fun x => H₀ x.1) (fun x => H₁ x.1)
    (fun x => hμ x.1) (fun x => hΩ x.1) (fun x => h₀ x.1)
  have hcurrent : (∑' x, μ x * (H₀ x * H₁ x)) =
      ∑ x : {x : α // x ∈ S}, μ x.1 * (H₀ x.1 * H₁ x.1) := by
    rw [tsum_eq_sum (s := S) (fun x hx => by simp [hzero x hx])]
    rw [← Finset.sum_attach]
    simp
  have hweight : (∑' x, μ x * Ω x) =
      ∑ x : {x : α // x ∈ S}, μ x.1 * Ω x.1 := by
    rw [tsum_eq_sum (s := S) (fun x hx => by simp [hzero x hx])]
    rw [← Finset.sum_attach]
    simp
  have hnext : (∑' x, μ x * (Ω x * H₁ x ^ 2)) =
      ∑ x : {x : α // x ∈ S}, μ x.1 * (Ω x.1 * H₁ x.1 ^ 2) := by
    rw [tsum_eq_sum (s := S) (fun x hx => by simp [hzero x hx])]
    rw [← Finset.sum_attach]
    simp
  rw [hcurrent, hweight, hnext]
  exact hcs

/-- A selected coordinate can be duplicated with its own finite-support law, independently
of the outside variables and of the laws assigned to other directions. -/
theorem opus_dpo_s_finiteSupport_coordinate_step {α β : Type*}
    (μ : α → ℝ) (σ : α → β → ℝ) (H₀ Ω : α → ℝ) (H : α → β → ℝ)
    (S : Finset α) (Selected : α → Finset β)
    (hzero : ∀ x, x ∉ S → μ x = 0)
    (hσzero : ∀ x z, z ∉ Selected x → σ x z = 0)
    (hμ : ∀ x, 0 ≤ μ x) (hΩ : ∀ x, 0 ≤ Ω x)
    (h₀ : ∀ x, |H₀ x| ≤ Ω x) :
    |∑' x, μ x * (H₀ x * ∑' z, σ x z * H x z)| ^ 2 ≤
      (∑' x, μ x * Ω x) *
        ∑' x, μ x * (Ω x * ∑' z₀, ∑' z₁,
          σ x z₀ * σ x z₁ * (H x z₀ * H x z₁)) := by
  have hcs := opus_dpo_s_finiteSupport_weighted_cauchy μ Ω H₀
    (fun x => ∑' z, σ x z * H x z) S hzero hμ hΩ h₀
  simpa only [opus_dpo_s_tsum_square (σ := σ _) (H := H _) (Selected _) (hσzero _)] using hcs
abbrev opus_dpo_s_PiExcept {α : Type*} [Fintype α] (a : α) :=
  {i : α // i ∈ (Finset.univ : Finset α).erase a}

noncomputable def opus_dpo_s_piSplitAt {α : Type*} [Fintype α]
    (a : α) : (α → ℤ) ≃ ((opus_dpo_s_PiExcept a → ℤ) × ℤ) where
  toFun x := (fun i => x i.1, x a)
  invFun z i := if h : i = a then z.2 else
    z.1 ⟨i, Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩⟩
  left_inv := by
    intro x
    funext i
    by_cases h : i = a <;> simp [h]
  right_inv := by
    intro z
    apply Prod.ext
    · funext i
      have hne : i.1 ≠ a := (Finset.mem_erase.mp i.2).1
      simp [hne]
    · simp

/-- Isolate one coordinate of a finite-support independent product law. -/
theorem opus_dpo_s_productLaw_tsum_splitAt {α : Type*} [Fintype α]
    (a : α) (law : α → ℤ → ℝ) (win : α → Finset ℤ)
    (hzero : ∀ i z, z ∉ win i → law i z = 0) (F : (α → ℤ) → ℝ) :
    (∑' x : α → ℤ, (∏ i, law i (x i)) * F x) =
      ∑' xr : opus_dpo_s_PiExcept a → ℤ,
        (∏ i : opus_dpo_s_PiExcept a, law i.1 (xr i)) *
          ∑' z : ℤ, law a z * F ((opus_dpo_s_piSplitAt a).symm (xr, z)) := by
  classical
  let e := opus_dpo_s_piSplitAt a
  let full (x : α → ℤ) : ℝ := (∏ i, law i (x i)) * F x
  let rest (xr : opus_dpo_s_PiExcept a → ℤ) : ℝ :=
    ∏ i : opus_dpo_s_PiExcept a, law i.1 (xr i)
  have hprod (x : α → ℤ) : (∏ i, law i (x i)) = rest (e x).1 * law a (e x).2 := by
    change (∏ i, law i (x i)) = rest (fun i => x i.1) * law a (x a)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    congr 1
    exact Finset.prod_subtype ((Finset.univ : Finset α).erase a)
      (by intro i; rfl) (fun i => law i (x i))
  have hfullzero (x : α → ℤ) (hx : x ∉ Fintype.piFinset win) : full x = 0 := by
    have hnot : ¬∀ i, x i ∈ win i := by
      intro hall
      exact hx (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hw : (∏ j, law j (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hzero i (x i) hi)
    simp [full, hw]
  have hs : Summable full := summable_of_ne_finset_zero hfullzero
  have hs' : Summable (fun z : (opus_dpo_s_PiExcept a → ℤ) × ℤ => full (e.symm z)) :=
    hs.comp_injective e.symm.injective
  calc
    _ = ∑' z : (opus_dpo_s_PiExcept a → ℤ) × ℤ, full (e.symm z) :=
      (e.symm.tsum_eq full).symm
    _ = ∑' xr : opus_dpo_s_PiExcept a → ℤ, ∑' z : ℤ, full (e.symm (xr, z)) := hs'.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro xr
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      dsimp [full]
      rw [hprod]
      simp only [e.apply_symm_apply, mul_assoc]
      rfl
abbrev opus_dpo_s_PiExceptPair {α : Type*} [Fintype α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀) :=
  opus_dpo_s_PiExcept (⟨a₁, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a₁⟩⟩ : opus_dpo_s_PiExcept a₀)

noncomputable def opus_dpo_s_pairInsert {α : Type*} [Fintype α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀)
    (xr : opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) (z₀ z₁ : ℤ) : α → ℤ :=
  (opus_dpo_s_piSplitAt a₀).symm
    ((opus_dpo_s_piSplitAt
      (⟨a₁, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a₁⟩⟩ : opus_dpo_s_PiExcept a₀)).symm
        (xr, z₁), z₀)

/-- Isolate two independent coordinates without assuming equal laws at the other coordinates. -/
theorem opus_dpo_s_productLaw_tsum_splitPair {α : Type*} [Fintype α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀) (law : α → ℤ → ℝ) (win : α → Finset ℤ)
    (hzero : ∀ i z, z ∉ win i → law i z = 0) (F : (α → ℤ) → ℝ) :
    (∑' x : α → ℤ, (∏ i, law i (x i)) * F x) =
      ∑' xr : opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ,
        (∏ i : opus_dpo_s_PiExceptPair a₀ a₁ hne, law i.1.1 (xr i)) *
          ∑' z₁ : ℤ, law a₁ z₁ *
            ∑' z₀ : ℤ, law a₀ z₀ * F (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) := by
  classical
  rw [opus_dpo_s_productLaw_tsum_splitAt a₀ law win hzero F]
  let a₁' : opus_dpo_s_PiExcept a₀ :=
    ⟨a₁, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a₁⟩⟩
  exact opus_dpo_s_productLaw_tsum_splitAt a₁'
    (fun i z => law i.1 z) (fun i => win i.1)
    (fun i z hz => hzero i.1 z hz)
    (fun xr => ∑' z : ℤ, law a₀ z * F ((opus_dpo_s_piSplitAt a₀).symm (xr, z)))
/-- Integrating an unused endpoint, a weight, and an independently duplicated factor. -/
theorem opus_dpo_s_pair_integrals {β : Type*} (σ H : β → ℝ)
    (hnorm : ∑' z, σ z = 1) (a Ω : ℝ) :
    (∑' z₁, σ z₁ * ∑' z₀, σ z₀ * (a * H z₀)) = a * ∑' z, σ z * H z ∧
    (∑' z₁, σ z₁ * ∑' z₀, σ z₀ * Ω) = Ω ∧
    (∑' z₁, σ z₁ * ∑' z₀, σ z₀ * (Ω * H z₀ * H z₁)) =
      Ω * (∑' z, σ z * H z) ^ 2 := by
  have hlinear (c : ℝ) : (∑' z, σ z * (c * H z)) = c * ∑' z, σ z * H z := by
    calc
      _ = ∑' z, c * (σ z * H z) := by apply tsum_congr; intro z; ring
      _ = _ := tsum_mul_left
  have hconst (c : ℝ) : (∑' z, σ z * c) = c := by rw [tsum_mul_right, hnorm, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hlinear a]
    exact hconst _
  · simp_rw [hconst Ω]
  · have hinner (z₁ : β) : (∑' z₀, σ z₀ * (Ω * H z₀ * H z₁)) =
        (Ω * H z₁) * ∑' z, σ z * H z := by
      calc
        _ = ∑' z₀, σ z₀ * ((Ω * H z₁) * H z₀) := by apply tsum_congr; intro z₀; ring
        _ = _ := hlinear _
    simp_rw [hinner]
    calc
      _ = ∑' z₁, σ z₁ * ((Ω * ∑' z, σ z * H z) * H z₁) := by
        apply tsum_congr; intro z₁; ring
      _ = _ := by rw [hlinear]; ring

/-- Integrate the three pointwise factors used in one weighted square step. -/
theorem opus_dpo_s_productLaw_pair_integrals {α : Type*} [Fintype α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀) (law : α → ℤ → ℝ) (win : α → Finset ℤ)
    (hzero : ∀ i z, z ∉ win i → law i z = 0)
    (hequal : law a₁ = law a₀) (hnorm : ∑' z, law a₀ z = 1)
    (H₀ Ω : (opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) → ℝ)
    (H : (opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) → ℤ → ℝ)
    (Current Weight Next : (α → ℤ) → ℝ)
    (hcurrent : ∀ xr z₀ z₁, Current (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) = H₀ xr * H xr z₀)
    (hweight : ∀ xr z₀ z₁, Weight (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) = Ω xr)
    (hnext : ∀ xr z₀ z₁, Next (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) = Ω xr * H xr z₀ * H xr z₁) :
    (∑' x, (∏ i, law i (x i)) * Current x) =
      (∑' xr, (∏ i : opus_dpo_s_PiExceptPair a₀ a₁ hne, law i.1.1 (xr i)) *
        (H₀ xr * ∑' z, law a₀ z * H xr z)) ∧
    (∑' x, (∏ i, law i (x i)) * Weight x) =
      (∑' xr, (∏ i : opus_dpo_s_PiExceptPair a₀ a₁ hne, law i.1.1 (xr i)) * Ω xr) ∧
    (∑' x, (∏ i, law i (x i)) * Next x) =
      (∑' xr, (∏ i : opus_dpo_s_PiExceptPair a₀ a₁ hne, law i.1.1 (xr i)) *
        (Ω xr * (∑' z, law a₀ z * H xr z) ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [opus_dpo_s_productLaw_tsum_splitPair a₀ a₁ hne law win hzero Current]
    apply tsum_congr
    intro xr
    congr 1
    simp_rw [hcurrent, hequal]
    exact (opus_dpo_s_pair_integrals (law a₀) (H xr) hnorm (H₀ xr) (Ω xr)).1
  · rw [opus_dpo_s_productLaw_tsum_splitPair a₀ a₁ hne law win hzero Weight]
    apply tsum_congr
    intro xr
    congr 1
    simp_rw [hweight, hequal]
    exact (opus_dpo_s_pair_integrals (law a₀) (H xr) hnorm (H₀ xr) (Ω xr)).2.1
  · rw [opus_dpo_s_productLaw_tsum_splitPair a₀ a₁ hne law win hzero Next]
    apply tsum_congr
    intro xr
    congr 1
    simp_rw [hnext, hequal]
    exact (opus_dpo_s_pair_integrals (law a₀) (H xr) hnorm (H₀ xr) (Ω xr)).2.2
/-- A finite prime-support law together with coordinate-dependent finite supports has finite
joint support, even though both ambient spaces can be infinite. -/
theorem opus_dpo_s_jointProduct_finiteSupport {P α : Type*} [Fintype α]
    (pmass : P → ℝ) (law : P → α → ℤ → ℝ) (primeSupport : Finset P)
    (win : P → α → Finset ℤ)
    (hpzero : ∀ p, p ∉ primeSupport → pmass p = 0)
    (hzero : ∀ p i z, z ∉ win p i → law p i z = 0) :
    ∃ S : Finset (P × (α → ℤ)), ∀ v, v ∉ S →
      pmass v.1 * (∏ i, law v.1 i (v.2 i)) = 0 := by
  classical
  let S : Finset (P × (α → ℤ)) := primeSupport.biUnion fun p =>
    ({p} : Finset P).product (Fintype.piFinset (win p))
  refine ⟨S, ?_⟩
  intro v hv
  by_cases hp : v.1 ∈ primeSupport
  · have hx : v.2 ∉ Fintype.piFinset (win v.1) := by
      intro hx
      apply hv
      apply Finset.mem_biUnion.mpr
      exact ⟨v.1, hp, Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hx⟩⟩
    have hn : ¬∀ i, v.2 i ∈ win v.1 i := by
      intro hall
      exact hx (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hw : (∏ j, law v.1 j (v.2 j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hzero v.1 i (v.2 i) hi)
    rw [hw, mul_zero]
  · rw [hpzero v.1 hp, zero_mul]

/-- Fubini over an explicitly finite joint support. -/
theorem opus_dpo_s_jointProduct_tsum {P α : Type*} [Fintype α]
    (pmass : P → ℝ) (law : P → α → ℤ → ℝ) (primeSupport : Finset P)
    (win : P → α → Finset ℤ)
    (hpzero : ∀ p, p ∉ primeSupport → pmass p = 0)
    (hzero : ∀ p i z, z ∉ win p i → law p i z = 0)
    (F : P → (α → ℤ) → ℝ) :
    (∑' p, pmass p * ∑' x, (∏ i, law p i (x i)) * F p x) =
      ∑' v : P × (α → ℤ),
        (pmass v.1 * ∏ i, law v.1 i (v.2 i)) * F v.1 v.2 := by
  obtain ⟨S, hS⟩ := opus_dpo_s_jointProduct_finiteSupport pmass law primeSupport win hpzero hzero
  have hs : Summable (fun v : P × (α → ℤ) =>
      (pmass v.1 * ∏ i, law v.1 i (v.2 i)) * F v.1 v.2) :=
    summable_of_ne_finset_zero (s := S) (fun v hv => by rw [hS v hv, zero_mul])
  rw [hs.tsum_prod]
  apply tsum_congr
  intro p
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  ring
/-- One weighted Cauchy–Schwarz step under independent prime and coordinate laws, with
finite supports and arbitrary laws on the unselected coordinates. -/
theorem opus_dpo_s_jointCoordinate_cauchy {P α : Type*} [Fintype α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀)
    (pmass : P → ℝ) (law : P → α → ℤ → ℝ)
    (primeSupport : Finset P) (win : P → α → Finset ℤ)
    (hpzero : ∀ p, p ∉ primeSupport → pmass p = 0)
    (hzero : ∀ p i z, z ∉ win p i → law p i z = 0)
    (hpnonneg : ∀ p, 0 ≤ pmass p) (hnonneg : ∀ p i z, 0 ≤ law p i z)
    (hequal : ∀ p, law p a₁ = law p a₀) (hnorm : ∀ p, ∑' z, law p a₀ z = 1)
    (H₀ Ω : P → (opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) → ℝ)
    (H : P → (opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) → ℤ → ℝ)
    (hΩ : ∀ p xr, 0 ≤ Ω p xr) (h₀ : ∀ p xr, |H₀ p xr| ≤ Ω p xr)
    (Current Weight Next : P → (α → ℤ) → ℝ)
    (hcurrent : ∀ p xr z₀ z₁,
      Current p (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) = H₀ p xr * H p xr z₀)
    (hweight : ∀ p xr z₀ z₁,
      Weight p (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) = Ω p xr)
    (hnext : ∀ p xr z₀ z₁,
      Next p (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) = Ω p xr * H p xr z₀ * H p xr z₁) :
    |∑' p, pmass p * ∑' x, (∏ i, law p i (x i)) * Current p x| ^ 2 ≤
      (∑' p, pmass p * ∑' x, (∏ i, law p i (x i)) * Weight p x) *
      (∑' p, pmass p * ∑' x, (∏ i, law p i (x i)) * Next p x) := by
  classical
  let Rest := opus_dpo_s_PiExceptPair a₀ a₁ hne
  let reducedLaw : P → Rest → ℤ → ℝ := fun p i z => law p i.1.1 z
  let reducedWin : P → Rest → Finset ℤ := fun p i => win p i.1.1
  have hreducedzero : ∀ p i z, z ∉ reducedWin p i → reducedLaw p i z = 0 :=
    fun p i z hz => hzero p i.1.1 z hz
  let μ : P × (Rest → ℤ) → ℝ := fun v => pmass v.1 * ∏ i, reducedLaw v.1 i (v.2 i)
  let avgH : P → (Rest → ℤ) → ℝ := fun p xr => ∑' z, law p a₀ z * H p xr z
  obtain ⟨S, hS⟩ := opus_dpo_s_jointProduct_finiteSupport
    pmass reducedLaw primeSupport reducedWin hpzero hreducedzero
  have hμ : ∀ v, 0 ≤ μ v := by
    intro v
    exact mul_nonneg (hpnonneg v.1) (Finset.prod_nonneg (fun i _ => hnonneg v.1 i.1.1 (v.2 i)))
  have hthree (p : P) := opus_dpo_s_productLaw_pair_integrals a₀ a₁ hne
    (law p) (win p) (hzero p) (hequal p) (hnorm p)
    (H₀ p) (Ω p) (H p) (Current p) (Weight p) (Next p)
    (hcurrent p) (hweight p) (hnext p)
  have hcurrentAvg :
      (∑' p, pmass p * ∑' x, (∏ i, law p i (x i)) * Current p x) =
        ∑' v : P × (Rest → ℤ), μ v * (H₀ v.1 v.2 * avgH v.1 v.2) := by
    calc
      _ = ∑' p, pmass p * ∑' xr, (∏ i, reducedLaw p i (xr i)) * (H₀ p xr * avgH p xr) := by
        apply tsum_congr; intro p; rw [(hthree p).1]
      _ = _ := opus_dpo_s_jointProduct_tsum pmass reducedLaw primeSupport reducedWin hpzero hreducedzero _
  have hweightAvg :
      (∑' p, pmass p * ∑' x, (∏ i, law p i (x i)) * Weight p x) =
        ∑' v : P × (Rest → ℤ), μ v * Ω v.1 v.2 := by
    calc
      _ = ∑' p, pmass p * ∑' xr, (∏ i, reducedLaw p i (xr i)) * Ω p xr := by
        apply tsum_congr; intro p; rw [(hthree p).2.1]
      _ = _ := opus_dpo_s_jointProduct_tsum pmass reducedLaw primeSupport reducedWin hpzero hreducedzero _
  have hnextAvg :
      (∑' p, pmass p * ∑' x, (∏ i, law p i (x i)) * Next p x) =
        ∑' v : P × (Rest → ℤ), μ v * (Ω v.1 v.2 * avgH v.1 v.2 ^ 2) := by
    calc
      _ = ∑' p, pmass p * ∑' xr, (∏ i, reducedLaw p i (xr i)) * (Ω p xr * avgH p xr ^ 2) := by
        apply tsum_congr; intro p; rw [(hthree p).2.2]
      _ = _ := opus_dpo_s_jointProduct_tsum pmass reducedLaw primeSupport reducedWin hpzero hreducedzero _
  rw [hcurrentAvg, hweightAvg, hnextAvg]
  exact opus_dpo_s_finiteSupport_weighted_cauchy μ
    (fun v => Ω v.1 v.2) (fun v => H₀ v.1 v.2) (fun v => avgH v.1 v.2)
    S hS hμ (fun v => hΩ v.1 v.2) (fun v => h₀ v.1 v.2)
/-- A zero response makes a row independent of either endpoint of that direction. -/
theorem opus_dpo_s_copyEvaluation_update_zero {R J C : Type*} [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ) (active : R → J → Prop)
    (E : Finset J) (o : opus_dpo_s_Copy active E) (r : J) (hρ : ρ o.1 r = 0)
    (x : C ⊕ (J × Fin 2) → ℤ) (side : Fin 2) (z : ℤ) :
    (∑ a, opus_dpo_s_copyCoeffInt c ρ active E o a *
      Function.update x (.inr (r, side)) z a) =
      ∑ a, opus_dpo_s_copyCoeffInt c ρ active E o a * x a := by
  classical
  rw [opus_dpo_s_copyEvaluation, opus_dpo_s_copyEvaluation]
  apply congrArg₂ (fun a b : ℤ => a + b)
  · apply Finset.sum_congr rfl; intro a _; simp
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = r
    · subst j; simp [hρ]
    · have hne (s : Fin 2) : (Sum.inr (j, s) : C ⊕ (J × Fin 2)) ≠ .inr (r, side) := by
        intro h; exact hj (congrArg Prod.fst (Sum.inr.inj h))
      rw [Function.update_of_ne (hne _)]

/-- An unduplicated direction uses only side zero in every occurrence. -/
theorem opus_dpo_s_copyEvaluation_update_unused {R J C : Type*} [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ) (active : R → J → Prop)
    (E : Finset J) (o : opus_dpo_s_Copy active E) (r : J) (hr : r ∉ E)
    (x : C ⊕ (J × Fin 2) → ℤ) (z : ℤ) :
    (∑ a, opus_dpo_s_copyCoeffInt c ρ active E o a *
      Function.update x (.inr (r, 1)) z a) =
      ∑ a, opus_dpo_s_copyCoeffInt c ρ active E o a * x a := by
  classical
  rw [opus_dpo_s_copyEvaluation, opus_dpo_s_copyEvaluation]
  apply congrArg₂ (fun a b : ℤ => a + b)
  · apply Finset.sum_congr rfl; intro a _; simp
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = r
    · subst j; simp [hr]
    · have hne (s : Fin 2) : (Sum.inr (j, s) : C ⊕ (J × Fin 2)) ≠ .inr (r, 1) := by
        intro h; exact hj (congrArg Prod.fst (Sum.inr.inj h))
      rw [Function.update_of_ne (hne _)]

@[simp] theorem opus_dpo_s_pairInsert_zero {α : Type*} [Fintype α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀)
    (xr : opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) (z₀ z₁ : ℤ) :
    opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁ a₀ = z₀ := by
  simp [opus_dpo_s_pairInsert, opus_dpo_s_piSplitAt]

@[simp] theorem opus_dpo_s_pairInsert_one {α : Type*} [Fintype α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀)
    (xr : opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) (z₀ z₁ : ℤ) :
    opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁ a₁ = z₁ := by
  simp [opus_dpo_s_pairInsert, opus_dpo_s_piSplitAt, hne]

@[simp] theorem opus_dpo_s_pairInsert_update_zero {α : Type*} [Fintype α] [DecidableEq α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀)
    (xr : opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) (z₀ z₁ t : ℤ) :
    Function.update (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) a₀ t =
      opus_dpo_s_pairInsert a₀ a₁ hne xr t z₁ := by
  classical
  funext i
  by_cases h : i = a₀ <;> simp [opus_dpo_s_pairInsert, opus_dpo_s_piSplitAt, h]

@[simp] theorem opus_dpo_s_pairInsert_update_one {α : Type*} [Fintype α] [DecidableEq α]
    (a₀ a₁ : α) (hne : a₁ ≠ a₀)
    (xr : opus_dpo_s_PiExceptPair a₀ a₁ hne → ℤ) (z₀ z₁ t : ℤ) :
    Function.update (opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ z₁) a₁ t =
      opus_dpo_s_pairInsert a₀ a₁ hne xr z₀ t := by
  classical
  funext i
  by_cases h₀ : i = a₀
  · subst i; simp [Function.update_of_ne hne.symm]
  · by_cases h₁ : i = a₁
    · subst i; simp
    · simp [opus_dpo_s_pairInsert, opus_dpo_s_piSplitAt, h₀, h₁, Subtype.ext_iff]
/-- Harmonic translation errors decay superpolynomially when the logarithmic cutoff
separates every fixed power of a scale dominating the displacement and block scale. -/
theorem opus_dpo_s_harmonicTranslation_superPolynomial
    (X W H V S : ℕ → ℕ) (q : ℕ)
    (hX : ∀ N, 1 ≤ X N) (hS : ∀ N, 1 ≤ S N)
    (hStendsto : Tendsto (fun N => (S N : ℝ)) atTop atTop)
    (hWle : ∀ᶠ N in atTop, W N ≤ S N)
    (hVle : ∀ᶠ N in atTop, V N ≤ S N)
    (hHle : ∀ᶠ N in atTop, H N ≤ S N ^ q)
    (hlog : OAI.MicrocellScale.Dominates (fun N => Real.log (X N : ℝ))
      (fun N => (S N : ℝ))) :
    SuperPolynomialSmall (fun N => harmonicTranslationUniformError (X N) (W N) (H N))
      (fun N => (V N : ℝ)) := by
  intro C hC
  let m : ℕ := Nat.ceil ((q : ℝ) + C + 1)
  have hm : (q : ℝ) + C + 1 ≤ (m : ℝ) := Nat.le_ceil _
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hSpos (N : ℕ) : (0 : ℝ) < (S N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hS N))
  have hSone (N : ℕ) : (1 : ℝ) ≤ (S N : ℝ) := by exact_mod_cast hS N
  have hlargeLog : ∀ᶠ N in atTop, 2 * (S N : ℝ) ≤ Real.log (X N : ℝ) := by
    filter_upwards [(hlog 1 (by norm_num)).eventually_ge_atTop 2] with N hN
    have hN' : (2 : ℝ) ≤ Real.log (X N : ℝ) / (S N : ℝ) := by simpa using hN
    exact (le_div_iff₀ (hSpos N)).mp hN'
  have hpowerLog : ∀ᶠ N in atTop, (S N : ℝ) ^ (m : ℝ) ≤ Real.log (X N : ℝ) := by
    filter_upwards [(hlog m hmpos).eventually_ge_atTop 1] with N hN
    simpa using (le_div_iff₀ (Real.rpow_pos_of_pos (hSpos N) _)).mp hN
  have hbound : ∀ᶠ N in atTop,
      harmonicTranslationUniformError (X N) (W N) (H N) * (V N : ℝ) ^ C ≤
        4 / (S N : ℝ) := by
    filter_upwards [hWle, hVle, hHle, hlargeLog, hpowerLog]
      with N hW hV hH hlogLarge hlogPower
    let L := Real.log (X N : ℝ)
    let D := (X N : ℝ) * (L - (W N : ℝ) / (X N : ℝ))
    have hXone : (1 : ℝ) ≤ (X N : ℝ) := by exact_mod_cast hX N
    have hXpos : (0 : ℝ) < (X N : ℝ) := by positivity
    have hWreal : (W N : ℝ) ≤ (S N : ℝ) := by exact_mod_cast hW
    have hVreal : (V N : ℝ) ≤ (S N : ℝ) := by exact_mod_cast hV
    have hHreal : (H N : ℝ) ≤ (S N : ℝ) ^ q := by exact_mod_cast hH
    have hLpos : 0 < L := by dsimp [L]; nlinarith [hSpos N]
    have hFrac : (W N : ℝ) / (X N : ℝ) ≤ (S N : ℝ) := by
      apply (div_le_iff₀ hXpos).mpr
      exact hWreal.trans (by nlinarith [hSpos N])
    have hDen : L / 2 ≤ L - (W N : ℝ) / (X N : ℝ) := by dsimp [L] at *; linarith
    have hD : L ≤ 2 * D := by
      dsimp [D]
      have hhalfpos : 0 ≤ L / 2 := by positivity
      have hmul := mul_le_mul hXone hDen hhalfpos (by positivity : (0 : ℝ) ≤ X N)
      nlinarith
    have hDpos : 0 < D := by linarith
    have herror : harmonicTranslationUniformError (X N) (W N) (H N) ≤ 4 * (H N : ℝ) / L := by
      calc
        _ ≤ 2 * (H N : ℝ) / D := min_le_right _ _
        _ ≤ _ := by
          apply (div_le_div_iff₀ hDpos hLpos).mpr
          nlinarith [Nat.cast_nonneg (α := ℝ) (H N)]
    have hpowV : (V N : ℝ) ^ C ≤ (S N : ℝ) ^ C :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hVreal hC.le
    have hpower : (H N : ℝ) * (V N : ℝ) ^ C * (S N : ℝ) ≤ L := by
      calc
        _ ≤ (S N : ℝ) ^ q * (S N : ℝ) ^ C * (S N : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hHreal hpowV (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))
            (Nat.cast_nonneg _)
        _ = (S N : ℝ) ^ ((q : ℝ) + C + 1) := by
          calc
            _ = (S N : ℝ) ^ ((q : ℝ) + C) * (S N : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_add (hSpos N)]
            _ = (S N : ℝ) ^ ((q : ℝ) + C) * (S N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := (Real.rpow_add (hSpos N) _ _).symm
        _ ≤ (S N : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le (hSone N) hm
        _ ≤ L := hlogPower
    calc
      _ ≤ (4 * (H N : ℝ) / L) * (V N : ℝ) ^ C :=
        mul_le_mul_of_nonneg_right herror (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = 4 * ((H N : ℝ) * (V N : ℝ) ^ C) / L := by ring
      _ ≤ 4 / (S N : ℝ) := by
        apply (div_le_div_iff₀ hLpos (hSpos N)).mpr
        nlinarith
  have hupper : Tendsto (fun N => 4 / (S N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hStendsto).const_mul 4
  have hnonneg : ∀ᶠ N in atTop,
      0 ≤ harmonicTranslationUniformError (X N) (W N) (H N) * (V N : ℝ) ^ C := by
    filter_upwards [hWle, hlargeLog] with N hW hlogLarge
    have hXone : (1 : ℝ) ≤ (X N : ℝ) := by exact_mod_cast hX N
    have hWreal : (W N : ℝ) ≤ (S N : ℝ) := by exact_mod_cast hW
    have hFrac : (W N : ℝ) / (X N : ℝ) ≤ (S N : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < X N)).mpr
      exact hWreal.trans (by nlinarith [hSpos N])
    unfold harmonicTranslationUniformError
    apply mul_nonneg
    · apply le_min (by norm_num)
      apply div_nonneg (by positivity)
      apply mul_nonneg (by positivity)
      nlinarith [hSpos N]
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact squeeze_zero' hnonneg hbound hupper
theorem opus_dpo_s_rowProduct_update_zero {R J C : Type*} [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ) (active : R → J → Prop)
    (E : Finset J) (t : R) (r : J) (hρ : ρ t r = 0) (f : ℤ → ℝ)
    (x : C ⊕ (J × Fin 2) → ℤ) (side : Fin 2) (z : ℤ) :
    opus_dpo_s_rowProduct c ρ active E t f (Function.update x (.inr (r, side)) z) =
      opus_dpo_s_rowProduct c ρ active E t f x := by
  classical
  unfold opus_dpo_s_rowProduct
  apply Finset.prod_congr rfl
  intro η _
  rw [opus_dpo_s_copyEvaluation_update_zero c ρ active E ⟨t, η⟩ r hρ]

theorem opus_dpo_s_rowProduct_update_unused {R J C : Type*} [Fintype J] [Fintype C]
    (c : R → C → ℤ) (ρ : R → J → ℤ) (active : R → J → Prop)
    (E : Finset J) (t : R) (r : J) (hr : r ∉ E) (f : ℤ → ℝ)
    (x : C ⊕ (J × Fin 2) → ℤ) (z : ℤ) :
    opus_dpo_s_rowProduct c ρ active E t f (Function.update x (.inr (r, 1)) z) =
      opus_dpo_s_rowProduct c ρ active E t f x := by
  classical
  unfold opus_dpo_s_rowProduct
  apply Finset.prod_congr rfl
  intro η _
  rw [opus_dpo_s_copyEvaluation_update_unused c ρ active E ⟨t, η⟩ r hr]
theorem opus_dpo_s_roughPart_le_natAbs {w : ℕ} {a : ℤ} (ha : a ≠ 0) :
    roughPart w a ≤ a.natAbs := by
  classical
  let n := a.natAbs
  let R := (Finset.range (n + 1)).filter fun p : ℕ => p.Prime ∧ w < p
  let S := (Finset.range (n + 1)).filter Nat.Prime
  let g : ℕ → ℕ := fun p => p ^ n.factorization p
  have hn : n ≠ 0 := by
    dsimp [n]
    exact Int.natAbs_ne_zero.mpr ha
  have hRsub : R ⊆ S := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpRange, hpcond⟩
    exact Finset.mem_filter.mpr ⟨hpRange, hpcond.1⟩
  have hRfilterEq :
      (∏ p ∈ R, g p) =
        ∏ p ∈ R.filter (fun p => p ∈ n.factorization.support), g p := by
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hps : p ∉ n.factorization.support := by
      intro hmem
      exact hnot (Finset.mem_filter.mpr ⟨hp, hmem⟩)
    have he : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hps
    simp [g, he]
  have hsub : R.filter (fun p => p ∈ n.factorization.support) ⊆ S :=
    (Finset.filter_subset _ _).trans hRsub
  have hRle :
      (∏ p ∈ R.filter (fun p => p ∈ n.factorization.support), g p) ≤
        ∏ p ∈ S, g p :=
    Finset.prod_le_prod_of_subset_of_one_le hsub fun p hp _ => by
      have hpPrime := (Finset.mem_filter.mp hp).2
      have hpOne : 1 ≤ p := le_trans (by norm_num) hpPrime.two_le
      exact one_le_pow₀ hpOne
  have hfull : ∏ p ∈ S, g p = n := by
    have hnat := Nat.prod_pow_prime_padicValNat n hn (n + 1) (by omega)
    have heq :
        (∏ p ∈ S, g p) =
          ∏ p ∈ Finset.range (n + 1) with p.Prime, p ^ padicValNat p n := by
      apply Finset.prod_congr rfl
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpRange, hpPrime⟩
      change p ^ n.factorization p = p ^ padicValNat p n
      rw [Nat.factorization_def n hpPrime]
    rw [heq]
    exact hnat
  calc
    roughPart w a = ∏ p ∈ R, g p := by rfl
    _ = ∏ p ∈ R.filter (fun p => p ∈ n.factorization.support), g p := hRfilterEq
    _ ≤ ∏ p ∈ S, g p := hRle
    _ = n := hfull
    _ = a.natAbs := rfl


theorem opus_dpo_s_renameEval {q m : ℕ} (ι : Fin q ↪ Fin m)
    (P : IntegerPolynomial q) (p : Fin m → ℕ) :
    evalIntegerPolynomial (MvPolynomial.rename ι P) (fun i => (p i : ℤ)) =
      evalIntegerPolynomial P (fun j => (p (ι j) : ℤ)) := by
  unfold evalIntegerPolynomial
  rw [MvPolynomial.eval_rename]
  rfl


/-- On a supported master tuple, an allowed type's modulus is bounded by the gap length.
This avoids a separate polynomial coefficient envelope when controlling root translations. -/
theorem opus_dpo_s_templateModulus_le_gap {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : CubeTemplate) (hT : Allowed Dm T) (l : Fin K) (N : ℕ)
    (p : Fin sl → ℕ)
    (hp : ∀ j, (MS.primeStage.pool N l).lower ≤ p j ∧
      p j < (MS.primeStage.pool N l).upper ∧ (p j).Prime)
    (hgood : T.Good (corrScales MS) l N (fun j => p ((Classical.choose hT) j))) :
    T.modulus (corrScales MS) N (fun j => p ((Classical.choose hT) j)) ≤
      MS.core.parameters.H N l := by
  classical
  let ι := Classical.choose hT
  let value := evalIntegerPolynomial T.D (fun j => (p (ι j) : ℤ))
  have hvalue : value ≠ 0 := hgood.2.2.1 T.D T.D_mem
  have hlisted : MvPolynomial.rename ι T.D ∈ Dm :=
    Classical.choose_spec hT T.D T.D_mem
  have hnonzero : evalIntegerPolynomial (MvPolynomial.rename ι T.D)
      (fun j => (p j : ℤ)) ≠ 0 := by
    rw [opus_dpo_s_renameEval]
    exact hvalue
  have hdvd := MS.gapStage.polynomial_values_divide_gap N l p
    (MvPolynomial.rename ι T.D) hlisted hp hnonzero
  have hle := Nat.le_of_dvd (MS.core.parameters.Hpos N l) hdvd
  rw [opus_dpo_s_renameEval] at hle
  change MS.core.parameters.M N * roughPart (N + 1) value ≤ MS.core.parameters.H N l
  exact (Nat.mul_le_mul_left _ (opus_dpo_s_roughPart_le_natAbs hvalue)).trans hle
/-- A row with zero own response ignores both endpoints of its selected direction. -/
theorem opus_dpo_s_rowProduct_pair_zero {R J C : Type*} [Fintype J] [Fintype C]
    [coordFT : Fintype (C ⊕ (J × Fin 2))]
    (c : R → C → ℤ) (ρ : R → J → ℤ) (active : R → J → Prop)
    (E : Finset J) (t : R) (r : J) (hρ : ρ t r = 0) (f : ℤ → ℝ)
    (hne : (Sum.inr (r, (1 : Fin 2)) : C ⊕ (J × Fin 2)) ≠ .inr (r, 0))
    (xr : opus_dpo_s_PiExceptPair (Sum.inr (r, 0) : C ⊕ (J × Fin 2))
      (.inr (r, 1)) hne → ℤ) (z₀ z₁ : ℤ) :
    opus_dpo_s_rowProduct c ρ active E t f
      (opus_dpo_s_pairInsert (.inr (r, 0)) (.inr (r, 1)) hne xr z₀ z₁) =
    opus_dpo_s_rowProduct c ρ active E t f
      (opus_dpo_s_pairInsert (.inr (r, 0)) (.inr (r, 1)) hne xr 0 0) := by
  classical
  have h₀ := opus_dpo_s_rowProduct_update_zero c ρ active E t r hρ f
    (opus_dpo_s_pairInsert (.inr (r, 0)) (.inr (r, 1)) hne xr 0 z₁) 0 z₀
  rw [opus_dpo_s_pairInsert_update_zero] at h₀
  have h₁ := opus_dpo_s_rowProduct_update_zero c ρ active E t r hρ f
    (opus_dpo_s_pairInsert (.inr (r, 0)) (.inr (r, 1)) hne xr 0 0) 1 z₁
  rw [opus_dpo_s_pairInsert_update_one] at h₁
  exact h₀.trans h₁

/-- Every old row ignores the second endpoint of an unduplicated direction. -/
theorem opus_dpo_s_rowProduct_pair_unused {R J C : Type*} [Fintype J] [Fintype C]
    [coordFT : Fintype (C ⊕ (J × Fin 2))]
    (c : R → C → ℤ) (ρ : R → J → ℤ) (active : R → J → Prop)
    (E : Finset J) (t : R) (r : J) (hr : r ∉ E) (f : ℤ → ℝ)
    (hne : (Sum.inr (r, (1 : Fin 2)) : C ⊕ (J × Fin 2)) ≠ .inr (r, 0))
    (xr : opus_dpo_s_PiExceptPair (Sum.inr (r, 0) : C ⊕ (J × Fin 2))
      (.inr (r, 1)) hne → ℤ) (z₀ z₁ : ℤ) :
    opus_dpo_s_rowProduct c ρ active E t f
      (opus_dpo_s_pairInsert (.inr (r, 0)) (.inr (r, 1)) hne xr z₀ z₁) =
    opus_dpo_s_rowProduct c ρ active E t f
      (opus_dpo_s_pairInsert (.inr (r, 0)) (.inr (r, 1)) hne xr z₀ 0) := by
  classical
  have h := opus_dpo_s_rowProduct_update_unused c ρ active E t r hr f
    (opus_dpo_s_pairInsert (.inr (r, 0)) (.inr (r, 1)) hne xr z₀ 0) z₁
  rw [opus_dpo_s_pairInsert_update_one] at h
  exact h
/-- Selecting the occurrences of one row is exactly the product over that row's branch bits. -/
theorem opus_dpo_s_sigmaFiber_product {R : Type*} {β : R → Type*}
    [Fintype R] [∀ t, Fintype (β t)] [wholeFT : Fintype (Sigma β)]
    (t : R) (f : Sigma β → ℝ) :
    (∏ o ∈ (Finset.univ : Finset (Sigma β)).filter (fun o => o.1 = t), f o) =
      ∏ η : β t, f ⟨t, η⟩ := by
  classical
  rw [Finset.prod_filter]
  have huniv : (Finset.univ : Finset (Sigma β)) =
      (Finset.univ : Finset R).sigma (fun s => (Finset.univ : Finset (β s))) := by
    ext o
    simp
  rw [huniv, Finset.prod_sigma]
  rw [Fintype.prod_eq_single t (fun s hs => Finset.prod_eq_one (fun η _ => if_neg hs))]
  exact Finset.prod_congr rfl (fun η _ => if_pos rfl)


end OpusDpoS

section OpusDpoSCheck

local instance (priority := 100000) opus_dpo_s_check_nonrootDecEq {b : ℕ}
    (T : Fin b → CubeTemplate) : DecidableEq (pkgB2_Nonroot T) := Classical.decEq _
local instance (priority := 100000) opus_dpo_s_check_rowDecEq {b : ℕ}
    (T : Fin b → CubeTemplate) : DecidableEq (pkgB2_BaseRow T) := Classical.decEq _
local instance (priority := 100000) opus_dpo_s_check_oldCoordDecEq {b : ℕ}
    (T : Fin b → CubeTemplate) : DecidableEq (pkgB2_OldCoord T) := Classical.decEq _
variable {K sl b : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

theorem opus_dpo_s_check_rowValue
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E))) (x : pkgB2_Coord T → ℤ) :
    pkgB2_stateRowValue MS T hT J0 gap direction E N p u
      (fun j => x (pkgB2_coordEnum T j)) =
      ∑ a : pkgB2_Coord T,
        pkgB2_occurrenceCoefficientInt T
          (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
          direction E (pkgB2_occurrenceEnum T E u) a * x a := by
  classical
  unfold pkgB2_stateRowValue
  rw [pkgB2_linearRowValue_eq_castInt
    MS T hT J0 gap direction E N p u (fun j => x (pkgB2_coordEnum T j))]
  simp only [Rat.num_intCast]
  exact Fintype.sum_equiv (pkgB2_coordEnum T) _ _ (fun _ => rfl)

noncomputable def opus_dpo_s_check_rowFunction
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (t : pkgB2_BaseRow T) (y : ℤ) : ℝ :=
  match t with
  | .inl _ => nu MS.core.parameters N B y - 1
  | .inr r => if r ∈ E then 1 + nu MS.core.parameters N B y
    else (I r.1).g r.2.1 (pkgB2_repPrimeProject hT p r.1) y

theorem opus_dpo_s_check_integrand
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (x : pkgB2_Coord T → ℤ) :
    pkgB2_stateIntegrand MS B gap T hT J0 direction E N I p
      (fun j => x (pkgB2_coordEnum T j)) =
      (if E = ∅ then ∏ k, (I k).e (pkgB2_repPrimeProject hT p k) else 1) *
      ∏ t : pkgB2_BaseRow T,
        opus_dpo_s_rowProduct
          (pkgB2_oldCoefficient T (fun k => ((T k).modulus (corrScales MS) N
            (pkgB2_repPrimeProject hT p k) : ℤ)))
          (fun t r => pkgB2_response T (fun k => ((T k).modulus (corrScales MS) N
            (pkgB2_repPrimeProject hT p k) : ℤ)) r
              (pkgB2_directionLift (T r.1).d (direction r)) t)
          (pkgB2_activeRow T) E t (opus_dpo_s_check_rowFunction MS B T hT E N I p t) x := by
  classical
  unfold pkgB2_stateIntegrand
  apply congrArg₂ (fun a b : ℝ => a * b)
  · by_cases h : E = ∅ <;> simp [h]
  · have hfactor (u : Fin (Fintype.card (pkgB2_Occurrence T E))) :
        pkgB2_stateFactor MS B gap T hT J0 direction E N I p
          (fun j => x (pkgB2_coordEnum T j)) u =
        opus_dpo_s_check_rowFunction MS B T hT E N I p (pkgB2_occurrenceEnum T E u).1
          (∑ a : pkgB2_Coord T,
            pkgB2_occurrenceCoefficientInt T
              (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
              direction E (pkgB2_occurrenceEnum T E u) a * x a) := by
      unfold pkgB2_stateFactor
      rw [opus_dpo_s_check_rowValue]
      cases ht : (pkgB2_occurrenceEnum T E u).1 with
      | inl a => simp [opus_dpo_s_check_rowFunction, ht]
      | inr r =>
          by_cases hr : r ∈ E <;> simp [opus_dpo_s_check_rowFunction, ht, hr]
    let f : pkgB2_Occurrence T E → ℝ := fun o =>
      opus_dpo_s_check_rowFunction MS B T hT E N I p o.1
        (∑ a : pkgB2_Coord T,
          pkgB2_occurrenceCoefficientInt T
            (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
            direction E o a * x a)
    have heq : (∏ u, f (pkgB2_occurrenceEnum T E u)) = ∏ o, f o :=
      Fintype.prod_equiv (pkgB2_occurrenceEnum T E) _ _ (fun _ => rfl)
    calc
      _ = ∏ u, f (pkgB2_occurrenceEnum T E u) := by
        apply Finset.prod_congr rfl
        intro u _
        exact hfactor u
      _ = ∏ o, f o := heq
      _ = ∏ t : pkgB2_BaseRow T,
          ∏ η : {j : pkgB2_Nonroot T // j ∈ E ∧ pkgB2_activeRow T t j} → Fin 2,
            f ⟨t, η⟩ := by
        have huniv : (Finset.univ : Finset (pkgB2_Occurrence T E)) =
            (Finset.univ : Finset (pkgB2_BaseRow T)).sigma (fun t =>
              (Finset.univ : Finset ({j : pkgB2_Nonroot T // j ∈ E ∧ pkgB2_activeRow T t j} → Fin 2))) := by
          ext o
          simp
        rw [huniv, Finset.prod_sigma]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro t _
        unfold opus_dpo_s_rowProduct
        apply Finset.prod_congr (by ext; simp)
        intro η _
        dsimp [f]
        congr 1
        apply Finset.sum_congr (by ext; simp)
        intro a _
        rfl

theorem opus_dpo_s_check_stateAverage
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (I : ∀ k, DualInput MS B (T k) N)
    (hreg : ∀ p, pkgB2_goodPrimeEvent MS gap T hT N p →
      pkgB2_baseRegular MS B T J0 gap hT N p) :
    pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 E N I =
      ∑' p : Fin (b * sl) → ℕ,
        ((independentPrimePoolProbability
          (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
          (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
          (pkgB2_goodPrimeEvent MS gap T hT N))⁻¹ *
        independentPrimePoolMass
          (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
          (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p *
        (if pkgB2_goodPrimeEvent MS gap T hT N p then 1 else 0)) *
        ∑' x : pkgB2_Coord T → ℤ,
          (∏ c, pkgB2_baseCoordinateLaw MS B T J0 gap hT N p c (x c)) *
            pkgB2_stateIntegrand MS B gap T hT J0 direction E N I p
              (fun j => x (pkgB2_coordEnum T j)) := by
  classical
  unfold pkgB2_stateAverage
  simp only [pkgB2_weightedLinearFormsData]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  by_cases hp : pkgB2_goodPrimeEvent MS gap T hT N p
  · simp only [hp, if_pos, mul_one]
    rw [← mul_assoc]
    congr 1
    have hregp := hreg p hp
    simp only [pkgB2_baseMass, hregp, dite_true]
    let e : (pkgB2_Coord T → ℤ) ≃
        (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :=
      Equiv.arrowCongr (pkgB2_coordEnum T).symm (Equiv.refl ℤ)
    calc
      _ = ∑' x : pkgB2_Coord T → ℤ,
          (∏ j, pkgB2_baseCoordinateLaw MS B T J0 gap hT N p (pkgB2_coordEnum T j)
            (x (pkgB2_coordEnum T j))) *
            pkgB2_stateIntegrand MS B gap T hT J0 direction E N I p
              (fun j => x (pkgB2_coordEnum T j)) :=
        (e.tsum_eq _).symm
      _ = _ := by
        apply tsum_congr
        intro x
        congr 1
        exact Fintype.prod_equiv (pkgB2_coordEnum T) _ _ (fun _ => rfl)
  · simp [hp]

noncomputable def opus_dpo_s_check_c
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (N : ℕ) (p : Fin (b * sl) → ℕ) :
    pkgB2_BaseRow T → pkgB2_OldCoord T → ℤ :=
  pkgB2_oldCoefficient T (fun k => ((T k).modulus (corrScales MS) N
    (pkgB2_repPrimeProject hT p k) : ℤ))

noncomputable def opus_dpo_s_check_rho
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (N : ℕ) (p : Fin (b * sl) → ℕ) : pkgB2_BaseRow T → pkgB2_Nonroot T → ℤ :=
  fun t r => pkgB2_response T (fun k => ((T k).modulus (corrScales MS) N
    (pkgB2_repPrimeProject hT p k) : ℤ)) r
      (pkgB2_directionLift (T r.1).d (direction r)) t

noncomputable def opus_dpo_s_check_rowProduct
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (t : pkgB2_BaseRow T) (x : pkgB2_Coord T → ℤ) : ℝ :=
  opus_dpo_s_rowProduct (opus_dpo_s_check_c MS T hT N p)
    (opus_dpo_s_check_rho MS T hT direction N p) (pkgB2_activeRow T) E t
    (opus_dpo_s_check_rowFunction MS B T hT E N I p t) x

theorem opus_dpo_s_check_rho_self
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (r : pkgB2_Nonroot T) : opus_dpo_s_check_rho MS T hT direction N p (.inr r) r = 0 := by
  apply pkgB2_response_self
  simpa only [pkgB2_directionLift_zero, pkgB2_directionLift_sum] using (hdir r).2.1

theorem opus_dpo_s_check_integrand_insert
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) (hr : r ∉ E)
    (N : ℕ) (p : Fin (b * sl) → ℕ) (I : ∀ k, DualInput MS B (T k) N)
    (x : pkgB2_Coord T → ℤ) :
    pkgB2_stateIntegrand MS B gap T hT J0 direction (insert r E) N I p
      (fun j => x (pkgB2_coordEnum T j)) =
      opus_dpo_s_rowProduct (opus_dpo_s_check_c MS T hT N p)
        (opus_dpo_s_check_rho MS T hT direction N p) (pkgB2_activeRow T) E (.inr r)
        (fun y => 1 + nu MS.core.parameters N B y) x *
      (∏ t ∈ Finset.univ.erase (Sum.inr r),
        opus_dpo_s_check_rowProduct MS B T hT direction E N I p t x) *
      (∏ t ∈ Finset.univ.erase (Sum.inr r),
        opus_dpo_s_check_rowProduct MS B T hT direction E N I p t
          (Function.update x (.inr (r, 0)) (x (.inr (r, 1))))) := by
  classical
  rw [opus_dpo_s_check_integrand]
  have hE : insert r E ≠ ∅ := Finset.insert_ne_empty r E
  simp only [hE, if_false, one_mul]
  have hstable : ∀ t : pkgB2_BaseRow T, t ≠ .inr r →
      opus_dpo_s_check_rowFunction MS B T hT (insert r E) N I p t =
        opus_dpo_s_check_rowFunction MS B T hT E N I p t := by
    intro t ht
    funext y
    cases t with
    | inl u => rfl
    | inr s =>
        have hs : s ≠ r := by intro h; exact ht (congrArg Sum.inr h)
        simp [opus_dpo_s_check_rowFunction, hs]
  have hstep := opus_dpo_s_occurrenceProduct_insert
    (opus_dpo_s_check_c MS T hT N p) (opus_dpo_s_check_rho MS T hT direction N p)
    Sum.inr E r hr (opus_dpo_s_check_rho_self MS T hT direction hdir N p r)
    (fun E t => opus_dpo_s_check_rowFunction MS B T hT E N I p t) hstable x
  have hown : opus_dpo_s_check_rowFunction MS B T hT (insert r E) N I p (.inr r) =
      (fun y => 1 + nu MS.core.parameters N B y) := by
    funext y
    simp [opus_dpo_s_check_rowFunction]
  rw [hown] at hstep
  dsimp only [opus_dpo_s_check_rowProduct, opus_dpo_s_check_c, opus_dpo_s_check_rho,
    pkgB2_activeRow] at hstep ⊢
  exact hstep
theorem opus_dpo_s_check_selected_bound
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) (hr : r ∉ E)
    (N : ℕ) (p : Fin (b * sl) → ℕ) (I : ∀ k, DualInput MS B (T k) N)
    (x : pkgB2_Coord T → ℤ) :
    |(if E = ∅ then ∏ k, (I k).e (pkgB2_repPrimeProject hT p k) else 1) *
      opus_dpo_s_check_rowProduct MS B T hT direction E N I p (.inr r) x| ≤
      opus_dpo_s_rowProduct (opus_dpo_s_check_c MS T hT N p)
        (opus_dpo_s_check_rho MS T hT direction N p) (pkgB2_activeRow T) E (.inr r)
        (fun y => 1 + nu MS.core.parameters N B y) x := by
  classical
  have he : |(if E = ∅ then ∏ k, (I k).e (pkgB2_repPrimeProject hT p k) else 1)| ≤ 1 := by
    split_ifs
    · simpa using c_elim2_abs_prod_le_of_nonneg Finset.univ
        (fun k => (I k).e (pkgB2_repPrimeProject hT p k)) (fun _ => 1)
        (fun _ _ => by norm_num) (fun k _ => (I k).e_bound _)
    · norm_num
  have hrow : |opus_dpo_s_check_rowProduct MS B T hT direction E N I p (.inr r) x| ≤
      opus_dpo_s_rowProduct (opus_dpo_s_check_c MS T hT N p)
        (opus_dpo_s_check_rho MS T hT direction N p) (pkgB2_activeRow T) E (.inr r)
        (fun y => 1 + nu MS.core.parameters N B y) x := by
    unfold opus_dpo_s_check_rowProduct opus_dpo_s_rowProduct
    simp only [opus_dpo_s_check_rowFunction, hr, if_false]
    apply c_elim2_abs_prod_le_of_nonneg Finset.univ
    · intro η _
      exact (abs_nonneg _).trans ((I r.1).g_bound r.2.1 (pkgB2_repPrimeProject hT p r.1) _)
    · intro η _
      exact (I r.1).g_bound r.2.1 (pkgB2_repPrimeProject hT p r.1) _
  rw [abs_mul]
  calc
    _ ≤ 1 * |opus_dpo_s_check_rowProduct MS B T hT direction E N I p (.inr r) x| :=
      mul_le_mul_of_nonneg_right he (abs_nonneg _)
    _ ≤ _ := by simpa using hrow
theorem opus_dpo_s_check_sideNe (T : Fin b → CubeTemplate) (r : pkgB2_Nonroot T) :
    (Sum.inr (r, (1 : Fin 2)) : pkgB2_Coord T) ≠ .inr (r, 0) := by
  intro h
  have h' := congrArg (fun z => z.2.val) (Sum.inr.inj h)
  norm_num at h'

noncomputable def opus_dpo_s_check_frame (T : Fin b → CubeTemplate) (r : pkgB2_Nonroot T)
    (xr : opus_dpo_s_PiExceptPair (Sum.inr (r, 0) : pkgB2_Coord T) (.inr (r, 1))
      (opus_dpo_s_check_sideNe T r) → ℤ) (z₀ z₁ : ℤ) : pkgB2_Coord T → ℤ :=
  opus_dpo_s_pairInsert (.inr (r, 0)) (.inr (r, 1)) (opus_dpo_s_check_sideNe T r) xr z₀ z₁

noncomputable def opus_dpo_s_check_weight
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) (N : ℕ)
    (p : Fin (b * sl) → ℕ) (x : pkgB2_Coord T → ℤ) : ℝ :=
  opus_dpo_s_rowProduct (opus_dpo_s_check_c MS T hT N p)
    (opus_dpo_s_check_rho MS T hT direction N p) (pkgB2_activeRow T) E (.inr r)
    (fun y => 1 + nu MS.core.parameters N B y) x

noncomputable def opus_dpo_s_check_other
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : pkgB2_Coord T → ℤ) : ℝ :=
  ∏ t ∈ Finset.univ.erase (Sum.inr r),
    opus_dpo_s_check_rowProduct MS B T hT direction E N I p t x

theorem opus_dpo_s_check_weight_frame
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (E : Finset (pkgB2_Nonroot T))
    (r : pkgB2_Nonroot T) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (xr : opus_dpo_s_PiExceptPair (Sum.inr (r, 0) : pkgB2_Coord T) (.inr (r, 1))
      (opus_dpo_s_check_sideNe T r) → ℤ) (z₀ z₁ : ℤ) :
    opus_dpo_s_check_weight MS B T hT direction E r N p (opus_dpo_s_check_frame T r xr z₀ z₁) =
      opus_dpo_s_check_weight MS B T hT direction E r N p (opus_dpo_s_check_frame T r xr 0 0) :=
  opus_dpo_s_rowProduct_pair_zero (coordFT := pkgB2_coordFintype T)
    (opus_dpo_s_check_c MS T hT N p) (opus_dpo_s_check_rho MS T hT direction N p)
    (pkgB2_activeRow T) E (.inr r) r (opus_dpo_s_check_rho_self MS T hT direction hdir N p r)
    (fun y => 1 + nu MS.core.parameters N B y) (opus_dpo_s_check_sideNe T r) xr z₀ z₁

theorem opus_dpo_s_check_row_frame
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (E : Finset (pkgB2_Nonroot T))
    (r : pkgB2_Nonroot T) (N : ℕ) (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (xr : opus_dpo_s_PiExceptPair (Sum.inr (r, 0) : pkgB2_Coord T) (.inr (r, 1))
      (opus_dpo_s_check_sideNe T r) → ℤ) (z₀ z₁ : ℤ) :
    opus_dpo_s_check_rowProduct MS B T hT direction E N I p (.inr r) (opus_dpo_s_check_frame T r xr z₀ z₁) =
      opus_dpo_s_check_rowProduct MS B T hT direction E N I p (.inr r) (opus_dpo_s_check_frame T r xr 0 0) :=
  opus_dpo_s_rowProduct_pair_zero (coordFT := pkgB2_coordFintype T)
    (opus_dpo_s_check_c MS T hT N p) (opus_dpo_s_check_rho MS T hT direction N p)
    (pkgB2_activeRow T) E (.inr r) r (opus_dpo_s_check_rho_self MS T hT direction hdir N p r)
    (opus_dpo_s_check_rowFunction MS B T hT E N I p (.inr r)) (opus_dpo_s_check_sideNe T r) xr z₀ z₁

theorem opus_dpo_s_check_other_frame
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) (hr : r ∉ E)
    (N : ℕ) (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (xr : opus_dpo_s_PiExceptPair (Sum.inr (r, 0) : pkgB2_Coord T) (.inr (r, 1))
      (opus_dpo_s_check_sideNe T r) → ℤ) (z₀ z₁ : ℤ) :
    opus_dpo_s_check_other MS B T hT direction E r N I p (opus_dpo_s_check_frame T r xr z₀ z₁) =
      opus_dpo_s_check_other MS B T hT direction E r N I p (opus_dpo_s_check_frame T r xr z₀ 0) := by
  classical
  apply Finset.prod_congr rfl
  intro t _
  exact opus_dpo_s_rowProduct_pair_unused (coordFT := pkgB2_coordFintype T)
    (opus_dpo_s_check_c MS T hT N p) (opus_dpo_s_check_rho MS T hT direction N p)
    (pkgB2_activeRow T) E t r hr (opus_dpo_s_check_rowFunction MS B T hT E N I p t)
    (opus_dpo_s_check_sideNe T r) xr z₀ z₁

theorem opus_dpo_s_check_current_point
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (E : Finset (pkgB2_Nonroot T))
    (r : pkgB2_Nonroot T) (hr : r ∉ E) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (xr : opus_dpo_s_PiExceptPair (Sum.inr (r, 0) : pkgB2_Coord T) (.inr (r, 1))
      (opus_dpo_s_check_sideNe T r) → ℤ) (z₀ z₁ : ℤ) :
    pkgB2_stateIntegrand MS B gap T hT J0 direction E N I p
      (fun j => opus_dpo_s_check_frame T r xr z₀ z₁ (pkgB2_coordEnum T j)) =
      ((if E = ∅ then ∏ k, (I k).e (pkgB2_repPrimeProject hT p k) else 1) *
        opus_dpo_s_check_rowProduct MS B T hT direction E N I p (.inr r)
          (opus_dpo_s_check_frame T r xr 0 0)) *
      opus_dpo_s_check_other MS B T hT direction E r N I p (opus_dpo_s_check_frame T r xr z₀ 0) := by
  classical
  rw [opus_dpo_s_check_integrand]
  change _ * (∏ t, opus_dpo_s_check_rowProduct MS B T hT direction E N I p t
    (opus_dpo_s_check_frame T r xr z₀ z₁)) = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (Sum.inr r))]
  change _ * (_ * opus_dpo_s_check_other MS B T hT direction E r N I p
    (opus_dpo_s_check_frame T r xr z₀ z₁)) = _
  rw [opus_dpo_s_check_row_frame MS B T hT direction hdir,
    opus_dpo_s_check_other_frame MS B T hT direction E r hr]
  ring

theorem opus_dpo_s_check_next_point
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (E : Finset (pkgB2_Nonroot T))
    (r : pkgB2_Nonroot T) (hr : r ∉ E) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (xr : opus_dpo_s_PiExceptPair (Sum.inr (r, 0) : pkgB2_Coord T) (.inr (r, 1))
      (opus_dpo_s_check_sideNe T r) → ℤ) (z₀ z₁ : ℤ) :
    pkgB2_stateIntegrand MS B gap T hT J0 direction (insert r E) N I p
      (fun j => opus_dpo_s_check_frame T r xr z₀ z₁ (pkgB2_coordEnum T j)) =
      opus_dpo_s_check_weight MS B T hT direction E r N p (opus_dpo_s_check_frame T r xr 0 0) *
      opus_dpo_s_check_other MS B T hT direction E r N I p (opus_dpo_s_check_frame T r xr z₀ 0) *
      opus_dpo_s_check_other MS B T hT direction E r N I p (opus_dpo_s_check_frame T r xr z₁ 0) := by
  classical
  rw [opus_dpo_s_check_integrand_insert MS B T hT J0 gap direction hdir E r hr]
  change opus_dpo_s_check_weight MS B T hT direction E r N p (opus_dpo_s_check_frame T r xr z₀ z₁) *
    opus_dpo_s_check_other MS B T hT direction E r N I p (opus_dpo_s_check_frame T r xr z₀ z₁) *
    opus_dpo_s_check_other MS B T hT direction E r N I p
      (Function.update (opus_dpo_s_check_frame T r xr z₀ z₁) (.inr (r, 0))
        (opus_dpo_s_check_frame T r xr z₀ z₁ (.inr (r, 1)))) = _
  rw [opus_dpo_s_check_weight_frame MS B T hT direction hdir,
    opus_dpo_s_check_other_frame MS B T hT direction E r hr]
  simp only [opus_dpo_s_check_frame, opus_dpo_s_pairInsert_one, opus_dpo_s_pairInsert_update_zero]
  exact congrArg (fun z => _ * _ * z)
    (opus_dpo_s_check_other_frame MS B T hT direction E r hr N I p xr z₁ z₁)
noncomputable def opus_dpo_s_check_probability
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (N : ℕ) : ℝ :=
  independentPrimePoolProbability
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
    (pkgB2_goodPrimeEvent MS gap T hT N)

noncomputable def opus_dpo_s_check_primeMass
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (N : ℕ) (p : Fin (b * sl) → ℕ) : ℝ :=
  (opus_dpo_s_check_probability MS gap T hT N)⁻¹ *
    independentPrimePoolMass
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p *
    (if pkgB2_goodPrimeEvent MS gap T hT N p then 1 else 0)

noncomputable def opus_dpo_s_check_primeSupport
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K) (N : ℕ) :
    Finset (Fin (b * sl) → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico
    (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
    (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)

theorem opus_dpo_s_check_primeMass_zero
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (hp : p ∉ opus_dpo_s_check_primeSupport MS gap N) :
    opus_dpo_s_check_primeMass MS gap T hT N p = 0 := by
  have hraw := pkgB2_independentPrimePoolMass_zero_of_not_mem
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p hp
  simp [opus_dpo_s_check_primeMass, hraw]

theorem opus_dpo_s_check_primeMass_nonneg
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (N : ℕ) (p : Fin (b * sl) → ℕ) :
    0 ≤ opus_dpo_s_check_primeMass MS gap T hT N p := by
  classical
  have hpool (lo hi n : ℕ) : 0 ≤ primePoolLaw lo hi n := by
    unfold primePoolLaw
    split_ifs
    · apply div_nonneg (by positivity)
      unfold primePoolMass
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    · positivity
  have hraw (p : Fin (b * sl) → ℕ) :
      0 ≤ independentPrimePoolMass
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p :=
    Finset.prod_nonneg (fun _ _ => hpool _ _ _)
  have hprob : 0 ≤ opus_dpo_s_check_probability MS gap T hT N := by
    unfold opus_dpo_s_check_probability independentPrimePoolProbability
    apply tsum_nonneg
    intro p
    exact mul_nonneg (hraw p) (by split_ifs <;> norm_num)
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hprob) (hraw p))
    (by split_ifs <;> norm_num)

noncomputable def opus_dpo_s_check_prefactor
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) (N : ℕ) : ℝ :=
  ∑' p : Fin (b * sl) → ℕ, opus_dpo_s_check_primeMass MS gap T hT N p *
    ∑' x : pkgB2_Coord T → ℤ,
      (∏ c, pkgB2_baseCoordinateLaw MS B T J0 gap hT N p c (x c)) *
        opus_dpo_s_check_weight MS B T hT direction E r N p x

theorem opus_dpo_s_check_state_step
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) (hr : r ∉ E) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N)
    (hreg : ∀ p, pkgB2_goodPrimeEvent MS gap T hT N p → pkgB2_baseRegular MS B T J0 gap hT N p)
    (hA : 0 < pkgB2_translationLength MS T J0 gap r.1 N) :
    |pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 E N I| ^ 2 ≤
      opus_dpo_s_check_prefactor MS B gap T J0 hT direction E r N *
        pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 (insert r E) N I := by
  classical
  let α := pkgB2_Coord T
  let a₀ : α := .inr (r, 0)
  let a₁ : α := .inr (r, 1)
  let hne : a₁ ≠ a₀ := opus_dpo_s_check_sideNe T r
  let frame := opus_dpo_s_pairInsert a₀ a₁ hne
  let μ := opus_dpo_s_check_primeMass MS gap T hT N
  let law := pkgB2_baseCoordinateLaw MS B T J0 gap hT N
  let Current (p : Fin (b * sl) → ℕ) (x : α → ℤ) :=
    pkgB2_stateIntegrand MS B gap T hT J0 direction E N I p (fun j => x (pkgB2_coordEnum T j))
  let Weight := opus_dpo_s_check_weight MS B T hT direction E r N
  let Next (p : Fin (b * sl) → ℕ) (x : α → ℤ) :=
    pkgB2_stateIntegrand MS B gap T hT J0 direction (insert r E) N I p
      (fun j => x (pkgB2_coordEnum T j))
  let H₀ (p : Fin (b * sl) → ℕ) xr :=
    (if E = ∅ then ∏ k, (I k).e (pkgB2_repPrimeProject hT p k) else 1) *
      opus_dpo_s_check_rowProduct MS B T hT direction E N I p (.inr r) (frame xr 0 0)
  let Ω (p : Fin (b * sl) → ℕ) xr := Weight p (frame xr 0 0)
  let H (p : Fin (b * sl) → ℕ) xr z :=
    opus_dpo_s_check_other MS B T hT direction E r N I p (frame xr z 0)
  have h₀ : ∀ p xr, |H₀ p xr| ≤ Ω p xr := by
    intro p xr
    exact opus_dpo_s_check_selected_bound MS B T hT direction E r hr N p I (frame xr 0 0)
  have hΩ : ∀ p xr, 0 ≤ Ω p xr := fun p xr => (abs_nonneg _).trans (h₀ p xr)
  have hnorm : ∀ p, ∑' z, law p a₀ z = 1 := by
    intro p
    simpa [law, a₀, pkgB2_baseCoordinateLaw] using uniformIntegerIntervalLaw_tsum_one hA
  have hcs := opus_dpo_s_jointCoordinate_cauchy a₀ a₁ hne μ law
    (opus_dpo_s_check_primeSupport MS gap N) (fun p _ => pkgB2_baseWindow MS B T J0 gap hT N p)
    (opus_dpo_s_check_primeMass_zero MS gap T hT N)
    (fun p c z hz => pkgB2_baseCoordinateLaw_zero_outside MS B T J0 gap hT N p c z hz)
    (opus_dpo_s_check_primeMass_nonneg MS gap T hT N)
    (fun p c z => pkgB2_baseCoordinateLaw_nonneg MS B T J0 gap hT N p c z)
    (fun _ => rfl) hnorm H₀ Ω H hΩ h₀ Current Weight Next
    (fun p xr z₀ z₁ => opus_dpo_s_check_current_point MS B T hT J0 gap direction hdir E r hr N I p xr z₀ z₁)
    (fun p xr z₀ z₁ => opus_dpo_s_check_weight_frame MS B T hT direction hdir E r N p xr z₀ z₁)
    (fun p xr z₀ z₁ => opus_dpo_s_check_next_point MS B T hT J0 gap direction hdir E r hr N I p xr z₀ z₁)
  rw [opus_dpo_s_check_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 E N I hreg,
    opus_dpo_s_check_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 (insert r E) N I hreg]
  exact hcs
theorem opus_dpo_s_check_rowProduct_enum
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (t : pkgB2_BaseRow T) (f : ℤ → ℝ)
    (N : ℕ) (p : Fin (b * sl) → ℕ) (x : pkgB2_Coord T → ℤ) :
    opus_dpo_s_rowProduct (opus_dpo_s_check_c MS T hT N p)
      (opus_dpo_s_check_rho MS T hT direction N p) (pkgB2_activeRow T) E t f x =
      ∏ u ∈ (Finset.univ : Finset (Fin (Fintype.card (pkgB2_Occurrence T E)))).filter
        (fun u => (pkgB2_occurrenceEnum T E u).1 = t),
        f (pkgB2_stateRowValue MS T hT J0 gap direction E N p u
          (fun j => x (pkgB2_coordEnum T j))) := by
  classical
  let g : pkgB2_Occurrence T E → ℝ := fun o =>
    f (∑ a : pkgB2_Coord T,
      pkgB2_occurrenceCoefficientInt T
        (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
        direction E o a * x a)
  have henum :
      (∏ u, if (pkgB2_occurrenceEnum T E u).1 = t then g (pkgB2_occurrenceEnum T E u) else 1) =
      ∏ o : pkgB2_Occurrence T E, if o.1 = t then g o else 1 :=
    Fintype.prod_equiv (pkgB2_occurrenceEnum T E) _ _ (fun _ => rfl)
  have hfiber := opus_dpo_s_sigmaFiber_product (wholeFT := pkgB2_occurrenceFintype T E) t g
  rw [Finset.prod_filter] at hfiber
  symm
  rw [Finset.prod_filter]
  have hfirst :
      (∏ u : Fin (Fintype.card (pkgB2_Occurrence T E)),
        if (pkgB2_occurrenceEnum T E u).1 = t then
          f (pkgB2_stateRowValue MS T hT J0 gap direction E N p u
            (fun j => x (pkgB2_coordEnum T j))) else 1) =
      ∏ u, if (pkgB2_occurrenceEnum T E u).1 = t then g (pkgB2_occurrenceEnum T E u) else 1 := by
    apply Finset.prod_congr rfl
    intro u _
    rw [opus_dpo_s_check_rowValue]
  rw [hfirst, henum, hfiber]
  unfold opus_dpo_s_rowProduct
  apply Finset.prod_congr (by ext; simp)
  intro η _
  dsimp [g]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rfl

noncomputable def opus_dpo_s_check_selectedOccurrences (T : Fin b → CubeTemplate)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) :
    Finset (Fin (Fintype.card (pkgB2_Occurrence T E))) :=
  Finset.univ.filter (fun u => (pkgB2_occurrenceEnum T E u).1 = Sum.inr r)

theorem opus_dpo_s_check_weight_expansion
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (r : pkgB2_Nonroot T) (N : ℕ)
    (p : Fin (b * sl) → ℕ) (x : pkgB2_Coord T → ℤ) :
    opus_dpo_s_check_weight MS B T hT direction E r N p x =
      ∑ U ∈ (opus_dpo_s_check_selectedOccurrences T E r).powerset,
        ∏ u ∈ U, nu MS.core.parameters N B
          (pkgB2_stateRowValue MS T hT J0 gap direction E N p u
            (fun j => x (pkgB2_coordEnum T j))) := by
  unfold opus_dpo_s_check_weight
  rw [opus_dpo_s_check_rowProduct_enum MS T hT J0 gap direction E (.inr r)]
  simpa only [Finset.prod_empty, mul_one, Finset.powerset_empty, Finset.sum_singleton,
    Finset.card_empty, Nat.sub_zero, pow_zero, one_mul, Finset.union_empty,
    opus_dpo_s_check_selectedOccurrences] using
      pkgB2_signedProductExpansion
        (opus_dpo_s_check_selectedOccurrences T E r) ∅ (by simp)
        (fun u => nu MS.core.parameters N B
          (pkgB2_stateRowValue MS T hT J0 gap direction E N p u
            (fun j => x (pkgB2_coordEnum T j))))


end OpusDpoSCheck


/-! ### Cauchy–Schwarz elimination step: the part lemma -/

/-- `opus_dpo_average` in structured coordinates, when every good tuple is regular. -/
theorem opus_dpo_average_eq_coord {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (F : (Fin (b * sl) → ℕ) → (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) → ℝ)
    (hreg : ∀ p, pkgB2_goodPrimeEvent MS gap T hT N p →
      pkgB2_baseRegular MS B T J0 gap hT N p) :
    opus_dpo_average MS B gap T J0 hT N F =
      ∑' p : Fin (b * sl) → ℕ, opus_dpo_s_check_primeMass MS gap T hT N p *
        ∑' x : pkgB2_Coord T → ℤ,
          (∏ c, pkgB2_baseCoordinateLaw MS B T J0 gap hT N p c (x c)) *
            F p (fun j => x (pkgB2_coordEnum T j)) := by
  classical
  unfold opus_dpo_average
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  unfold opus_dpo_s_check_primeMass opus_dpo_s_check_probability
  by_cases hp : pkgB2_goodPrimeEvent MS gap T hT N p
  · simp only [hp, if_true, mul_one]
    rw [← mul_assoc]
    congr 1
    simp only [pkgB2_baseMass, hreg p hp, dite_true]
    let e : (pkgB2_Coord T → ℤ) ≃ (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :=
      Equiv.arrowCongr (pkgB2_coordEnum T).symm (Equiv.refl ℤ)
    calc
      _ = ∑' x : pkgB2_Coord T → ℤ,
          (∏ j, pkgB2_baseCoordinateLaw MS B T J0 gap hT N p (pkgB2_coordEnum T j)
            (x (pkgB2_coordEnum T j))) * F p (fun j => x (pkgB2_coordEnum T j)) :=
        (e.tsum_eq _).symm
      _ = _ := by
        apply tsum_congr
        intro x
        congr 1
        exact Fintype.prod_equiv (pkgB2_coordEnum T) _ _ (fun _ => rfl)
  · simp [hp]

theorem opus_dpo_prefactor_eq_check {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (s : pkgB2_Nonroot T) (N : ℕ)
    (hreg : ∀ p, pkgB2_goodPrimeEvent MS gap T hT N p →
      pkgB2_baseRegular MS B T J0 gap hT N p) :
    opus_dpo_prefactor MS B gap T J0 hT direction E s N =
      opus_dpo_s_check_prefactor MS B gap T J0 hT direction E s N := by
  classical
  unfold opus_dpo_prefactor opus_dpo_s_check_prefactor
  rw [opus_dpo_average_eq_coord MS B gap T J0 hT N _ hreg]
  apply tsum_congr
  intro p
  congr 1
  apply tsum_congr
  intro x
  congr 1
  unfold opus_dpo_s_check_weight
  rw [opus_dpo_s_check_rowProduct_enum MS T hT J0 gap direction E (.inr s)]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Proof of the part `opus_dpo_cs_step`. -/
theorem opus_dpo_cs_step_proof {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (s : pkgB2_Nonroot T) (hs : s ∉ E) :
    ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 E N I| ^ 2 ≤
        opus_dpo_prefactor MS B gap T J0 hT direction E s N *
          pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 (insert s E) N I := by
  have hAev : ∀ᶠ N : ℕ in atTop, 0 < pkgB2_translationLength MS T J0 gap s.1 N := by
    filter_upwards [pkgB2_translationLength_ge_blockScale_pow MS B T J0 gap hgap hJ0 s.1 1]
      with N hN
    have hV : 1 ≤ pkgB2_blockScale MS.core.parameters B N := by
      dsimp [pkgB2_blockScale]
      omega
    rw [pow_one] at hN
    exact lt_of_lt_of_le (by omega) hN
  filter_upwards [opus_dpo_regular_eventually MS B gap T J0 hgap hT hJ0, hAev]
    with N hreg hA I
  rw [opus_dpo_prefactor_eq_check MS B gap T J0 hT direction E s N hreg]
  convert opus_dpo_s_check_state_step MS B gap T J0 hgap hT hJ0 direction hdir k0 E s hs N I
    hreg hA

end

end Prediction
end HindmanSumsProducts
