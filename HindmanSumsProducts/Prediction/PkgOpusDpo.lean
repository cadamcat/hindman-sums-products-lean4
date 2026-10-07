import HindmanSumsProducts.Prediction.PkgB2
import HindmanSumsProducts.Prediction.PkgD
import HindmanSumsProducts.Prediction.PkgB

/-!
# Lead helpers for `dual_products_orthogonal` (lane opus-dpo)

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

end

end Prediction
end HindmanSumsProducts
