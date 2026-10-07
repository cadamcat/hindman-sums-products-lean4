import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import Mathlib.Algebra.Polynomial.Roots

/-! Helper lemmas for the §4 proof package `Rows` (owned by its proof lane). -/

namespace HindmanSumsProducts

open scoped BigOperators Topology
open Filter FromArithmetic

private lemma rowPoly_ne_zero_of_some {m q : ℕ} (T : RowTemplate m q)
    (k : Fin m) (e : Fin q → ℕ) (he : T.entry k = some e) : T.poly k ≠ 0 := by
  simp [RowTemplate.poly, he]

private lemma rowPoly_mul_entry {m q : ℕ} (T : RowTemplate m q)
    (k : Fin m) (e : Fin q → ℕ) (he : T.entry k = some e) :
    T.poly k = MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) (1 : ℤ) := by
  simp [RowTemplate.poly, he]

private lemma parallel_of_all_minors_zero {m q : ℕ} (T U : RowTemplate m q)
    (hminor : ∀ j k, T.poly j * U.poly k - T.poly k * U.poly j = 0) :
    T.Parallel U := by
  classical
  have hentry : ∀ k, (T.entry k).isSome ↔ (U.entry k).isSome := by
    intro k
    constructor
    · intro hk
      by_contra hkU
      obtain ⟨e, he⟩ := (Option.isSome_iff_exists).mp hk
      obtain ⟨j, hjmem⟩ := U.support_nonempty
      have hj : (U.entry j).isSome := by simpa [RowTemplate.support] using hjmem
      obtain ⟨f, hf⟩ := (Option.isSome_iff_exists).mp hj
      have hprod : T.poly k * U.poly j ≠ 0 :=
        mul_ne_zero (rowPoly_ne_zero_of_some T k e he)
          (rowPoly_ne_zero_of_some U j f hf)
      have hkU0 : U.poly k = 0 := by
        cases h : U.entry k with
        | none => simp [RowTemplate.poly, h]
        | some f' => exact (hkU (by simp [h])).elim
      have hzero := hminor k j
      exact hprod (by simpa [hkU0] using hzero)
    · intro hk
      by_contra hkT
      obtain ⟨e, he⟩ := (Option.isSome_iff_exists).mp hk
      obtain ⟨j, hjmem⟩ := T.support_nonempty
      have hj : (T.entry j).isSome := by simpa [RowTemplate.support] using hjmem
      obtain ⟨f, hf⟩ := (Option.isSome_iff_exists).mp hj
      have hprod : U.poly k * T.poly j ≠ 0 :=
        mul_ne_zero (rowPoly_ne_zero_of_some U k e he)
          (rowPoly_ne_zero_of_some T j f hf)
      have hkT0 : T.poly k = 0 := by
        cases h : T.entry k with
        | none => simp [RowTemplate.poly, h]
        | some f' => exact (hkT (by simp [h])).elim
      have hzero := hminor j k
      exact hprod (by
        have hzero' : T.poly j * U.poly k = 0 := by simpa [hkT0] using hzero
        simpa [mul_comm] using hzero')
  have hsupport : T.support = U.support := by
    ext k
    simp [RowTemplate.support, hentry k]
  have hδ : ∃ δ : Fin q → ℤ, ∀ k e e', T.entry k = some e → U.entry k = some e' →
      ∀ i, (e' i : ℤ) = e i + δ i := by
    obtain ⟨k₀, hk₀mem⟩ := T.support_nonempty
    have hk₀ : (T.entry k₀).isSome := by simpa [RowTemplate.support] using hk₀mem
    obtain ⟨e₀, he₀⟩ := (Option.isSome_iff_exists).mp hk₀
    have hu₀ : (U.entry k₀).isSome := by
      have : k₀ ∈ U.support := by rw [← hsupport]; exact hk₀mem
      simpa [RowTemplate.support] using this
    obtain ⟨f₀, hf₀⟩ := (Option.isSome_iff_exists).mp hu₀
    refine ⟨fun i => (f₀ i : ℤ) - e₀ i, ?_⟩
    intro k e f he hf i
    have hkT : T.poly k₀ * U.poly k - T.poly k * U.poly k₀ = 0 := hminor k₀ k
    have hmon : T.poly k₀ * U.poly k = T.poly k * U.poly k₀ := sub_eq_zero.mp hkT
    rw [rowPoly_mul_entry T k₀ e₀ he₀, rowPoly_mul_entry U k f hf,
      rowPoly_mul_entry T k e he, rowPoly_mul_entry U k₀ f₀ hf₀] at hmon
    have hexp : Finsupp.equivFunOnFinite.symm e₀ + Finsupp.equivFunOnFinite.symm f =
        Finsupp.equivFunOnFinite.symm e + Finsupp.equivFunOnFinite.symm f₀ := by
      rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial] at hmon
      exact (MvPolynomial.monomial_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)) hmon
    have hcoords := congrArg Finsupp.equivFunOnFinite hexp
    have hcoords' : e₀ + f = e + f₀ := by
      ext i
      simpa [Finsupp.equivFunOnFinite] using congrFun hcoords i
    have hcast : (e₀ i : ℤ) + f i = e i + f₀ i := by
      exact_mod_cast congrFun hcoords' i
    change (f i : ℤ) = (e i : ℤ) + ((f₀ i : ℤ) - e₀ i)
    omega
  exact ⟨hsupport, hδ⟩

private noncomputable def rowSyzygy {m q : ℕ} (T : RowTemplate m q) (j k : Fin m) :
    Fin m → IntegerPolynomial q :=
  fun i => (Pi.single j (T.poly k) : Fin m → IntegerPolynomial q) i +
    (Pi.single k (-T.poly j) : Fin m → IntegerPolynomial q) i

private lemma rowSyzygy_response {m q : ℕ} (T U : RowTemplate m q)
    (j k : Fin m) (hjk : j ≠ k) :
    templateResponse U (rowSyzygy T j k) =
      U.poly j * T.poly k - U.poly k * T.poly j := by
  classical
  unfold templateResponse rowSyzygy
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [Fintype.sum_eq_single j]
  · rw [Fintype.sum_eq_single k]
    · simp [Pi.single_apply, mul_comm]
      ring
    · intro x hx
      simp [Pi.single_apply, hx]
  · intro x hx
    simp [Pi.single_apply, hx]

private lemma rowSyzygy_target_response {m q : ℕ} (T : RowTemplate m q)
    (j k : Fin m) (hjk : j ≠ k) : templateResponse T (rowSyzygy T j k) = 0 := by
  rw [rowSyzygy_response T T j k hjk]
  ring

private lemma exists_separating_minor {m q : ℕ} (T U : RowTemplate m q)
    (hpar : ¬ T.Parallel U) :
    ∃ j k, U.poly j * T.poly k - U.poly k * T.poly j ≠ 0 := by
  obtain ⟨j, k, h⟩ : ∃ j k, T.poly j * U.poly k - T.poly k * U.poly j ≠ 0 := by
    by_contra h
    apply hpar
    apply parallel_of_all_minors_zero T U
    intro j k
    by_contra hz
    exact h ⟨j, k, hz⟩
  refine ⟨j, k, ?_⟩
  intro hz
  apply h
  calc
    T.poly j * U.poly k - T.poly k * U.poly j =
        -(U.poly j * T.poly k - U.poly k * T.poly j) := by ring
    _ = 0 := by rw [hz]; simp

private lemma rowPolyVector_response_sum {m q r : ℕ} (T : RowTemplate m q)
    (others : Finset (Fin r)) (v : Fin r → Fin m → IntegerPolynomial q) :
    (∑ k, Polynomial.C (T.poly k) *
        (∑ i ∈ others, Polynomial.monomial i.val (v i k))) =
      ∑ i ∈ others, Polynomial.monomial i.val (templateResponse T (v i)) := by
  classical
  calc
    (∑ k, Polynomial.C (T.poly k) *
        (∑ i ∈ others, Polynomial.monomial i.val (v i k))) =
      ∑ k, ∑ i ∈ others, Polynomial.monomial i.val (T.poly k * v i k) := by
        simp_rw [Finset.mul_sum, Polynomial.C_mul_monomial]
    _ = ∑ i ∈ others, ∑ k, Polynomial.monomial i.val (T.poly k * v i k) := by
        rw [Finset.sum_comm]
    _ = ∑ i ∈ others, Polynomial.monomial i.val
        (∑ k, T.poly k * v i k) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (map_sum (Polynomial.monomial i.val)
            (fun k => T.poly k * v i k) Finset.univ).symm
    _ = ∑ i ∈ others, Polynomial.monomial i.val (templateResponse T (v i)) := rfl

theorem rowDirections_exists_kernel_separating {m q r : ℕ} (Sh : RowShape m q r)
    (target : Fin r) (hsep : ∀ I, I ≠ target → ¬ (Sh.row target).Parallel (Sh.row I)) :
    ∃ w : Fin m → IntegerPolynomial q,
      templateResponse (Sh.row target) w = 0 ∧
      ∀ I, I ≠ target → templateResponse (Sh.row I) w ≠ 0 := by
  classical
  let others : Finset (Fin r) := Finset.univ.erase target
  obtain ⟨j₀, hj₀mem⟩ := (Sh.row target).support_nonempty
  have hpairs : ∀ I, I ∈ others → ∃ j k,
      (Sh.row I).poly j * (Sh.row target).poly k -
        (Sh.row I).poly k * (Sh.row target).poly j ≠ 0 := by
    intro I hI
    have hIt : I ≠ target := (Finset.mem_erase.mp hI).1
    exact exists_separating_minor (Sh.row target) (Sh.row I) (hsep I hIt)
  let pair : Fin r → Fin m × Fin m := fun I =>
    if hI : I ∈ others then
      (Classical.choose (hpairs I hI),
        Classical.choose (Classical.choose_spec (hpairs I hI)))
    else (j₀, j₀)
  let syz : Fin r → Fin m → IntegerPolynomial q := fun I =>
    rowSyzygy (Sh.row target) (pair I).1 (pair I).2
  have hpairs_nonzero : ∀ I, I ∈ others →
      (Sh.row I).poly (pair I).1 * (Sh.row target).poly (pair I).2 -
        (Sh.row I).poly (pair I).2 * (Sh.row target).poly (pair I).1 ≠ 0 := by
    intro I hI
    simp [pair, hI]
    exact Classical.choose_spec (Classical.choose_spec (hpairs I hI))
  have hpair_ne : ∀ I, I ∈ others → (pair I).1 ≠ (pair I).2 := by
    intro I hI hEq
    have hzero := hpairs_nonzero I hI
    rw [hEq] at hzero
    simp at hzero
  have hresponse_nonzero : ∀ I, I ∈ others →
      templateResponse (Sh.row I) (syz I) ≠ 0 := by
    intro I hI
    rw [rowSyzygy_response (Sh.row target) (Sh.row I)
      (pair I).1 (pair I).2 (hpair_ne I hI)]
    exact hpairs_nonzero I hI
  let responsePoly : Fin r → Polynomial (IntegerPolynomial q) := fun I =>
    ∑ J ∈ others, Polynomial.monomial J.val (templateResponse (Sh.row I) (syz J))
  let F : Polynomial (IntegerPolynomial q) := ∏ I ∈ others, responsePoly I
  have hresponse_coeff : ∀ I, I ∈ others →
      (responsePoly I).coeff I.val = templateResponse (Sh.row I) (syz I) := by
    intro I hI
    dsimp [responsePoly]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single I]
    · simp [hI]
    · intro J hJ hJI
      have hval : J.val ≠ I.val := by
        intro hv
        exact hJI (Fin.ext hv)
      simp [hval]
    · intro hnot
      exact (hnot hI).elim
  have hresponsePoly_ne : ∀ I, I ∈ others → responsePoly I ≠ 0 := by
    intro I hI hzero
    have hcoeff_zero : (responsePoly I).coeff I.val = 0 := by rw [hzero]; simp
    rw [hresponse_coeff I hI] at hcoeff_zero
    exact (hresponse_nonzero I hI) hcoeff_zero
  have hF : F ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro I hI
    exact hresponsePoly_ne I hI
  have hcard : F.natDegree < Cardinal.mk (IntegerPolynomial q) := by
    exact (Cardinal.natCast_lt_aleph0 (n := F.natDegree)).trans_le
      (Cardinal.aleph0_le_mk (IntegerPolynomial q))
  obtain ⟨t, ht⟩ := F.exists_eval_ne_zero_of_natDegree_lt_card hF hcard
  let w : Fin m → IntegerPolynomial q := fun k =>
    (∑ I ∈ others, Polynomial.monomial I.val (syz I k)).eval t
  refine ⟨w, ?_, ?_⟩
  · have hpoly := rowPolyVector_response_sum (Sh.row target) others syz
    have hpoly_zero :
        (∑ I ∈ others, Polynomial.monomial I.val
          (templateResponse (Sh.row target) (syz I))) = 0 := by
      apply Finset.sum_eq_zero
      intro I hI
      have hzero : templateResponse (Sh.row target) (syz I) = 0 := by
        change templateResponse (Sh.row target)
          (rowSyzygy (Sh.row target) (pair I).1 (pair I).2) = 0
        exact rowSyzygy_target_response (Sh.row target) (pair I).1 (pair I).2
          (hpair_ne I hI)
      simp [hzero]
    calc
      templateResponse (Sh.row target) w =
          ((∑ k, Polynomial.C ((Sh.row target).poly k) *
            (∑ I ∈ others, Polynomial.monomial I.val (syz I k))).eval t) := by
              unfold templateResponse
              change (∑ k, (Sh.row target).poly k *
                  (∑ I ∈ others, Polynomial.monomial I.val (syz I k)).eval t) =
                (Polynomial.evalRingHom t) (∑ k, Polynomial.C ((Sh.row target).poly k) *
                  (∑ I ∈ others, Polynomial.monomial I.val (syz I k)))
              rw [map_sum]
              simp [Polynomial.coe_evalRingHom, Polynomial.eval_C_mul]
      _ = ((∑ I ∈ others, Polynomial.monomial I.val
            (templateResponse (Sh.row target) (syz I))).eval t) := by rw [hpoly]
      _ = 0 := by rw [hpoly_zero]; simp
  · intro I hIt
    have hIothers : I ∈ others := Finset.mem_erase.mpr ⟨hIt, Finset.mem_univ I⟩
    have hpoly := rowPolyVector_response_sum (Sh.row I) others syz
    have hIeval : (responsePoly I).eval t ≠ 0 := by
      intro hz
      apply ht
      have hevalprod : F.eval t = ∏ J ∈ others, (responsePoly J).eval t := by
        simp [F, Polynomial.eval_prod]
      rw [hevalprod]
      exact Finset.prod_eq_zero hIothers hz
    have hactual : templateResponse (Sh.row I) w = (responsePoly I).eval t := by
      calc
        templateResponse (Sh.row I) w =
            ((∑ k, Polynomial.C ((Sh.row I).poly k) *
              (∑ J ∈ others, Polynomial.monomial J.val (syz J k))).eval t) := by
                unfold templateResponse
                change (∑ k, (Sh.row I).poly k *
                    (∑ J ∈ others, Polynomial.monomial J.val (syz J k)).eval t) =
                  (Polynomial.evalRingHom t) (∑ k, Polynomial.C ((Sh.row I).poly k) *
                    (∑ J ∈ others, Polynomial.monomial J.val (syz J k)))
                rw [map_sum]
                simp [Polynomial.coe_evalRingHom, Polynomial.eval_C_mul]
        _ = (responsePoly I).eval t := by rw [hpoly]
    intro hzero
    rw [hactual] at hzero
    exact hIeval hzero

private lemma rowDirections_tests_nonzero {m q r : ℕ} (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (hdirs : dirs.Valid) :
    ∀ P ∈ dirs.tests, P ≠ 0 := by
  have hD : dirs.poly ≠ 0 := by
    unfold RowDirections.poly
    apply Finset.prod_ne_zero_iff.mpr
    intro R hR
    have hRstar : R ≠ Sh.star := (Finset.mem_erase.mp hR).1
    exact hdirs.2.1 R Sh.star hRstar (Ne.symm hRstar)
  intro P hP
  rcases Finset.mem_insert.mp hP with hEq | hrest
  · simpa [hEq] using hD
  · rcases Finset.mem_union.mp hrest with hresponse | hminor
    · exact (Finset.mem_filter.mp hresponse).2
    · exact (Finset.mem_filter.mp hminor).2

private lemma eventually_eq_after_one {α : Type*} {f g : ℕ → α}
    (h : ∀ N, 1 ≤ N → f N = g N) : f =ᶠ[atTop] g := by
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => h N hN⟩] with N hN
  exact hN

private lemma dominates_congr_eventually {f f' s s' : ℕ → ℝ}
    (hf : f =ᶠ[atTop] f') (hs : s =ᶠ[atTop] s')
    (h : OAI.MicrocellScale.Dominates f s) :
    OAI.MicrocellScale.Dominates f' s' := by
  intro C hC
  have heq : (fun N => f' N / (s' N) ^ C) =ᶠ[atTop]
      fun N => f N / (s N) ^ C :=
    (hf.and hs).mono fun N hN => by
      change f' N / (s' N) ^ C = f N / (s N) ^ C
      rw [← hN.1, ← hN.2]
  exact (Filter.tendsto_congr' heq).mpr (h C hC)

private lemma superPolynomialSmall_congr_eventually {e e' V : ℕ → ℝ}
    (he : e =ᶠ[atTop] e') (h : SuperPolynomialSmall e' V) :
    SuperPolynomialSmall e V := by
  intro C hC
  have heq : (fun N => e N * V N ^ C) =ᶠ[atTop]
      fun N => e' N * V N ^ C := he.mono fun N hN => by
        change e N * V N ^ C = e' N * V N ^ C
        rw [hN]
  exact (Filter.tendsto_congr' heq).mpr (h C hC)

private lemma tendsto_congr_eventually {f g : ℕ → ℝ}
    (hfg : f =ᶠ[atTop] g) {L : ℝ} (hg : Tendsto g atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := (Filter.tendsto_congr' hfg).mpr hg

private def zeroPrimePool : PrimePool where
  lower := 1
  upper := 2
  lower_pos := by norm_num
  lower_lt_upper := by norm_num
  lower_pow_two := ⟨0, by norm_num⟩
  upper_pow_two := ⟨1, by norm_num⟩
  consecutive_complete_intervals := ⟨1, by norm_num⟩

private lemma masterScaleCore_modulus_zero {K : ℕ} {Aset : Finset ℚ}
    (C : FromArithmetic.MasterScaleCore K Aset) : C.parameters.M 0 = 1 := by
  obtain ⟨e, he⟩ := C.modulus_power 0
  rw [he]
  simp

private def modifyParametersAtZero {K : ℕ} (P : OAI.SourceAdmissible.Parameters K)
    (hM0 : P.M 0 = 1) : OAI.SourceAdmissible.Parameters K :=
  { P with
    H := fun N l => if N = 0 then 1 else P.H N l
    Hpos := by
      intro N l
      by_cases hN : N = 0
      · simp [hN]
      · simpa [hN] using P.Hpos N l
    Hdiv := by
      intro N l
      by_cases hN : N = 0
      · subst N
        simpa [hM0]
      · simpa [hN] using P.Hdiv N l
    Hdom := by
      intro l
      have hH : (fun N => ((if N = 0 then 1 else P.H N l : ℕ) : ℝ)) =ᶠ[atTop]
          fun N => (P.H N l : ℝ) := by
        apply eventually_eq_after_one
        intro N hN
        have hN0 : N ≠ 0 := by omega
        simp [hN0]
      exact dominates_congr_eventually hH.symm Filter.EventuallyEq.rfl (P.Hdom l)
    Xdom := by
      intro l
      have hH : (fun N => ((if N = 0 then 1 else P.H N l : ℕ) : ℝ)) =ᶠ[atTop]
          fun N => (P.H N l : ℝ) := by
        apply eventually_eq_after_one
        intro N hN
        have hN0 : N ≠ 0 := by omega
        simp [hN0]
      exact dominates_congr_eventually Filter.EventuallyEq.rfl hH.symm (P.Xdom l) }

private noncomputable def modifyCoreAtZero {K : ℕ} {Aset : Finset ℚ}
    (C : FromArithmetic.MasterScaleCore K Aset) : FromArithmetic.MasterScaleCore K Aset :=
  { parameters := modifyParametersAtZero C.parameters (masterScaleCore_modulus_zero C)
    height_formula := by
      simpa [modifyParametersAtZero] using C.height_formula
    modulus_power := by
      simpa [modifyParametersAtZero] using C.modulus_power
    adding_pair_ratio := by
      simpa [modifyParametersAtZero] using C.adding_pair_ratio
    chain_coefficients := by
      simpa [modifyParametersAtZero] using C.chain_coefficients }

private def modifyPoolAtZero {K : ℕ} (pool : ℕ → Fin K → PrimePool) :
    ℕ → Fin K → PrimePool :=
  fun N l => if N = 0 then zeroPrimePool else pool N l

private noncomputable def modifyPrimeStageAtZero {K : ℕ} {Aset : Finset ℚ}
    {s : ℕ} {Dm : Finset (IntegerPolynomial s)}
    (C : FromArithmetic.MasterScaleCore K Aset)
    (P : FromArithmetic.MasterScalePrimeStage C s Dm) :
    FromArithmetic.MasterScalePrimeStage (modifyCoreAtZero C) s Dm := by
  let pool' := modifyPoolAtZero P.pool
  refine { P with
    pool := pool'
    pool_lower_dominates := ?_
    pool_harmonic_mass_dominates := ?_
    pool_residue_error := ?_
    actual_small_prime_exception := ?_
    zero_and_repeat_probability := ?_ }
  · intro l
    have heq : (fun N => ((pool' N l).lower : ℝ)) =ᶠ[atTop]
        fun N => ((P.pool N l).lower : ℝ) := by
      apply eventually_eq_after_one
      intro N hN
      simp [pool', modifyPoolAtZero, Nat.ne_of_gt (by omega : 0 < N)]
    exact dominates_congr_eventually heq.symm Filter.EventuallyEq.rfl
      (P.pool_lower_dominates l)
  · intro l
    have heq : (fun N => primePoolMass (pool' N l).lower (pool' N l).upper) =ᶠ[atTop]
        fun N => primePoolMass (P.pool N l).lower (P.pool N l).upper := by
      apply eventually_eq_after_one
      intro N hN
      simp [pool', modifyPoolAtZero, Nat.ne_of_gt (by omega : 0 < N)]
    exact dominates_congr_eventually heq.symm Filter.EventuallyEq.rfl
      (P.pool_harmonic_mass_dominates l)
  · intro l
    have heq : (fun N => finiteL1
        (primePoolResidueLaw (pool' N l).lower (pool' N l).upper
          (masterCRTModulus (N + 1) (P.e0 N)
            (masterScaleV (modifyCoreAtZero C).parameters N l)))
        (uniformUnitResidueLaw (masterCRTModulus (N + 1) (P.e0 N)
          (masterScaleV (modifyCoreAtZero C).parameters N l)))) =ᶠ[atTop]
        fun N => finiteL1
          (primePoolResidueLaw (P.pool N l).lower (P.pool N l).upper
            (masterCRTModulus (N + 1) (P.e0 N)
              (masterScaleV C.parameters N l)))
          (uniformUnitResidueLaw (masterCRTModulus (N + 1) (P.e0 N)
            (masterScaleV C.parameters N l))) := by
      apply eventually_eq_after_one
      intro N hN
      simp [pool', modifyPoolAtZero, Nat.ne_of_gt (by omega : 0 < N), modifyCoreAtZero,
        modifyParametersAtZero, masterScaleV] <;> rfl
    exact superPolynomialSmall_congr_eventually heq (P.pool_residue_error l)
  · intro l
    have heq : (fun N => independentPrimePoolProbability
        (fun _ : Fin s => (pool' N l).lower) (fun _ => (pool' N l).upper)
        (primeSmallDivisibilityEvent Dm (N + 1) (P.e0 N))) =ᶠ[atTop]
        fun N => independentPrimePoolProbability
          (fun _ : Fin s => (P.pool N l).lower) (fun _ => (P.pool N l).upper)
          (primeSmallDivisibilityEvent Dm (N + 1) (P.e0 N)) := by
      apply eventually_eq_after_one
      intro N hN
      simp [pool', modifyPoolAtZero, Nat.ne_of_gt (by omega : 0 < N)]
    exact tendsto_congr_eventually heq (P.actual_small_prime_exception l)
  · intro l
    have heq : (fun N => independentPrimePoolProbability
        (fun _ : Fin s => (pool' N l).lower) (fun _ => (pool' N l).upper)
        (polynomialZeroOrRepeated Dm)) =ᶠ[atTop]
        fun N => independentPrimePoolProbability
          (fun _ : Fin s => (P.pool N l).lower) (fun _ => (P.pool N l).upper)
          (polynomialZeroOrRepeated Dm) := by
      apply eventually_eq_after_one
      intro N hN
      simp [pool', modifyPoolAtZero, Nat.ne_of_gt (by omega : 0 < N)]
    exact superPolynomialSmall_congr_eventually heq
      (P.zero_and_repeat_probability l)

private noncomputable def modifyGapStageAtZeroOne {K : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial 1)}
    (C : FromArithmetic.MasterScaleCore K Aset)
    (P : FromArithmetic.MasterScalePrimeStage C 1 Dm)
    (G : FromArithmetic.MasterScaleGapStage C P) :
    FromArithmetic.MasterScaleGapStage (modifyCoreAtZero C) (modifyPrimeStageAtZero C P) := by
  let C' := modifyCoreAtZero C
  let P' := modifyPrimeStageAtZero C P
  have hM0 : C.parameters.M 0 = 1 := masterScaleCore_modulus_zero C
  have hH (l : Fin K) : (fun N => ((C'.parameters.H N l : ℕ) : ℝ)) =ᶠ[atTop]
      fun N => ((C.parameters.H N l : ℕ) : ℝ) := by
    apply eventually_eq_after_one
    intro N hN
    simp [C', modifyCoreAtZero, modifyParametersAtZero, Nat.ne_of_gt (by omega : 0 < N)]
  have hpool (l : Fin K) :
      (fun N => ((P'.pool N l).upper + masterScaleV C'.parameters N l : ℝ)) =ᶠ[atTop]
        fun N => ((P.pool N l).upper + masterScaleV C.parameters N l : ℝ) := by
    apply eventually_eq_after_one
    intro N hN
    simp [P', modifyPrimeStageAtZero, modifyPoolAtZero,
      C', modifyCoreAtZero, modifyParametersAtZero, Nat.ne_of_gt (by omega : 0 < N),
      masterScaleV]
  refine { G with
    gap_dominates_pool_and_bound := ?_
    gap_modulus_divides := ?_
    earlier_gaps_divide := ?_
    polynomial_values_divide_gap := ?_
    raw_cutoff_log_dominates_gap := ?_
    coefficient_divides_modulus := ?_
    valid_raw_cutoffs := ?_ }
  · intro l
    exact dominates_congr_eventually (hH l).symm (hpool l).symm
      (G.gap_dominates_pool_and_bound l)
  · intro N l
    by_cases hN : N = 0
    · subst N
      simp [C', modifyCoreAtZero, modifyParametersAtZero, hM0]
    · simpa [C', modifyCoreAtZero, modifyParametersAtZero, hN] using
        (G.gap_modulus_divides N l)
  · intro N i j hij
    by_cases hN : N = 0
    · subst N
      simp [C', modifyCoreAtZero, modifyParametersAtZero]
    · simpa [C', modifyCoreAtZero, modifyParametersAtZero, hN] using
        (G.earlier_gaps_divide N i j hij)
  · intro N l p Q hQ hp hQne
    by_cases hN : N = 0
    · subst N
      have hp0 := hp 0
      have hprime : Nat.Prime (p 0) := hp0.2.2
      have hlt : p 0 < 2 := by
        simpa [P', modifyPrimeStageAtZero, modifyPoolAtZero, zeroPrimePool] using hp0.2.1
      have hge : 2 ≤ p 0 := hprime.two_le
      omega
    · have hp' : ∀ i, (P.pool N l).lower ≤ p i ∧ p i < (P.pool N l).upper ∧ (p i).Prime := by
        intro i
        simpa [P', modifyPrimeStageAtZero, modifyPoolAtZero, hN] using hp i
      simpa [C', modifyCoreAtZero, modifyParametersAtZero, hN] using
        (G.polynomial_values_divide_gap N l p Q hQ hp' hQne)
  · intro l
    exact dominates_congr_eventually Filter.EventuallyEq.rfl (hH l).symm
      (G.raw_cutoff_log_dominates_gap l)
  · simpa [C', modifyCoreAtZero, modifyParametersAtZero, P', modifyPrimeStageAtZero,
      modifyPoolAtZero] using G.coefficient_divides_modulus
  · simpa [C', modifyCoreAtZero, modifyParametersAtZero, P', modifyPrimeStageAtZero,
      modifyPoolAtZero] using G.valid_raw_cutoffs

private noncomputable def modifyScalesAtZeroOne {K : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial 1)} (S : FromArithmetic.MasterScales K Aset 1 Dm) :
    FromArithmetic.MasterScales K Aset 1 Dm :=
  ⟨modifyCoreAtZero S.core, modifyPrimeStageAtZero S.core S.primeStage,
    modifyGapStageAtZeroOne S.core S.primeStage S.gapStage⟩

def zeroSlotRow0 : RowTemplate 2 0 where
  entry := fun k => if k = 0 then some (fun i => Fin.elim0 i) else none
  support_nonempty := by
    refine ⟨0, ?_⟩
    simp
  slots_disjoint := by
    intro k k' e e' hkk he he' i
    exact Fin.elim0 i

def zeroSlotRow1 : RowTemplate 2 0 where
  entry := fun k => if k = 1 then some (fun i => Fin.elim0 i) else none
  support_nonempty := by
    refine ⟨1, ?_⟩
    simp
  slots_disjoint := by
    intro k k' e e' hkk he he' i
    exact Fin.elim0 i

def zeroSlotRowShape : RowShape 2 0 2 where
  row := fun R => if R = 0 then zeroSlotRow0 else zeroSlotRow1
  star := 0
  nonparallel := by
    intro R I hRI
    fin_cases R
    · fin_cases I
      · exact (hRI rfl).elim
      · intro hpar
        have hs : zeroSlotRow0.support = zeroSlotRow1.support := hpar.1
        have hmem : (0 : Fin 2) ∈ zeroSlotRow0.support := by
          simp [RowTemplate.support, zeroSlotRow0]
        have hnot : (0 : Fin 2) ∉ zeroSlotRow1.support := by
          simp [RowTemplate.support, zeroSlotRow1]
        rw [hs] at hmem
        exact hnot hmem
    · fin_cases I
      · intro hpar
        have hs : zeroSlotRow1.support = zeroSlotRow0.support := hpar.1
        have hmem : (1 : Fin 2) ∈ zeroSlotRow1.support := by
          simp [RowTemplate.support, zeroSlotRow1]
        have hnot : (1 : Fin 2) ∉ zeroSlotRow0.support := by
          simp [RowTemplate.support, zeroSlotRow0]
        rw [hs] at hmem
        exact hnot hmem
      · exact (hRI rfl).elim

noncomputable def zeroSlotRowDirs : RowDirections zeroSlotRowShape where
  w := fun R k => if R = 1 ∧ k = 0 then 2 else 0
  w0 := fun k => if k = 1 then 1 else 0

private lemma zeroSlotExponent_eq_zero :
    Finsupp.equivFunOnFinite.symm (fun i : Fin 0 => Fin.elim0 i) = (0 : Fin 0 →₀ ℕ) := by
  ext i
  exact Fin.elim0 i

theorem zeroSlotRowDirs_valid : zeroSlotRowDirs.Valid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    fin_cases R <;> simp_all [zeroSlotRowDirs, zeroSlotRowShape, zeroSlotRow0,
      zeroSlotRow1, templateResponse, RowTemplate.poly]
  · intro R I hR hIR
    fin_cases R <;> fin_cases I <;> simp_all [zeroSlotRowDirs, zeroSlotRowShape,
      zeroSlotRow0, zeroSlotRow1, templateResponse, RowTemplate.poly]
  · simp [zeroSlotRowDirs, zeroSlotRowShape, zeroSlotRow0, zeroSlotRow1,
      templateResponse, RowTemplate.poly]
  · intro I hI
    fin_cases I <;> simp_all [zeroSlotRowDirs, zeroSlotRowShape, zeroSlotRow0,
      zeroSlotRow1, templateResponse, RowTemplate.poly]

theorem zeroSlotRowDirs_poly_eval :
    evalIntegerPolynomial zeroSlotRowDirs.poly (fun i => Fin.elim0 i) = 2 := by
  have hErase : Finset.univ.erase zeroSlotRowShape.star = {1} := by
    change Finset.univ.erase (0 : Fin 2) = {1}
    ext i
    fin_cases i <;> simp
  have hresp : RowDirections.targetResponse zeroSlotRowDirs 1 = (2 : IntegerPolynomial 0) := by
    simp [RowDirections.targetResponse, zeroSlotRowDirs, zeroSlotRowShape, zeroSlotRow0,
      zeroSlotRow1, templateResponse, RowTemplate.poly, zeroSlotExponent_eq_zero,
      MvPolynomial.monomial_zero']
  unfold RowDirections.poly
  rw [hErase]
  simp [hresp, evalIntegerPolynomial]

theorem zeroSlotRowDirs_tests_nonzero :
    ∀ P ∈ zeroSlotRowDirs.tests, P ≠ 0 := by
  exact rowDirections_tests_nonzero zeroSlotRowShape zeroSlotRowDirs zeroSlotRowDirs_valid

private lemma eval_empty_ne_zero {P : IntegerPolynomial 0} (hP : P ≠ 0) :
    evalIntegerPolynomial P (fun i => Fin.elim0 i) ≠ 0 := by
  intro hEval
  let f : Fin 0 → ℤ := fun i => Fin.elim0 i
  have hinj : Function.Injective (MvPolynomial.aeval (R := ℤ) (S₁ := ℤ) f) :=
    (MvPolynomial.aeval_injective_iff_of_isEmpty (R := ℤ) (S₁ := ℤ) (f := f)).2
      (by intro a b hab; simpa using hab)
  have hmap : MvPolynomial.aeval (R := ℤ) (S₁ := ℤ) f P =
      MvPolynomial.aeval (R := ℤ) (S₁ := ℤ) f 0 := by
    simpa [evalIntegerPolynomial, MvPolynomial.aeval_eq_eval, f] using hEval
  exact hP (hinj hmap)

private def zeroSlotBlock0 : OAI.SourceBlocks.Block 5 :=
  ⟨⟨3, by omega⟩, ⟨{⟨0, by omega⟩}, ⟨by simp, by
    intro j hj
    simp at hj
    subst j
    norm_num⟩⟩⟩

private def zeroSlotBlock1 : OAI.SourceBlocks.Block 5 :=
  ⟨⟨4, by omega⟩, ⟨{⟨1, by omega⟩}, ⟨by simp, by
    intro j hj
    simp at hj
    subst j
    norm_num⟩⟩⟩

private def zeroSlotBlocks (d : Fin 2) : OAI.SourceBlocks.Block 5 :=
  if d = 0 then zeroSlotBlock0 else zeroSlotBlock1

def zeroSlotChain : MasterChain 5 2 where
  gap := ⟨2, by omega⟩
  block := zeroSlotBlocks
  tails_before_gap := by
    intro d j hj
    fin_cases d <;> simp_all [zeroSlotBlocks, zeroSlotBlock0, zeroSlotBlock1] <;> omega
  tails_ordered := by
    intro u d hud j hj k hk
    fin_cases u <;> fin_cases d <;>
      simp_all [zeroSlotBlocks, zeroSlotBlock0, zeroSlotBlock1] <;> omega
  pivots_after_gap := by
    intro d
    fin_cases d <;> simp [zeroSlotBlocks, zeroSlotBlock0, zeroSlotBlock1] <;> omega
  pivots_ordered := by
    intro u d hud
    fin_cases u <;> fin_cases d <;>
      simp_all [zeroSlotBlocks, zeroSlotBlock0, zeroSlotBlock1] <;> omega

def zeroSlotEmbedding : Fin 0 ↪ Fin 1 where
  toFun := fun i => Fin.elim0 i
  inj' := by
    intro i j h
    exact Fin.elim0 i

noncomputable def zeroSlotMasterTests : Finset (IntegerPolynomial 1) :=
  zeroSlotRowDirs.tests.image (MvPolynomial.rename zeroSlotEmbedding)

theorem zeroSlotMasterTests_nonzero :
    ∀ P ∈ zeroSlotMasterTests, P ≠ 0 := by
  intro P hP hzero
  rcases Finset.mem_image.mp hP with ⟨Q, hQ, rfl⟩
  have hQzero : Q = 0 :=
    (MvPolynomial.rename_eq_zero_iff_of_injective Q zeroSlotEmbedding.injective).mp hzero
  exact (zeroSlotRowDirs_tests_nonzero Q hQ) hQzero

def zeroSlotAset : Finset ℚ := {1}

private lemma zeroSlotAset_pos : ∀ a ∈ zeroSlotAset, 0 < a := by
  intro a ha
  simp [zeroSlotAset] at ha
  simpa [ha]

noncomputable def zeroSlotBaseScales :
    FromArithmetic.MasterScales 5 zeroSlotAset 1 zeroSlotMasterTests :=
  Classical.choice (FromArithmetic.lem_master_scales 5 zeroSlotAset zeroSlotAset_pos
    1 zeroSlotMasterTests zeroSlotMasterTests_nonzero)

noncomputable def zeroSlotBadScales :
    FromArithmetic.MasterScales 5 zeroSlotAset 1 zeroSlotMasterTests :=
  modifyScalesAtZeroOne zeroSlotBaseScales

theorem zeroSlotTestsListed : TestsListed zeroSlotMasterTests zeroSlotEmbedding
    zeroSlotRowDirs.tests := by
  intro P hP
  exact Finset.mem_image.mpr ⟨P, hP, rfl⟩

def zeroSlotMultipliers : Fin 2 → ℚ := fun _ => 1

theorem zeroSlotMultipliers_valid : ∀ d, zeroSlotMultipliers d ∈ zeroSlotAset := by
  intro d
  simp [zeroSlotMultipliers, zeroSlotAset]

def zeroSlotGap : Fin 5 := ⟨2, by omega⟩

theorem roughPart_one_two : roughPart 1 (2 : ℤ) = 2 := by
  change (∏ p ∈ (Finset.range 3).filter (fun p : ℕ => p.Prime ∧ 1 < p),
    p ^ (Nat.factorization 2 p)) = 2
  have hfilter : (Finset.range 3).filter (fun p : ℕ => p.Prime ∧ 1 < p) = {2} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hp3, hp, hp1⟩
      interval_cases p <;> norm_num at *
    · rintro rfl
      norm_num
  have hfac : Nat.factorization 2 2 = 1 := by
    norm_num [Nat.Prime.factorization]
  rw [hfilter]
  simp [hfac]

theorem zeroSlotGood_but_modulus_not_dividing :
    GoodTuple zeroSlotBadScales zeroSlotGap 0 zeroSlotRowDirs.tests
      zeroSlotRowDirs.poly (fun i => Fin.elim0 i) ∧
    ¬ directionModulus zeroSlotBadScales 0 zeroSlotRowDirs.poly
        (fun i => Fin.elim0 i) ∣ zeroSlotBadScales.core.parameters.H 0 zeroSlotGap := by
  let p : Fin 0 → ℕ := fun i => Fin.elim0 i
  have hgood : GoodTuple zeroSlotBadScales zeroSlotGap 0 zeroSlotRowDirs.tests
      zeroSlotRowDirs.poly p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i j hij
      exact Fin.elim0 i
    · intro P hP
      have hpCast : (fun i : Fin 0 => (p i : ℤ)) = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      rw [hpCast]
      exact eval_empty_ne_zero (zeroSlotRowDirs_tests_nonzero P hP)
    · intro π hπ hπle
      have hπtwo := hπ.two_le
      omega
  have hM0 : zeroSlotBadScales.core.parameters.M 0 = 1 := by
    exact masterScaleCore_modulus_zero zeroSlotBadScales.core
  have hmod : directionModulus zeroSlotBadScales 0 zeroSlotRowDirs.poly p = 2 := by
    have hpCast : (fun i : Fin 0 => (p i : ℤ)) = (fun i => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    have hEval : evalIntegerPolynomial zeroSlotRowDirs.poly
        (fun i => (p i : ℤ)) = 2 := by rw [hpCast]; exact zeroSlotRowDirs_poly_eval
    unfold directionModulus
    rw [hM0, hEval]
    change 1 * roughPart 1 2 = 2
    rw [roughPart_one_two]
  have hH : zeroSlotBadScales.core.parameters.H 0 zeroSlotGap = 1 := by
    simp [zeroSlotBadScales, modifyScalesAtZeroOne, modifyCoreAtZero,
      modifyParametersAtZero]
  refine ⟨hgood, ?_⟩
  rw [hmod, hH]
  norm_num

theorem zeroSlot_integer_clause_counterexample :
    ∃ C : MasterChain 5 2, ∃ a : Fin 2 → ℚ,
      TestsListed zeroSlotMasterTests zeroSlotEmbedding zeroSlotRowDirs.tests ∧
      (∀ d, a d ∈ zeroSlotAset) ∧
      GoodTuple zeroSlotBadScales C.gap 0 zeroSlotRowDirs.tests zeroSlotRowDirs.poly
        (fun i => Fin.elim0 i) ∧
      ¬ directionModulus zeroSlotBadScales 0 zeroSlotRowDirs.poly
        (fun i => Fin.elim0 i) ∣ zeroSlotBadScales.core.parameters.H 0 C.gap := by
  refine ⟨zeroSlotChain, zeroSlotMultipliers, zeroSlotTestsListed,
    zeroSlotMultipliers_valid, ?_⟩
  simpa [zeroSlotChain, zeroSlotGap] using zeroSlotGood_but_modulus_not_dividing

end HindmanSumsProducts
