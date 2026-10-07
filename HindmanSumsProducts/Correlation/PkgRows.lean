import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import Mathlib.Algebra.Polynomial.Roots

/-! Helper lemmas for §4 (part Rows). -/

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

private def constantPrimeTupleSupport {α : Type*} [Fintype α] [DecidableEq α]
    (lo hi : ℕ) :
    Finset (α → ℕ) :=
  Fintype.piFinset (fun _ : α => Finset.Ico lo hi)

private noncomputable def constantPrimePoolMass {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : ℕ)
    (p : α → ℕ) : ℝ :=
  ∏ i, primePoolLaw lo hi (p i)

private noncomputable def constantPrimePoolProbability {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : ℕ) (E : (α → ℕ) → Prop) [DecidablePred E] : ℝ :=
  ∑' p, constantPrimePoolMass lo hi p * if E p then 1 else 0

private lemma constantPrimePoolMass_zero_of_not_mem_support {α : Type*} [Fintype α]
    [DecidableEq α]
    (lo hi : ℕ) (p : α → ℕ)
    (hp : p ∉ constantPrimeTupleSupport lo hi) :
    constantPrimePoolMass lo hi p = 0 := by
  classical
  have hnotall : ¬ ∀ i : α, p i ∈ Finset.Ico lo hi := by
    intro hall
    apply hp
    simpa [constantPrimeTupleSupport] using hall
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  unfold constantPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private lemma constantPrimePoolMass_summable {α : Type*} [Fintype α] [DecidableEq α]
    (lo hi : ℕ) : Summable (constantPrimePoolMass (α := α) lo hi) := by
  apply summable_of_ne_finset_zero (s := constantPrimeTupleSupport (α := α) lo hi)
  intro p hp
  exact constantPrimePoolMass_zero_of_not_mem_support lo hi p hp

private lemma constantPrimePoolProbability_summable {α : Type*} [Fintype α] [DecidableEq α]
    (lo hi : ℕ) (E : (α → ℕ) → Prop) [DecidablePred E] :
    Summable (fun p => constantPrimePoolMass lo hi p * if E p then 1 else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := constantPrimeTupleSupport lo hi)
  intro p hp
  rw [constantPrimePoolMass_zero_of_not_mem_support lo hi p hp]
  simp

private lemma primePoolLaw_sum_interval {lo hi : ℕ}
    (hpos : 0 < primePoolMass lo hi) :
    (∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p) = 1 := by
  classical
  calc
    (∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p) =
        ∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
          (1 / (p : ℝ)) / primePoolMass lo hi := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_Ico.mp hp
      simp [primePoolLaw, hp', and_left_comm, and_assoc]
    _ = (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime, 1 / (p : ℝ)) /
          primePoolMass lo hi := by rw [Finset.sum_div]
    _ = 1 := by
      unfold primePoolMass
      exact div_self hpos.ne'

private lemma constantPrimePoolProbability_true {α : Type*} [Fintype α] [DecidableEq α]
    (lo hi : ℕ) (hpos : 0 < primePoolMass lo hi) :
    constantPrimePoolProbability (α := α) lo hi (fun _ => True) = 1 := by
  classical
  unfold constantPrimePoolProbability
  have hsum : (∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p) = 1 :=
    primePoolLaw_sum_interval hpos
  have hsupportSum :
      (∑' p : α → ℕ, constantPrimePoolMass lo hi p) =
        Finset.sum (constantPrimeTupleSupport (α := α) lo hi)
          (fun p : α → ℕ => constantPrimePoolMass (α := α) lo hi p) := by
    letI : DecidableEq (α → ℕ) := Classical.decEq (α → ℕ)
    apply tsum_eq_sum
      (s := (constantPrimeTupleSupport (α := α) lo hi : Finset (α → ℕ)))
    intro p hp
    exact constantPrimePoolMass_zero_of_not_mem_support lo hi p hp
  calc
    (∑' p : α → ℕ, constantPrimePoolMass lo hi p * if True then 1 else 0) =
      ∑ p ∈ constantPrimeTupleSupport lo hi, constantPrimePoolMass lo hi p := by
        simp only [if_true, mul_one]
        exact hsupportSum
    _ = ∏ _i : α, ∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p := by
      simp only [constantPrimeTupleSupport, constantPrimePoolMass]
      exact (Finset.prod_univ_sum (fun _i : α => Finset.Ico lo hi)
        (fun _i p => primePoolLaw lo hi p)).symm
    _ = 1 := by simp [hsum]

private lemma constantPrimePoolProbability_cylinder {q s : ℕ}
    (ι : Fin q ↪ Fin s) (lo hi : ℕ)
    (hpos : 0 < primePoolMass lo hi)
    (E : (Fin q → ℕ) → Prop) [DecidablePred E] :
    constantPrimePoolProbability lo hi E =
      constantPrimePoolProbability lo hi (fun p => E (fun i => p (ι i))) := by
  classical
  let extra := {j : Fin s // j ∉ Set.range ι}
  let eRange : Fin q ≃ {j : Fin s // j ∈ Set.range ι} :=
    { toFun := fun i => ⟨ι i, ⟨i, rfl⟩⟩
      invFun := fun j => Classical.choose j.2
      left_inv := by
        intro i
        apply ι.injective
        exact Classical.choose_spec (show ∃ k, ι k = ι i from ⟨i, rfl⟩)
      right_inv := by
        intro j
        apply Subtype.ext
        exact (Classical.choose_spec j.2) }
  let eIndex : Fin q ⊕ extra ≃ Fin s :=
    (Equiv.sumCongr eRange (Equiv.refl extra)).trans
      (Equiv.Set.sumCompl (Set.range (ι : Fin q → Fin s)))
  let eTuple : (Fin q → ℕ) × (extra → ℕ) ≃ (Fin s → ℕ) :=
    (Equiv.sumArrowEquivProdArrow (Fin q) extra ℕ).symm.trans
      (Equiv.piCongrLeft (fun _ : Fin s => ℕ) eIndex)
  have heIndexL (i : Fin q) : eIndex (Sum.inl i) = ι i := by
    change Equiv.Set.sumCompl (Set.range (ι : Fin q → Fin s))
      (Sum.inl (eRange i)) = ι i
    exact Equiv.Set.sumCompl_apply_inl _ _
  have heIndexR (j : extra) : eIndex (Sum.inr j) = j.1 := by
    change Equiv.Set.sumCompl (Set.range (ι : Fin q → Fin s)) (Sum.inr j) = j.1
    exact Equiv.Set.sumCompl_apply_inr _ _
  have hcoordL (x : Fin q → ℕ) (y : extra → ℕ) (i : Fin q) :
      eTuple (x, y) (ι i) = x i := by
    have hi : eIndex.symm (ι i) = Sum.inl i := by
      apply eIndex.injective
      calc
        eIndex (eIndex.symm (ι i)) = ι i := eIndex.apply_symm_apply _
        _ = eIndex (Sum.inl i) := (heIndexL i).symm
    simp [eTuple, Equiv.piCongrLeft, hi]
  have hcoordR (x : Fin q → ℕ) (y : extra → ℕ) (j : extra) :
      eTuple (x, y) j.1 = y j := by
    have hj : eIndex.symm j.1 = Sum.inr j := by
      apply eIndex.injective
      calc
        eIndex (eIndex.symm j.1) = j.1 := eIndex.apply_symm_apply _
        _ = eIndex (Sum.inr j) := (heIndexR j).symm
    simp [eTuple, Equiv.piCongrLeft, hj]
  have hmass (x : Fin q → ℕ) (y : extra → ℕ) :
      constantPrimePoolMass lo hi (eTuple (x, y)) =
        constantPrimePoolMass lo hi x * constantPrimePoolMass lo hi y := by
    unfold constantPrimePoolMass
    rw [← Fintype.prod_equiv eIndex
      (fun k : Fin q ⊕ extra => primePoolLaw lo hi (eTuple (x, y) (eIndex k)))
      (fun k : Fin s => primePoolLaw lo hi (eTuple (x, y) k)) (fun _ => rfl)]
    rw [Fintype.prod_sum_type]
    simp_rw [heIndexL, heIndexR, hcoordL, hcoordR]
  have hextraTotal :
      ∑' y : extra → ℕ, constantPrimePoolMass lo hi y = 1 :=
    by simpa [constantPrimePoolProbability] using
      (constantPrimePoolProbability_true (α := extra) lo hi hpos)
  have hqsum := constantPrimePoolProbability_summable lo hi E
  have hextrasum := constantPrimePoolMass_summable (α := extra) lo hi
  have hprodSum : Summable (fun z : (Fin q → ℕ) × (extra → ℕ) =>
      constantPrimePoolMass lo hi z.1 * constantPrimePoolMass lo hi z.2 *
          (if E z.1 then 1 else 0)) := by
    apply summable_of_ne_finset_zero
      (s := (constantPrimeTupleSupport lo hi).product
        (constantPrimeTupleSupport lo hi))
    intro z hz
    have hnot : z.1 ∉ constantPrimeTupleSupport lo hi ∨
        z.2 ∉ constantPrimeTupleSupport lo hi := by
      by_contra h
      push_neg at h
      exact hz (Finset.mem_product.mpr h)
    rcases hnot with hx | hy
    · rw [constantPrimePoolMass_zero_of_not_mem_support lo hi z.1 hx]
      simp
    · rw [constantPrimePoolMass_zero_of_not_mem_support lo hi z.2 hy]
      simp
  have hPair :
      (∑' z : (Fin q → ℕ) × (extra → ℕ),
        constantPrimePoolMass lo hi z.1 * constantPrimePoolMass lo hi z.2 *
          (if E z.1 then 1 else 0)) = constantPrimePoolProbability lo hi E := by
    rw [hprodSum.tsum_prod]
    have hinner (x : Fin q → ℕ) :
        (∑' y : extra → ℕ,
          constantPrimePoolMass lo hi x * constantPrimePoolMass lo hi y *
            (if E x then 1 else 0)) =
          (constantPrimePoolMass lo hi x * (if E x then 1 else 0)) *
            ∑' y : extra → ℕ, constantPrimePoolMass lo hi y := by
      calc
        _ = ∑' y : extra → ℕ,
            (constantPrimePoolMass lo hi x * (if E x then 1 else 0)) *
              constantPrimePoolMass lo hi y := by
                apply tsum_congr
                intro y
                ring
        _ = _ := tsum_mul_left
    rw [show (∑' x : Fin q → ℕ,
          ∑' y : extra → ℕ,
            constantPrimePoolMass lo hi x * constantPrimePoolMass lo hi y *
              (if E x then 1 else 0)) =
        ∑' x : Fin q → ℕ,
          (constantPrimePoolMass lo hi x * (if E x then 1 else 0)) *
            ∑' y : extra → ℕ, constantPrimePoolMass lo hi y by
          apply tsum_congr
          exact hinner]
    rw [hextraTotal]
    simp [constantPrimePoolProbability]
  have hFull :
      constantPrimePoolProbability lo hi (fun p : Fin s → ℕ => E (fun i => p (ι i))) =
        ∑' z : (Fin q → ℕ) × (extra → ℕ),
          constantPrimePoolMass lo hi z.1 * constantPrimePoolMass lo hi z.2 *
            (if E z.1 then 1 else 0) := by
    unfold constantPrimePoolProbability
    rw [← (eTuple.symm).tsum_eq]
    apply tsum_congr
    intro z
    have hz : eTuple ((eTuple.symm z).1, (eTuple.symm z).2) = z := by
      simpa using eTuple.apply_symm_apply z
    rw [← hz]
    simp only [Equiv.symm_apply_apply]
    rw [hmass]
    simp [hcoordL]
  exact hPair.symm.trans hFull.symm

private lemma primePoolMass_pos_of_pool (P : PrimePool) (hlo : 2 ≤ P.lower) :
    0 < primePoolMass P.lower P.upper := by
  obtain ⟨k, hk⟩ := P.consecutive_complete_intervals
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp [hk0] at hk
    have hlt := P.lower_lt_upper
    omega
  have hpow : 2 ≤ 2 ^ k := by
    cases k with
    | zero => omega
    | succ k =>
      rw [Nat.pow_succ]
      have hp : 0 < 2 ^ k := Nat.pow_pos (by omega)
      nlinarith
  have hupper : 2 * P.lower ≤ P.upper := by
    rw [hk]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left P.lower hpow
  obtain ⟨p, hp, hlow, hpupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul P.lower (by omega)
  have h2not : ¬ Nat.Prime (2 * P.lower) :=
    Nat.not_prime_mul (by norm_num) (by omega)
  have hpstrict : p < 2 * P.lower := by
    by_contra h
    have hpEq : p = 2 * P.lower := by omega
    exact h2not (hpEq ▸ hp)
  have hmem : p ∈ (Finset.Ico P.lower P.upper).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hlow.le, hpstrict.trans_le hupper⟩, hp⟩
  unfold primePoolMass
  have hle := Finset.single_le_sum (f := fun q : ℕ => 1 / (q : ℝ))
    (fun q hq => by positivity) hmem
  have hpPos : 0 < (1 / (p : ℝ)) := one_div_pos.mpr (by exact_mod_cast hp.pos)
  linarith

private lemma exists_prime_in_pool (P : PrimePool) (hlo : 2 ≤ P.lower) :
    ∃ p, P.lower ≤ p ∧ p < P.upper ∧ p.Prime := by
  obtain ⟨k, hk⟩ := P.consecutive_complete_intervals
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp [hk0] at hk
    have hlt := P.lower_lt_upper
    omega
  have hpow : 2 ≤ 2 ^ k := by
    cases k with
    | zero => omega
    | succ k =>
      rw [Nat.pow_succ]
      have hp : 0 < 2 ^ k := Nat.pow_pos (by omega)
      nlinarith
  have hupper : 2 * P.lower ≤ P.upper := by
    rw [hk]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left P.lower hpow
  obtain ⟨p, hp, hlow, hpupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul P.lower (by omega)
  have h2not : ¬ Nat.Prime (2 * P.lower) :=
    Nat.not_prime_mul (by norm_num) (by omega)
  have hpstrict : p < 2 * P.lower := by
    by_contra h
    have hpEq : p = 2 * P.lower := by omega
    exact h2not (hpEq ▸ hp)
  exact ⟨p, hlow.le, hpstrict.trans_le hupper, hp⟩

private lemma eventually_pool_lower_ge_two {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) :
    ∀ᶠ N in atTop, 2 ≤ (S.primeStage.pool N l).lower := by
  have hdom := S.primeStage.pool_lower_dominates l (1 : ℝ) (by norm_num)
  have hlarge := hdom.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlarge] with N hN
  have hV : 1 ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
    have hNat : 1 ≤ FromArithmetic.masterScaleV S.core.parameters N l := by
      unfold FromArithmetic.masterScaleV
      omega
    exact_mod_cast hNat
  have hN' : 2 ≤ ((S.primeStage.pool N l).lower : ℝ) /
      (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
    simpa [Real.rpow_one] using hN
  have hreal : (2 : ℝ) ≤ ((S.primeStage.pool N l).lower : ℝ) := by
    have hnonneg : 0 ≤ ((S.primeStage.pool N l).lower : ℝ) := Nat.cast_nonneg _
    calc
      2 ≤ ((S.primeStage.pool N l).lower : ℝ) /
          (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := hN'
      _ ≤ ((S.primeStage.pool N l).lower : ℝ) := div_le_self hnonneg hV
  exact_mod_cast hreal

private lemma eventually_pool_mass_pos {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) :
    ∀ᶠ N in atTop, 0 < primePoolMass (S.primeStage.pool N l).lower
      (S.primeStage.pool N l).upper := by
  filter_upwards [eventually_pool_lower_ge_two S l] with N hN
  exact primePoolMass_pos_of_pool (S.primeStage.pool N l) hN

private def rowPrimeTupleSupport {m : ℕ} (lo hi : Fin m → ℕ) :
    Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

private lemma rowPrimeMass_zero_of_not_mem_support {m : ℕ}
    (lo hi : Fin m → ℕ) (p : Fin m → ℕ)
    (hp : p ∉ rowPrimeTupleSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnot : ¬ ∀ i, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hp
    exact Fintype.mem_piFinset.mpr hall
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩)).elim
  · rfl

private lemma rowPrimeMass_summable {m : ℕ} (lo hi : Fin m → ℕ) :
    Summable (independentPrimePoolMass lo hi) := by
  apply summable_of_ne_finset_zero (s := rowPrimeTupleSupport lo hi)
  intro p hp
  exact rowPrimeMass_zero_of_not_mem_support lo hi p hp

private lemma rowPrimeMass_nonneg {m : ℕ} (lo hi : Fin m → ℕ) (p : Fin m → ℕ) :
    0 ≤ independentPrimePoolMass lo hi p := by
  unfold independentPrimePoolMass
  apply Finset.prod_nonneg
  intro i hi
  unfold primePoolLaw
  split_ifs with h
  · unfold primePoolMass
    apply div_nonneg
    · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    · apply Finset.sum_nonneg
      intro p hp
      exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · simp

private lemma rowPrimeMass_nonzero_implies_pool {m : ℕ}
    (lo hi : Fin m → ℕ) (p : Fin m → ℕ)
    (hmass : independentPrimePoolMass lo hi p ≠ 0) :
    ∀ i, lo i ≤ p i ∧ p i < hi i ∧ (p i).Prime := by
  intro i
  by_contra h
  have hz : primePoolLaw (lo i) (hi i) (p i) = 0 := by
    by_cases hc : lo i ≤ p i ∧ p i < hi i ∧ (p i).Prime
    · exact (h hc).elim
    · simp [primePoolLaw, hc]
  apply hmass
  unfold independentPrimePoolMass
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

private lemma rowPrimeProbability_summable {m : ℕ}
    (lo hi : Fin m → ℕ) (E : (Fin m → ℕ) → Prop) [DecidablePred E] :
    Summable (fun p => independentPrimePoolMass lo hi p * if E p then 1 else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := rowPrimeTupleSupport lo hi)
  intro p hp
  rw [rowPrimeMass_zero_of_not_mem_support lo hi p hp]
  simp

private lemma rowPrimeProbability_nonneg {m : ℕ}
    (lo hi : Fin m → ℕ) (E : (Fin m → ℕ) → Prop) :
    0 ≤ independentPrimePoolProbability lo hi E := by
  classical
  letI : DecidablePred E := fun p => Classical.propDecidable (E p)
  unfold independentPrimePoolProbability
  apply tsum_nonneg
  intro p
  exact mul_nonneg (rowPrimeMass_nonneg lo hi p) (by split_ifs <;> positivity)

private lemma rowPrimeProbability_mono_of_support {m : ℕ}
    (lo hi : Fin m → ℕ) (E F : (Fin m → ℕ) → Prop)
    (hEF : ∀ p, independentPrimePoolMass lo hi p ≠ 0 → E p → F p) :
    independentPrimePoolProbability lo hi E ≤ independentPrimePoolProbability lo hi F := by
  classical
  letI : DecidablePred E := fun p => Classical.propDecidable (E p)
  letI : DecidablePred F := fun p => Classical.propDecidable (F p)
  have hE := rowPrimeProbability_summable lo hi E
  have hF := rowPrimeProbability_summable lo hi F
  unfold independentPrimePoolProbability
  apply hE.tsum_le_tsum ?_ hF
  intro p
  by_cases hmass : independentPrimePoolMass lo hi p = 0
  · simp [hmass]
  by_cases hE' : E p
  · have hF' := hEF p hmass hE'
    simp [hE', hF']
  · by_cases hF' : F p
    · simpa [hE', hF'] using rowPrimeMass_nonneg lo hi p
    · simp [hE', hF']

private lemma rowPrimeProbability_union_le {m : ℕ}
    (lo hi : Fin m → ℕ) (E F : (Fin m → ℕ) → Prop) :
    independentPrimePoolProbability lo hi (fun p => E p ∨ F p) ≤
      independentPrimePoolProbability lo hi E + independentPrimePoolProbability lo hi F := by
  classical
  letI : DecidablePred E := fun p => Classical.propDecidable (E p)
  letI : DecidablePred F := fun p => Classical.propDecidable (F p)
  letI : DecidablePred (fun p => E p ∨ F p) := fun p => Classical.propDecidable (E p ∨ F p)
  have hE := rowPrimeProbability_summable lo hi E
  have hF := rowPrimeProbability_summable lo hi F
  have hU := rowPrimeProbability_summable lo hi (fun p => E p ∨ F p)
  unfold independentPrimePoolProbability
  calc
    (∑' p, independentPrimePoolMass lo hi p * if E p ∨ F p then 1 else 0) ≤
        ∑' p, ((independentPrimePoolMass lo hi p * if E p then 1 else 0) +
          (independentPrimePoolMass lo hi p * if F p then 1 else 0)) := by
      apply hU.tsum_le_tsum ?_ (hE.add hF)
      intro p
      by_cases hE' : E p
      · by_cases hF' : F p
        · have hm := rowPrimeMass_nonneg lo hi p
          simp [hE', hF']
          linarith
        · simp [hE', hF']
      · by_cases hF' : F p <;> simp [hE', hF']
    _ = (∑' p, independentPrimePoolMass lo hi p * if E p then 1 else 0) +
        ∑' p, independentPrimePoolMass lo hi p * if F p then 1 else 0 := hE.tsum_add hF

private lemma rowPrimeProbability_cylinder {q s : ℕ}
    (ι : Fin q ↪ Fin s) (lo hi : ℕ) (hpos : 0 < primePoolMass lo hi)
    (E : (Fin q → ℕ) → Prop) [DecidablePred E] :
    independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi) E =
      independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi)
        (fun p => E (fun i => p (ι i))) := by
  classical
  have h := constantPrimePoolProbability_cylinder ι lo hi hpos E
  simpa [constantPrimePoolProbability, constantPrimePoolMass,
    independentPrimePoolProbability, independentPrimePoolMass] using h

private lemma roughPart_dvd_natAbs {w : ℕ} {z : ℤ} (hz : z ≠ 0) :
    roughPart w z ∣ z.natAbs := by
  let n := z.natAbs
  let S := (Finset.range (n + 1)).filter (fun p : ℕ => p.Prime ∧ w < p)
  let T := n.factorization.support.filter (fun p : ℕ => w < p)
  have hTsubS : T ⊆ S := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hwp⟩
    have hpFactors : p ∈ n.primeFactors := by simpa [Nat.support_factorization] using hpSupport
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
    have hpLe : p ≤ n := Nat.le_of_mem_primeFactors hpFactors
    simp [S, Finset.mem_filter, Finset.mem_range, hpLe, hpPrime, hwp]
  have hone : ∀ p ∈ S \ T, p ^ n.factorization p = 1 := by
    intro p hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpS, hpNotT⟩
    have hpS' := (Finset.mem_filter.mp hpS).2
    have hpNotSupport : p ∉ n.factorization.support := by
      intro hmem
      apply hpNotT
      exact Finset.mem_filter.mpr ⟨hmem, hpS'.2⟩
    have hfac : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hpNotSupport
    simp [hfac]
  have hrough : roughPart w z = ∏ p ∈ T, p ^ n.factorization p := by
    unfold roughPart
    dsimp [S, T, n]
    calc
      _ = ∏ p ∈ S, p ^ n.factorization p := rfl
      _ = ∏ p ∈ T, p ^ n.factorization p :=
        (Finset.prod_subset_one_on_sdiff hTsubS hone (fun _ _ => rfl)).symm
  have hn : n ≠ 0 := by
    dsimp [n]
    exact (Int.natAbs_pos.mpr hz).ne'
  have hdiv : (∏ p ∈ T, p ^ n.factorization p) ∣ n := by
    have hsub : T ⊆ n.factorization.support := Finset.filter_subset _ _
    have hprod := Finset.prod_dvd_prod_of_subset T n.factorization.support
      (fun p => p ^ n.factorization p) hsub
    have hself : (∏ p ∈ n.factorization.support, p ^ n.factorization p) = n := by
      simpa [Finsupp.prod] using (Nat.prod_factorization_pow_eq_self hn)
    rw [hself] at hprod
    exact hprod
  rw [hrough]
  exact hdiv

private lemma roughPart_pos (w : ℕ) (z : ℤ) : 0 < roughPart w z := by
  unfold roughPart
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp |>.2.1)) _

private lemma roughPart_covers_divisor {w e : ℕ} (he : 1 ≤ e) {D d : ℤ}
    (hD : D ≠ 0) (hd : d ≠ 0) (hdiv : d ∣ D)
    (hsmall : ∀ p, p.Prime → p ≤ w → ¬ (((p ^ e : ℕ) : ℤ) ∣ D)) :
    d.natAbs ∣ (primorial w) ^ (e - 1) * roughPart w D := by
  let n := D.natAbs
  let r := d.natAbs
  let W := primorial w
  let target := W ^ (e - 1) * roughPart w D
  have hn : n ≠ 0 := by dsimp [n]; exact (Int.natAbs_pos.mpr hD).ne'
  have hr : r ≠ 0 := by dsimp [r]; exact (Int.natAbs_pos.mpr hd).ne'
  have hroughPos : 0 < roughPart w D := roughPart_pos w D
  have hWpos : 0 < W := by
    dsimp [W]
    exact primorial_pos w
  have htarget : target ≠ 0 := by
    dsimp [target, W]
    positivity
  have hnatDvd : r ∣ n := by
    exact Int.natAbs_dvd_natAbs.mpr hdiv
  have hfacD : r.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hr hn).2 hnatDvd
  have hfacTarget (p : ℕ) : target.factorization p =
      (W ^ (e - 1)).factorization p + (roughPart w D).factorization p := by
    dsimp [target]
    rw [Nat.factorization_mul (pow_ne_zero _ hWpos.ne') hroughPos.ne']
    rfl
  have hfacLE : r.factorization ≤ target.factorization := by
    intro p
    by_cases hp : p.Prime
    · by_cases hpw : p ≤ w
      · have hno : ¬ p ^ e ∣ n := by
          intro hpow
          apply hsmall p hp hpw
          exact Int.natCast_dvd.mpr hpow
        have hfacSmall : n.factorization p < e := by
          by_contra hge
          apply hno
          exact hp.pow_dvd_iff_le_factorization hn |>.2 (by omega)
        have hWdiv : p ∣ W := hp.dvd_primorial_iff.mpr hpw
        have hWfac : W.factorization p = 1 :=
          Nat.factorization_eq_one_of_squarefree (squarefree_primorial w) hp hWdiv
        have hfacPow : (W ^ (e - 1)).factorization p = e - 1 := by
          simp [Nat.factorization_pow, hWfac]
        rw [hfacTarget, hfacPow]
        exact le_trans (hfacD p) (by omega)
      · have hWnot : ¬ p ∣ W := by
          intro hdivW
          exact hpw (hp.dvd_primorial_iff.mp hdivW)
        have hWfac : W.factorization p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd hWnot
        by_cases hfacZero : n.factorization p = 0
        · rw [hfacTarget]
          have hfacRzero : r.factorization p = 0 := by
            exact le_antisymm (by simpa [hfacZero] using hfacD p) (Nat.zero_le _)
          simp [hfacRzero, Nat.factorization_pow, hWfac]
        · have hpD : p ∣ n := by
            exact hp.dvd_iff_one_le_factorization hn |>.2 (Nat.pos_of_ne_zero hfacZero)
          have hpLe : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpD
          have hpMem : p ∈ (Finset.range (n + 1)).filter (fun x : ℕ => x.Prime ∧ w < x) := by
            simp [Finset.mem_filter, Finset.mem_range, hpLe, hp, lt_of_not_ge hpw]
          have hroughDvd : p ^ n.factorization p ∣ roughPart w D := by
            unfold roughPart
            exact Finset.dvd_prod_of_mem (fun x => x ^ n.factorization x) hpMem
          have hroughFac : n.factorization p ≤ (roughPart w D).factorization p :=
            hp.pow_dvd_iff_le_factorization hroughPos.ne' |>.1 hroughDvd
          rw [hfacTarget]
          have hfacRle : r.factorization p ≤ n.factorization p := hfacD p
          simp [Nat.factorization_pow, hWfac]
          omega
    · rw [hfacTarget]
      simp [Nat.factorization_eq_zero_of_not_prime r hp,
        Nat.factorization_pow, Nat.factorization_eq_zero_of_not_prime W hp,
        Nat.factorization_eq_zero_of_not_prime (roughPart w D) hp]
  exact (Nat.factorization_le_iff_dvd hr htarget).1 hfacLE

private lemma rowDirections_bad_probability_le {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s) (l : Fin K)
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q))
    (hlisted : TestsListed Dm ι tests) (hdt : dirs.tests ⊆ tests) :
    ∀ N, 0 < primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper →
      gapSlotProbability S l N (fun p =>
        ¬ GoodTuple S l N tests dirs.poly p) ≤
      independentPrimePoolProbability
          (fun _ : Fin s => (S.primeStage.pool N l).lower)
          (fun _ => (S.primeStage.pool N l).upper)
          (FromArithmetic.polynomialZeroOrRepeated Dm) +
        independentPrimePoolProbability
          (fun _ : Fin s => (S.primeStage.pool N l).lower)
          (fun _ => (S.primeStage.pool N l).upper)
          (FromArithmetic.primeSmallDivisibilityEvent Dm (N + 1)
            (S.primeStage.e0 N)) := by
  classical
  intro N hpos
  let lo := (S.primeStage.pool N l).lower
  let hi := (S.primeStage.pool N l).upper
  let zeroQ : (Fin q → ℕ) → Prop := fun p =>
    (∃ P ∈ tests, evalIntegerPolynomial P (fun i => (p i : ℤ)) = 0) ∨
      ¬ Function.Injective p
  let smallQ : (Fin q → ℕ) → Prop := fun p =>
    ∃ π : ℕ, π.Prime ∧ π ≤ N + 1 ∧
      (((π ^ S.primeStage.e0 N : ℕ) : ℤ) ∣
        evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ)))
  let zeroS : (Fin s → ℕ) → Prop := FromArithmetic.polynomialZeroOrRepeated Dm
  let smallS : (Fin s → ℕ) → Prop :=
    FromArithmetic.primeSmallDivisibilityEvent Dm (N + 1) (S.primeStage.e0 N)
  have hDdirs : dirs.poly ∈ dirs.tests := by simp [RowDirections.tests]
  have hDlisted : MvPolynomial.rename ι dirs.poly ∈ Dm := hlisted dirs.poly (hdt hDdirs)
  have heval (P : IntegerPolynomial q) (p : Fin s → ℕ) :
      evalIntegerPolynomial (MvPolynomial.rename ι P) (fun i => (p i : ℤ)) =
        evalIntegerPolynomial P (fun i => (p (ι i) : ℤ)) := by
    change MvPolynomial.eval (fun i => (p i : ℤ)) (MvPolynomial.rename ι P) =
      MvPolynomial.eval (fun i => (p (ι i) : ℤ)) P
    rw [MvPolynomial.eval_rename]
    rfl
  have hzeroMap : ∀ p : Fin s → ℕ, zeroQ (fun i => p (ι i)) → zeroS p := by
    intro p hbad
    rcases hbad with hz | hrep
    · rcases hz with ⟨P, hP, hzero⟩
      left
      refine ⟨MvPolynomial.rename ι P, hlisted P hP, ?_⟩
      rw [heval]
      exact hzero
    · right
      simp only [Function.Injective] at hrep
      push_neg at hrep
      obtain ⟨i, j, hp, hij⟩ := hrep
      refine ⟨ι i, ι j, ?_, ?_⟩
      · intro heq
        exact hij (ι.injective heq)
      · exact hp
  have hsmallMap : ∀ p : Fin s → ℕ, smallQ (fun i => p (ι i)) → smallS p := by
    intro p hbad
    obtain ⟨π, hπ, hπN, hdiv⟩ := hbad
    refine ⟨π, hπ, hπN, MvPolynomial.rename ι dirs.poly, hDlisted, ?_⟩
    rw [heval]
    exact hdiv
  have hbadSub (p : Fin q → ℕ)
      (hgood0 : ∀ i, lo ≤ p i ∧ p i < hi ∧ (p i).Prime)
      (hbad : ¬ GoodTuple S l N tests dirs.poly p) : zeroQ p ∨ smallQ p := by
    by_cases hzero : ∃ P ∈ tests, evalIntegerPolynomial P (fun i => (p i : ℤ)) = 0
    · exact Or.inl (Or.inl hzero)
    by_cases hinj : Function.Injective p
    · right
      by_contra hsmall
      apply hbad
      refine ⟨?_, hinj, ?_, ?_⟩
      · simpa [lo, hi] using hgood0
      · intro P hP hval
        exact hzero ⟨P, hP, hval⟩
      · intro π hπ hπN
        by_contra hdiv
        exact hsmall ⟨π, hπ, hπN, hdiv⟩
    · exact Or.inl (Or.inr hinj)
  have hbadProb :
      independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi)
        (fun p => ¬ GoodTuple S l N tests dirs.poly p) ≤
      independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi)
        (fun p => zeroQ p ∨ smallQ p) := by
    apply rowPrimeProbability_mono_of_support
    intro p hmass hbad
    have hpool := rowPrimeMass_nonzero_implies_pool (fun _ : Fin q => lo)
      (fun _ => hi) p hmass
    exact hbadSub p (by simpa [lo, hi] using hpool) hbad
  have hzeroCyl :
      independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi) zeroQ =
        independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi)
          (fun p => zeroQ (fun i => p (ι i))) := by
    simpa [lo, hi, zeroQ] using rowPrimeProbability_cylinder ι lo hi hpos
      (fun p => (∃ P ∈ tests, evalIntegerPolynomial P (fun i => (p i : ℤ)) = 0) ∨
        ¬ Function.Injective p)
  have hsmallCyl :
      independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi) smallQ =
        independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi)
          (fun p => smallQ (fun i => p (ι i))) := by
    simpa [lo, hi, smallQ] using rowPrimeProbability_cylinder ι lo hi hpos
      (fun p => ∃ π : ℕ, π.Prime ∧ π ≤ N + 1 ∧
        (((π ^ S.primeStage.e0 N : ℕ) : ℤ) ∣
          evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))))
  have hzeroBound :
      independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi)
          (fun p => zeroQ (fun i => p (ι i))) ≤
        independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi) zeroS := by
    apply rowPrimeProbability_mono_of_support
    intro p _ h
    exact hzeroMap p h
  have hsmallBound :
      independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi)
          (fun p => smallQ (fun i => p (ι i))) ≤
        independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi) smallS := by
    apply rowPrimeProbability_mono_of_support
    intro p _ h
    exact hsmallMap p h
  calc
    gapSlotProbability S l N (fun p => ¬ GoodTuple S l N tests dirs.poly p) =
        independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi)
          (fun p => ¬ GoodTuple S l N tests dirs.poly p) := rfl
    _ ≤ independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi)
          (fun p => zeroQ p ∨ smallQ p) := hbadProb
    _ ≤ independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi) zeroQ +
          independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi) smallQ :=
      rowPrimeProbability_union_le (fun _ : Fin q => lo) (fun _ => hi) zeroQ smallQ
    _ = independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi)
          (fun p => zeroQ (fun i => p (ι i))) +
        independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi)
          (fun p => smallQ (fun i => p (ι i))) := by rw [hzeroCyl, hsmallCyl]
    _ ≤ independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi) zeroS +
        independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi) smallS :=
      add_le_add hzeroBound hsmallBound
    _ = _ := by rfl

theorem rowDirections_bad_probability_tendsto {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q))
    (hdt : dirs.tests ⊆ tests) :
    ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
      (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s),
      TestsListed Dm ι tests → ∀ l : Fin K,
      Tendsto (fun N => gapSlotProbability S l N fun p =>
        ¬ GoodTuple S l N tests dirs.poly p) atTop (𝓝 0) := by
  intro K s Aset Dm S ι hlisted l
  let zeroSeq := fun N => independentPrimePoolProbability
    (fun _ : Fin s => (S.primeStage.pool N l).lower)
    (fun _ => (S.primeStage.pool N l).upper)
    (FromArithmetic.polynomialZeroOrRepeated Dm)
  let smallSeq := fun N => independentPrimePoolProbability
    (fun _ : Fin s => (S.primeStage.pool N l).lower)
    (fun _ => (S.primeStage.pool N l).upper)
    (FromArithmetic.primeSmallDivisibilityEvent Dm (N + 1) (S.primeStage.e0 N))
  have hzeroWeighted : Tendsto
      (fun N => zeroSeq N * (FromArithmetic.masterScaleV S.core.parameters N l : ℝ))
      atTop (𝓝 0) := by
    simpa [zeroSeq, FromArithmetic.masterScaleV, pow_one] using
      (S.primeStage.zero_and_repeat_probability l) 1 (by norm_num)
  have hzeroNonneg : ∀ N, 0 ≤ zeroSeq N := by
    intro N
    exact rowPrimeProbability_nonneg
      (fun _ : Fin s => (S.primeStage.pool N l).lower)
      (fun _ => (S.primeStage.pool N l).upper)
      (FromArithmetic.polynomialZeroOrRepeated Dm)
  have hzero : Tendsto zeroSeq atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzeroWeighted
    · exact Filter.Eventually.of_forall hzeroNonneg
    · filter_upwards with N
      have hV : 1 ≤ FromArithmetic.masterScaleV S.core.parameters N l := by
        unfold FromArithmetic.masterScaleV
        omega
      have hVreal : (1 : ℝ) ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) :=
        by exact_mod_cast hV
      have hmul : zeroSeq N ≤ zeroSeq N *
          (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
        calc
          zeroSeq N = zeroSeq N * 1 := by ring
          _ ≤ zeroSeq N * (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) :=
            mul_le_mul_of_nonneg_left hVreal (hzeroNonneg N)
      exact hmul
  have hsmall : Tendsto smallSeq atTop (𝓝 0) := by
    simpa [smallSeq] using S.primeStage.actual_small_prime_exception l
  have hupper : Tendsto (fun N => zeroSeq N + smallSeq N) atTop (𝓝 0) :=
    by simpa using hzero.add hsmall
  have hbadNonneg : ∀ N, 0 ≤ gapSlotProbability S l N fun p =>
      ¬ GoodTuple S l N tests dirs.poly p := by
    intro N
    exact rowPrimeProbability_nonneg
      (fun _ : Fin q => (S.primeStage.pool N l).lower)
      (fun _ => (S.primeStage.pool N l).upper)
      (fun p => ¬ GoodTuple S l N tests dirs.poly p)
  have hbound : ∀ᶠ N in atTop,
      gapSlotProbability S l N (fun p => ¬ GoodTuple S l N tests dirs.poly p) ≤
        zeroSeq N + smallSeq N := by
    filter_upwards [eventually_pool_mass_pos S l] with N hpos
    simpa [zeroSeq, smallSeq] using
      rowDirections_bad_probability_le S ι l dirs tests hlisted hdt N hpos
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall hbadNonneg
  · exact hbound

private lemma rowTemplate_value_eq_eval_poly {m q : ℕ} (T : RowTemplate m q)
    (k : Fin m) (p : Fin q → ℕ) :
    (evalIntegerPolynomial (T.poly k) (fun i => (p i : ℤ)) : ℚ) = T.value p k := by
  cases h : T.entry k with
  | none => simp [RowTemplate.poly, RowTemplate.value, h, evalIntegerPolynomial]
  | some e =>
      simp only [RowTemplate.poly, RowTemplate.value, h]
      change (MvPolynomial.eval (fun i => (p i : ℤ))
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) 1) : ℚ) =
          ∏ i, (p i : ℚ) ^ e i
      have he : ∀ i, (Finsupp.equivFunOnFinite.symm e) i = e i := by
        intro i
        exact congrFun (Finsupp.coe_equivFunOnFinite_symm e) i
      rw [MvPolynomial.eval_monomial]
      simp [Finsupp.prod_fintype, he]

private lemma rowTemplate_response_eval {m q : ℕ} (T : RowTemplate m q)
    (v : Fin m → IntegerPolynomial q) (p : Fin q → ℕ) :
  (evalIntegerPolynomial (templateResponse T v) (fun i => (p i : ℤ)) : ℚ) =
      ∑ k, (T.value p k : ℚ) *
        (evalIntegerPolynomial (v k) (fun i => (p i : ℤ)) : ℚ) := by
  calc
    _ = ∑ k, (evalIntegerPolynomial (T.poly k) (fun i => (p i : ℤ)) : ℚ) *
          (evalIntegerPolynomial (v k) (fun i => (p i : ℤ)) : ℚ) := by
        simp [templateResponse, evalIntegerPolynomial]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [rowTemplate_value_eq_eval_poly]

private lemma exists_eval_natAbs_bound {q : ℕ} (P : IntegerPolynomial q) :
    ∃ e : ℕ, ∀ T : ℕ, 2 ≤ T → ∀ x : Fin q → ℤ,
      (∀ i, (x i).natAbs ≤ T) →
      (evalIntegerPolynomial P x).natAbs ≤ T ^ e := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      refine ⟨Nat.clog 2 a.natAbs, ?_⟩
      intro T hT x hx
      calc
        (evalIntegerPolynomial (MvPolynomial.C a) x).natAbs = a.natAbs := by
          simp [evalIntegerPolynomial]
        _ ≤ 2 ^ Nat.clog 2 a.natAbs := Nat.le_pow_clog (by norm_num) _
        _ ≤ T ^ Nat.clog 2 a.natAbs := Nat.pow_le_pow_left hT _
  | add P Q hP hQ =>
      obtain ⟨eP, hP⟩ := hP
      obtain ⟨eQ, hQ⟩ := hQ
      refine ⟨eP + eQ + 1, ?_⟩
      intro T hT x hx
      have hPP := hP T hT x hx
      have hQQ := hQ T hT x hx
      have hpowP : T ^ eP ≤ T ^ (eP + eQ) :=
        Nat.pow_le_pow_right (by omega : 0 < T) (Nat.le_add_right eP eQ)
      have hpowQ : T ^ eQ ≤ T ^ (eP + eQ) := by
        simpa [Nat.add_comm] using
          (Nat.pow_le_pow_right (by omega : 0 < T) (Nat.le_add_right eQ eP))
      calc
        (evalIntegerPolynomial (P + Q) x).natAbs ≤
            (evalIntegerPolynomial P x).natAbs + (evalIntegerPolynomial Q x).natAbs := by
              simp [evalIntegerPolynomial]
              exact Int.natAbs_add_le _ _
        _ ≤ T ^ eP + T ^ eQ := Nat.add_le_add hPP hQQ
        _ ≤ T ^ (eP + eQ) + T ^ (eP + eQ) := Nat.add_le_add hpowP hpowQ
        _ = 2 * T ^ (eP + eQ) := by omega
        _ ≤ T ^ (eP + eQ + 1) := by
          rw [Nat.pow_succ]
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right (T ^ (eP + eQ)) hT
  | mul_X P i hP =>
      obtain ⟨eP, hP⟩ := hP
      refine ⟨eP + 1, ?_⟩
      intro T hT x hx
      have hval := hP T hT x hx
      calc
        (evalIntegerPolynomial (P * MvPolynomial.X i) x).natAbs =
            (evalIntegerPolynomial P x).natAbs * (x i).natAbs := by
              simp [evalIntegerPolynomial, Int.natAbs_mul]
        _ ≤ T ^ eP * T := Nat.mul_le_mul hval (hx i)
        _ = T ^ (eP + 1) := by rw [Nat.pow_succ]

private noncomputable def polynomialEvalExponent {q : ℕ} (P : IntegerPolynomial q) : ℕ :=
  Classical.choose (exists_eval_natAbs_bound P)

private lemma polynomialEvalExponent_spec {q : ℕ} (P : IntegerPolynomial q) :
    ∀ T : ℕ, 2 ≤ T → ∀ x : Fin q → ℤ,
      (∀ i, (x i).natAbs ≤ T) →
      (evalIntegerPolynomial P x).natAbs ≤ T ^ polynomialEvalExponent P :=
  Classical.choose_spec (exists_eval_natAbs_bound P)

private noncomputable def rowDirectionsEvalBudget {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) : ℕ :=
  polynomialEvalExponent dirs.poly +
    (∑ R : Fin r, ∑ k : Fin m, polynomialEvalExponent (dirs.w R k)) +
    ∑ k : Fin m, polynomialEvalExponent (dirs.w0 k)

private noncomputable def rowDirectionsSizeExponent {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) : ℕ := 2 + 2 * rowDirectionsEvalBudget dirs

private lemma rowDirections_evalExponent_poly_le_budget {m q r : ℕ}
    {Sh : RowShape m q r} (dirs : RowDirections Sh) :
    polynomialEvalExponent dirs.poly ≤ rowDirectionsEvalBudget dirs := by
  unfold rowDirectionsEvalBudget
  omega

private lemma rowDirections_evalExponent_w_le_budget {m q r : ℕ}
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (R : Fin r) (k : Fin m) :
    polynomialEvalExponent (dirs.w R k) ≤ rowDirectionsEvalBudget dirs := by
  unfold rowDirectionsEvalBudget
  calc
    polynomialEvalExponent (dirs.w R k) ≤
        ∑ j : Fin m, polynomialEvalExponent (dirs.w R j) :=
      Finset.single_le_sum (f := fun j : Fin m => polynomialEvalExponent (dirs.w R j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ ≤ ∑ I : Fin r, ∑ j : Fin m, polynomialEvalExponent (dirs.w I j) :=
      Finset.single_le_sum
        (f := fun I : Fin r => ∑ j : Fin m, polynomialEvalExponent (dirs.w I j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ R)
    _ ≤ polynomialEvalExponent dirs.poly +
        (∑ I : Fin r, ∑ j : Fin m, polynomialEvalExponent (dirs.w I j)) +
        ∑ j : Fin m, polynomialEvalExponent (dirs.w0 j) := by omega

private lemma rowDirections_evalExponent_w0_le_budget {m q r : ℕ}
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (k : Fin m) :
    polynomialEvalExponent (dirs.w0 k) ≤ rowDirectionsEvalBudget dirs := by
  unfold rowDirectionsEvalBudget
  calc
    polynomialEvalExponent (dirs.w0 k) ≤
        ∑ j : Fin m, polynomialEvalExponent (dirs.w0 j) :=
      Finset.single_le_sum (f := fun j : Fin m => polynomialEvalExponent (dirs.w0 j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ ≤ polynomialEvalExponent dirs.poly +
        (∑ R : Fin r, ∑ j : Fin m, polynomialEvalExponent (dirs.w R j)) +
        ∑ j : Fin m, polynomialEvalExponent (dirs.w0 j) := by omega

private lemma rowDirections_polynomial_values_bounded {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ)
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (p : Fin q → ℕ)
    (hp : ∀ i, (S.primeStage.pool N l).lower ≤ p i ∧
      p i < (S.primeStage.pool N l).upper ∧ (p i).Prime) :
    let size := (S.primeStage.pool N l).upper +
      FromArithmetic.masterScaleV S.core.parameters N l
    (evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))).natAbs ≤ size ^
      rowDirectionsSizeExponent dirs ∧
    (∀ R k, (evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ))).natAbs ≤
      size ^ rowDirectionsSizeExponent dirs) ∧
    (∀ k, (evalIntegerPolynomial (dirs.w0 k) (fun i => (p i : ℤ))).natAbs ≤
      size ^ rowDirectionsSizeExponent dirs) := by
  classical
  dsimp
  let size := (S.primeStage.pool N l).upper +
    FromArithmetic.masterScaleV S.core.parameters N l
  let E := rowDirectionsEvalBudget dirs
  let B := rowDirectionsSizeExponent dirs
  have hsize : 2 ≤ size := by
    dsimp [size, FromArithmetic.masterScaleV]
    omega
  have hupper : (S.primeStage.pool N l).upper ≤ size := by
    dsimp [size]
    exact Nat.le_add_right _ _
  have hcoord : ∀ i, ((p i : ℤ).natAbs) ≤ size := by
    intro i
    simp
    exact (Nat.le_of_lt (hp i).2.1).trans hupper
  have hpoly (P : IntegerPolynomial q) (hE : polynomialEvalExponent P ≤ E) :
      (evalIntegerPolynomial P (fun i => (p i : ℤ))).natAbs ≤ size ^ B := by
    calc
      _ ≤ size ^ polynomialEvalExponent P :=
        polynomialEvalExponent_spec P size hsize (fun i => (p i : ℤ)) hcoord
      _ ≤ size ^ E := Nat.pow_le_pow_right (by omega : 0 < size) hE
      _ ≤ size ^ B := Nat.pow_le_pow_right (by omega : 0 < size) (by
        dsimp [B, E, rowDirectionsSizeExponent]
        omega)
  refine ⟨hpoly dirs.poly (rowDirections_evalExponent_poly_le_budget dirs), ?_, ?_⟩
  · intro R k
    exact hpoly (dirs.w R k) (rowDirections_evalExponent_w_le_budget dirs R k)
  · intro k
    have hE : polynomialEvalExponent (dirs.w0 k) ≤ E :=
      rowDirections_evalExponent_w0_le_budget dirs k
    exact hpoly (dirs.w0 k) hE

private lemma rowForm_translation_response {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) (c : Fin m → ℚ) (hc : ∀ k, c k ≠ 0)
    (Mp : ℕ) (p : Fin q → ℕ) (R : Fin r) (T : RowTemplate m q)
    (hd : evalIntegerPolynomial (dirs.targetResponse R) (fun i => (p i : ℤ)) ≠ 0) :
    rowForm c T p (dirs.translation c Mp p R) =
      (Mp : ℚ) * (c ((Sh.row Sh.star).anchor) / c T.anchor) *
        ((evalIntegerPolynomial (templateResponse T (dirs.w R))
          (fun i => (p i : ℤ)) : ℚ) /
          (evalIntegerPolynomial (dirs.targetResponse R)
            (fun i => (p i : ℤ)) : ℚ)) := by
  rw [rowTemplate_response_eval]
  unfold rowForm RowDirections.translation
  let common : ℚ := (Mp : ℚ) *
    (c ((Sh.row Sh.star).anchor) / c T.anchor)
  have hstar := hc ((Sh.row Sh.star).anchor)
  have hanchor := hc T.anchor
  have hdk : (evalIntegerPolynomial (dirs.targetResponse R)
      (fun i => (p i : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast hd
  calc
    _ = ∑ k, common * ((T.value p k : ℚ) *
        (evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ)) : ℚ) /
          (evalIntegerPolynomial (dirs.targetResponse R)
            (fun i => (p i : ℤ)) : ℚ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [common]
      field_simp [hc k, hstar, hanchor, hdk] <;> ring
    _ = common * ∑ k, (T.value p k : ℚ) *
          (evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ)) : ℚ) /
            (evalIntegerPolynomial (dirs.targetResponse R)
              (fun i => (p i : ℤ)) : ℚ) := by
      rw [← Finset.mul_sum]
    _ = common *
          ((∑ k, (T.value p k : ℚ) *
            (evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ)) : ℚ)) /
            (evalIntegerPolynomial (dirs.targetResponse R)
              (fun i => (p i : ℤ)) : ℚ)) := by
      rw [Finset.sum_div]
    _ = _ := rfl

private lemma rowForm_rootTranslation_response {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) (c : Fin m → ℚ) (hc : ∀ k, c k ≠ 0)
    (M : ℕ) (p : Fin q → ℕ) (T : RowTemplate m q) :
  rowForm c T p (dirs.rootTranslation c M p) =
      (M : ℚ) * (c ((Sh.row Sh.star).anchor) / c T.anchor) *
        (evalIntegerPolynomial (templateResponse T dirs.w0)
          (fun i => (p i : ℤ)) : ℚ) := by
  rw [rowTemplate_response_eval]
  unfold rowForm RowDirections.rootTranslation
  let common : ℚ := (M : ℚ) *
    (c ((Sh.row Sh.star).anchor) / c T.anchor)
  have hstar := hc ((Sh.row Sh.star).anchor)
  have hanchor := hc T.anchor
  calc
    _ = ∑ k, common * ((T.value p k : ℚ) *
        (evalIntegerPolynomial (dirs.w0 k) (fun i => (p i : ℤ)) : ℚ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [common]
      field_simp [hc k, hstar, hanchor] <;> ring
    _ = common * ∑ k, (T.value p k : ℚ) *
        (evalIntegerPolynomial (dirs.w0 k) (fun i => (p i : ℤ)) : ℚ) := by
      rw [← Finset.mul_sum]
    _ = _ := rfl

private lemma rowResponse_mem_tests {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) {R I : Fin r} {P : IntegerPolynomial q}
    (hP : P = templateResponse (Sh.row I) (dirs.w R)) (hR : R ≠ Sh.star)
    (hIR : I ≠ R) (hdirs : dirs.Valid) : P ∈ dirs.tests := by
  have hne : templateResponse (Sh.row I) (dirs.w R) ≠ 0 := hdirs.2.1 R I hR hIR
  have hmem : templateResponse (Sh.row I) (dirs.w R) ∈ dirs.responses := by
    unfold RowDirections.responses
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ?_)), hne⟩
    exact ⟨(I, R), Finset.mem_univ _, rfl⟩
  subst P
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hmem)))

private lemma rootRowResponse_mem_tests {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) {I : Fin r} (hI : I ≠ Sh.star) (hdirs : dirs.Valid) :
    templateResponse (Sh.row I) dirs.w0 ∈ dirs.tests := by
  have hne : templateResponse (Sh.row I) dirs.w0 ≠ 0 := hdirs.2.2.2 I hI
  have hmem : templateResponse (Sh.row I) dirs.w0 ∈ dirs.responses := by
    unfold RowDirections.responses
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ?_)), hne⟩
    exact ⟨I, Finset.mem_univ _, rfl⟩
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hmem)))

private lemma targetResponse_mem_tests {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) {R : Fin r} (hR : R ≠ Sh.star) (hdirs : dirs.Valid) :
    dirs.targetResponse R ∈ dirs.tests := by
  apply rowResponse_mem_tests (R := R) (I := Sh.star) dirs rfl hR (Ne.symm hR) hdirs

private lemma targetResponse_eval_dvd_poly {m q r : ℕ} {Sh : RowShape m q r}
    (dirs : RowDirections Sh) {R : Fin r} (hR : R ≠ Sh.star) (p : Fin q → ℕ) :
    evalIntegerPolynomial (dirs.targetResponse R) (fun i => (p i : ℤ)) ∣
      evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ)) := by
  have hmem : R ∈ Finset.univ.erase Sh.star :=
    Finset.mem_erase.mpr ⟨hR, Finset.mem_univ R⟩
  have heval : evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ)) =
      ∏ I ∈ Finset.univ.erase Sh.star,
        evalIntegerPolynomial (dirs.targetResponse I) (fun i => (p i : ℤ)) := by
    unfold RowDirections.poly evalIntegerPolynomial
    rw [MvPolynomial.eval_prod]
  rw [heval]
  exact Finset.dvd_prod_of_mem
    (fun I => evalIntegerPolynomial (dirs.targetResponse I) (fun i => (p i : ℤ))) hmem

private lemma rowDirections_response_identities_at {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (c : Fin m → ℚ) (hc : ∀ k, c k ≠ 0)
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (hdirs : dirs.Valid)
    (tests : Finset (IntegerPolynomial q)) (hdt : dirs.tests ⊆ tests)
    (p : Fin q → ℕ) (hgood : GoodTuple S C.gap N tests dirs.poly p) :
    (∀ R, R ≠ Sh.star → rowForm c (Sh.row Sh.star) p
      (dirs.translation c (directionModulus S N dirs.poly p) p R) =
        directionModulus S N dirs.poly p) ∧
    (∀ R, R ≠ Sh.star → rowForm c (Sh.row R) p
      (dirs.translation c (directionModulus S N dirs.poly p) p R) = 0) ∧
    rowForm c (Sh.row Sh.star) p (dirs.rootTranslation c (S.core.parameters.M N) p) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro R hR
    have htest : dirs.targetResponse R ∈ tests :=
      hdt (targetResponse_mem_tests dirs hR hdirs)
    have hd : evalIntegerPolynomial (dirs.targetResponse R) (fun i => (p i : ℤ)) ≠ 0 :=
      hgood.2.2.1 _ htest
    have h := rowForm_translation_response dirs c hc
      (directionModulus S N dirs.poly p) p R (Sh.row Sh.star) hd
    have hresp : templateResponse (Sh.row Sh.star) (dirs.w R) = dirs.targetResponse R := rfl
    rw [hresp] at h
    have hcstar : c ((Sh.row Sh.star).anchor) / c ((Sh.row Sh.star).anchor) = 1 :=
      div_self (hc _)
    simpa [hcstar, hd] using h
  · intro R hR
    have htest : dirs.targetResponse R ∈ tests :=
      hdt (targetResponse_mem_tests dirs hR hdirs)
    have hd : evalIntegerPolynomial (dirs.targetResponse R) (fun i => (p i : ℤ)) ≠ 0 :=
      hgood.2.2.1 _ htest
    have hzero : templateResponse (Sh.row R) (dirs.w R) = 0 := hdirs.1 R hR
    have h := rowForm_translation_response dirs c hc
      (directionModulus S N dirs.poly p) p R (Sh.row R) hd
    rw [hzero] at h
    have hEvalZero : evalIntegerPolynomial (0 : IntegerPolynomial q)
        (fun i => (p i : ℤ)) = 0 := by simp [evalIntegerPolynomial]
    rw [hEvalZero] at h
    simpa using h
  · have hzero : templateResponse (Sh.row Sh.star) dirs.w0 = 0 := hdirs.2.2.1
    have h := rowForm_rootTranslation_response dirs c hc
      (S.core.parameters.M N) p (Sh.row Sh.star)
    rw [hzero] at h
    have hEvalZero : evalIntegerPolynomial (0 : IntegerPolynomial q)
        (fun i => (p i : ℤ)) = 0 := by simp [evalIntegerPolynomial]
    rw [hEvalZero] at h
    simpa using h

private noncomputable def extendPrimeTuple {q s : ℕ} (ι : Fin q ↪ Fin s)
    (p : Fin q → ℕ) (default : ℕ) : Fin s → ℕ := fun j =>
  if h : ∃ i, ι i = j then p (Classical.choose h) else default

private lemma extendPrimeTuple_on_image {q s : ℕ} (ι : Fin q ↪ Fin s)
    (p : Fin q → ℕ) (default : ℕ) (i : Fin q) :
    extendPrimeTuple ι p default (ι i) = p i := by
  unfold extendPrimeTuple
  have h : ∃ j, ι j = ι i := ⟨i, rfl⟩
  rw [dif_pos h]
  congr 1
  exact ι.injective (Classical.choose_spec h)

private lemma evalIntegerPolynomial_rename {q s : ℕ} (ι : Fin q ↪ Fin s)
    (P : IntegerPolynomial q) (p : Fin s → ℕ) :
    evalIntegerPolynomial (MvPolynomial.rename ι P) (fun i => (p i : ℤ)) =
      evalIntegerPolynomial P (fun i => (p (ι i) : ℤ)) := by
  change MvPolynomial.eval (fun i => (p i : ℤ)) (MvPolynomial.rename ι P) =
    MvPolynomial.eval (fun i => (p (ι i) : ℤ)) P
  rw [MvPolynomial.eval_rename]
  rfl

private lemma rowDirections_modulus_divides_gap {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset)
    {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (hlisted : TestsListed Dm ι tests)
    (hdt : dirs.tests ⊆ tests) :
    ∀ᶠ N in atTop, ∀ p,
      GoodTuple S C.gap N tests dirs.poly p →
        directionModulus S N dirs.poly p ∣ S.core.parameters.H N C.gap := by
  filter_upwards [eventually_pool_lower_ge_two S C.gap] with N hlow
  intro p hgood
  obtain ⟨p0, hp0lo, hp0hi, hp0prime⟩ :=
    exists_prime_in_pool (S.primeStage.pool N C.gap) hlow
  let pfull := extendPrimeTuple ι p p0
  have hpfull : ∀ j, (S.primeStage.pool N C.gap).lower ≤ pfull j ∧
      pfull j < (S.primeStage.pool N C.gap).upper ∧ (pfull j).Prime := by
    intro j
    by_cases hex : ∃ i, ι i = j
    · have hval : pfull j = p (Classical.choose hex) := by
        dsimp [pfull, extendPrimeTuple]
        rw [dif_pos hex]
      rw [hval]
      exact hgood.1 (Classical.choose hex)
    · have hval : pfull j = p0 := by
        dsimp [pfull, extendPrimeTuple]
        rw [dif_neg hex]
      rw [hval]
      exact ⟨hp0lo, hp0hi, hp0prime⟩
  have hDtests : dirs.poly ∈ tests := hdt (by simp [RowDirections.tests])
  have hDlisted : MvPolynomial.rename ι dirs.poly ∈ Dm := hlisted dirs.poly hDtests
  have hDeval : evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ)) ≠ 0 :=
    hgood.2.2.1 dirs.poly hDtests
  have hDevalFull : evalIntegerPolynomial (MvPolynomial.rename ι dirs.poly)
      (fun i => (pfull i : ℤ)) ≠ 0 := by
    rw [evalIntegerPolynomial_rename ι dirs.poly pfull]
    simpa [pfull, extendPrimeTuple_on_image] using hDeval
  have hgap := S.gapStage.polynomial_values_divide_gap N C.gap pfull
    (MvPolynomial.rename ι dirs.poly) hDlisted hpfull hDevalFull
  have hrough := roughPart_dvd_natAbs (w := N + 1) hDeval
  have hmult : S.core.parameters.M N *
      roughPart (N + 1) (evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))) ∣
      S.core.parameters.M N *
        (evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))).natAbs :=
    Nat.mul_dvd_mul_left _ hrough
  have hgap' : S.core.parameters.M N *
      (evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))).natAbs ∣
      S.core.parameters.H N C.gap := by
    simpa [evalIntegerPolynomial_rename, pfull, extendPrimeTuple_on_image] using hgap
  change S.core.parameters.M N *
      roughPart (N + 1) (evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))) ∣
    S.core.parameters.H N C.gap
  exact hmult.trans hgap'

private lemma rowCoefficient_quotient {K s m r : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (c : Fin m → ℤ)
    (hc : ∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d)
    (hcpos : ∀ d, 0 < c d)
    (hcoef : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ)) (k : Fin m) :
    ∃ q : ℤ,
      (S.core.parameters.M N : ℚ) / chainScale S.core.parameters C a N k =
        (((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) : ℚ) * q ∧
      (S.core.parameters.M N : ℤ) =
        ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c k * q ∧
      0 < q ∧ q.natAbs ≤ S.core.parameters.M N ∧
        (primorial (N + 1) ^ (S.primeStage.e0 N + 1)) * q.natAbs ≤
          S.core.parameters.M N := by
  obtain ⟨q, hq⟩ := hcoef k
  let Wpow := primorial (N + 1) ^ (S.primeStage.e0 N + 1)
  have hWpow : 0 < Wpow := by
    dsimp [Wpow]
    exact pow_pos (primorial_pos (N + 1)) _
  have hdivisor : 0 < (Wpow : ℤ) * c k := mul_pos (by exact_mod_cast hWpow) (hcpos k)
  have hMpos : (0 : ℤ) < S.core.parameters.M N := by
    exact_mod_cast S.core.parameters.Mpos N
  have hqpos : 0 < q := by
    by_contra hqnot
    have hqle : q ≤ 0 := by omega
    have hMnonpos : (Wpow : ℤ) * c k * q ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdivisor.le hqle
    rw [hq] at hMpos
    exact (not_le_of_gt hMpos) hMnonpos
  have hdivisorOne : (1 : ℤ) ≤ (Wpow : ℤ) * c k := by omega
  have hqle : q ≤ (S.core.parameters.M N : ℤ) := by
    calc
      q ≤ (Wpow : ℤ) * c k * q :=
        by
          simpa using Int.mul_le_mul_of_nonneg_right
            hdivisorOne (le_of_lt hqpos)
      _ = S.core.parameters.M N := hq.symm
  have hqcast : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg hqpos.le
  have hqle' : (q.natAbs : ℤ) ≤ (S.core.parameters.M N : ℤ) := by
    rw [hqcast]
    exact hqle
  have hqabs : q.natAbs ≤ S.core.parameters.M N := by exact_mod_cast hqle'
  have hcge : (1 : ℤ) ≤ c k := by
    have hck := hcpos k
    omega
  have hWnonneg : (0 : ℤ) ≤ (Wpow : ℤ) := by exact_mod_cast Nat.zero_le Wpow
  have hWc : (Wpow : ℤ) ≤ (Wpow : ℤ) * c k := by
    calc
      (Wpow : ℤ) = (Wpow : ℤ) * 1 := by ring
      _ ≤ (Wpow : ℤ) * c k := Int.mul_le_mul_of_nonneg_left hcge hWnonneg
  have hWqle : (Wpow : ℤ) * q ≤ S.core.parameters.M N := by
    calc
      (Wpow : ℤ) * q ≤ (Wpow : ℤ) * c k * q :=
        by simpa using Int.mul_le_mul_of_nonneg_right hWc (le_of_lt hqpos)
      _ = S.core.parameters.M N := hq.symm
  have hWqcast : ((Wpow * q.natAbs : ℕ) : ℤ) = (Wpow : ℤ) * q := by
    rw [Nat.cast_mul, hqcast]
  have hWqleNat : Wpow * q.natAbs ≤ S.core.parameters.M N := by
    have h : ((Wpow * q.natAbs : ℕ) : ℤ) ≤ (S.core.parameters.M N : ℤ) := by
      rw [hWqcast]
      exact hWqle
    exact_mod_cast h
  have hWqabs : Wpow * q.natAbs ≤ S.core.parameters.M N := hWqleNat
  have hquot : (S.core.parameters.M N : ℚ) / chainScale S.core.parameters C a N k =
      (Wpow : ℚ) * (q : ℚ) := by
    rw [← hc k]
    have hqcast : (S.core.parameters.M N : ℚ) =
        (((Wpow : ℤ) * c k * q : ℤ) : ℚ) := by exact_mod_cast hq
    rw [hqcast]
    push_cast
    field_simp [ne_of_gt (hcpos k)] <;> ring
  refine ⟨q, ?_, ?_, hqpos, hqabs, hWqabs⟩
  · simpa [Wpow] using hquot
  · simpa [Wpow] using hq

private lemma exists_W_divisible_quotient {w e : ℕ} (he : 1 ≤ e)
    (d : ℤ) (hd : d ≠ 0) (rough : ℕ)
    (hcover : d.natAbs ∣ (primorial w) ^ (e - 1) * rough)
    (q ca x : ℤ) :
    ∃ v : ℤ,
      ((primorial w : ℕ) ^ (e + 1) : ℤ) * q * ca * rough * x = d * v ∧
      (primorial w : ℤ) ∣ v ∧
      v.natAbs ≤
        (((primorial w : ℕ) ^ (e + 1) : ℤ) * q * ca * rough * x).natAbs := by
  let W := primorial w
  let Wpow := W ^ (e + 1)
  let num : ℤ := (Wpow : ℤ) * q * ca * (rough : ℤ) * x
  have hWpos : 0 < W := by dsimp [W]; exact primorial_pos w
  have hWnat : 0 < W := hWpos
  have hpow : W * (W ^ (e - 1) * rough) = W ^ e * rough := by
    have hpow' : W * W ^ (e - 1) = W ^ e := by
      calc
        W * W ^ (e - 1) = W ^ (e - 1) * W := Nat.mul_comm _ _
        _ = W ^ ((e - 1) + 1) := by rw [Nat.pow_succ]
        _ = W ^ e := by rw [Nat.sub_add_cancel (by omega)]
    calc
      W * (W ^ (e - 1) * rough) = (W * W ^ (e - 1)) * rough := by ac_rfl
      _ = W ^ e * rough := by rw [hpow']
  have hmulCover : W * d.natAbs ∣ W ^ e * rough := by
    calc
      W * d.natAbs ∣ W * (W ^ (e - 1) * rough) := Nat.mul_dvd_mul_left W hcover
      _ = W ^ e * rough := hpow
  have hpowDvd : W ^ e ∣ W ^ (e + 1) := Nat.pow_dvd_pow W (Nat.le_succ e)
  have hbase : W * d.natAbs ∣ Wpow * rough := by
    exact hmulCover.trans (Nat.mul_dvd_mul_right hpowDvd rough)
  have hbase' : W * d.natAbs ∣ Wpow * rough *
      (q.natAbs * ca.natAbs * x.natAbs) :=
    dvd_mul_of_dvd_left hbase _
  have hnumAbs : num.natAbs = Wpow * rough *
      (q.natAbs * ca.natAbs * x.natAbs) := by
    simp [num, Wpow, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm]
  have hnat : W * d.natAbs ∣ num.natAbs := by
    simpa [hnumAbs, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbase'
  have hInt : (W : ℤ) * d ∣ num := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using hnat
  obtain ⟨t, ht⟩ := hInt
  let v : ℤ := (W : ℤ) * t
  have hv : num = d * v := by
    dsimp [v] at *
    rw [ht]
    ring
  have hWdvd : (W : ℤ) ∣ v := by
    exact ⟨t, rfl⟩
  have hdabs : 1 ≤ d.natAbs := Nat.succ_le_of_lt (Int.natAbs_pos.mpr hd)
  have hsize : v.natAbs ≤ num.natAbs := by
    calc
      v.natAbs = 1 * v.natAbs := by omega
      _ ≤ d.natAbs * v.natAbs := Nat.mul_le_mul_right _ hdabs
      _ = num.natAbs := by rw [hv]; simp [v, Int.natAbs_mul]
  refine ⟨v, ?_, hWdvd, ?_⟩
  · simpa [num, Wpow] using hv
  · simpa [num, Wpow] using hsize

private lemma rowDirections_translation_integer_at {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (c : Fin m → ℤ)
    (hscale : ∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d)
    (hcpos : ∀ d, 0 < c d)
    (hcoef : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (hdirs : dirs.Valid)
    (tests : Finset (IntegerPolynomial q)) (hdt : dirs.tests ⊆ tests)
    (p : Fin q → ℕ) (hgood : GoodTuple S C.gap N tests dirs.poly p)
    (R : Fin r) (hR : R ≠ Sh.star) (k : Fin m) :
    ∃ v : ℤ,
      (v : ℚ) = dirs.translation (chainScale S.core.parameters C a N)
        (directionModulus S N dirs.poly p) p R k ∧
      (primorial (N + 1) : ℤ) ∣ v ∧
      v.natAbs ≤ S.core.parameters.M N *
        (c ((Sh.row Sh.star).anchor)).natAbs *
          roughPart (N + 1) (evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))) *
          (evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ))).natAbs := by
  classical
  let w := N + 1
  let e := S.primeStage.e0 N
  let W := primorial w
  let Wpow := W ^ (e + 1)
  let Dval := evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))
  let rough := roughPart w Dval
  let M := S.core.parameters.M N
  let Mp := directionModulus S N dirs.poly p
  let dval := evalIntegerPolynomial (dirs.targetResponse R) (fun i => (p i : ℤ))
  let wval := evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ))
  have hDtests : dirs.poly ∈ tests := hdt (by simp [RowDirections.tests])
  have hDne : Dval ≠ 0 := hgood.2.2.1 dirs.poly hDtests
  have hdtests : dirs.targetResponse R ∈ tests :=
    hdt (targetResponse_mem_tests dirs hR hdirs)
  have hdne : dval ≠ 0 := hgood.2.2.1 (dirs.targetResponse R) hdtests
  have hDdvd : dval ∣ Dval := targetResponse_eval_dvd_poly dirs hR p
  have hsmall : ∀ π, π.Prime → π ≤ w → ¬ (((π ^ e : ℕ) : ℤ) ∣ Dval) := by
    intro π hπ hπw hdiv
    exact hgood.2.2.2 π hπ (by simpa [w] using hπw) hdiv
  have hcover := roughPart_covers_divisor (w := w) (e := e)
    (S.primeStage.e0_pos N) hDne hdne hDdvd hsmall
  obtain ⟨q, hquot, hqInt, hqpos, hqabs, hWqabs⟩ :=
    rowCoefficient_quotient (r := r) S C a N c hscale hcpos hcoef k
  obtain ⟨v, hnum, hWdvd, hvle⟩ :=
    exists_W_divisible_quotient (w := w) (e := e) (S.primeStage.e0_pos N)
      dval hdne rough hcover q (c ((Sh.row Sh.star).anchor)) wval
  have hdRat : (dval : ℚ) ≠ 0 := by exact_mod_cast hdne
  have hckRat : chainScale S.core.parameters C a N k ≠ 0 := by
    rw [← hscale k]
    exact_mod_cast ne_of_gt (hcpos k)
  have hcaRat : chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) ≠ 0 := by
    rw [← hscale ((Sh.row Sh.star).anchor)]
    exact_mod_cast ne_of_gt (hcpos ((Sh.row Sh.star).anchor))
  have htrans : (v : ℚ) =
      dirs.translation (chainScale S.core.parameters C a N) Mp p R k := by
    calc
      (v : ℚ) = ((dval : ℚ) * (v : ℚ)) / (dval : ℚ) := by
        field_simp [hdRat]
      _ = ((dval * v : ℤ) : ℚ) / (dval : ℚ) := by push_cast; rfl
      _ = ((((primorial w ^ (e + 1) : ℕ) : ℤ) * q *
          c ((Sh.row Sh.star).anchor) * rough * wval : ℤ) : ℚ) /
            (dval : ℚ) := by
        rw [← hnum]
        rfl
      _ = (Wpow : ℚ) * (q : ℚ) * (c ((Sh.row Sh.star).anchor) : ℚ) *
          (rough : ℚ) * (wval : ℚ) / (dval : ℚ) := by
        simp [Wpow, W, w, e]
      _ = ((M : ℚ) / chainScale S.core.parameters C a N k) *
          (chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) : ℚ) *
          (rough : ℚ) * (wval : ℚ) / (dval : ℚ) := by
        have hquot' : (M : ℚ) / chainScale S.core.parameters C a N k =
            (Wpow : ℚ) * (q : ℚ) := by simpa [M, Wpow, W, w, e] using hquot
        rw [← hquot', hscale ((Sh.row Sh.star).anchor)]
      _ = ((Mp : ℚ) *
          (chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) /
            chainScale S.core.parameters C a N k) *
          ((wval : ℚ) / (dval : ℚ))) := by
        dsimp [Mp, directionModulus, Dval, rough, w]
        field_simp [hckRat, hcaRat, hdRat]
        <;> push_cast
        <;> ring
      _ = _ := rfl
  have hnumAbs : ((Wpow : ℤ) * q * c ((Sh.row Sh.star).anchor) *
      (rough : ℤ) * wval).natAbs = Wpow * q.natAbs *
        (c ((Sh.row Sh.star).anchor)).natAbs * rough * wval.natAbs := by
    simp [Int.natAbs_mul, Int.natAbs_of_nonneg hqpos.le,
      Int.natAbs_of_nonneg (hcpos ((Sh.row Sh.star).anchor)).le,
      Int.natAbs_natCast, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  refine ⟨v, htrans, hWdvd, ?_⟩
  calc
    v.natAbs ≤ ((Wpow : ℤ) * q * c ((Sh.row Sh.star).anchor) *
        (rough : ℤ) * wval).natAbs := hvle
    _ = Wpow * q.natAbs * (c ((Sh.row Sh.star).anchor)).natAbs *
        rough * wval.natAbs := hnumAbs
    _ ≤ S.core.parameters.M N * (c ((Sh.row Sh.star).anchor)).natAbs *
        roughPart (N + 1) (evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))) *
          (evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ))).natAbs := by
      calc
        Wpow * q.natAbs * (c ((Sh.row Sh.star).anchor)).natAbs * rough * wval.natAbs =
            (Wpow * q.natAbs) *
              ((c ((Sh.row Sh.star).anchor)).natAbs * rough * wval.natAbs) := by ac_rfl
        _ ≤ S.core.parameters.M N *
            ((c ((Sh.row Sh.star).anchor)).natAbs * rough * wval.natAbs) :=
          by
            simpa [Wpow, W, w, e] using Nat.mul_le_mul_right
              ((c ((Sh.row Sh.star).anchor)).natAbs * rough * wval.natAbs) hWqabs
        _ = _ := by simp [rough, Dval, w] <;> ring

private lemma rowCoefficient_natAbs_le_modulus {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (N : ℕ)
    (c : Fin m → ℤ) (hcpos : ∀ d, 0 < c d)
    (hcoef : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ)) (d : Fin m) :
    (c d).natAbs ≤ S.core.parameters.M N := by
  have hcM : c d ∣ (S.core.parameters.M N : ℤ) := by
    apply dvd_trans ?_ (hcoef d)
    exact ⟨((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ), by ring⟩
  have hNat : (c d).natAbs ∣ S.core.parameters.M N := by
    have h := Int.natAbs_dvd_natAbs.mpr hcM
    simpa [Int.natAbs_of_nonneg (hcpos d).le] using h
  exact Nat.le_of_dvd (S.core.parameters.Mpos N) hNat

private lemma nat_mul_le_power_succ {T A B e : ℕ}
    (hT : 1 ≤ T) (hA : A ≤ T) (hB : B ≤ T ^ e) :
    A * B ≤ T ^ (e + 1) := by
  calc
    A * B ≤ T * T ^ e := Nat.mul_le_mul hA hB
    _ = T ^ (e + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

private lemma nat_mul_mul_le_power_budget {T A B C e : ℕ}
    (hT : 1 ≤ T) (hA : A ≤ T) (hB : B ≤ T) (hC : C ≤ T ^ e) :
    A * B * C ≤ T ^ (2 + e) := by
  have hAB : A * B ≤ T ^ 2 :=
    nat_mul_le_power_succ hT hA (by simpa [pow_one] using hB)
  calc
    A * B * C ≤ T ^ 2 * T ^ e := Nat.mul_le_mul hAB hC
    _ = T ^ (2 + e) := by rw [← Nat.pow_add]

private lemma natPrime_not_dvd_int_mul {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    ¬ (p : ℤ) ∣ a * b := by
  intro hab
  have hnat : p ∣ (a * b).natAbs := Int.natCast_dvd.mp hab
  rw [Int.natAbs_mul] at hnat
  rcases hp.dvd_mul.mp hnat with hA | hB
  · exact ha (Int.natCast_dvd.mpr hA)
  · exact hb (Int.natCast_dvd.mpr hB)

private lemma prime_not_divides_master_modulus {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : FromArithmetic.MasterScales K Aset s Dm)
    (N π : ℕ) (hp : π.Prime) (hπ : N + 1 < π) :
    ¬ (π : ℤ) ∣ (S.core.parameters.M N : ℤ) := by
  obtain ⟨eM, hM⟩ := S.core.modulus_power N
  have hW : ¬ π ∣ primorial (N + 1) := by
    intro hdiv
    exact (Nat.not_le_of_gt hπ) (hp.dvd_primorial_iff.mp hdiv)
  intro hdivM
  have hdivNat : π ∣ S.core.parameters.M N := Int.natCast_dvd.mp hdivM
  rw [hM] at hdivNat
  exact hW (hp.dvd_of_dvd_pow hdivNat)

private lemma prime_not_divides_large_roughPart {w : ℕ} {D : ℤ} (hD : D ≠ 0)
    {π : ℕ} (hp : π.Prime) (hπ : w < π)
    (hDπ : ¬ (π : ℤ) ∣ D) :
    ¬ (π : ℤ) ∣ roughPart w D := by
  intro hrough
  have hNat : π ∣ roughPart w D := Int.natCast_dvd.mp hrough
  have hDabs : π ∣ D.natAbs := Nat.dvd_trans hNat (roughPart_dvd_natAbs hD)
  exact hDπ (Int.natCast_dvd.mpr hDabs)


private lemma rowDirections_translation_response_unit_at {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (c : Fin m → ℤ)
    (hscale : ∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d)
    (hcpos : ∀ d, 0 < c d)
    (hcoef : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (hdirs : dirs.Valid)
    (tests : Finset (IntegerPolynomial q)) (hdt : dirs.tests ⊆ tests)
    (p : Fin q → ℕ) (hgood : GoodTuple S C.gap N tests dirs.poly p)
    (R I : Fin r) (hR : R ≠ Sh.star) (hIR : I ≠ R) :
    ResponseUnit N (FromArithmetic.masterScaleV S.core.parameters N C.gap)
      tests p (rowForm (chainScale S.core.parameters C a N) (Sh.row I) p
        (dirs.translation (chainScale S.core.parameters C a N)
          (directionModulus S N dirs.poly p) p R)) := by
  classical
  let w := N + 1
  let e := S.primeStage.e0 N
  let W := primorial w
  let Wpow := W ^ (e + 1)
  let Dval := evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))
  let rough := roughPart w Dval
  let Mp := directionModulus S N dirs.poly p
  let dval := evalIntegerPolynomial (dirs.targetResponse R) (fun i => (p i : ℤ))
  let Epoly := templateResponse (Sh.row I) (dirs.w R)
  let Eval := evalIntegerPolynomial Epoly (fun i => (p i : ℤ))
  have hDtests : dirs.poly ∈ tests := hdt (by simp [RowDirections.tests])
  have hDne : Dval ≠ 0 := hgood.2.2.1 dirs.poly hDtests
  have hroughPos : 0 < rough := by dsimp [rough]; exact roughPart_pos w Dval
  have hEtests : Epoly ∈ tests := by
    apply hdt
    exact rowResponse_mem_tests dirs rfl hR hIR hdirs
  have hEvalNe : Eval ≠ 0 := hgood.2.2.1 Epoly hEtests
  have hdtests : dirs.targetResponse R ∈ tests :=
    hdt (targetResponse_mem_tests dirs hR hdirs)
  have hdne : dval ≠ 0 := hgood.2.2.1 (dirs.targetResponse R) hdtests
  have hDdvd : dval ∣ Dval := targetResponse_eval_dvd_poly dirs hR p
  have hsmall : ∀ π, π.Prime → π ≤ w → ¬ (((π ^ e : ℕ) : ℤ) ∣ Dval) := by
    intro π hπ hπw hdiv
    exact hgood.2.2.2 π hπ (by simpa [w] using hπw) hdiv
  have hcover := roughPart_covers_divisor (w := w) (e := e)
    (S.primeStage.e0_pos N) hDne hdne hDdvd hsmall
  obtain ⟨q, hquot, hqInt, hqpos, hqabs, hWqabs⟩ :=
    rowCoefficient_quotient (r := r) S C a N c hscale hcpos hcoef ((Sh.row I).anchor)
  obtain ⟨v, hnum, hWv, hvle⟩ :=
    exists_W_divisible_quotient (w := w) (e := e) (S.primeStage.e0_pos N)
      dval hdne rough hcover q (c ((Sh.row Sh.star).anchor)) Eval
  have hrow := rowForm_translation_response dirs (chainScale S.core.parameters C a N)
    (fun k => by
      rw [← hscale k]
      exact_mod_cast ne_of_gt (hcpos k)) Mp p R (Sh.row I) hdne
  have hIRat : chainScale S.core.parameters C a N ((Sh.row I).anchor) ≠ 0 := by
    rw [← hscale ((Sh.row I).anchor)]
    exact_mod_cast ne_of_gt (hcpos ((Sh.row I).anchor))
  have hStarRat : chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) ≠ 0 := by
    rw [← hscale ((Sh.row Sh.star).anchor)]
    exact_mod_cast ne_of_gt (hcpos ((Sh.row Sh.star).anchor))
  have hquot' : (S.core.parameters.M N : ℚ) /
      chainScale S.core.parameters C a N ((Sh.row I).anchor) = (Wpow : ℚ) * (q : ℚ) := by
    simpa [Wpow, W, w, e] using hquot
  have hdRat : (dval : ℚ) ≠ 0 := by exact_mod_cast hdne
  have hvRat : (v : ℚ) =
      ((Wpow : ℚ) * (q : ℚ) * (c ((Sh.row Sh.star).anchor) : ℚ) *
        (rough : ℚ) * (Eval : ℚ)) / (dval : ℚ) := by
    calc
      (v : ℚ) = ((dval : ℚ) * (v : ℚ)) / (dval : ℚ) := by field_simp [hdRat]
      _ = ((dval * v : ℤ) : ℚ) / (dval : ℚ) := by push_cast; rfl
      _ = ((((primorial w ^ (e + 1) : ℕ) : ℤ) * q *
          c ((Sh.row Sh.star).anchor) * rough * Eval : ℤ) : ℚ) /
            (dval : ℚ) := by rw [← hnum]; rfl
      _ = (Wpow : ℚ) * (q : ℚ) * (c ((Sh.row Sh.star).anchor) : ℚ) *
          (rough : ℚ) * (Eval : ℚ) / (dval : ℚ) := by simp [Wpow, W, w, e]
  have hformula : (Mp : ℚ) *
        (chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) /
          chainScale S.core.parameters C a N ((Sh.row I).anchor)) *
        ((Eval : ℚ) / (dval : ℚ)) = (v : ℚ) := by
    calc
      _ = ((S.core.parameters.M N : ℚ) /
          chainScale S.core.parameters C a N ((Sh.row I).anchor)) *
          (chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) : ℚ) *
          (rough : ℚ) * (Eval : ℚ) / (dval : ℚ) := by
        dsimp [Mp, directionModulus, Dval, rough, w]
        field_simp [hIRat, hStarRat, hdRat] <;> push_cast <;> ring
      _ = (v : ℚ) := by
        rw [hquot', ← hscale ((Sh.row Sh.star).anchor)]
        exact hvRat.symm
  have hval : rowForm (chainScale S.core.parameters C a N) (Sh.row I) p
      (dirs.translation (chainScale S.core.parameters C a N) Mp p R) = (v : ℚ) := by
    calc
      _ = (Mp : ℚ) *
          (chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) /
            chainScale S.core.parameters C a N ((Sh.row I).anchor)) *
          ((Eval : ℚ) / (dval : ℚ)) := hrow
      _ = (v : ℚ) := hformula
  have hnumNe : ((Wpow : ℤ) * q * c ((Sh.row Sh.star).anchor) *
      (rough : ℤ) * Eval) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · exact_mod_cast (pow_pos (primorial_pos w) (e + 1)).ne'
          · exact hqpos.ne'
        · exact (hcpos ((Sh.row Sh.star).anchor)).ne'
      · exact_mod_cast (Nat.ne_of_gt hroughPos)
    · exact hEvalNe
  have hvne : v ≠ 0 := by
    intro hv
    rw [hv, mul_zero] at hnum
    exact hnumNe hnum
  have hMpow : ∃ j, S.core.parameters.M N = (primorial (N + 1)) ^ j :=
    S.core.modulus_power N
  have hWnot : ∀ π, π.Prime → N + 1 < π → ¬ π ∣ primorial (N + 1) := by
    intro π hπ hπlo hπW
    exact (Nat.not_le_of_gt hπlo) (hπ.dvd_primorial_iff.mp hπW)
  have hNoWpow : ∀ π, π.Prime → N + 1 < π →
      ¬ (π : ℤ) ∣ (Wpow : ℤ) := by
    intro π hπ hπlo hπWpow
    exact hWnot π hπ hπlo (hπ.dvd_of_dvd_pow (Int.natCast_dvd.mp hπWpow))
  have hNoM : ∀ π, π.Prime → N + 1 < π → ¬ (π : ℤ) ∣ (S.core.parameters.M N : ℤ) := by
    intro π hπ hπlo hπM
    obtain ⟨j, hj⟩ := hMpow
    have hNat : π ∣ S.core.parameters.M N := Int.natCast_dvd.mp hπM
    rw [hj] at hNat
    exact hWnot π hπ hπlo (hπ.dvd_of_dvd_pow hNat)
  have hqDivM : (q : ℤ) ∣ (S.core.parameters.M N : ℤ) := by
    refine ⟨(Wpow : ℤ) * c ((Sh.row I).anchor), ?_⟩
    calc
      (S.core.parameters.M N : ℤ) = (Wpow : ℤ) * c ((Sh.row I).anchor) * q := by
        simpa [Wpow, W, w, e] using hqInt
      _ = q * ((Wpow : ℤ) * c ((Sh.row I).anchor)) := by ring
  have hNoQ : ∀ π, π.Prime → N + 1 < π → ¬ (π : ℤ) ∣ q := by
    intro π hπ hπlo hπq
    apply hNoM π hπ hπlo
    exact dvd_trans hπq hqDivM
  have hcaDivM : c ((Sh.row Sh.star).anchor) ∣ (S.core.parameters.M N : ℤ) := by
    apply dvd_trans ?_ (hcoef ((Sh.row Sh.star).anchor))
    exact ⟨((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ), by ring⟩
  have hNoCa : ∀ π, π.Prime → N + 1 < π →
      ¬ (π : ℤ) ∣ c ((Sh.row Sh.star).anchor) := by
    intro π hπ hπlo hπca
    apply hNoM π hπ hπlo
    exact dvd_trans hπca hcaDivM
  unfold ResponseUnit
  rw [hval]
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hvne
  · simp
  · intro π hπ hπlo hπV hOff
    have hDπ : ¬ (π : ℤ) ∣ Dval := hOff dirs.poly hDtests
    have hNoRough : ¬ (π : ℤ) ∣ (rough : ℤ) :=
      prime_not_divides_large_roughPart hDne hπ (by omega) hDπ
    have hNoEval : ¬ (π : ℤ) ∣ Eval := hOff Epoly hEtests
    have hNoNum : ¬ (π : ℤ) ∣
        (Wpow : ℤ) * q * c ((Sh.row Sh.star).anchor) * (rough : ℤ) * Eval := by
      have hNoWQ := natPrime_not_dvd_int_mul hπ
        (hNoWpow π hπ hπlo) (hNoQ π hπ hπlo)
      have hNoWQCa := natPrime_not_dvd_int_mul hπ hNoWQ (hNoCa π hπ hπlo)
      have hNoWQCaRough := natPrime_not_dvd_int_mul hπ hNoWQCa hNoRough
      exact natPrime_not_dvd_int_mul hπ hNoWQCaRough hNoEval
    intro hπv
    apply hNoNum
    have hπv' : (π : ℤ) ∣ v := by simpa using hπv
    have hπmul : (π : ℤ) ∣ dval * v := by
      simpa [mul_comm] using dvd_mul_of_dvd_right hπv' dval
    rw [← hnum] at hπmul
    simpa [Wpow, W, w, e] using hπmul

private lemma rowDirections_root_response_unit_at {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (c : Fin m → ℤ)
    (hscale : ∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d)
    (hcpos : ∀ d, 0 < c d)
    (hcoef : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (hdirs : dirs.Valid)
    (tests : Finset (IntegerPolynomial q)) (hdt : dirs.tests ⊆ tests)
    (p : Fin q → ℕ) (hgood : GoodTuple S C.gap N tests dirs.poly p)
    (I : Fin r) (hI : I ≠ Sh.star) :
    ResponseUnit N (FromArithmetic.masterScaleV S.core.parameters N C.gap)
      tests p (rowForm (chainScale S.core.parameters C a N) (Sh.row I) p
        (dirs.rootTranslation (chainScale S.core.parameters C a N)
          (S.core.parameters.M N) p)) := by
  classical
  let W := primorial (N + 1)
  let Wpow := W ^ (S.primeStage.e0 N + 1)
  let Epoly := templateResponse (Sh.row I) dirs.w0
  let Eval := evalIntegerPolynomial Epoly (fun i => (p i : ℤ))
  obtain ⟨q, hquot, hqInt, hqpos, hqabs, hWqabs⟩ :=
    rowCoefficient_quotient (r := r) S C a N c hscale hcpos hcoef ((Sh.row I).anchor)
  have hEtests : Epoly ∈ tests := hdt (rootRowResponse_mem_tests dirs hI hdirs)
  have hEvalNe : Eval ≠ 0 := hgood.2.2.1 Epoly hEtests
  let v : ℤ := (Wpow : ℤ) * q * c ((Sh.row Sh.star).anchor) * Eval
  have hWpowDvd : (W : ℤ) ∣ (Wpow : ℤ) := by
    apply Int.natCast_dvd_natCast.mpr
    exact dvd_pow_self W (by omega : S.primeStage.e0 N + 1 ≠ 0)
  have hWv : (W : ℤ) ∣ v := by
    apply hWpowDvd.trans
    refine ⟨q * c ((Sh.row Sh.star).anchor) * Eval, ?_⟩
    dsimp [v]
    ring
  have hrow := rowForm_rootTranslation_response dirs
    (chainScale S.core.parameters C a N)
    (fun k => by
      rw [← hscale k]
      exact_mod_cast ne_of_gt (hcpos k))
    (S.core.parameters.M N) p (Sh.row I)
  have hvalue : rowForm (chainScale S.core.parameters C a N) (Sh.row I) p
      (dirs.rootTranslation (chainScale S.core.parameters C a N)
        (S.core.parameters.M N) p) = (v : ℚ) := by
    have hvRat : (v : ℚ) = ((Wpow : ℚ) * (q : ℚ) *
        (c ((Sh.row Sh.star).anchor) : ℚ) * (Eval : ℚ)) := by
      simp [v, Wpow, W]
    calc
      rowForm (chainScale S.core.parameters C a N) (Sh.row I) p
          (dirs.rootTranslation (chainScale S.core.parameters C a N)
            (S.core.parameters.M N) p) =
        (S.core.parameters.M N : ℚ) *
          (chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) /
            chainScale S.core.parameters C a N ((Sh.row I).anchor)) * (Eval : ℚ) := by
          simpa [Epoly, Eval] using hrow
      _ = ((S.core.parameters.M N : ℚ) /
          chainScale S.core.parameters C a N ((Sh.row I).anchor)) *
          (chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) : ℚ) *
          (Eval : ℚ) := by
            field_simp [ne_of_gt (hcpos ((Sh.row I).anchor))]
      _ = (v : ℚ) := by
          rw [hquot, ← hscale ((Sh.row Sh.star).anchor)]
          exact hvRat.symm
  have hnumNe : (Wpow : ℤ) * q * c ((Sh.row Sh.star).anchor) * Eval ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact_mod_cast (pow_pos (primorial_pos (N + 1))
            (S.primeStage.e0 N + 1)).ne'
        · exact hqpos.ne'
      · exact (hcpos ((Sh.row Sh.star).anchor)).ne'
    · exact hEvalNe
  have hvne : v ≠ 0 := by
    intro hv
    apply hnumNe
    simpa [v] using hv
  have hMpow : ∃ j, S.core.parameters.M N = (primorial (N + 1)) ^ j :=
    S.core.modulus_power N
  have hWnot : ∀ π, π.Prime → N + 1 < π → ¬ π ∣ primorial (N + 1) := by
    intro π hπ hπlo hπW
    exact (Nat.not_le_of_gt hπlo) (hπ.dvd_primorial_iff.mp hπW)
  have hNoWpow : ∀ π, π.Prime → N + 1 < π → ¬ (π : ℤ) ∣ (Wpow : ℤ) := by
    intro π hπ hπlo hπWpow
    exact hWnot π hπ hπlo (hπ.dvd_of_dvd_pow (Int.natCast_dvd.mp hπWpow))
  have hNoM : ∀ π, π.Prime → N + 1 < π → ¬ (π : ℤ) ∣ (S.core.parameters.M N : ℤ) := by
    intro π hπ hπlo hπM
    obtain ⟨j, hj⟩ := hMpow
    have hNat : π ∣ S.core.parameters.M N := Int.natCast_dvd.mp hπM
    rw [hj] at hNat
    exact hWnot π hπ hπlo (hπ.dvd_of_dvd_pow hNat)
  have hqDivM : (q : ℤ) ∣ (S.core.parameters.M N : ℤ) := by
    refine ⟨(Wpow : ℤ) * c ((Sh.row I).anchor), ?_⟩
    calc
      (S.core.parameters.M N : ℤ) = (Wpow : ℤ) * c ((Sh.row I).anchor) * q := by
        simpa [Wpow, W] using hqInt
      _ = q * ((Wpow : ℤ) * c ((Sh.row I).anchor)) := by ring
  have hcaDivM : c ((Sh.row Sh.star).anchor) ∣ (S.core.parameters.M N : ℤ) := by
    apply dvd_trans ?_ (hcoef ((Sh.row Sh.star).anchor))
    exact ⟨((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ), by ring⟩
  have hNoEval : ∀ π, π.Prime → N + 1 < π →
      (∀ P ∈ tests, ¬ (π : ℤ) ∣ evalIntegerPolynomial P (fun i => (p i : ℤ))) →
      ¬ (π : ℤ) ∣ Eval := by
    intro π hπ hπlo hOff
    exact hOff Epoly hEtests
  unfold ResponseUnit
  rw [hvalue]
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hvne
  · simp
  · intro π hπ hπlo hπV hOff
    have hNoQ : ¬ (π : ℤ) ∣ q := by
      intro hdiv
      apply hNoM π hπ hπlo
      exact dvd_trans hdiv hqDivM
    have hNoCa : ¬ (π : ℤ) ∣ c ((Sh.row Sh.star).anchor) := by
      intro hdiv
      apply hNoM π hπ hπlo
      exact dvd_trans hdiv hcaDivM
    have hNoE := hNoEval π hπ hπlo hOff
    have hNoNum : ¬ (π : ℤ) ∣
        (Wpow : ℤ) * q * c ((Sh.row Sh.star).anchor) * Eval := by
      have hNoWQ := natPrime_not_dvd_int_mul hπ (hNoWpow π hπ hπlo) hNoQ
      have hNoWQCa := natPrime_not_dvd_int_mul hπ hNoWQ hNoCa
      exact natPrime_not_dvd_int_mul hπ hNoWQCa hNoE
    have hNoV : ¬ (π : ℤ) ∣ v := by
      intro hdiv
      apply hNoNum
      simpa [v] using hdiv
    simpa using hNoV

private lemma rowDirections_root_translation_integer_at {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (c : Fin m → ℤ)
    (hscale : ∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d)
    (hcpos : ∀ d, 0 < c d)
    (hcoef : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (p : Fin q → ℕ) (k : Fin m) :
    ∃ v : ℤ,
      (v : ℚ) = dirs.rootTranslation (chainScale S.core.parameters C a N)
        (S.core.parameters.M N) p k ∧
      (primorial (N + 1) : ℤ) ∣ v ∧
      v.natAbs ≤ S.core.parameters.M N * (c ((Sh.row Sh.star).anchor)).natAbs *
        (evalIntegerPolynomial (dirs.w0 k) (fun i => (p i : ℤ))).natAbs := by
  classical
  let W := primorial (N + 1)
  let Wpow := W ^ (S.primeStage.e0 N + 1)
  let wval := evalIntegerPolynomial (dirs.w0 k) (fun i => (p i : ℤ))
  obtain ⟨q, hquot, hqInt, hqpos, hqabs, hWqabs⟩ :=
    rowCoefficient_quotient (r := r) S C a N c hscale hcpos hcoef k
  let v : ℤ := (Wpow : ℤ) * q * c ((Sh.row Sh.star).anchor) * wval
  have hval : (v : ℚ) = dirs.rootTranslation (chainScale S.core.parameters C a N)
      (S.core.parameters.M N) p k := by
    calc
      (v : ℚ) = (Wpow : ℚ) * (q : ℚ) * (c ((Sh.row Sh.star).anchor) : ℚ) *
          (wval : ℚ) := by simp [v, Wpow, W]
      _ = ((S.core.parameters.M N : ℚ) / chainScale S.core.parameters C a N k) *
          chainScale S.core.parameters C a N ((Sh.row Sh.star).anchor) * (wval : ℚ) := by
        have hquot' : (S.core.parameters.M N : ℚ) / chainScale S.core.parameters C a N k =
            (Wpow : ℚ) * (q : ℚ) := by simpa [Wpow, W] using hquot
        rw [← hquot', hscale ((Sh.row Sh.star).anchor)]
      _ = dirs.rootTranslation (chainScale S.core.parameters C a N)
          (S.core.parameters.M N) p k := by
        unfold RowDirections.rootTranslation
        rw [← hscale k]
        field_simp [ne_of_gt (hcpos k)] <;> ring
  have hWpowDvd : (W : ℤ) ∣ (Wpow : ℤ) := by
    apply Int.natCast_dvd_natCast.mpr
    exact dvd_pow_self W (by omega : S.primeStage.e0 N + 1 ≠ 0)
  have hWv : (W : ℤ) ∣ v := by
    apply hWpowDvd.trans
    refine ⟨q * c ((Sh.row Sh.star).anchor) * wval, ?_⟩
    dsimp [v]
    ring
  have hsize : v.natAbs ≤ Wpow * q.natAbs *
      (c ((Sh.row Sh.star).anchor)).natAbs * wval.natAbs := by
    simp [v, Wpow, W, Int.natAbs_mul, Int.natAbs_of_nonneg hqpos.le,
      Int.natAbs_of_nonneg (hcpos ((Sh.row Sh.star).anchor)).le,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hsize' : v.natAbs ≤ S.core.parameters.M N *
      (c ((Sh.row Sh.star).anchor)).natAbs * wval.natAbs := by
    calc
      v.natAbs ≤ Wpow * q.natAbs * (c ((Sh.row Sh.star).anchor)).natAbs * wval.natAbs := hsize
      _ ≤ S.core.parameters.M N * (c ((Sh.row Sh.star).anchor)).natAbs * wval.natAbs := by
        simpa [Wpow, W, Nat.mul_assoc] using Nat.mul_le_mul_right
          ((c ((Sh.row Sh.star).anchor)).natAbs * wval.natAbs) hWqabs
  exact ⟨v, hval, hWv, hsize'⟩

private lemma rowDirections_coefficients_eventually {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, ∃ c : Fin m → ℤ,
      (∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d) ∧
      (∀ d, 0 < c d) ∧
      ∀ d, ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ) := by
  filter_upwards [S.core.chain_coefficients, S.gapStage.coefficient_divides_modulus]
    with N hchain hdiv
  obtain ⟨c, hc, hcpos, _hratio⟩ := hchain m C a ha
  refine ⟨c, ?_, hcpos, ?_⟩
  · simpa [chainScale] using hc
  · exact hdiv m C a ha c hc

private lemma rowDirections_integer_algebraic_facts_eventually {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset)
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (hdirs : dirs.Valid)
    (tests : Finset (IntegerPolynomial q)) (hdt : dirs.tests ⊆ tests) :
    ∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      (∀ R k, R ≠ Sh.star → ∃ v : ℤ,
        (v : ℚ) = dirs.translation (chainScale S.core.parameters C a N)
          (directionModulus S N dirs.poly p) p R k ∧
        (primorial (N + 1) : ℤ) ∣ v ∧
        v.natAbs ≤ ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ rowDirectionsSizeExponent dirs) ∧
      (∀ k, ∃ v : ℤ,
        (v : ℚ) = dirs.rootTranslation (chainScale S.core.parameters C a N)
          (S.core.parameters.M N) p k ∧
        (primorial (N + 1) : ℤ) ∣ v ∧
        v.natAbs ≤ ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ rowDirectionsSizeExponent dirs) ∧
      directionModulus S N dirs.poly p ≤
        ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ rowDirectionsSizeExponent dirs ∧
      (∀ R, R ≠ Sh.star → rowForm (chainScale S.core.parameters C a N)
        (Sh.row Sh.star) p
        (dirs.translation (chainScale S.core.parameters C a N)
          (directionModulus S N dirs.poly p) p R) = directionModulus S N dirs.poly p) ∧
      (∀ R, R ≠ Sh.star → rowForm (chainScale S.core.parameters C a N)
        (Sh.row R) p
        (dirs.translation (chainScale S.core.parameters C a N)
          (directionModulus S N dirs.poly p) p R) = 0) ∧
      rowForm (chainScale S.core.parameters C a N) (Sh.row Sh.star) p
        (dirs.rootTranslation (chainScale S.core.parameters C a N)
          (S.core.parameters.M N) p) = 0 := by
  have hcoeffEvent := rowDirections_coefficients_eventually S C a ha
  filter_upwards [hcoeffEvent] with N hcoeff
  obtain ⟨c, hscale, hcpos, hcoef⟩ := hcoeff
  intro p hgood
  let w := N + 1
  let eD := polynomialEvalExponent dirs.poly
  let budget := rowDirectionsEvalBudget dirs
  let B := rowDirectionsSizeExponent dirs
  let size := (S.primeStage.pool N C.gap).upper +
    FromArithmetic.masterScaleV S.core.parameters N C.gap
  let Dval := evalIntegerPolynomial dirs.poly (fun i => (p i : ℤ))
  let rough := roughPart w Dval
  have hVnat : 2 ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap := by
    unfold FromArithmetic.masterScaleV
    omega
  have hSize : 2 ≤ size := by dsimp [size]; omega
  have hMle : S.core.parameters.M N ≤ size := by
    dsimp [size, FromArithmetic.masterScaleV]
    omega
  have hUpper : (S.primeStage.pool N C.gap).upper ≤ size := by
    dsimp [size]
    exact Nat.le_add_right _ _
  have hcoords : ∀ i, ((p i : ℤ).natAbs) ≤ size := by
    intro i
    simp
    exact (Nat.le_of_lt (hgood.1 i).2.1).trans hUpper
  have hDtest : dirs.poly ∈ tests := hdt (by simp [RowDirections.tests])
  have hDne : Dval ≠ 0 := hgood.2.2.1 dirs.poly hDtest
  have hDsize : Dval.natAbs ≤ size ^ eD :=
    polynomialEvalExponent_spec dirs.poly size hSize
      (fun i => (p i : ℤ)) hcoords
  have hroughDiv : rough ∣ Dval.natAbs := roughPart_dvd_natAbs (w := w) hDne
  have hroughSize : rough ≤ size ^ eD :=
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hDne) hroughDiv).trans hDsize
  have hDExponent : eD ≤ budget := rowDirections_evalExponent_poly_le_budget dirs
  have hMp : directionModulus S N dirs.poly p ≤ size ^ B := by
    change S.core.parameters.M N * rough ≤ size ^ B
    calc
      S.core.parameters.M N * rough ≤ size * size ^ eD := Nat.mul_le_mul hMle hroughSize
      _ = size ^ (eD + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      _ ≤ size ^ B := Nat.pow_le_pow_right (by omega : 0 < size) (by
        dsimp [B, rowDirectionsSizeExponent]
        omega)
  have hcaSize : ∀ k, (c k).natAbs ≤ S.core.parameters.M N := by
    intro k
    exact rowCoefficient_natAbs_le_modulus S N c hcpos hcoef k
  have hcaSizeBound : ∀ k, (c k).natAbs ≤ size := by
    intro k
    exact (hcaSize k).trans hMle
  have hcRat : ∀ k, chainScale S.core.parameters C a N k ≠ 0 := by
    intro k
    rw [← hscale k]
    exact_mod_cast ne_of_gt (hcpos k)
  have hWrootExponent : ∀ k,
      polynomialEvalExponent (dirs.w0 k) ≤ budget :=
    fun k => rowDirections_evalExponent_w0_le_budget dirs k
  have hWExponent : ∀ R k,
      polynomialEvalExponent (dirs.w R k) ≤ budget :=
    fun R k => rowDirections_evalExponent_w_le_budget dirs R k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R k hR
    obtain ⟨v, hv, hWv, hvle⟩ :=
      rowDirections_translation_integer_at S C a N c hscale hcpos hcoef
        dirs hdirs tests hdt p hgood R hR k
    have hquot := rowCoefficient_quotient (r := r) S C a N c hscale hcpos hcoef k
    obtain ⟨q, hq, hqInt, hqpos, hqabs, hWqabs⟩ := hquot
    have hWbound := polynomialEvalExponent_spec (dirs.w R k) size hSize
      (fun i => (p i : ℤ)) hcoords
    have hWexp := rowDirections_evalExponent_w_le_budget dirs R k
    have hroughW : rough *
        (evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ))).natAbs ≤
        size ^ (eD + polynomialEvalExponent (dirs.w R k)) := by
      calc
        _ ≤ size ^ eD * size ^ polynomialEvalExponent (dirs.w R k) :=
          Nat.mul_le_mul hroughSize hWbound
        _ = _ := by rw [← Nat.pow_add]
    have hbudgetExp : 2 + eD + polynomialEvalExponent (dirs.w R k) ≤ B := by
      dsimp [B, rowDirectionsSizeExponent, budget]
      omega
    have hnumBound :
        S.core.parameters.M N * (c ((Sh.row Sh.star).anchor)).natAbs * rough *
          (evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ))).natAbs ≤
        size ^ B := by
      calc
        _ ≤ size ^ (2 + eD + polynomialEvalExponent (dirs.w R k)) :=
          by
            simpa [Nat.mul_assoc, Nat.add_assoc] using
              nat_mul_mul_le_power_budget (by omega : 1 ≤ size) hMle
                (hcaSizeBound (Sh.row Sh.star).anchor) hroughW
        _ ≤ size ^ B := Nat.pow_le_pow_right (by omega : 0 < size) hbudgetExp
    exact ⟨v, hv, hWv, hvle.trans hnumBound⟩
  · intro k
    obtain ⟨v, hv, hWv, hvle⟩ :=
      rowDirections_root_translation_integer_at S C a N c hscale hcpos hcoef dirs p k
    have hW0bound := polynomialEvalExponent_spec (dirs.w0 k) size hSize
      (fun i => (p i : ℤ)) hcoords
    have hW0exp := rowDirections_evalExponent_w0_le_budget dirs k
    have hbudgetExp : 2 + polynomialEvalExponent (dirs.w0 k) ≤ B := by
      dsimp [B, rowDirectionsSizeExponent, budget]
      omega
    have hnumBound :
        S.core.parameters.M N * (c ((Sh.row Sh.star).anchor)).natAbs *
          (evalIntegerPolynomial (dirs.w0 k) (fun i => (p i : ℤ))).natAbs ≤
        size ^ B := by
      calc
        _ ≤ size ^ (2 + polynomialEvalExponent (dirs.w0 k)) :=
          nat_mul_mul_le_power_budget (by omega : 1 ≤ size) hMle
            (hcaSizeBound (Sh.row Sh.star).anchor) hW0bound
        _ ≤ size ^ B := Nat.pow_le_pow_right (by omega : 0 < size) hbudgetExp
    exact ⟨v, hv, hWv, hvle.trans hnumBound⟩
  · exact hMp
  · exact (rowDirections_response_identities_at S C a N (chainScale S.core.parameters C a N)
      hcRat dirs hdirs tests hdt p hgood).1
  · exact (rowDirections_response_identities_at S C a N (chainScale S.core.parameters C a N)
      hcRat dirs hdirs tests hdt p hgood).2.1
  · exact (rowDirections_response_identities_at S C a N (chainScale S.core.parameters C a N)
      hcRat dirs hdirs tests hdt p hgood).2.2

private lemma rowDirections_integer_facts_eventually {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset)
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (hdirs : dirs.Valid)
    (tests : Finset (IntegerPolynomial q)) (hdt : dirs.tests ⊆ tests) :
    ∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      IntegerDirectionFacts S C a N dirs tests (rowDirectionsSizeExponent dirs) p := by
  have hcoeffEvent := rowDirections_coefficients_eventually S C a ha
  have hAlgebraicEvent :=
    rowDirections_integer_algebraic_facts_eventually S C a ha dirs hdirs tests hdt
  filter_upwards [hcoeffEvent, hAlgebraicEvent] with N hcoeff hAlgebraic
  obtain ⟨c, hscale, hcpos, hcoef⟩ := hcoeff
  intro p hgood
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hAlgebraic p hgood
  unfold IntegerDirectionFacts
  exact ⟨h1, h2, h3, h4, h5, h6,
    (fun R hR I hIR =>
      rowDirections_translation_response_unit_at S C a N c hscale hcpos hcoef
        dirs hdirs tests hdt p hgood R hR I hIR),
    (fun I hI =>
      rowDirections_root_response_unit_at S C a N c hscale hcpos hcoef
        dirs hdirs tests hdt p hgood I hI)⟩

theorem row_directions_integer_core {m q r : ℕ} (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (hdirs : dirs.Valid) (tests : Finset (IntegerPolynomial q))
    (htests : ∀ P ∈ tests, P ≠ 0) (hdt : dirs.tests ⊆ tests) :
    ∃ B : ℕ, ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
      (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s),
      TestsListed Dm ι tests → ∀ (C : MasterChain K m) (a : Fin m → ℚ),
      (∀ d, a d ∈ Aset) →
      Tendsto (fun N => gapSlotProbability S C.gap N fun p =>
        ¬ GoodTuple S C.gap N tests dirs.poly p) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
        directionModulus S N dirs.poly p ∣ S.core.parameters.H N C.gap) ∧
      ∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
        IntegerDirectionFacts S C a N dirs tests B p := by
  refine ⟨rowDirectionsSizeExponent dirs, ?_⟩
  intro K s Aset Dm S ι hlisted C a ha
  exact ⟨rowDirections_bad_probability_tendsto dirs tests hdt S ι hlisted C.gap,
    rowDirections_modulus_divides_gap S ι C a ha dirs tests hlisted hdt,
    rowDirections_integer_facts_eventually S C a ha dirs hdirs tests hdt⟩

end HindmanSumsProducts
