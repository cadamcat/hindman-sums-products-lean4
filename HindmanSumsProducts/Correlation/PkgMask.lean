import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for the §4 proof package `Mask` (owned by its proof lane). -/

namespace HindmanSumsProducts

open scoped BigOperators
open FromArithmetic

/-- The initial additive row encoding the indicator vector of a nonempty mask. -/
noncomputable def initialMaskRow {m : ℕ} (U : Finset (Fin m)) (hU : U.Nonempty) :
    RowTemplate m 0 where
  entry k := if k ∈ U then some (fun _ : Fin 0 => 0) else none
  support_nonempty := by
    rcases hU with ⟨k, hk⟩
    exact ⟨k, by simp [hk]⟩
  slots_disjoint := by
    intro k k' e e' hkk he he' i
    exact Fin.elim0 i

theorem initialMaskRow_support {m : ℕ} (U : Finset (Fin m)) (hU : U.Nonempty) :
    (initialMaskRow U hU).support = U := by
  ext k
  simp [RowTemplate.support, initialMaskRow]

theorem initialMaskRow_self_parallel {m q : ℕ} (T : RowTemplate m q) :
    T.Parallel T := by
  refine ⟨rfl, 0, ?_⟩
  intro k e e' he he' i
  have heq : e = e' := Option.some.inj (he.symm.trans he')
  subst e'
  simp

theorem initialMaskRow_parallel_iff {m : ℕ} (U V : Finset (Fin m))
    (hU : U.Nonempty) (hV : V.Nonempty) :
    (initialMaskRow U hU).Parallel (initialMaskRow V hV) ↔ U = V := by
  constructor
  · intro h
    calc
      U = (initialMaskRow U hU).support := (initialMaskRow_support U hU).symm
      _ = (initialMaskRow V hV).support := h.1
      _ = V := initialMaskRow_support V hV
  · intro h
    subst V
    exact initialMaskRow_self_parallel _

theorem card_nonempty_mask_subsets (m : ℕ) :
    Fintype.card {U : Finset (Fin m) // U.Nonempty} = maskCount m := by
  classical
  let α := Finset (Fin m)
  let e : {U : α // U.Nonempty} ≃ {U : α // U ≠ ∅} :=
    Equiv.subtypeEquivRight fun U => Finset.nonempty_iff_ne_empty
  calc
    Fintype.card {U : α // U.Nonempty} = Fintype.card {U : α // U ≠ ∅} :=
      Fintype.card_congr e
    _ = Fintype.card α - Fintype.card {U : α // U = ∅} :=
      Fintype.card_subtype_compl (fun U => U = ∅)
    _ = 2 ^ m - 1 := by simp [α, Fintype.card_finset]
    _ = maskCount m := rfl

noncomputable def maskIndexEquiv (m : ℕ) :
    {U : Finset (Fin m) // U.Nonempty} ≃ Fin (maskCount m) :=
  Fintype.equivFinOfCardEq (card_nonempty_mask_subsets m)

theorem maskCount_le_maskRowBound (m : ℕ) : maskCount m ≤ maskRowBound m := by
  unfold maskRowBound
  calc
    maskCount m = maskCount m * 1 := by simp
    _ ≤ maskCount m * 2 ^ maskCount m :=
      Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by decide))

theorem exists_mask_substitution_coordinates {m : ℕ} (Jstar U : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) :
    (∃ u, u ∈ Jstar ∧ u ∉ U) ∨
      ∃ u v, u ∈ Jstar ∧ v ∈ Jstar ∧ u ≠ v := by
  by_cases hsub : Jstar ⊆ U
  · right
    exact Finset.one_lt_card_iff.mp (by omega)
  · left
    exact Finset.not_subset.mp hsub

theorem mask_product_update_outside {m : ℕ} (U : Finset (Fin m)) (u : Fin m)
    (hu : u ∉ U) (z : Fin m → ℤ) (w : ℤ) :
    (∏ k ∈ U, Function.update z u w k) = ∏ k ∈ U, z k :=
  Finset.prod_update_of_notMem hu z w

theorem mask_product_balanced_update {m : ℕ} (U : Finset (Fin m)) (u v : Fin m)
    (hu : u ∈ U) (hv : v ∈ U) (huv : u ≠ v) (z : Fin m → ℤ) (p : ℤ)
    (hdiv : p ∣ z u) :
    (∏ k ∈ U, Function.update (Function.update z u (z u / p)) v (p * z v) k) =
      ∏ k ∈ U, z k := by
  classical
  let z₁ := Function.update z u (z u / p)
  let z₂ := Function.update z₁ v (p * z v)
  have huErase : u ∈ U.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
  have hvErase : v ∉ U.erase v := by simp
  have huRest : u ∉ (U.erase v).erase u := by simp
  have hRest :
      (∏ k ∈ (U.erase v).erase u, z₁ k) = ∏ k ∈ (U.erase v).erase u, z k := by
    dsimp [z₁]
    exact Finset.prod_update_of_notMem huRest z (z u / p)
  have hVprod :
      (∏ k ∈ U.erase v, z₂ k) = ∏ k ∈ U.erase v, z₁ k := by
    dsimp [z₂]
    exact Finset.prod_update_of_notMem hvErase z₁ (p * z v)
  have hOriginal :
      (∏ k ∈ U, z k) = z v * (z u * ∏ k ∈ (U.erase v).erase u, z k) := by
    calc
      (∏ k ∈ U, z k) = z v * ∏ k ∈ U.erase v, z k :=
        (Finset.mul_prod_erase U z hv).symm
      _ = z v * (z u * ∏ k ∈ (U.erase v).erase u, z k) := by
        rw [← Finset.mul_prod_erase (U.erase v) z huErase]
  have hChanged :
      (∏ k ∈ U, z₂ k) = (p * z v) * ((z u / p) * ∏ k ∈ (U.erase v).erase u, z k) := by
    calc
      (∏ k ∈ U, z₂ k) = z₂ v * ∏ k ∈ U.erase v, z₂ k :=
        (Finset.mul_prod_erase U z₂ hv).symm
      _ = (p * z v) * ∏ k ∈ U.erase v, z₁ k := by
        simp only [z₂, Function.update_self, hVprod]
      _ = (p * z v) * ((z u / p) * ∏ k ∈ (U.erase v).erase u, z₁ k) := by
        rw [← Finset.mul_prod_erase (U.erase v) z₁ huErase]
        simp [z₁]
      _ = (p * z v) * ((z u / p) * ∏ k ∈ (U.erase v).erase u, z k) := by
        rw [hRest]
      _ = _ := rfl
  have hcancel : p * (z u / p) = z u := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiv
  calc
    (∏ k ∈ U, Function.update (Function.update z u (z u / p)) v (p * z v) k) =
        (p * z v) * ((z u / p) * ∏ k ∈ (U.erase v).erase u, z k) := hChanged
    _ = z v * (z u * ∏ k ∈ (U.erase v).erase u, z k) := by
      calc
        _ = z v * ((p * (z u / p)) * ∏ k ∈ (U.erase v).erase u, z k) := by ring
        _ = _ := by rw [hcancel]
    _ = ∏ k ∈ U, z k := hOriginal.symm

theorem nuB_mul_eq_of_coprime_support (tailLaw : TailProductLaw) (p : ℕ)
    (hp : ∀ σ, tailLaw σ ≠ 0 → Nat.Coprime σ p) (y : ℤ) :
    nuB tailLaw ((p : ℤ) * y) = nuB tailLaw y := by
  unfold nuB
  apply tsum_congr
  intro σ
  by_cases hσ : tailLaw σ = 0
  · simp [hσ]
  · have hcop := hp σ hσ
    have hgcd : Int.gcd (σ : ℤ) (p : ℤ) = 1 := by
      rw [Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
      exact_mod_cast (Nat.coprime_iff_gcd_eq_one.mp hcop)
    have hdiv : ((σ : ℤ) ∣ (p : ℤ) * y) ↔ (σ : ℤ) ∣ y := by
      constructor
      · intro h
        exact Int.dvd_of_dvd_mul_right_of_gcd_one h hgcd
      · intro h
        exact dvd_mul_of_dvd_right h (p : ℤ)
    simp [hdiv]

theorem natCoprime_of_pos_lt_prime {σ p : ℕ} (hσ : 0 < σ) (hp : p.Prime)
    (hlt : σ < p) : Nat.Coprime σ p :=
  (Nat.coprime_of_lt_prime hσ.ne' hlt hp).symm

theorem nuB_div_eq_of_coprime_support (tailLaw : TailProductLaw) (p : ℕ)
    (hp : ∀ σ, tailLaw σ ≠ 0 → Nat.Coprime σ p) (y : ℤ)
    (hdiv : (p : ℤ) ∣ y) : nuB tailLaw (y / (p : ℤ)) = nuB tailLaw y := by
  have hcancel : (p : ℤ) * (y / (p : ℤ)) = y := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiv
  have h := nuB_mul_eq_of_coprime_support tailLaw p hp (y / (p : ℤ))
  rw [hcancel] at h
  exact h.symm

theorem nuB_mul_eq_of_prime_gt_support (tailLaw : TailProductLaw) (p V : ℕ)
    (hp : p.Prime) (hV : V < p)
    (hSupport : ∀ σ, tailLaw σ ≠ 0 → 1 ≤ σ ∧ σ ≤ V) (y : ℤ) :
    nuB tailLaw ((p : ℤ) * y) = nuB tailLaw y := by
  apply nuB_mul_eq_of_coprime_support
  intro σ hσ
  obtain ⟨hpos, hle⟩ := hSupport σ hσ
  exact natCoprime_of_pos_lt_prime (by omega) hp (lt_of_le_of_lt hle hV)

theorem nuB_div_eq_of_prime_gt_support (tailLaw : TailProductLaw) (p V : ℕ)
    (hp : p.Prime) (hV : V < p)
    (hSupport : ∀ σ, tailLaw σ ≠ 0 → 1 ≤ σ ∧ σ ≤ V) (y : ℤ)
    (hdiv : (p : ℤ) ∣ y) : nuB tailLaw (y / (p : ℤ)) = nuB tailLaw y := by
  apply nuB_div_eq_of_coprime_support tailLaw p ?_ y hdiv
  intro σ hσ
  obtain ⟨hpos, hle⟩ := hSupport σ hσ
  exact natCoprime_of_pos_lt_prime (by omega) hp (lt_of_le_of_lt hle hV)

theorem nuB_le_of_probability_support (tailLaw : TailProductLaw)
    (hNonneg : ∀ σ, 0 ≤ tailLaw σ) (hSummable : Summable tailLaw)
    (hMass : ∑' σ, tailLaw σ = 1) (V : ℕ)
    (hSupport : ∀ σ, tailLaw σ ≠ 0 → σ ≤ V) (y : ℤ) :
    nuB tailLaw y ≤ (V : ℝ) := by
  let term : ℕ → ℝ := fun σ => tailLaw σ * (σ : ℝ) * if (σ : ℤ) ∣ y then 1 else 0
  have hterm_nonneg (σ : ℕ) : 0 ≤ term σ := by
    dsimp [term]
    by_cases hdiv : (σ : ℤ) ∣ y
    · simp [hdiv]
      exact mul_nonneg (hNonneg σ) (by positivity)
    · simp [hdiv]
  have hterm_le (σ : ℕ) : term σ ≤ tailLaw σ * (V : ℝ) := by
    dsimp [term]
    by_cases hzero : tailLaw σ = 0
    · simp [hzero]
    · have hσ := hSupport σ hzero
      have hσR : (σ : ℝ) ≤ (V : ℝ) := by exact_mod_cast hσ
      by_cases hdiv : (σ : ℤ) ∣ y
      · simp [hdiv]
        exact mul_le_mul_of_nonneg_left hσR (hNonneg σ)
      · simp [hdiv]
        exact mul_nonneg (hNonneg σ) (by positivity)
  have hdom : Summable fun σ => tailLaw σ * (V : ℝ) := hSummable.mul_right _
  have hterm_summable : Summable term := by
    apply hdom.of_norm_bounded
    intro σ
    rw [Real.norm_eq_abs, abs_of_nonneg (hterm_nonneg σ)]
    exact hterm_le σ
  calc
    nuB tailLaw y = ∑' σ, term σ := by simp [nuB, term]
    _ ≤ ∑' σ, tailLaw σ * (V : ℝ) :=
      hterm_summable.tsum_le_tsum (fun σ => hterm_le σ) hdom
    _ = (∑' σ, tailLaw σ) * (V : ℝ) := hSummable.tsum_mul_right _
    _ = (V : ℝ) := by rw [hMass]; ring

private theorem harmonicNatLaw_support_upper (X W n : ℕ)
    (h : harmonicNatLaw X W n ≠ 0) : n < X ^ 2 := by
  by_contra hlt
  have hnot : ¬ (X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W) := by
    intro hcond
    exact hlt hcond.2.1
  exact h (by simp [harmonicNatLaw, hnot])

theorem parameterTailProductLaw_support_le {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n)) (σ : ℕ)
    (hσ : FromArithmetic.parameterTailProductLaw A N T σ ≠ 0) :
    σ ≤ ∏ j ∈ T, (A.X N j) ^ 2 := by
  classical
  by_contra hnot
  have hlarge : (∏ j ∈ T, (A.X N j) ^ 2) < σ := Nat.lt_of_not_ge hnot
  have hterm (t : Fin n → ℕ) :
      (if (∏ j ∈ T, t j) = σ then 1 else 0) *
          ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
    by_cases hprod : (∏ j ∈ T, t j) = σ
    · by_cases hall : ∀ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) ≠ 0
      · have hbound : (∏ j ∈ T, t j) ≤ ∏ j ∈ T, (A.X N j) ^ 2 := by
          apply Finset.prod_le_prod
          intro j hj
          exact Nat.le_of_lt (harmonicNatLaw_support_upper _ _ _ (hall j))
        have hsigma : σ ≤ ∏ j ∈ T, (A.X N j) ^ 2 := by rw [← hprod]; exact hbound
        exact False.elim (not_le_of_gt hlarge hsigma)
      · push_neg at hall
        obtain ⟨j, hj⟩ := hall
        have hprodZero :
            (∏ k : Fin n, harmonicNatLaw (A.X N k) (primorial (N + 1)) (t k)) = 0 := by
          exact Finset.prod_eq_zero (s := Finset.univ)
            (f := fun k => harmonicNatLaw (A.X N k) (primorial (N + 1)) (t k))
            (Finset.mem_univ j) hj
        simp [hprod, hprodZero]
    · simp [hprod]
  apply hσ
  unfold FromArithmetic.parameterTailProductLaw
  simp_rw [hterm]
  simp

theorem chainTail_support_le_masterScaleV {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (C : MasterChain n m) (d : Fin m) (σ : ℕ)
    (hσ : FromArithmetic.parameterTailProductLaw A N (C.block d).2.val σ ≠ 0) :
    σ ≤ FromArithmetic.masterScaleV A N C.gap := by
  let T := (C.block d).2.val
  let E := Finset.univ.filter (fun j : Fin n => j < C.gap)
  have hsubset : T ⊆ E := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, C.tails_before_gap d j hj⟩
  have hprod_le :
      (∏ j ∈ T, (A.X N j) ^ 2) ≤ ∏ j ∈ E, (A.X N j) ^ 2 := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsubset
    intro j hj hjnot
    exact Nat.one_le_pow 2 (A.X N j) (A.Xpos N j)
  have hmaster : (∏ j ∈ E, (A.X N j) ^ 2) ≤ FromArithmetic.masterScaleV A N C.gap := by
    dsimp [FromArithmetic.masterScaleV, E]
    omega
  exact (parameterTailProductLaw_support_le A N T σ hσ).trans (hprod_le.trans hmaster)

noncomputable def initialMaskShape {m : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) : RowShape m 0 (maskCount m) := by
  classical
  have hJne : Jstar.Nonempty := Finset.card_pos.mp (by omega)
  let E := maskIndexEquiv m
  exact {
    row := fun i => initialMaskRow (E.symm i).val (E.symm i).property
    star := E ⟨Jstar, hJne⟩
    nonparallel := by
      intro R I hRI hpar
      have hsupp : (E.symm R).val = (E.symm I).val :=
        (initialMaskRow_parallel_iff _ _ (E.symm R).property (E.symm I).property).mp hpar
      have hsub : E.symm R = E.symm I := Subtype.ext hsupp
      have hEq : R = I := by simpa using congrArg E hsub
      exact hRI hEq
  }

theorem initialMaskShape_star_support {m : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) :
    ((initialMaskShape Jstar hJ).row (initialMaskShape Jstar hJ).star).support = Jstar := by
  classical
  have hJne : Jstar.Nonempty := Finset.card_pos.mp (by omega)
  let E := maskIndexEquiv m
  change (initialMaskRow (E.symm (E ⟨Jstar, hJne⟩)).val
    (E.symm (E ⟨Jstar, hJne⟩)).property).support = Jstar
  rw [Equiv.symm_apply_apply]
  exact initialMaskRow_support Jstar hJne

theorem initialMaskShape_row {m : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) (R : Fin (maskCount m)) :
    (initialMaskShape Jstar hJ).row R =
      initialMaskRow ((maskIndexEquiv m).symm R).val ((maskIndexEquiv m).symm R).property := by
  rfl

theorem exists_initialMaskShape {m : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) :
    ∃ Sh : RowShape m 0 (maskCount m), (Sh.row Sh.star).support = Jstar :=
  ⟨initialMaskShape Jstar hJ, initialMaskShape_star_support Jstar hJ⟩

theorem exists_initialMaskData {m : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) :
    ∃ (q r : ℕ) (Sh : RowShape m q r) (tests : Finset (IntegerPolynomial q)) (Cm : ℝ),
      r ≤ maskRowBound m ∧ q ≤ 2 * maskCount m ∧ (Sh.row Sh.star).support = Jstar ∧
      (∀ P ∈ tests, P ≠ 0) ∧ 0 < Cm := by
  obtain ⟨Sh, hSh⟩ := exists_initialMaskShape Jstar hJ
  refine ⟨0, maskCount m, Sh, ∅, 1, ?_, ?_, hSh, ?_, by norm_num⟩
  · exact maskCount_le_maskRowBound m
  · exact Nat.zero_le _
  · simp

theorem initialMaskRow_form_eq_chainForm {m : ℕ} (c : Fin m → ℚ)
    (U : Finset (Fin m)) (hU : U.Nonempty) (p : Fin 0 → ℕ) (z : Fin m → ℤ) :
    rowForm c (initialMaskRow U hU) p (fun k => (z k : ℚ)) = chainForm c U z := by
  classical
  have hanchor : (initialMaskRow U hU).anchor = U.max' hU := by
    unfold RowTemplate.anchor
    apply (Finset.max'_eq_iff (s := (initialMaskRow U hU).support)
      (H := (initialMaskRow U hU).support_nonempty) (U.max' hU)).2
    constructor
    · rw [initialMaskRow_support U hU]
      exact Finset.max'_mem U hU
    · intro b hb
      rw [initialMaskRow_support U hU] at hb
      exact Finset.le_max' U b hb
  have hvalue (k : Fin m) :
      (initialMaskRow U hU).value p k = if k ∈ U then 1 else 0 := by
    by_cases hk : k ∈ U <;> simp [RowTemplate.value, initialMaskRow, hk]
  unfold rowForm chainForm
  rw [dif_pos hU, hanchor]
  simp_rw [hvalue]
  have hsum :
      (∑ k : Fin m, (c k / c (U.max' hU) * (if k ∈ U then 1 else 0)) * (z k : ℚ)) =
        ∑ k ∈ U, c k / c (U.max' hU) * (z k : ℚ) := by
    simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
    change (∑ k ∈ (Finset.univ : Finset (Fin m)),
      if k ∈ U then c k / c (U.max' hU) * (z k : ℚ) else 0) = _
    rw [← Finset.sum_filter]
    simp
  rw [hsum]

/-- An intermediate mask-removal state. The masks remain multiplicative functions of the
corresponding coordinate products, while every additive factor is represented by a row template.
The prime-dependent functions record all slots introduced by earlier Cauchy–Schwarz steps. -/
structure MaskRemovalState (m q r : ℕ) where
  shape : RowShape m q r
  masks : Finset (Finset (Fin m))
  maskFunction : Finset (Fin m) → (Fin q → ℕ) → ℤ → ℝ
  rowFunction : Fin r → (Fin q → ℕ) → ℤ → ℝ

noncomputable def initialMaskRemovalState {m : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) (b g : Finset (Fin m) → ℤ → ℝ) :
    MaskRemovalState m 0 (maskCount m) := by
  classical
  refine ⟨initialMaskShape Jstar hJ,
    Finset.univ.filter (fun U : Finset (Fin m) => U.Nonempty),
    (fun U _ y => b U y), ?_⟩
  intro R _ y
  exact g ((initialMaskShape Jstar hJ).row R).support y

namespace MaskRemovalState

def Valid {m q r K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (st : MaskRemovalState m q r) (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    (Jstar : Finset (Fin m)) (gstar : ℤ → ℝ) : Prop :=
  (st.shape.row st.shape.star).support = Jstar ∧
  (∀ U ∈ st.masks, ∀ p y, |st.maskFunction U p y| ≤ 1) ∧
  (∀ R p y, |st.rowFunction R p y| ≤
    1 + chainWeight S.core.parameters C N (st.shape.row R).anchor y) ∧
  ∀ p, st.rowFunction st.shape.star p = gstar

noncomputable def correlation {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ) : ℝ :=
  gapSlotAverage S C.gap N fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      ((∏ U ∈ st.masks, st.maskFunction U p (∏ k ∈ U, z k)) *
        ∏ R, atQ (st.rowFunction R p)
          (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
            fun k => (z k : ℚ)))

theorem correlation_empty {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    (hmasks : st.masks = ∅) :
    st.correlation S C a N = rowCorrelation S C a N st.shape st.rowFunction := by
  simp [correlation, rowCorrelation, hmasks]

end MaskRemovalState

theorem initialMaskRemovalState_valid {m K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ) (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) (b g : Finset (Fin m) → ℤ → ℝ)
    (hvalid : FunctionsValid S.core.parameters C N b g) :
    (initialMaskRemovalState Jstar hJ b g).Valid S C a N Jstar (g Jstar) := by
  rcases hvalid with ⟨hb, hg⟩
  refine ⟨initialMaskShape_star_support Jstar hJ, ?_, ?_, ?_⟩
  · intro U hU p y
    exact hb U (Finset.mem_filter.mp hU).2 y
  · intro R p y
    change |g ((initialMaskShape Jstar hJ).row R).support y| ≤
      1 + chainWeight S.core.parameters C N ((initialMaskShape Jstar hJ).row R).anchor y
    exact hg ((initialMaskShape Jstar hJ).row R).support
      ((initialMaskShape Jstar hJ).row R).support_nonempty y
  · intro p
    change g ((initialMaskShape Jstar hJ).row (initialMaskShape Jstar hJ).star).support =
      g Jstar
    rw [initialMaskShape_star_support]

theorem initialMaskRemovalState_correlation {m K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ) (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) (b g : Finset (Fin m) → ℤ → ℝ) :
    (initialMaskRemovalState Jstar hJ b g).correlation S C a N =
      maskedCorrelation S.core.parameters C a N b g := by
  classical
  let E : {U : Finset (Fin m) // U.Nonempty} ≃ Fin (maskCount m) := maskIndexEquiv m
  let Sh := initialMaskShape Jstar hJ
  have hrowterm (R : Fin (maskCount m)) (p : Fin 0 → ℕ) (z : Fin m → ℤ) :
      atQ (g ((Sh.row R).support)) (rowForm (chainScale S.core.parameters C a N)
        (Sh.row R) p fun k => (z k : ℚ)) =
        atQ (g ((E.symm R).val)) (chainForm (chainScale S.core.parameters C a N)
          (E.symm R).val z) := by
    rw [initialMaskShape_row Jstar hJ R]
    rw [initialMaskRow_support]
    rw [initialMaskRow_form_eq_chainForm]
  have hrowprod (p : Fin 0 → ℕ) (z : Fin m → ℤ) :
      (∏ R : Fin (maskCount m), atQ (g ((Sh.row R).support))
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
          fun k => (z k : ℚ))) =
        ∏ J ∈ Finset.univ.filter Finset.Nonempty,
          atQ (g J) (chainForm (chainScale S.core.parameters C a N) J z) := by
    change (∏ R ∈ (Finset.univ : Finset (Fin (maskCount m))),
      atQ (g ((Sh.row R).support))
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
          fun k => (z k : ℚ))) = _
    exact Finset.prod_bij (fun R _ => (E.symm R).val)
      (fun R _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (E.symm R).property⟩)
      (by
        intro R hR I hI hEq
        have hsub : E.symm R = E.symm I := Subtype.ext hEq
        exact E.symm.injective hsub)
      (by
        intro J hJ
        have hJne : J.Nonempty := (Finset.mem_filter.mp hJ).2
        refine ⟨E ⟨J, hJne⟩, Finset.mem_univ _, ?_⟩
        simp)
      (fun R _ => hrowterm R p z)
  have hgap (F : (Fin 0 → ℕ) → ℝ) :
      gapSlotAverage S C.gap N F = F (fun _ : Fin 0 => 0) := by
    classical
    unfold gapSlotAverage gapSlotMass
    rw [tsum_eq_single (fun _ : Fin 0 => 0) (by
      intro p hp
      have heq : p = (fun _ : Fin 0 => 0) := Subsingleton.elim _ _
      exact (hp heq).elim)]
    simp [independentPrimePoolMass]
  calc
    (initialMaskRemovalState Jstar hJ b g).correlation S C a N =
        ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
          ((∏ U ∈ Finset.univ.filter Finset.Nonempty, b U (∏ k ∈ U, z k)) *
            ∏ R, atQ (g (Sh.row R).support)
              (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                (fun _ : Fin 0 => 0)
                fun k => (z k : ℚ))) := by
      simp only [MaskRemovalState.correlation, initialMaskRemovalState]
      rw [hgap]
    _ = maskedCorrelation S.core.parameters C a N b g := by
      unfold maskedCorrelation
      apply tsum_congr
      intro z
      rw [hrowprod]

theorem weighted_cauchy_schwarz_aux {α : Type*} (μ Ω H₀ H₁ : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hΩ : ∀ x, 0 ≤ Ω x) (h0 : ∀ x, |H₀ x| ≤ Ω x)
    (hΩs : Summable fun x => μ x * Ω x)
    (h1s : Summable fun x => μ x * (Ω x * H₁ x ^ 2)) :
    |∑' x, μ x * (H₀ x * H₁ x)| ^ 2 ≤
      (∑' x, μ x * Ω x) * ∑' x, μ x * (Ω x * H₁ x ^ 2) := by
  let w : α → ℝ := fun x => μ x * Ω x
  have hw : ∀ x, 0 ≤ w x := fun x => mul_nonneg (hμ x) (hΩ x)
  have hws : Summable w := by simpa [w] using hΩs
  have h1ws : Summable (fun x => w x * H₁ x ^ 2) := by
    simpa [w, mul_assoc] using h1s
  let g : α → ℝ := fun x => w x * |H₁ x|
  have hsmall (x : α) : |H₁ x| ≤ 1 + H₁ x ^ 2 := by
    have h := sq_nonneg (|H₁ x| - (1 / 2 : ℝ))
    have habs : |H₁ x| ^ 2 = H₁ x ^ 2 := sq_abs _
    nlinarith
  have hgs : Summable g := by
    apply (hws.add h1ws).of_norm_bounded
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw x) (abs_nonneg _))]
    calc
      w x * |H₁ x| ≤ w x * (1 + H₁ x ^ 2) :=
        mul_le_mul_of_nonneg_left (hsmall x) (hw x)
      _ = w x + w x * H₁ x ^ 2 := by ring
  let F : α → ℝ := fun x => μ x * (H₀ x * H₁ x)
  have hFnorm (x : α) : ‖F x‖ ≤ g x := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hμ x)]
    calc
      μ x * (|H₀ x| * |H₁ x|) ≤ μ x * (Ω x * |H₁ x|) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (h0 x) (abs_nonneg _)) (hμ x)
      _ = g x := by simp [g, w, mul_assoc]
  have hFs : Summable F := hgs.of_norm_bounded fun x => by
    simpa only [Real.norm_eq_abs] using hFnorm x
  have hA : 0 ≤ ∑' x, w x := tsum_nonneg hw
  have hB : 0 ≤ ∑' x, w x * H₁ x ^ 2 :=
    tsum_nonneg fun x => mul_nonneg (hw x) (sq_nonneg _)
  have hfinite (s : Finset α) :
      (∑ x ∈ s, g x) ≤ Real.sqrt (∑' x, w x) * Real.sqrt (∑' x, w x * H₁ x ^ 2) := by
    have hsquare₁ :
        (∑ x ∈ s, Real.sqrt (w x) ^ 2) = ∑ x ∈ s, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Real.sq_sqrt (hw x)]
    have hsquare₂ :
        (∑ x ∈ s, (Real.sqrt (w x) * |H₁ x|) ^ 2) =
          ∑ x ∈ s, w x * H₁ x ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [mul_pow, Real.sq_sqrt (hw x), sq_abs]
    calc
      (∑ x ∈ s, g x) =
          ∑ x ∈ s, Real.sqrt (w x) * (Real.sqrt (w x) * |H₁ x|) := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [g]
        calc
          w x * |H₁ x| = (Real.sqrt (w x)) ^ 2 * |H₁ x| := by
            rw [Real.sq_sqrt (hw x)]
          _ = Real.sqrt (w x) * (Real.sqrt (w x) * |H₁ x|) := by ring
      _ ≤ Real.sqrt (∑ x ∈ s, Real.sqrt (w x) ^ 2) *
          Real.sqrt (∑ x ∈ s, (Real.sqrt (w x) * |H₁ x|) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
      _ ≤ Real.sqrt (∑' x, w x) * Real.sqrt (∑' x, w x * H₁ x ^ 2) := by
        rw [hsquare₁, hsquare₂]
        apply mul_le_mul (Real.sqrt_le_sqrt (hws.sum_le_tsum s (fun x hx => hw x)))
          (Real.sqrt_le_sqrt (h1ws.sum_le_tsum s fun x hx =>
            mul_nonneg (hw x) (sq_nonneg _)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hgs_bound :
      ∑' x, g x ≤ Real.sqrt (∑' x, w x) * Real.sqrt (∑' x, w x * H₁ x ^ 2) :=
    Real.tsum_le_of_sum_le (fun x => mul_nonneg (hw x) (abs_nonneg _)) hfinite
  have hF_bound :
      |∑' x, F x| ≤ Real.sqrt (∑' x, w x) * Real.sqrt (∑' x, w x * H₁ x ^ 2) := by
    calc
      |∑' x, F x| = ‖∑' x, F x‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' x, ‖F x‖ := norm_tsum_le_tsum_norm hFs.norm
      _ ≤ ∑' x, g x := hFs.norm.tsum_le_tsum hFnorm hgs
      _ ≤ _ := hgs_bound
  have hleft_nonneg : 0 ≤ |∑' x, F x| := abs_nonneg _
  have hroot_nonneg :
      0 ≤ Real.sqrt (∑' x, w x) * Real.sqrt (∑' x, w x * H₁ x ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ hleft_nonneg hroot_nonneg).2 hF_bound
  have hroot_sq :
      (Real.sqrt (∑' x, w x) * Real.sqrt (∑' x, w x * H₁ x ^ 2)) ^ 2 =
        (∑' x, w x) * ∑' x, w x * H₁ x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  calc
    |∑' x, μ x * (H₀ x * H₁ x)| ^ 2 = |∑' x, F x| ^ 2 := by simp [F]
    _ ≤ (Real.sqrt (∑' x, w x) * Real.sqrt (∑' x, w x * H₁ x ^ 2)) ^ 2 := hsq
    _ = (∑' x, w x) * ∑' x, w x * H₁ x ^ 2 := hroot_sq
    _ = (∑' x, μ x * Ω x) * ∑' x, μ x * (Ω x * H₁ x ^ 2) := by
      simp [w, mul_assoc]

end HindmanSumsProducts
