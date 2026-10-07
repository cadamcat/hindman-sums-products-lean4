import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.PkgMask
import HindmanSumsProducts.Correlation.PkgPrime
import HindmanSumsProducts.Correlation.PkgOpusCorr

namespace HindmanSumsProducts
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev sol_mso_primeSlotComplement {q s : ℕ} (ι : Fin q ↪ Fin s) :=
  {j : Fin s // j ∉ Set.range ι}

noncomputable def sol_mso_primeSlotIndexEquiv {q s : ℕ} (ι : Fin q ↪ Fin s) :
    Fin q ⊕ sol_mso_primeSlotComplement ι ≃ Fin s := by
  classical
  let eRange : Fin q ≃ {j : Fin s // j ∈ Set.range ι} := ι.toEquivRange
  exact (Equiv.sumCongr eRange (Equiv.refl _)).trans
    (Equiv.sumCompl (fun j : Fin s => j ∈ Set.range ι))

@[simp] theorem sol_mso_primeSlotIndexEquiv_apply_inl {q s : ℕ}
    (ι : Fin q ↪ Fin s) (i : Fin q) :
    sol_mso_primeSlotIndexEquiv ι (.inl i) = ι i := by
  simp [sol_mso_primeSlotIndexEquiv]

@[simp] theorem sol_mso_primeSlotIndexEquiv_apply_inr {q s : ℕ}
    (ι : Fin q ↪ Fin s) (j : sol_mso_primeSlotComplement ι) :
    sol_mso_primeSlotIndexEquiv ι (.inr j) = j.1 := by
  simp [sol_mso_primeSlotIndexEquiv]

noncomputable def sol_mso_primeTupleSplitEquiv {q s : ℕ} (ι : Fin q ↪ Fin s) :
    (Fin q → ℕ) × (sol_mso_primeSlotComplement ι → ℕ) ≃ (Fin s → ℕ) := by
  classical
  let e := sol_mso_primeSlotIndexEquiv ι
  let ePi : (Fin s → ℕ) ≃ (Fin q ⊕ sol_mso_primeSlotComplement ι → ℕ) :=
    Equiv.piCongrLeft' (fun _ : Fin s => ℕ) e.symm
  let ePair : (Fin q → ℕ) × (sol_mso_primeSlotComplement ι → ℕ) ≃
      (Fin q ⊕ sol_mso_primeSlotComplement ι → ℕ) :=
    { toFun := fun x => fun i => Sum.elim x.1 x.2 i
      invFun := fun f => (fun i => f (.inl i), fun j => f (.inr j))
      left_inv := by
        rintro ⟨f, g⟩
        apply Prod.ext
        · funext i
          rfl
        · funext j
          rfl
      right_inv := by
        intro f
        funext i
        cases i <;> rfl }
  exact ePair.trans ePi.symm

@[simp] theorem sol_mso_primeTupleSplitEquiv_apply_left {q s : ℕ}
    (ι : Fin q ↪ Fin s) (p : Fin q → ℕ)
    (u : sol_mso_primeSlotComplement ι → ℕ) (i : Fin q) :
    sol_mso_primeTupleSplitEquiv ι (p, u) (ι i) = p i := by
  classical
  simp [sol_mso_primeTupleSplitEquiv, sol_mso_primeSlotIndexEquiv]

@[simp] theorem sol_mso_primeTupleSplitEquiv_apply_right {q s : ℕ}
    (ι : Fin q ↪ Fin s) (p : Fin q → ℕ)
    (u : sol_mso_primeSlotComplement ι → ℕ) (j : sol_mso_primeSlotComplement ι) :
    sol_mso_primeTupleSplitEquiv ι (p, u) j.1 = u j := by
  classical
  simp [sol_mso_primeTupleSplitEquiv, sol_mso_primeSlotIndexEquiv]

theorem sol_mso_primePoolMass_tsum_one_fintype {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : ℕ) (hmass : 0 < primePoolMass lo hi) :
    ∑' p : α → ℕ, ∏ i, primePoolLaw lo hi (p i) = 1 := by
  classical
  let P : Finset ℕ := (Finset.Ico lo hi).filter Nat.Prime
  let μ : α → ℕ → ℝ := fun _ n => primePoolLaw lo hi n
  have hzero (n : ℕ) (hn : n ∉ P) : primePoolLaw lo hi n = 0 := by
    have hcond : ¬ (lo ≤ n ∧ n < hi ∧ Nat.Prime n) := by
      intro h
      apply hn
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
    simp [primePoolLaw, hcond]
  have hsupp (i : α) (n : ℕ) (hn : n ∉ P) : μ i n = 0 := by
    exact hzero n hn
  have hcoord (i : α) : ∑ n ∈ P, μ i n = 1 := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (f := primePoolLaw lo hi) (s := P) hzero]
    exact primePoolLaw_tsum_one lo hi hmass
  let D := Fintype.piFinset (fun _ : α => P)
  have hzeroPi (p : α → ℕ) (hp : p ∉ D) : (∏ i, μ i (p i)) = 0 := by
    have hnot : ∃ i, p i ∉ P := by
      by_contra h
      push Not at h
      exact hp (by simpa [D] using h)
    obtain ⟨i, hi⟩ := hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hsupp i (p i) hi)
  calc
    _ = ∑ p ∈ D, ∏ i, μ i (p i) := tsum_eq_sum hzeroPi
    _ = ∏ i, ∑ n ∈ P, μ i n := (Finset.prod_univ_sum _ _).symm
    _ = 1 := by simp [hcoord]

theorem sol_mso_independentPrimePoolAverage_cylinder {q s : ℕ}
    (ι : Fin q ↪ Fin s) (lo hi : ℕ)
    (hmass : 0 < primePoolMass lo hi) (f : (Fin q → ℕ) → ℝ) :
    ∑' p' : Fin s → ℕ,
      independentPrimePoolMass (fun _ : Fin s => lo) (fun _ => hi) p' *
        f (fun i => p' (ι i)) =
    ∑' p : Fin q → ℕ,
      independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi) p * f p := by
  classical
  let R := sol_mso_primeSlotComplement ι
  let E := sol_mso_primeTupleSplitEquiv ι
  let P : Finset ℕ := (Finset.Ico lo hi).filter Nat.Prime
  let Sfull : Finset (Fin s → ℕ) := Fintype.piFinset fun _ : Fin s => P
  let Sloc : Finset (Fin q → ℕ) := Fintype.piFinset fun _ : Fin q => P
  let Srest : Finset (R → ℕ) := Fintype.piFinset fun _ : R => P
  let Spair : Finset ((Fin q → ℕ) × (R → ℕ)) := Sloc.product Srest
  let fullMass : (Fin s → ℕ) → ℝ :=
    independentPrimePoolMass (fun _ : Fin s => lo) (fun _ => hi)
  let locMass : (Fin q → ℕ) → ℝ :=
    independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi)
  let restMass : (R → ℕ) → ℝ := fun u => ∏ j : R, primePoolLaw lo hi (u j)
  let pairTerm : ((Fin q → ℕ) × (R → ℕ)) → ℝ := fun z =>
    locMass z.1 * restMass z.2 * f z.1
  have hlawZero (n : ℕ) (hn : n ∉ P) : primePoolLaw lo hi n = 0 := by
    have hcond : ¬ (lo ≤ n ∧ n < hi ∧ Nat.Prime n) := by
      intro h
      apply hn
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
    simp [primePoolLaw, hcond]
  have hfullZero (p' : Fin s → ℕ) (hp' : p' ∉ Sfull) : fullMass p' = 0 := by
    have hnot : ∃ i : Fin s, p' i ∉ P := by
      by_contra h
      push Not at h
      apply hp'
      simpa [Sfull] using h
    obtain ⟨i, hi⟩ := hnot
    dsimp [fullMass, independentPrimePoolMass]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hlawZero (p' i) hi)
  have hlocZero (p : Fin q → ℕ) (hp : p ∉ Sloc) : locMass p = 0 := by
    have hnot : ∃ i : Fin q, p i ∉ P := by
      by_contra h
      push Not at h
      apply hp
      simpa [Sloc] using h
    obtain ⟨i, hi⟩ := hnot
    dsimp [locMass, independentPrimePoolMass]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hlawZero (p i) hi)
  have hrestZero (u : R → ℕ) (hu : u ∉ Srest) : restMass u = 0 := by
    have hnot : ∃ j : R, u j ∉ P := by
      by_contra h
      push Not at h
      apply hu
      simpa [Srest] using h
    obtain ⟨j, hj⟩ := hnot
    dsimp [restMass]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (hlawZero (u j) hj)
  have hrestTotal : ∑' u : R → ℕ, restMass u = 1 := by
    simpa [restMass] using
      (sol_mso_primePoolMass_tsum_one_fintype (α := R) lo hi hmass)
  have hrestSum : ∑ u ∈ Srest, restMass u = 1 := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional (R → ℕ))
      (f := restMass) (s := Srest) (by intro u hu; exact hrestZero u hu)]
    exact hrestTotal
  have hfactor (p : Fin q → ℕ) (u : R → ℕ) :
      fullMass (E (p, u)) = locMass p * restMass u := by
    unfold fullMass locMass restMass independentPrimePoolMass
    let eI := sol_mso_primeSlotIndexEquiv ι
    calc
      (∏ j : Fin s, primePoolLaw lo hi (E (p, u) j)) =
          ∏ z : Fin q ⊕ R, primePoolLaw lo hi (E (p, u) (eI z)) := by
        exact (Fintype.prod_equiv eI
          (fun z => primePoolLaw lo hi (E (p, u) (eI z)))
          (fun j => primePoolLaw lo hi (E (p, u) j))
          (by intro z; simp)).symm
      _ = (∏ i : Fin q, primePoolLaw lo hi (p i)) *
          ∏ j : R, primePoolLaw lo hi (u j) := by
        rw [Fintype.prod_sum_type]
        simp [E, eI, sol_mso_primeTupleSplitEquiv, sol_mso_primeSlotIndexEquiv]
  have hproj (p : Fin q → ℕ) (u : R → ℕ) :
      (fun i => E (p, u) (ι i)) = p := by
    funext i
    simp [E]
  have hpairZero (z : (Fin q → ℕ) × (R → ℕ)) (hz : z ∉ Spair) :
      pairTerm z = 0 := by
    have hnot : z.1 ∉ Sloc ∨ z.2 ∉ Srest := by
      by_contra h
      push Not at h
      apply hz
      exact Finset.mem_product.mpr h
    rcases hnot with hp | hu
    · simp [pairTerm, hlocZero z.1 hp]
    · simp [pairTerm, hrestZero z.2 hu]
  have hlocSupport : ∀ p : Fin q → ℕ,
      p ∉ Sloc → locMass p * f p = 0 := by
    intro p hp
    simp [hlocZero p hp]
  calc
    _ = ∑' p' : Fin s → ℕ, fullMass p' * f (fun i => p' (ι i)) := by rfl
    _ = ∑' z : (Fin q → ℕ) × (R → ℕ), fullMass (E z) * f (fun i => E z (ι i)) := by
      exact (E.tsum_eq (fun p' => fullMass p' * f (fun i => p' (ι i)))).symm
    _ = ∑ z ∈ Spair, pairTerm z := by
      rw [tsum_eq_sum (L := SummationFilter.unconditional
        ((Fin q → ℕ) × (R → ℕ))) (f := fun z => fullMass (E z) *
          f (fun i => E z (ι i))) (s := Spair) (by
            intro z hz
            have hfactor' := hfactor z.1 z.2
            have hproj' := hproj z.1 z.2
            rw [hfactor', hproj']
            exact hpairZero z hz)]
      apply Finset.sum_congr rfl
      intro z hz
      simp [pairTerm, hfactor z.1 z.2, hproj z.1 z.2]
    _ = ∑ p ∈ Sloc, locMass p * f p := by
      change (∑ z ∈ Sloc ×ˢ Srest, pairTerm z) = _
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = ∑ u ∈ Srest, (locMass p * f p) * restMass u := by
          apply Finset.sum_congr rfl
          intro u hu
          dsimp [pairTerm]
          ring
        _ = locMass p * f p * ∑ u ∈ Srest, restMass u := by
          rw [← Finset.mul_sum]
        _ = locMass p * f p := by rw [hrestSum]; ring
    _ = ∑' p : Fin q → ℕ, locMass p * f p := by
      symm
      rw [tsum_eq_sum (L := SummationFilter.unconditional (Fin q → ℕ))
        (f := fun p => locMass p * f p) (s := Sloc) hlocSupport]



theorem sol_mso_subsetAverage_eq_joint
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (Sh : RowShape m q r) (ι : Fin q ↪ Fin s)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper)
    (hden : ∀ T : RowTemplate m q, ∀ p : Fin q → ℕ, ∀ z : Fin m → ℤ,
      (rowForm (chainScale S.core.parameters C a N) T p
        (fun k => (z k : ℚ))).den = 1)
    (J : Finset (Fin r)) :
    maskRowSubsetAverage S C a N Sh ι J =
      ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        ∏ i ∈ J, chainWeight S.core.parameters C N (Sh.row i).anchor
          (rowForm (chainScale S.core.parameters C a N) (Sh.row i) x.1
            (fun k => (x.2 k : ℚ))).num := by
  classical
  let F : (Fin q → ℕ) × (Fin m → ℤ) → ℝ := fun x =>
    ∏ i ∈ J, chainWeight S.core.parameters C N (Sh.row i).anchor
      (rowForm (chainScale S.core.parameters C a N) (Sh.row i) x.1
        (fun k => (x.2 k : ℚ))).num
  unfold maskRowSubsetAverage gapSlotAverage
  simp only [atQ, hden, ite_true]
  change (∑' p : Fin s → ℕ, gapSlotMass S C.gap N p *
    (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      F ((fun i => p (ι i)), z))) = _
  have h := sol_mso_independentPrimePoolAverage_cylinder ι
    (S.primeStage.pool N C.gap).lower (S.primeStage.pool N C.gap).upper hMass
    (fun p => ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z * F (p, z))
  change (∑' p : Fin s → ℕ, gapSlotMass S C.gap N p *
    (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      F ((fun i => p (ι i)), z))) =
    (∑' p : Fin q → ℕ, gapSlotMass S C.gap N p *
      (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z * F (p, z))) at h
  rw [h]
  exact pkgMask_gapPivotTsum_fubini S C N F

theorem sol_mso_invariantAverage_le_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm) :
    ∀ᶠ N in atTop, ∀ (st : MaskRemovalState m q r), st.shape = Sh →
      ∀ I : Fin r → Prop,
        (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          pkgMask_invariantRowWeight st S C a N I x.1 x.2) ≤ 2 * (2 : ℝ) ^ r := by
  classical
  have hsub : ∀ᶠ N in atTop, ∀ J : Finset (Fin r),
      maskRowSubsetAverage S C a N Sh ι J ≤ 2 :=
    Filter.eventually_all.2 fun J =>
      maskRowSubsetAverage_le_two_eventually S C a ha Sh ι hlisted J
  filter_upwards [hsub, rowForm_den_one_eventually (q := q) S C a ha,
    primePoolMass_pos_eventually S C.gap] with N hsub hden hMass
  intro st hshape I
  let w : ((Fin q → ℕ) × (Fin m → ℤ)) → Fin r → ℝ := fun x i =>
    chainWeight S.core.parameters C N (Sh.row i).anchor
      (rowForm (chainScale S.core.parameters C a N) (Sh.row i) x.1
        (fun k => (x.2 k : ℚ))).num
  let Jall : Finset (Fin r) := Finset.univ
  have hw (x : (Fin q → ℕ) × (Fin m → ℤ)) (i : Fin r) : 0 ≤ w x i :=
    chainWeight_nonneg S C N _ _
  have hle (x : (Fin q → ℕ) × (Fin m → ℤ)) :
      pkgMask_invariantRowWeight st S C a N I x.1 x.2 ≤ ∏ i, (1 + w x i) := by
    unfold pkgMask_invariantRowWeight
    rw [hshape]
    apply Finset.prod_le_prod₀
    · intro i hi
      by_cases hI : I i
      · simp only [dite_eq_left hI]
        change 0 ≤ 1 + w x i
        linarith [hw x i]
      · simp [hI]
    · intro i hi
      by_cases hI : I i
      · simp [hI, w]
      · simp only [dite_eq_right hI]
        linarith [hw x i]
  have hexpand (x : (Fin q → ℕ) × (Fin m → ℤ)) :
      (∏ i, (1 + w x i)) = ∑ J ∈ Jall.powerset, ∏ i ∈ J, w x i :=
    Finset.prod_one_add Jall
  have hswap :
      (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        ∏ i, (1 + w x i)) =
      ∑ J ∈ Jall.powerset, ∑' x : (Fin q → ℕ) × (Fin m → ℤ),
        gapPivotMass S C N x.1 x.2 * ∏ i ∈ J, w x i := by
    simp_rw [hexpand, Finset.mul_sum]
    exact Summable.tsum_finsetSum (fun J hJ =>
      gapPivotMass_mul_summable S C N (fun x => ∏ i ∈ J, w x i))
  calc
    _ ≤ ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        ∏ i, (1 + w x i) := by
      exact (gapPivotMass_mul_summable S C N _).tsum_le_tsum
        (fun x => mul_le_mul_of_nonneg_left (hle x) (gapPivotMass_nonneg S C N hMass x.1 x.2))
        (gapPivotMass_mul_summable S C N _)
    _ = ∑ J ∈ Jall.powerset, maskRowSubsetAverage S C a N Sh ι J := by
      rw [hswap]
      apply Finset.sum_congr rfl
      intro J hJ
      exact (sol_mso_subsetAverage_eq_joint S C a N Sh ι hMass hden J).symm
    _ ≤ ∑ J ∈ Jall.powerset, (2 : ℝ) := Finset.sum_le_sum fun J hJ => hsub J
    _ = 2 * (2 : ℝ) ^ r := by simp [Jall, mul_comm]


theorem sol_mso_mask_step_outside {m q r : ℕ}
    (Jstar : Finset (Fin m)) (hJ : 2 ≤ Jstar.card)
    (Sh : RowShape m q r) (hStar : (Sh.row Sh.star).support = Jstar)
    (masks : Finset (Finset (Fin m))) (U : Finset (Fin m)) (hU : U ∈ masks)
    (u : Fin m) (huJ : u ∈ Jstar) (huU : u ∉ U) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r') (tests : Finset (IntegerPolynomial (q + 2)))
      (C₁ : ℝ),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar ∧ (∀ P ∈ tests, P ≠ 0) ∧ 0 < C₁ ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin (q + 2) ↪ Fin s),
        TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ∀ (st : MaskRemovalState m q r) (gstar : ℤ → ℝ),
          st.shape = Sh → st.masks = masks → st.Valid S C a N Jstar gstar →
          ∃ st' : MaskRemovalState m (q + 2) r',
            st'.shape = Sh' ∧ st'.masks = masks.erase U ∧ st'.Valid S C a N Jstar gstar ∧
            |st.correlation S C a N| ^ 2 ≤ C₁ * |st'.correlation S C a N| + ε := by
  classical
  have hvexists : ∃ v ∈ Jstar, v ≠ u := by
    by_contra h
    push Not at h
    have hsub : Jstar ⊆ {u} := by
      intro v hv
      simp [h v hv]
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  obtain ⟨v, hvJ, hvu⟩ := hvexists
  have hu : u ∈ (Sh.row Sh.star).support := by rwa [hStar]
  have hv : v ∈ (Sh.row Sh.star).support := by rwa [hStar]
  have hstarNot := RowTemplate.scaleBranches_not_parallel (Sh.row Sh.star) u hu ⟨v, hv, hvu⟩
  obtain ⟨r', Sh', e, hrow, hr', hstar', hstarIndex⟩ :=
    exists_scaleBranch_row_shape Sh Jstar hStar u v hu hv hvu
  let emb : Fin q ↪ Fin (q + 2) := ⟨fun i => i.succ.succ,
    fun i j h => Fin.succ_inj.mp (Fin.succ_inj.mp h)⟩
  let tests := (templateMinors Sh).image (MvPolynomial.rename emb)
  refine ⟨r', Sh', tests, 4 * (2 : ℝ) ^ r, hr', hstar', ?_, by positivity, ?_⟩
  · intro P hP
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    have hP₀ne : P₀ ≠ 0 := (Finset.mem_filter.mp hP₀).2
    intro hzero
    apply hP₀ne
    apply MvPolynomial.rename_injective emb emb.injective
    simpa using hzero
  · intro K s Aset Dm S ι hlisted C a ha ε hε
    let ιold : Fin q ↪ Fin s := emb.trans ι
    have hlistedOld : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ιold P ∈ Dm := by
      intro P hP
      have h := hlisted (MvPolynomial.rename emb P) (Finset.mem_image_of_mem _ hP)
      rw [MvPolynomial.rename_rename] at h
      exact h
    let δ : ℝ := min 1 (ε / 4)
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    have hδone : δ ≤ 1 := min_le_left _ _
    have hδε : δ ≤ ε / 4 := min_le_right _ _
    filter_upwards [sol_mso_invariantAverage_le_eventually S C a ha Sh ιold hlistedOld,
      opus_corr_insertion_estimate S C u (2 * r) δ hδ,
      pool_lower_gt_masterScaleV_eventually S C.gap,
      rowForm_den_one_eventually (q := q) S C a ha,
      rowForm_den_one_eventually (q := q + 2) S C a ha,
      chainScale_pos_eventually S C a ha,
      primePoolMass_pos_eventually S C.gap]
      with N hboundN hinsertN hpoolN hdenOld hdenNew hscaleN hMassN
    intro st gstar hshape hmasks hvalid
    subst hshape
    subst hmasks
    let I : Fin r → Prop := fun i =>
      ((st.shape.row i).scaleBranchP u).Parallel ((st.shape.row i).scaleBranchQ u)
    let Ω : (Fin q → ℕ) × (Fin m → ℤ) → ℝ := fun x =>
      pkgMask_invariantRowWeight st S C a N I x.1 x.2
    have hΩpos (x : (Fin q → ℕ) × (Fin m → ℤ)) : 0 < Ω x :=
      pkgMask_invariantRowWeight_pos st S C a N I x.1 x.2
    let st' := outsideBranchMaskRemovalState S C N st U u Sh' e
    have hvalid' : st'.Valid S C a N Jstar gstar :=
      outsideBranchMaskRemovalState_valid S C a N st U u Jstar gstar hvalid
        Sh' e hrow hstarIndex hstarNot hpoolN
    refine ⟨st', rfl, rfl, hvalid', ?_⟩
    have herr : |st.correlation S C a N -
        st.pkgMask_stateCoordinatePrimeInsertion S C a N u| ≤ δ := by
      have h := hinsertN q (fun x => st.pkgMask_stateIntegrand S C a N x.1 x.2)
        (fun x => st.pkgMask_stateIntegrand_abs_le S C a N Jstar gstar hvalid x.1 x.2)
      rw [st.pkgMask_stateCorrelation_joint S C a N,
        st.pkgMask_stateCoordinatePrimeInsertion_joint S C a N u]
      exact h
    have hcs := st.pkgMask_stateCoordinatePrimeInsertion_weightedCS S C a N Jstar gstar
      hMassN hvalid U u hU huU Ω (fun x => (hΩpos x).le) (fun x => ne_of_gt (hΩpos x))
    have hsquare := st.pkgMask_outsideWeightedSquare_eq_correlation S C a N U u Sh' e hrow
      I (fun _ => Iff.rfl) (ne_of_gt (hscaleN u)) hpoolN
      (fun p z i => hdenOld (st.shape.row i) p z)
      (fun p z T => hdenNew T p z)
    change (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
      (Ω x * (poolAverage S C.gap N
        (st.pkgMask_outsideStepAverageFunction S C a N U u Ω x)) ^ 2)) =
      st'.correlation S C a N at hsquare
    rw [hsquare] at hcs
    have hΩnonneg : 0 ≤ ∑' x : (Fin q → ℕ) × (Fin m → ℤ),
        gapPivotMass S C N x.1 x.2 * Ω x :=
      tsum_nonneg fun x => mul_nonneg (gapPivotMass_nonneg S C N hMassN x.1 x.2) (hΩpos x).le
    have hΩbound : (∑' x : (Fin q → ℕ) × (Fin m → ℤ),
        gapPivotMass S C N x.1 x.2 * Ω x) ≤ 2 * (2 : ℝ) ^ r := hboundN st rfl I
    have hcs' : |st.pkgMask_stateCoordinatePrimeInsertion S C a N u| ^ 2 ≤
        (2 * (2 : ℝ) ^ r) * |st'.correlation S C a N| := by
      calc
        _ ≤ _ := hcs
        _ ≤ (∑' x : (Fin q → ℕ) × (Fin m → ℤ),
            gapPivotMass S C N x.1 x.2 * Ω x) * |st'.correlation S C a N| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hΩnonneg
        _ ≤ _ := mul_le_mul_of_nonneg_right hΩbound (abs_nonneg _)
    have habs : |st.correlation S C a N| ≤
        |st.pkgMask_stateCoordinatePrimeInsertion S C a N u| + δ := by
      calc
        _ ≤ |st.correlation S C a N - st.pkgMask_stateCoordinatePrimeInsertion S C a N u| +
            |st.pkgMask_stateCoordinatePrimeInsertion S C a N u| := by
          have h := abs_add_le
            (st.correlation S C a N - st.pkgMask_stateCoordinatePrimeInsertion S C a N u)
            (st.pkgMask_stateCoordinatePrimeInsertion S C a N u)
          simpa only [sub_add_cancel] using h
        _ ≤ _ := by linarith
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    have htwo := opus_corr_sq_add_le |st.pkgMask_stateCoordinatePrimeInsertion S C a N u| δ
    have hδsq : δ ^ 2 ≤ δ := by nlinarith [hδ.le]
    nlinarith

end
end HindmanSumsProducts
