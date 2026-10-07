import HindmanSumsProducts.Prediction.Outside
import Mathlib.Analysis.MeanInequalities

/-! Helper lemmas for the §5 proof package S5-B (owned by its proof lane). -/

namespace HindmanSumsProducts

namespace Prediction

open Filter
open scoped Topology

private abbrev MomentPrimeIndex (b q : ℕ) := Fin b × Fin q
private abbrev MomentBaseIndex (b d : ℕ) := Unit ⊕ (Fin b × (Fin d × Fin 2))
private abbrev MomentRowIndex (b d : ℕ) :=
  Unit ⊕ (Fin b × {ω : Finset (Fin d) // ω.Nonempty})

private noncomputable def momentPrimeEnum (b q : ℕ) :
    Fin (Fintype.card (MomentPrimeIndex b q)) ≃ MomentPrimeIndex b q :=
  (Fintype.equivFin _).symm

private noncomputable def momentBaseEnum (b d : ℕ) :
    Fin (Fintype.card (MomentBaseIndex b d)) ≃ MomentBaseIndex b d :=
  (Fintype.equivFin _).symm

private noncomputable def momentRowEnum (b d : ℕ) :
    Fin (Fintype.card (MomentRowIndex b d)) ≃ MomentRowIndex b d :=
  (Fintype.equivFin _).symm

private noncomputable def momentModulus {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate) (l : Fin K)
    (N : ℕ) (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ) (k : Fin b) : ℕ :=
  T.modulus (corrScales MS) N
    (fun j => p ((momentPrimeEnum b T.q).symm (k, j)))

private noncomputable def momentRowCoeff {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) :
    ℕ → (Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ) →
      Fin (Fintype.card (MomentRowIndex b T.d)) →
        Fin (Fintype.card (MomentBaseIndex b T.d)) → ℚ :=
  fun N p u j =>
    match momentRowEnum b T.d u, momentBaseEnum b T.d j with
    | .inl _, .inl _ => 1
    | .inl _, .inr _ => 0
    | .inr _, .inl _ => 1
    | .inr (k, ω), .inr (k', (j', side)) =>
        if h : k = k' ∧ j' ∈ ω.1 then
          if side.val = 0 then
            -((momentModulus MS b T l N p k : ℕ) : ℚ)
          else (momentModulus MS b T l N p k : ℚ)
        else 0

private noncomputable def momentRowCoeffInt {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) :
    ℕ → (Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ) →
      Fin (Fintype.card (MomentRowIndex b T.d)) →
        Fin (Fintype.card (MomentBaseIndex b T.d)) → ℤ :=
  fun N p u j =>
    match momentRowEnum b T.d u, momentBaseEnum b T.d j with
    | .inl _, .inl _ => 1
    | .inl _, .inr _ => 0
    | .inr _, .inl _ => 1
    | .inr (k, ω), .inr (k', (j', side)) =>
        if h : k = k' ∧ j' ∈ ω.1 then
          if side.val = 0 then -(momentModulus MS b T l N p k : ℤ)
          else (momentModulus MS b T l N p k : ℤ)
        else 0

private theorem momentRowCoeff_eq_castInt {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (u : Fin (Fintype.card (MomentRowIndex b T.d)))
    (j : Fin (Fintype.card (MomentBaseIndex b T.d))) :
    momentRowCoeff MS b T l N p u j =
      (momentRowCoeffInt MS b T l N p u j : ℚ) := by
  classical
  cases e1 : momentRowEnum b T.d u <;>
    cases e2 : momentBaseEnum b T.d j <;>
    simp [momentRowCoeff, momentRowCoeffInt, e1, e2]

private theorem momentRowCoeff_den_eq_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (u : Fin (Fintype.card (MomentRowIndex b T.d)))
    (j : Fin (Fintype.card (MomentBaseIndex b T.d))) :
    (momentRowCoeff MS b T l N p u j).den = 1 := by
  rw [momentRowCoeff_eq_castInt]
  simp

private theorem momentRowCoeff_root_eq_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (u : Fin (Fintype.card (MomentRowIndex b T.d))) :
    momentRowCoeff MS b T l N p u
      ((momentBaseEnum b T.d).symm (.inl ())) = 1 := by
  classical
  let j0 := (momentBaseEnum b T.d).symm (.inl ())
  have hj0 : momentBaseEnum b T.d j0 = Sum.inl () := by simp [j0]
  change momentRowCoeff MS b T l N p u j0 = 1
  unfold momentRowCoeff
  rw [hj0]
  cases momentRowEnum b T.d u <;> rfl

private theorem momentRowCoeff_root_residue {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (u : Fin (Fintype.card (MomentRowIndex b T.d)))
    (r : ℕ) (hr : r.Prime) :
    rationalResidue r hr (momentRowCoeff MS b T l N p u
      ((momentBaseEnum b T.d).symm (.inl ()))) = 1 := by
  letI : Fact r.Prime := ⟨hr⟩
  rw [momentRowCoeff_root_eq_one]
  simp [rationalResidue]

private theorem prime_dvd_roughPart_implies_dvd_natAbs {w r : ℕ} {a : ℤ}
    (hr : r.Prime) (hrough : r ∣ roughPart w a) : r ∣ a.natAbs := by
  classical
  unfold roughPart at hrough
  obtain ⟨p, hp, hpow⟩ := (hr.prime.dvd_finsetProd_iff _).mp hrough
  have hp' := Finset.mem_filter.mp hp
  have hrp : r ∣ p := hr.dvd_of_dvd_pow hpow
  have hpeq : r = p := (Nat.prime_dvd_prime_iff_eq hr hp'.2.1).mp hrp
  have hexp : a.natAbs.factorization p ≠ 0 := by
    intro he
    rw [he] at hpow
    simp at hpow
    exact hr.not_dvd_one (by simpa [hpeq] using hpow)
  have hpdvd : p ∣ a.natAbs := Nat.dvd_of_factorization_pos hexp
  simpa [hpeq] using hpdvd

private theorem roughPart_le_natAbs {w : ℕ} {a : ℤ} (ha : a ≠ 0) :
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

private theorem roughPart_pos (w : ℕ) (a : ℤ) : 0 < roughPart w a := by
  classical
  unfold roughPart
  apply lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
  apply Finset.one_le_prod
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2.1
  exact one_le_pow₀ (le_trans (by norm_num) hpPrime.two_le)

private theorem momentPolynomialEval_natAbs_le {q : ℕ}
    (P : IntegerPolynomial q) (U : ℕ) (p : Fin q → ℕ)
    (hp : ∀ i, p i ≤ U) :
    (evalIntegerPolynomial P (fun i => (p i : ℤ))).natAbs ≤
      (∑ d ∈ P.support, (P.coeff d).natAbs) * (U + 1) ^ P.totalDegree := by
  classical
  have heval : evalIntegerPolynomial P (fun i => (p i : ℤ)) =
      ∑ d ∈ P.support,
        (P.coeff d : ℤ) * ∏ i, (p i : ℤ) ^ d i := by
    simpa only [evalIntegerPolynomial] using
      (MvPolynomial.eval_eq' (fun i => (p i : ℤ)) P)
  have htermCast (d : (Fin q) →₀ ℕ) :
      (∏ i : Fin q, (p i : ℤ) ^ d i) =
        ((∏ i : Fin q, p i ^ d i : ℕ) : ℤ) := by
    simp
  have htermAbs (d : (Fin q) →₀ ℕ) :
      ((P.coeff d : ℤ) * ∏ i : Fin q, (p i : ℤ) ^ d i).natAbs =
        (P.coeff d).natAbs * ∏ i : Fin q, p i ^ d i := by
    rw [Int.natAbs_mul, htermCast d, Int.natAbs_natCast]
  have hmonomial (d : (Fin q) →₀ ℕ) :
      (∏ i : Fin q, p i ^ d i) ≤ (U + 1) ^ d.sum (fun _ e => e) := by
    calc
      ∏ i : Fin q, p i ^ d i ≤ ∏ i : Fin q, (U + 1) ^ d i := by
        apply Finset.prod_le_prod
        intro i hi
        exact Nat.pow_le_pow_left (le_trans (hp i) (Nat.le_add_right U 1)) (d i)
      _ = (U + 1) ^ d.sum (fun _ e => e) := by
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        change (∑ i : Fin q, d i) = ∑ i ∈ d.support, d i
        symm
        apply Finset.sum_subset (Finset.subset_univ d.support)
        intro i hi hnot
        exact Finsupp.notMem_support_iff.mp hnot
  have htermLe (d : (Fin q) →₀ ℕ) (hd : d ∈ P.support) :
      ((P.coeff d : ℤ) * ∏ i : Fin q, (p i : ℤ) ^ d i).natAbs ≤
        (P.coeff d).natAbs * (U + 1) ^ P.totalDegree := by
    rw [htermAbs d]
    exact Nat.mul_le_mul_left _ <|
      (hmonomial d).trans (Nat.pow_le_pow_right (by omega) (MvPolynomial.le_totalDegree hd))
  calc
    _ = (∑ d ∈ P.support,
          (P.coeff d : ℤ) * ∏ i : Fin q, (p i : ℤ) ^ d i).natAbs := by rw [heval]
    _ ≤ ∑ d ∈ P.support,
          ((P.coeff d : ℤ) * ∏ i : Fin q, (p i : ℤ) ^ d i).natAbs :=
      Int.natAbs_sum_le P.support _
    _ ≤ ∑ d ∈ P.support, (P.coeff d).natAbs * (U + 1) ^ P.totalDegree :=
      Finset.sum_le_sum fun d hd => htermLe d hd
    _ = (∑ d ∈ P.support, (P.coeff d).natAbs) * (U + 1) ^ P.totalDegree := by
      rw [← Finset.sum_mul]

private def momentPolynomialCoefficientMass {q : ℕ} (P : IntegerPolynomial q) : ℕ :=
  ∑ d ∈ P.support, (P.coeff d).natAbs

private noncomputable def momentShiftLengthLower {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (T : CubeTemplate) (J0 N : ℕ) : ℕ :=
  MS.core.parameters.H N l /
    (J0 * (MS.core.parameters.M N *
      ((momentPolynomialCoefficientMass T.D + 1) *
        ((MS.primeStage.pool N l).upper + 1) ^ T.D.totalDegree)))

private def momentGapScale {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (N : ℕ) : ℕ :=
  (MS.primeStage.pool N l).upper + masterScaleV MS.core.parameters N l

private theorem momentMasterScaleV_tendsto {K : ℕ} (A : Parameters K) (l : Fin K) :
    Tendsto (fun N => masterScaleV A N l) atTop atTop := by
  have hbound (N : ℕ) : N ≤ masterScaleV A N l := by
    calc
      N ≤ primorial (N + 1) := Nat.le_trans (Nat.le_succ N) le_primorial_self
      _ ≤ A.M N := A.Wle N
      _ ≤ masterScaleV A N l := by dsimp [masterScaleV]; omega
  rw [tendsto_atTop]
  intro n
  filter_upwards [eventually_ge_atTop n] with N hN
  exact hN.trans (hbound N)

private theorem momentGapScale_tendsto {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) :
    Tendsto (momentGapScale MS l) atTop atTop := by
  have hV := momentMasterScaleV_tendsto MS.core.parameters l
  rw [tendsto_atTop]
  intro n
  filter_upwards [hV.eventually_ge_atTop n] with N hN
  dsimp [momentGapScale]
  omega

private theorem momentPivotLog_dominates_gap_scale {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hgap : ValidGap B l) :
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (MS.core.parameters.X N B.1 : ℝ))
      (fun N => (momentGapScale MS l N : ℝ)) := by
  intro C hC
  have hgapRatio := MS.gapStage.gap_dominates_pool_and_bound l C hC
  have hparamRatio := MS.core.parameters.Xdom B.1 1 (by norm_num)
  have hPivotGeLog : ∀ᶠ N : ℕ in atTop,
      (MS.core.parameters.H N B.1 : ℝ) ≤
        Real.log (MS.core.parameters.X N B.1 : ℝ) := by
    filter_upwards [hparamRatio.eventually_ge_atTop (1 : ℝ)] with N hratio
    have hHpos : (0 : ℝ) < MS.core.parameters.H N B.1 := by
      exact_mod_cast MS.core.parameters.Hpos N B.1
    have hratio' : (1 : ℝ) ≤
        Real.log (MS.core.parameters.X N B.1 : ℝ) /
          (MS.core.parameters.H N B.1 : ℝ) := by simpa using hratio
    simpa using (le_div_iff₀ hHpos).1 hratio'
  have hEarlier (N : ℕ) : MS.core.parameters.H N l ≤ MS.core.parameters.H N B.1 := by
    apply Nat.le_of_dvd (MS.core.parameters.Hpos N B.1)
    exact MS.gapStage.earlier_gaps_divide N l B.1 hgap.2
  have hratioCompare : ∀ᶠ N : ℕ in atTop,
      (MS.core.parameters.H N l : ℝ) / (momentGapScale MS l N : ℝ) ^ C ≤
        Real.log (MS.core.parameters.X N B.1 : ℝ) /
          (momentGapScale MS l N : ℝ) ^ C := by
    filter_upwards [hPivotGeLog] with N hlog
    have hnum : (MS.core.parameters.H N l : ℝ) ≤
        Real.log (MS.core.parameters.X N B.1 : ℝ) := by
      have hEarlierReal : (MS.core.parameters.H N l : ℝ) ≤
          (MS.core.parameters.H N B.1 : ℝ) := by exact_mod_cast (hEarlier N)
      exact hEarlierReal.trans hlog
    exact div_le_div_of_nonneg_right hnum (by positivity)
  rw [Filter.tendsto_atTop]
  intro y
  filter_upwards [hgapRatio.eventually_ge_atTop y, hratioCompare] with N hN hcmp
  have hN' : y ≤ (MS.core.parameters.H N l : ℝ) /
      (momentGapScale MS l N : ℝ) ^ C := by
    simpa [momentGapScale] using hN
  exact hN'.trans hcmp

private theorem momentPivotCutoff_dominates_gap_scale {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hgap : ValidGap B l) :
    OAI.MicrocellScale.Dominates
      (fun N => (MS.core.parameters.X N B.1 : ℝ))
      (fun N => (momentGapScale MS l N : ℝ)) := by
  intro C hC
  let G : ℕ → ℕ := fun N => momentGapScale MS l N
  let S : ℕ → ℝ := fun N => (G N : ℝ)
  have hS : Tendsto S atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (momentGapScale_tendsto MS l)
  have hlogDom := momentPivotLog_dominates_gap_scale MS B l hgap
  have hlogRatio := hlogDom (C + 1) (by linarith)
  have hSpos (N : ℕ) : 0 < S N := by
    have hNat : 0 < G N := by
      dsimp [G, momentGapScale]
      have hV : 2 ≤ masterScaleV MS.core.parameters N l := by
        dsimp [masterScaleV]
        omega
      omega
    change (0 : ℝ) < (G N : ℝ)
    exact_mod_cast hNat
  have hXpos (N : ℕ) :
      (0 : ℝ) < (MS.core.parameters.X N B.1 : ℝ) := by
    exact_mod_cast MS.core.parameters.Xpos N B.1
  have hlogLeX (N : ℕ) :
      Real.log (MS.core.parameters.X N B.1 : ℝ) ≤
        (MS.core.parameters.X N B.1 : ℝ) := by
    have h := Real.add_one_le_exp (Real.log (MS.core.parameters.X N B.1 : ℝ))
    rw [Real.exp_log (hXpos N)] at h
    linarith
  have hlogPower : ∀ᶠ N : ℕ in atTop,
      S N ^ (C + 1) ≤ Real.log (MS.core.parameters.X N B.1 : ℝ) := by
    filter_upwards [hlogRatio.eventually_ge_atTop (1 : ℝ)] with N hN
    simpa using (le_div_iff₀ (Real.rpow_pos_of_pos (hSpos N) (C + 1))).1 hN
  have hXPower : ∀ᶠ N : ℕ in atTop,
      S N ^ (C + 1) ≤ (MS.core.parameters.X N B.1 : ℝ) := by
    filter_upwards [hlogPower] with N hN
    exact hN.trans (hlogLeX N)
  have hRatioLower : ∀ᶠ N : ℕ in atTop,
      S N ≤ (MS.core.parameters.X N B.1 : ℝ) / S N ^ C := by
    filter_upwards [hXPower] with N hN
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (hSpos N) C)).2
    calc
      S N * S N ^ C = S N ^ C * S N := by ring
      _ = S N ^ C * S N ^ (1 : ℝ) := by simp
      _ = S N ^ (C + 1) := (Real.rpow_add (hSpos N) C 1).symm
      _ ≤ (MS.core.parameters.X N B.1 : ℝ) := hN
  rw [Filter.tendsto_atTop]
  intro y
  filter_upwards [hS.eventually_ge_atTop y, hRatioLower] with N hN hratio
  exact hN.trans hratio

private theorem momentShiftLength_lower {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (T : CubeTemplate)
    (J0 N : ℕ) (hJ0 : 0 < J0) (p : Fin T.q → ℕ)
    (hgood : T.Good (corrScales MS) l N p) :
    momentShiftLengthLower MS l T J0 N ≤ T.length (corrScales MS) l J0 N p := by
  classical
  let U := (MS.primeStage.pool N l).upper
  let A := MS.core.parameters
  let value := evalIntegerPolynomial T.D (fun i => (p i : ℤ))
  let C := momentPolynomialCoefficientMass T.D
  rcases hgood with ⟨hp, hinj, htests, hsmall⟩
  have hpBound : ∀ i, p i ≤ U := fun i => (hp i).2.1.le
  have hEval := momentPolynomialEval_natAbs_le T.D U p hpBound
  have hrough := roughPart_le_natAbs (w := N + 1) (a := value) (htests T.D T.D_mem)
  have hmodle : A.M N * roughPart (N + 1) value ≤
      A.M N * ((C + 1) * (U + 1) ^ T.D.totalDegree) := by
    calc
      A.M N * roughPart (N + 1) value ≤
          A.M N * (C * (U + 1) ^ T.D.totalDegree) :=
        Nat.mul_le_mul_left _ (hrough.trans (by simpa [value, C, momentPolynomialCoefficientMass] using hEval))
      _ ≤ A.M N * ((C + 1) * (U + 1) ^ T.D.totalDegree) :=
        Nat.mul_le_mul_left (A.M N)
          (Nat.mul_le_mul_right ((U + 1) ^ T.D.totalDegree) (Nat.le_add_right C 1))
  let denUpper := J0 * (A.M N * ((C + 1) * (U + 1) ^ T.D.totalDegree))
  have hdenle : J0 * (A.M N * roughPart (N + 1) value) ≤
      denUpper := by
    dsimp [denUpper]
    exact Nat.mul_le_mul_left J0 hmodle
  have hdenpos : 0 < J0 * (A.M N * roughPart (N + 1) value) :=
    Nat.mul_pos hJ0 (Nat.mul_pos (A.Mpos N) (roughPart_pos (N + 1) value))
  unfold momentShiftLengthLower
  unfold CubeTemplate.length shiftLength directionModulus
  dsimp [U, A, C, momentPolynomialCoefficientMass] at hdenle ⊢
  change MS.core.parameters.H N l / denUpper ≤
    MS.core.parameters.H N l / (J0 * (MS.core.parameters.M N *
      roughPart (N + 1) value))
  apply (Nat.le_div_iff_mul_le hdenpos).2
  calc
    (MS.core.parameters.H N l / denUpper) *
        (J0 * (MS.core.parameters.M N * roughPart (N + 1) value)) ≤
      (MS.core.parameters.H N l / denUpper) * denUpper :=
        Nat.mul_le_mul_left _ hdenle
    _ ≤ MS.core.parameters.H N l := Nat.div_mul_le_self _ _

private theorem momentShiftLengthLower_ge_pow {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (T : CubeTemplate)
    (J0 : ℕ) (hJ0 : 0 < J0) (m : ℕ) :
    ∀ᶠ N in atTop, (momentGapScale MS l N) ^ m ≤ momentShiftLengthLower MS l T J0 N := by
  classical
  let Cplus := momentPolynomialCoefficientMass T.D + 1
  let degree := T.D.totalDegree
  let E := 3 + degree
  let e : ℝ := (m + E + 1 : ℕ)
  have he : 0 < e := by dsimp [e, E]; positivity
  have hGap := MS.gapStage.gap_dominates_pool_and_bound l e he
  have hRatio : Tendsto
      (fun N => (MS.core.parameters.H N l : ℝ) /
        (momentGapScale MS l N : ℝ) ^ e) atTop atTop := by
    apply hGap.congr'
    filter_upwards with N
    simp [momentGapScale]
  have hScale := momentGapScale_tendsto MS l
  have hJ : ∀ᶠ N : ℕ in atTop, J0 ≤ momentGapScale MS l N :=
    hScale.eventually_ge_atTop J0
  have hC : ∀ᶠ N : ℕ in atTop, Cplus ≤ momentGapScale MS l N :=
    hScale.eventually_ge_atTop Cplus
  have hRatioOne : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ (MS.core.parameters.H N l : ℝ) /
        (momentGapScale MS l N : ℝ) ^ e :=
    hRatio.eventually_ge_atTop 1
  filter_upwards [hJ, hC, hRatioOne] with N hJN hCN hRN
  let S := momentGapScale MS l N
  let U := (MS.primeStage.pool N l).upper
  let Dupper := J0 * (MS.core.parameters.M N * (Cplus * (U + 1) ^ degree))
  have hSpos : 0 < S := by dsimp [S, momentGapScale, masterScaleV]; omega
  have hSone : 1 ≤ S := Nat.one_le_iff_ne_zero.mpr hSpos.ne'
  have hMle : MS.core.parameters.M N ≤ S := by
    dsimp [S, momentGapScale, masterScaleV]
    omega
  have hUle : U + 1 ≤ S := by
    dsimp [S, momentGapScale, masterScaleV, U]
    omega
  have hJle : J0 ≤ S := by simpa [S] using hJN
  have hCle : Cplus ≤ S := by simpa [S] using hCN
  have hpowle : (U + 1) ^ degree ≤ S ^ degree :=
    Nat.pow_le_pow_left hUle degree
  have hDupper : Dupper ≤ S ^ E := by
    have hCoeff : Cplus * (U + 1) ^ degree ≤ S * S ^ degree :=
      Nat.mul_le_mul hCle hpowle
    have hMterm : MS.core.parameters.M N * (Cplus * (U + 1) ^ degree) ≤
        S * (S * S ^ degree) := Nat.mul_le_mul hMle hCoeff
    have hAll : J0 * (MS.core.parameters.M N * (Cplus * (U + 1) ^ degree)) ≤
        S * (S * (S * S ^ degree)) := Nat.mul_le_mul hJle hMterm
    have hpow3 : S * S * S = S ^ 3 := by rw [pow_succ, pow_two]
    change Dupper ≤ S ^ (3 + degree)
    calc
      _ = J0 * (MS.core.parameters.M N * (Cplus * (U + 1) ^ degree)) := rfl
      _ ≤ S * (S * (S * S ^ degree)) := hAll
      _ = (S * S * S) * S ^ degree := by ring
      _ = S ^ 3 * S ^ degree := by rw [hpow3]
      _ = S ^ (3 + degree) := (pow_add S 3 degree).symm
  have hDenpos : 0 < Dupper := by
    have hCpos : 0 < Cplus := by dsimp [Cplus]; omega
    dsimp [Dupper]
    exact Nat.mul_pos hJ0 <| Nat.mul_pos (MS.core.parameters.Mpos N) <|
      Nat.mul_pos hCpos (Nat.pow_pos (Nat.zero_lt_succ U))
  have hHreal : (S : ℝ) ^ e ≤ MS.core.parameters.H N l := by
    have hsreal : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hSpos
    have hpowpos : (0 : ℝ) < (S : ℝ) ^ e := Real.rpow_pos_of_pos hsreal e
    have hmul := (le_div_iff₀ hpowpos).1 hRN
    simpa using hmul
  have hHnat : S ^ (m + E + 1) ≤ MS.core.parameters.H N l := by
    have hpowcast : (S : ℝ) ^ e = (S : ℝ) ^ ((m + E + 1 : ℕ) : ℝ) := by
      rfl
    have hpowNat : (S : ℝ) ^ ((m + E + 1 : ℕ) : ℝ) =
        (S : ℝ) ^ (m + E + 1 : ℕ) := Real.rpow_natCast (S : ℝ) _
    rw [hpowcast, hpowNat] at hHreal
    exact_mod_cast hHreal
  have hq : S ^ m ≤ MS.core.parameters.H N l / Dupper := by
    apply (Nat.le_div_iff_mul_le hDenpos).2
    calc
      S ^ m * Dupper ≤ S ^ m * S ^ E := Nat.mul_le_mul_left _ hDupper
      _ = S ^ (m + E) := (pow_add S m E).symm
      _ ≤ S ^ (m + E + 1) := Nat.pow_le_pow_right hSpos (by omega)
      _ ≤ MS.core.parameters.H N l := hHnat
  simpa [momentShiftLengthLower, Cplus, degree, Dupper, U, S, momentGapScale] using hq

private theorem momentModulus_rationalResidue_ne_zero {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ) (k : Fin b)
    (r : ℕ) (hr : r.Prime) (hrN : N + 1 < r)
    (hno : ¬ ((r : ℤ) ∣ evalIntegerPolynomial T.D
      (fun j => (p ((momentPrimeEnum b T.q).symm (k, j)) : ℤ)))) :
    rationalResidue r hr (momentModulus MS b T l N p k : ℚ) ≠ 0 := by
  have hM : ¬ r ∣ MS.core.parameters.M N := by
    obtain ⟨e, he⟩ := MS.core.modulus_power N
    intro hdiv
    rw [he] at hdiv
    have hW : r ∣ primorial (N + 1) := hr.dvd_of_dvd_pow hdiv
    have hle := (Nat.Prime.dvd_primorial_iff hr).mp hW
    omega
  have hrough : ¬ r ∣ roughPart (N + 1)
      (evalIntegerPolynomial T.D
        (fun j => (p ((momentPrimeEnum b T.q).symm (k, j)) : ℤ))) := by
    intro hd
    have hnat := prime_dvd_roughPart_implies_dvd_natAbs hr hd
    exact hno (Int.natCast_dvd.mpr hnat)
  have hmod : ¬ r ∣ momentModulus MS b T l N p k := by
    change ¬ r ∣ MS.core.parameters.M N * roughPart (N + 1)
      (evalIntegerPolynomial T.D
        (fun j => (p ((momentPrimeEnum b T.q).symm (k, j)) : ℤ)))
    intro hd
    rcases hr.dvd_mul.mp hd with hdivM | hdivR
    · exact hM hdivM
    · exact hrough hdivR
  have hcast : (momentModulus MS b T l N p k : ZMod r) ≠ 0 := by
    intro hz
    have hd : r ∣ momentModulus MS b T l N p k :=
      (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact hmod hd
  have hres : rationalResidue r hr (momentModulus MS b T l N p k : ℚ) =
      (momentModulus MS b T l N p k : ZMod r) := by
    letI : Fact r.Prime := ⟨hr⟩
    simp [rationalResidue]
  rw [hres]
  exact hcast

private def momentRowSupport {b d : ℕ} : MomentRowIndex b d → Finset (Fin b × Fin d)
  | .inl _ => ∅
  | .inr (k, ω) => Finset.univ.filter fun x => x.1 = k ∧ x.2 ∈ ω.1

private theorem momentRowSupport_injective {b d : ℕ} :
    Function.Injective (momentRowSupport (b := b) (d := d)) := by
  classical
  intro u v huv
  cases u with
  | inl a =>
      cases v with
      | inl b' => rfl
      | inr pair =>
          rcases pair with ⟨k, ω⟩
          obtain ⟨j, hj⟩ := ω.2
          have hmem : (k, j) ∈ momentRowSupport (Sum.inr (k, ω)) := by
            simp [momentRowSupport, hj]
          rw [← huv] at hmem
          simp [momentRowSupport] at hmem
  | inr pair =>
      rcases pair with ⟨k, ω⟩
      cases v with
      | inl b' =>
          obtain ⟨j, hj⟩ := ω.2
          have hmem : (k, j) ∈ momentRowSupport (Sum.inr (k, ω)) := by
            simp [momentRowSupport, hj]
          rw [huv] at hmem
          simp [momentRowSupport] at hmem
      | inr pair' =>
          rcases pair' with ⟨k', ω'⟩
          have hk : k = k' := by
            obtain ⟨j, hj⟩ := ω.2
            have hmem : (k, j) ∈ momentRowSupport (Sum.inr (k, ω)) := by
              simp [momentRowSupport, hj]
            have hmem' : (k, j) ∈ momentRowSupport (Sum.inr (k', ω')) := by
              simpa [huv] using hmem
            have hpair : k = k' ∧ j ∈ ω'.1 := by
              simpa [momentRowSupport] using hmem'
            exact hpair.1
          have hω : ω.1 = ω'.1 := by
            apply Finset.ext
            intro j
            constructor
            · intro hj
              have hmem : (k, j) ∈ momentRowSupport (Sum.inr (k, ω)) := by
                simp [momentRowSupport, hj]
              have hmem' : (k, j) ∈ momentRowSupport (Sum.inr (k', ω')) := by
                simpa [huv] using hmem
              simpa [momentRowSupport, hk] using hmem'
            · intro hj
              have hmem : (k', j) ∈ momentRowSupport (Sum.inr (k', ω')) := by
                simp [momentRowSupport, hj]
              have hmem' : (k', j) ∈ momentRowSupport (Sum.inr (k, ω)) := by
                simpa [huv.symm] using hmem
              simpa [momentRowSupport, hk] using hmem'
          subst k'
          have hω' : ω = ω' := Subtype.ext hω
          subst ω'
          rfl

private theorem momentRowCoeffInt_shift_formula {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (u : Fin (Fintype.card (MomentRowIndex b T.d))) (k : Fin b) (j : Fin T.d) :
    momentRowCoeffInt MS b T l N p u
      ((momentBaseEnum b T.d).symm (.inr (k, (j, (0 : Fin 2))))) =
      if (k, j) ∈ momentRowSupport (momentRowEnum b T.d u) then
        -(momentModulus MS b T l N p k : ℤ) else 0 := by
  classical
  have hbase := (momentBaseEnum b T.d).apply_symm_apply
    (.inr (k, (j, (0 : Fin 2))))
  cases hrow : momentRowEnum b T.d u with
  | inl _ =>
      simp [momentRowCoeffInt, momentRowSupport, hbase, hrow]
  | inr row =>
      rcases row with ⟨k', ω⟩
      by_cases hk : k = k'
      · subst k'
        by_cases hj : j ∈ ω.1 <;>
          simp [momentRowCoeffInt, momentRowSupport, hbase, hrow, hj]
      · simp [momentRowCoeffInt, momentRowSupport, hbase, hrow, hk, eq_comm]

private theorem momentRowSupport_exists_symmetric_difference {b d : ℕ}
    {u v : MomentRowIndex b d} (huv : u ≠ v) :
    ∃ x, (x ∈ momentRowSupport u ∧ x ∉ momentRowSupport v) ∨
      (x ∈ momentRowSupport v ∧ x ∉ momentRowSupport u) := by
  classical
  have hne : momentRowSupport u ≠ momentRowSupport v := fun h => huv
    (momentRowSupport_injective h)
  by_contra hnone
  have hmem (x : Fin b × Fin d) :
      x ∈ momentRowSupport u ↔ x ∈ momentRowSupport v := by
    by_cases hx : x ∈ momentRowSupport u
    · have hy : x ∈ momentRowSupport v := by
        by_contra hy
        exact hnone ⟨x, Or.inl ⟨hx, hy⟩⟩
      exact ⟨fun _ => hy, fun _ => hx⟩
    · have hy : x ∉ momentRowSupport v := by
        intro hy
        exact hnone ⟨x, Or.inr ⟨hy, hx⟩⟩
      exact ⟨fun h => (hx h).elim, fun h => (hy h).elim⟩
  exact hne (Finset.ext hmem)

private theorem rationalResidue_intCast (r : ℕ) (hr : r.Prime) (z : ℤ) :
    rationalResidue r hr (z : ℚ) = (z : ZMod r) := by
  letI : Fact r.Prime := ⟨hr⟩
  simp [rationalResidue]

private theorem momentRows_pairwise_independent {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (r : ℕ) (hr : r.Prime) (hrN : N + 1 < r)
    (hno : ∀ k : Fin b, ¬ ((r : ℤ) ∣ evalIntegerPolynomial T.D
      (fun j => (p ((momentPrimeEnum b T.q).symm (k, j)) : ℤ))))
    (u v : Fin (Fintype.card (MomentRowIndex b T.d))) (huv : u ≠ v) :
    ∃ i j, rationalResidue r hr
        (momentRowCoeff MS b T l N p u i) *
          rationalResidue r hr (momentRowCoeff MS b T l N p v j) ≠
        rationalResidue r hr (momentRowCoeff MS b T l N p u j) *
          rationalResidue r hr (momentRowCoeff MS b T l N p v i) := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  have hrows : momentRowEnum b T.d u ≠ momentRowEnum b T.d v := by
    intro h
    exact huv ((momentRowEnum b T.d).injective h)
  obtain ⟨⟨k, j⟩, hsep⟩ := momentRowSupport_exists_symmetric_difference hrows
  let root := (momentBaseEnum b T.d).symm (.inl ())
  let shift := (momentBaseEnum b T.d).symm (.inr (k, (j, (0 : Fin 2))))
  have hM := momentModulus_rationalResidue_ne_zero MS b T l N p k r hr hrN (hno k)
  have hMZ : (momentModulus MS b T l N p k : ZMod r) ≠ 0 := by
    have hM' : rationalResidue r hr
        ((momentModulus MS b T l N p k : ℤ) : ℚ) ≠ 0 := by
      simpa using hM
    rw [rationalResidue_intCast] at hM'
    simpa only [Int.cast_natCast] using hM'
  have hneg : rationalResidue r hr
      (-(momentModulus MS b T l N p k : ℤ) : ℚ) ≠ 0 := by
    have hMZInt : ((momentModulus MS b T l N p k : ℤ) : ZMod r) ≠ 0 := by
      simpa only [Int.cast_natCast] using hMZ
    have hnegZ : ((-(momentModulus MS b T l N p k : ℤ) : ℤ) : ZMod r) ≠ 0 := by
      simpa only [Int.cast_neg] using (neg_ne_zero.mpr hMZInt)
    rw [← Int.cast_neg, rationalResidue_intCast]
    exact hnegZ
  have hr0 : rationalResidue r hr (0 : ℚ) = 0 := by
    simp [rationalResidue]
  have hrootU := momentRowCoeff_root_residue MS b T l N p u r hr
  have hrootV := momentRowCoeff_root_residue MS b T l N p v r hr
  rcases hsep with hsep | hsep
  · have hu : momentRowCoeff MS b T l N p u shift =
        (-(momentModulus MS b T l N p k : ℤ) : ℚ) := by
      rw [momentRowCoeff_eq_castInt, momentRowCoeffInt_shift_formula]
      simp [hsep.1]
    have hv : momentRowCoeff MS b T l N p v shift = 0 := by
      rw [momentRowCoeff_eq_castInt, momentRowCoeffInt_shift_formula]
      simp [hsep.2]
    refine ⟨root, shift, ?_⟩
    rw [hrootU, hrootV, hu, hv]
    simpa [hr0] using hneg.symm
  · have hu : momentRowCoeff MS b T l N p u shift = 0 := by
      rw [momentRowCoeff_eq_castInt, momentRowCoeffInt_shift_formula]
      simp [hsep.2]
    have hv : momentRowCoeff MS b T l N p v shift =
        (-(momentModulus MS b T l N p k : ℤ) : ℚ) := by
      rw [momentRowCoeff_eq_castInt, momentRowCoeffInt_shift_formula]
      simp [hsep.1]
    refine ⟨root, shift, ?_⟩
    rw [hrootU, hrootV, hu, hv]
    simpa [hr0] using hneg

private noncomputable def momentReplicaEmbedding {b q : ℕ} (k : Fin b) :
    Fin q ↪ Fin (Fintype.card (MomentPrimeIndex b q)) where
  toFun j := (momentPrimeEnum b q).symm (k, j)
  inj' := by
    intro i j hij
    have hpairs : (k, i) = (k, j) := by
      simpa using congrArg (momentPrimeEnum b q) hij
    exact congrArg Prod.snd hpairs

private noncomputable def momentMasterEmbedding {sl : ℕ} {Dm : Finset (IntegerPolynomial sl)}
    {T : CubeTemplate} (hT : Allowed Dm T) : Fin T.q ↪ Fin sl := Classical.choose hT

private theorem momentMasterEmbedding_tests {sl : ℕ} {Dm : Finset (IntegerPolynomial sl)}
    {T : CubeTemplate} (hT : Allowed Dm T) :
    TestsListed Dm (momentMasterEmbedding hT) T.tests := Classical.choose_spec hT

private noncomputable def momentPrimeDiagonal {sl b : ℕ} {Dm : Finset (IntegerPolynomial sl)}
    {T : CubeTemplate} (hT : Allowed Dm T) :
    (Fin sl → ℕ) → Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ :=
  fun p u => p (momentMasterEmbedding hT (momentPrimeEnum b T.q u).2)

private theorem momentPrimeDiagonal_apply {sl b : ℕ}
    {Dm : Finset (IntegerPolynomial sl)} {T : CubeTemplate}
    (hT : Allowed Dm T) (p : Fin sl → ℕ) (k : Fin b) (j : Fin T.q) :
    momentPrimeDiagonal hT p ((momentPrimeEnum b T.q).symm (k, j)) =
      p (momentMasterEmbedding hT j) := by
  simp [momentPrimeDiagonal]

private theorem momentModulus_diagonal {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (b : ℕ) (T : CubeTemplate) (l : Fin K) (N : ℕ)
    (hT : Allowed Dm T) (p : Fin sl → ℕ) (k : Fin b) :
    momentModulus MS b T l N (momentPrimeDiagonal hT p) k =
      T.modulus (corrScales MS) N (fun j => p (momentMasterEmbedding hT j)) := by
  simp only [momentModulus]
  congr 1
  funext j
  simp [momentPrimeDiagonal]

private theorem momentMasterEmbedding_eval {sl q : ℕ}
    (ι : Fin q ↪ Fin sl) (P : IntegerPolynomial q) (p : Fin sl → ℕ) :
    evalIntegerPolynomial (MvPolynomial.rename ι P) (fun i => (p i : ℤ)) =
      evalIntegerPolynomial P (fun j => (p (ι j) : ℤ)) := by
  unfold evalIntegerPolynomial
  rw [MvPolynomial.eval_rename]
  apply congrArg (fun f : Fin q → ℤ => MvPolynomial.eval f P)
  funext j
  rfl

private theorem momentMasterEmbedding_divisor_test {sl : ℕ} {Dm : Finset (IntegerPolynomial sl)}
    {T : CubeTemplate} (hT : Allowed Dm T) (P : IntegerPolynomial T.q)
    (hP : P ∈ T.tests) (p : Fin sl → ℕ) (r : ℕ) :
    ((r : ℤ) ∣ evalIntegerPolynomial P
      (fun j => (p (momentMasterEmbedding hT j) : ℤ))) ↔
      ((r : ℤ) ∣ evalIntegerPolynomial (MvPolynomial.rename (momentMasterEmbedding hT) P)
        (fun i => (p i : ℤ))) := by
  rw [momentMasterEmbedding_eval]

private theorem momentRows_pairwise_independent_master {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (b : ℕ) (T : CubeTemplate) (l : Fin K) (N : ℕ)
    (hT : Allowed Dm T) (p : Fin sl → ℕ)
    (r : ℕ) (hr : r.Prime) (hrN : N + 1 < r)
    (hno : ∀ Q ∈ Dm, ¬ ((r : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ))))
    (u v : Fin (Fintype.card (MomentRowIndex b T.d))) (huv : u ≠ v) :
    ∃ i j, rationalResidue r hr
        (momentRowCoeff MS b T l N (momentPrimeDiagonal hT p) u i) *
          rationalResidue r hr (momentRowCoeff MS b T l N (momentPrimeDiagonal hT p) v j) ≠
        rationalResidue r hr (momentRowCoeff MS b T l N (momentPrimeDiagonal hT p) u j) *
          rationalResidue r hr (momentRowCoeff MS b T l N (momentPrimeDiagonal hT p) v i) := by
  have hD : MvPolynomial.rename (momentMasterEmbedding hT) T.D ∈ Dm :=
    momentMasterEmbedding_tests hT T.D T.D_mem
  have hnoReplica : ∀ k : Fin b, ¬ ((r : ℤ) ∣ evalIntegerPolynomial T.D
      (fun j => (momentPrimeDiagonal hT p ((momentPrimeEnum b T.q).symm (k, j)) : ℤ))) := by
    intro k hdiv
    apply hno (MvPolynomial.rename (momentMasterEmbedding hT) T.D) hD
    exact (momentMasterEmbedding_divisor_test hT T.D T.D_mem p r).mp
      (by simpa only [momentPrimeDiagonal_apply] using hdiv)
  exact momentRows_pairwise_independent MS b T l N (momentPrimeDiagonal hT p)
    r hr hrN hnoReplica u v huv

private noncomputable def momentReplicaPolynomial {b q : ℕ} (k : Fin b)
    (P : IntegerPolynomial q) : IntegerPolynomial (Fintype.card (MomentPrimeIndex b q)) :=
  MvPolynomial.rename (momentReplicaEmbedding (b := b) (q := q) k) P

private theorem momentReplicaPolynomial_eval {b q : ℕ} (k : Fin b)
    (P : IntegerPolynomial q)
    (p : Fin (Fintype.card (MomentPrimeIndex b q)) → ℕ) :
    evalIntegerPolynomial (momentReplicaPolynomial (b := b) (q := q) k P) (fun i => (p i : ℤ)) =
      evalIntegerPolynomial P (fun j => (p ((momentPrimeEnum b q).symm (k, j)) : ℤ)) := by
  unfold momentReplicaPolynomial evalIntegerPolynomial
  rw [MvPolynomial.eval_rename]
  apply congrArg (fun f : Fin q → ℤ => MvPolynomial.eval f P)
  funext j
  rfl

private noncomputable def momentLinearFormsTests (b : ℕ) (T : CubeTemplate) :
    Finset (IntegerPolynomial (Fintype.card (MomentPrimeIndex b T.q))) :=
  Finset.univ.image fun k : Fin b =>
    momentReplicaPolynomial (b := b) (q := T.q) k T.D

private theorem momentReplicaTemplateTest_mem {b : ℕ} (T : CubeTemplate) (k : Fin b) :
    momentReplicaPolynomial (b := b) (q := T.q) k T.D ∈ momentLinearFormsTests b T := by
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩

private abbrev MomentTailIndex (K : ℕ) (B : Block K) := {j : Fin K // j ∈ B.2.val}
private abbrev MomentTailComplementFinset (K : ℕ) (B : Block K) :=
  (Finset.univ : Finset (Fin K)) \ B.2.val
private abbrev MomentTailComplementIndex (K : ℕ) (B : Block K) :=
  {j : Fin K // j ∈ MomentTailComplementFinset K B}

private noncomputable def momentTailEnum {K : ℕ} (B : Block K) :
    Fin (Fintype.card (MomentTailIndex K B)) ≃ MomentTailIndex K B :=
  (Fintype.equivFin _).symm

private noncomputable def momentTailTupleEquiv {K : ℕ} (B : Block K) :
    (Fin (Fintype.card (MomentTailIndex K B)) → ℕ) ≃ (MomentTailIndex K B → ℕ) :=
  (momentTailEnum B).arrowCongr (Equiv.refl ℕ)

private noncomputable def momentTailComplementEquiv {K : ℕ} (B : Block K) :
    {j : Fin K // j ∉ B.2.val} ≃ MomentTailComplementIndex K B where
  toFun j := ⟨j.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, j.2⟩⟩
  invFun j := ⟨j.1, (Finset.mem_sdiff.mp j.2).2⟩
  left_inv := by intro j; apply Subtype.ext; rfl
  right_inv := by intro j; apply Subtype.ext; rfl

private noncomputable def momentTailSplitEquiv {K : ℕ} (B : Block K) :
    (Fin K → ℕ) ≃
      (MomentTailIndex K B → ℕ) × (MomentTailComplementIndex K B → ℕ) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun j : Fin K => j ∈ B.2.val) (fun _ => ℕ)).trans
    (Equiv.prodCongr (Equiv.refl _) ((momentTailComplementEquiv B).arrowCongr (Equiv.refl ℕ)))

private noncomputable def momentTailDivisorTemplate {K : ℕ} (B : Block K) :
    DivisorTemplate K K :=
  { arity := Fintype.card (MomentTailIndex K B)
    arity_le := by
      have h := Fintype.card_le_of_injective
        (fun j : MomentTailIndex K B => j.1) Subtype.val_injective
      simpa using h
    cutoff := fun i => (momentTailEnum B i).1 }

private def momentUnitDivisorTemplate (K : ℕ) : DivisorTemplate K K :=
  { arity := 0
    arity_le := Nat.zero_le K
    cutoff := Fin.elim0 }

private noncomputable def momentDivisorFamily {K b d : ℕ} (B : Block K)
    (active : Finset (Fin (Fintype.card (MomentRowIndex b d)))) :
    Fin (Fintype.card (MomentRowIndex b d)) → DivisorTemplate K K := by
  classical
  exact fun u => if u ∈ active then momentTailDivisorTemplate B
    else momentUnitDivisorTemplate K

private def momentHarmonicNatSupport (X W : ℕ) : Finset ℕ :=
  (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)

private theorem momentHarmonicNatLaw_zero_of_not_mem (X W n : ℕ)
    (hn : n ∉ momentHarmonicNatSupport X W) : harmonicNatLaw X W n = 0 := by
  have hnot : ¬ (X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W) := by
    intro h
    apply hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
  simp [harmonicNatLaw, hnot]

private theorem momentDivisorLaw_support_witness {K : ℕ} (A : Parameters K) (N : ℕ)
    (D : DivisorTemplate K K) (σ : ℕ)
    (hσ : divisorTemplateLaw A N D σ ≠ 0) :
    ∃ t : Fin D.arity → ℕ,
      (∏ i, t i) = σ ∧
      ∀ i, A.X N (D.cutoff i) ≤ t i ∧ t i < (A.X N (D.cutoff i)) ^ 2 ∧
        Nat.Coprime (t i) (primorial (N + 1)) := by
  classical
  let X : Fin D.arity → ℕ := fun i => A.X N (D.cutoff i)
  let S : Fin D.arity → Finset ℕ := fun i => momentHarmonicNatSupport (X i)
    (primorial (N + 1))
  let T : Finset (Fin D.arity → ℕ) := Fintype.piFinset S
  let weight : (Fin D.arity → ℕ) → ℝ := fun t =>
    ∏ i, harmonicNatLaw (X i) (primorial (N + 1)) (t i)
  let product : (Fin D.arity → ℕ) → ℕ := fun t => ∏ i, t i
  have hweight_zero (t : Fin D.arity → ℕ) (ht : t ∉ T) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hzero : harmonicNatLaw (X i) (primorial (N + 1)) (t i) = 0 :=
      momentHarmonicNatLaw_zero_of_not_mem (X i) (primorial (N + 1)) (t i)
        (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
  have hterm_zero (t : Fin D.arity → ℕ) (ht : t ∉ T) :
      (if product t = σ then (1 : ℝ) else 0) * weight t = 0 := by
    simp [hweight_zero t ht]
  have hLawEq : divisorTemplateLaw A N D σ =
      ∑ t ∈ T, (if product t = σ then (1 : ℝ) else 0) * weight t := by
    unfold divisorTemplateLaw harmonicProductLaw
    rw [tsum_eq_sum (s := T) hterm_zero]
  have hsum :
      (∑ t ∈ T, (if product t = σ then (1 : ℝ) else 0) * weight t) ≠ 0 := by
    intro hzero
    apply hσ
    rw [hLawEq, hzero]
  have hsome : ∃ t ∈ T,
      (if product t = σ then (1 : ℝ) else 0) * weight t ≠ 0 := by
    by_contra hnone
    have hz : ∀ t ∈ T,
        (if product t = σ then (1 : ℝ) else 0) * weight t = 0 := by
      intro t ht
      by_contra hne
      exact hnone ⟨t, ht, hne⟩
    exact hsum (Finset.sum_eq_zero hz)
  obtain ⟨t, ht, hterm⟩ := hsome
  have hproduct : product t = σ := by
    by_contra hneq
    have : (if product t = σ then (1 : ℝ) else 0) * weight t = 0 := by simp [hneq]
    exact hterm this
  have hweight : weight t ≠ 0 := by
    intro hz
    exact hterm (by simp [hz])
  have hraw (i : Fin D.arity) :
      X i ≤ t i ∧ t i < X i ^ 2 ∧ Nat.Coprime (t i) (primorial (N + 1)) := by
    have hfactor : harmonicNatLaw (X i) (primorial (N + 1)) (t i) ≠ 0 := by
      intro hz
      apply hweight
      dsimp [weight]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    by_contra hbad
    apply hfactor
    simp [harmonicNatLaw, hbad]
  refine ⟨t, ?_, ?_⟩
  · exact hproduct
  · intro i
    simpa [X] using hraw i

private theorem momentTailProduct_bounds {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm)
    (B : Block K) (l : Fin K) (hgap : ∀ j ∈ B.2.val, j < l)
    (N : ℕ) (t : Fin (Fintype.card (MomentTailIndex K B)) → ℕ)
    (ht : ∀ i, MS.core.parameters.X N (momentTailEnum B i).1 ≤ t i ∧
      t i < (MS.core.parameters.X N (momentTailEnum B i).1) ^ 2) :
    1 ≤ ∏ i, t i ∧ ∏ i, t i ≤ masterScaleV MS.core.parameters N l := by
  classical
  let f : MomentTailIndex K B → ℕ := fun j => (MS.core.parameters.X N j.1) ^ 2
  have hxone (j : MomentTailIndex K B) : 1 ≤ MS.core.parameters.X N j.1 :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (MS.core.parameters.Xpos N j.1))
  have hone : 1 ≤ ∏ i, t i :=
    Finset.one_le_prod fun i _ => (hxone (momentTailEnum B i)).trans (ht i).1
  have hprod : ∏ i : Fin (Fintype.card (MomentTailIndex K B)), f (momentTailEnum B i) =
      ∏ j : MomentTailIndex K B, f j := by
    exact Fintype.prod_equiv (momentTailEnum B) _ _ (fun i => rfl)
  have hsubtype : ∏ j : MomentTailIndex K B, f j =
      ∏ j ∈ B.2.val, (MS.core.parameters.X N j) ^ 2 := by
    change (∏ j : {j : Fin K // j ∈ B.2.val},
        (MS.core.parameters.X N j.1) ^ 2) = _
    symm
    exact Finset.prod_subtype B.2.val (by intro j; rfl)
      (fun j => (MS.core.parameters.X N j) ^ 2)
  have htail : B.2.val ⊆ Finset.univ.filter (fun j : Fin K => j < l) := by
    intro j hj
    simp [hgap j hj]
  have hprefix : (∏ j ∈ B.2.val, (MS.core.parameters.X N j) ^ 2) ≤
      ∏ j ∈ Finset.univ.filter (fun j : Fin K => j < l), (MS.core.parameters.X N j) ^ 2 :=
    Finset.prod_le_prod_of_subset_of_one_le htail fun j hj _ =>
      one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr
        (ne_of_gt (MS.core.parameters.Xpos N j)))
  have htprod : ∏ i : Fin (Fintype.card (MomentTailIndex K B)), t i ≤
      ∏ i : Fin (Fintype.card (MomentTailIndex K B)), f (momentTailEnum B i) :=
    Finset.prod_le_prod fun i _ => (ht i).2.le
  constructor
  · exact hone
  · dsimp [masterScaleV]
    calc
      ∏ i, t i ≤ ∏ i, f (momentTailEnum B i) := htprod
      _ = ∏ j ∈ B.2.val, (MS.core.parameters.X N j) ^ 2 := hprod.trans hsubtype
      _ ≤ ∏ j ∈ Finset.univ.filter (fun j : Fin K => j < l),
            (MS.core.parameters.X N j) ^ 2 := hprefix
      _ ≤ 2 + MS.core.parameters.M N +
            ∏ j ∈ Finset.univ.filter (fun j : Fin K => j < l),
              (MS.core.parameters.X N j) ^ 2 := by omega

private theorem momentDivisorFamily_support_specs {K b d sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hgap : ∀ j ∈ B.2.val, j < l)
    (active : Finset (Fin (Fintype.card (MomentRowIndex b d))))
    (u : Fin (Fintype.card (MomentRowIndex b d))) (N σ : ℕ)
    (hσ : divisorTemplateLaw MS.core.parameters N (momentDivisorFamily B active u) σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ masterScaleV MS.core.parameters N l := by
  classical
  by_cases ha : u ∈ active
  · have hlaw : divisorTemplateLaw MS.core.parameters N (momentTailDivisorTemplate B) σ ≠ 0 := by
      simpa [momentDivisorFamily, ha] using hσ
    obtain ⟨t, hprod, hraw⟩ :=
      momentDivisorLaw_support_witness MS.core.parameters N (momentTailDivisorTemplate B) σ hlaw
    have ht (i : Fin (Fintype.card (MomentTailIndex K B))) :
        MS.core.parameters.X N (momentTailEnum B i).1 ≤ t i ∧
          t i < (MS.core.parameters.X N (momentTailEnum B i).1) ^ 2 := by
      simpa [momentTailDivisorTemplate] using ⟨(hraw i).1, (hraw i).2.1⟩
    have hb := momentTailProduct_bounds MS B l hgap N t ht
    constructor
    · calc
        1 ≤ ∏ i, t i := hb.1
        _ = σ := hprod
    · calc
        σ = ∏ i, t i := hprod.symm
        _ ≤ masterScaleV MS.core.parameters N l := hb.2
  · have hlaw : divisorTemplateLaw MS.core.parameters N (momentUnitDivisorTemplate K) σ ≠ 0 := by
      simpa [momentDivisorFamily, ha] using hσ
    obtain ⟨t, hprod, _⟩ :=
      momentDivisorLaw_support_witness MS.core.parameters N (momentUnitDivisorTemplate K) σ hlaw
    have hσeq : σ = 1 := by
      have hprod0 : (∏ i : Fin 0, t i) = σ := by
        change (∏ i : Fin 0, t i) = σ at hprod
        exact hprod
      calc
        σ = ∏ i : Fin 0, t i := hprod0.symm
        _ = 1 := Fintype.prod_empty _
    refine ⟨by omega, ?_⟩
    rw [hσeq]
    dsimp [masterScaleV]
    omega

private theorem momentDivisorFamily_support_coprime {K b d sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (active : Finset (Fin (Fintype.card (MomentRowIndex b d))))
    (u : Fin (Fintype.card (MomentRowIndex b d))) (N σ : ℕ)
    (hσ : divisorTemplateLaw MS.core.parameters N (momentDivisorFamily B active u) σ ≠ 0) :
    Nat.Coprime σ (primorial (N + 1)) := by
  classical
  by_cases ha : u ∈ active
  · have hlaw : divisorTemplateLaw MS.core.parameters N (momentTailDivisorTemplate B) σ ≠ 0 := by
      simpa [momentDivisorFamily, ha] using hσ
    obtain ⟨t, hprod, hraw⟩ := momentDivisorLaw_support_witness
      MS.core.parameters N (momentTailDivisorTemplate B) σ hlaw
    have hcop : Nat.Coprime (∏ i, t i) (primorial (N + 1)) := by
      rw [Nat.coprime_fintype_prod_left_iff]
      intro i
      exact (hraw i).2.2
    rw [← hprod]
    exact hcop
  · have hlaw : divisorTemplateLaw MS.core.parameters N (momentUnitDivisorTemplate K) σ ≠ 0 := by
      simpa [momentDivisorFamily, ha] using hσ
    obtain ⟨t, hprod, _⟩ := momentDivisorLaw_support_witness
      MS.core.parameters N (momentUnitDivisorTemplate K) σ hlaw
    have hσeq : σ = 1 := by
      calc
        σ = ∏ i : Fin 0, t i := hprod.symm
        _ = 1 := Fintype.prod_empty _
    simpa [hσeq]

private theorem momentLinearRowValue_eq_castInt {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (u : Fin (Fintype.card (MomentRowIndex b T.d)))
    (x : Fin (Fintype.card (MomentBaseIndex b T.d)) → ℤ) :
    linearRowValue (momentRowCoeff MS b T l) N p u x =
      ((∑ j : Fin (Fintype.card (MomentBaseIndex b T.d)),
        momentRowCoeffInt MS b T l N p u j * x j : ℤ) : ℚ) := by
  classical
  unfold linearRowValue
  calc
    (∑ j, momentRowCoeff MS b T l N p u j * (x j : ℚ)) =
        ∑ j, ((momentRowCoeffInt MS b T l N p u j * x j : ℤ) : ℚ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [momentRowCoeff_eq_castInt]
          exact (Int.cast_mul _ _).symm
    _ = ((∑ j : Fin (Fintype.card (MomentBaseIndex b T.d)),
        momentRowCoeffInt MS b T l N p u j * x j : ℤ) : ℚ) := by
          rw [Int.cast_sum]

private theorem momentLinearRowValue_den_eq_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (b : ℕ) (T : CubeTemplate)
    (l : Fin K) (N : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (u : Fin (Fintype.card (MomentRowIndex b T.d)))
    (x : Fin (Fintype.card (MomentBaseIndex b T.d)) → ℤ) :
    (linearRowValue (momentRowCoeff MS b T l) N p u x).den = 1 := by
  rw [momentLinearRowValue_eq_castInt]
  simp only [Rat.den_intCast]

theorem clip_eq_self_of_abs_le (K x : ℝ) (hx : |x| ≤ K) :
    clip K x = x := by
  have hx' := (abs_le.mp hx)
  simp [clip, max_eq_right hx'.1, min_eq_right hx'.2]

theorem clip_error_abs_le_abs (K x : ℝ) (hK : 0 ≤ K) :
    |x - clip K x| ≤ |x| := by
  by_cases hx : |x| ≤ K
  · rw [clip_eq_self_of_abs_le K x hx]
    simp
  · have hxK : K < |x| := lt_of_not_ge hx
    by_cases hneg : x < 0
    · have hxlow : x < -K := by
        rw [abs_of_neg hneg] at hxK
        linarith
      have hclip : clip K x = -K := by
        simp [clip, max_eq_left (le_of_lt hxlow),
          min_eq_right (by linarith : x ≤ K)]
      rw [hclip, show x - -K = x + K by ring,
        abs_of_nonpos (by linarith), abs_of_neg hneg]
      linarith
    · have hxpos : 0 ≤ x := le_of_not_gt hneg
      have hxhigh : K < x := by
        rw [abs_of_nonneg hxpos] at hxK
        exact hxK
      have hclip : clip K x = K := by
        simp [clip, min_eq_left (le_of_lt hxhigh),
          max_eq_right (by linarith : -K ≤ K)]
      rw [hclip, show x - K = x - K by rfl,
        abs_of_nonneg (by linarith), abs_of_nonneg hxpos]
      linarith

theorem clip_abs_le_abs (K x : ℝ) (hK : 0 ≤ K) :
    |clip K x| ≤ |x| := by
  by_cases hx : |x| ≤ K
  · rw [clip_eq_self_of_abs_le K x hx]
  · have hxK : K < |x| := lt_of_not_ge hx
    by_cases hneg : x < 0
    · have hxlow : x < -K := by
        rw [abs_of_neg hneg] at hxK
        linarith
      have hclip : clip K x = -K := by
        simp [clip, max_eq_left (le_of_lt hxlow),
          min_eq_right (by linarith : x ≤ K)]
      rw [hclip]
      have hclipabs : |-K| = K := by simp [abs_of_nonneg hK]
      rw [hclipabs]
      exact le_of_lt hxK
    · have hxpos : 0 ≤ x := le_of_not_gt hneg
      have hxhigh : K < x := by
        rw [abs_of_nonneg hxpos] at hxK
        exact hxK
      have hclip : clip K x = K := by
        simp [clip, min_eq_left (le_of_lt hxhigh),
          max_eq_right (by linarith : -K ≤ K)]
      rw [hclip, abs_of_nonneg hK, abs_of_nonneg hxpos]
      exact le_of_lt hxhigh

theorem clip_error_pow_le (K x : ℝ) (hK : 0 < K) (p b : ℕ)
    (hp : p ≤ b) (hp0 : 0 < p) :
    |x - clip K x| ^ p ≤ (K ^ p * (K ^ b)⁻¹) * |x| ^ b := by
  have hK0 : 0 ≤ K := le_of_lt hK
  by_cases hx : |x| ≤ K
  · rw [clip_eq_self_of_abs_le K x hx]
    simp [Nat.ne_of_gt hp0]
    positivity
  · have hKx : K < |x| := lt_of_not_ge hx
    have herr := clip_error_abs_le_abs K x hK0
    have hpow : |x - clip K x| ^ p ≤ |x| ^ p := by gcongr
    have hsub : p + (b - p) = b := Nat.add_sub_of_le hp
    have hKpow : K ^ b = K ^ p * K ^ (b - p) := by
      calc
        K ^ b = K ^ (p + (b - p)) := by rw [hsub]
        _ = K ^ p * K ^ (b - p) := by rw [pow_add]
    have hpower : K ^ b * |x| ^ p ≤ K ^ p * |x| ^ b := by
      calc
        K ^ b * |x| ^ p = (K ^ p * K ^ (b - p)) * |x| ^ p := by rw [hKpow]
        _ ≤ (K ^ p * |x| ^ (b - p)) * |x| ^ p := by
          gcongr
        _ = K ^ p * |x| ^ b := by
          calc
            _ = K ^ p * (|x| ^ p * |x| ^ (b - p)) := by ring
            _ = K ^ p * |x| ^ b := by rw [← pow_add, hsub]
    have hmain :
        K ^ b * |x - clip K x| ^ p ≤ K ^ p * |x| ^ b :=
      le_trans (mul_le_mul_of_nonneg_left hpow (pow_nonneg hK0 _)) hpower
    have hinv : 0 ≤ (K ^ b)⁻¹ := inv_nonneg.mpr (pow_nonneg hK0 _)
    calc
      |x - clip K x| ^ p =
          (K ^ b)⁻¹ * (K ^ b * |x - clip K x| ^ p) := by
            field_simp [ne_of_gt (pow_pos hK b)]
      _ ≤ (K ^ b)⁻¹ * (K ^ p * |x| ^ b) :=
        mul_le_mul_of_nonneg_left hmain hinv
      _ = (K ^ p * (K ^ b)⁻¹) * |x| ^ b := by ring

private theorem harmonicLaw_support_finite (X W : ℕ) :
    (Function.support (harmonicLaw X W)).Finite := by
  apply (Set.finite_Icc (X : ℤ) ((X ^ 2 : ℕ) : ℤ)).subset
  intro y hy
  change harmonicLaw X W y ≠ 0 at hy
  have hcond : 0 ≤ y ∧ X ≤ y.toNat ∧ y.toNat < X ^ 2 ∧
      Nat.Coprime y.toNat W := by
    by_contra h
    simpa [harmonicLaw, h] using hy
  rcases hcond with ⟨hy0, hX, hX2, _⟩
  have hcast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
  constructor
  · have hX' : (X : ℤ) ≤ (y.toNat : ℤ) := by exact_mod_cast hX
    simpa [hcast] using hX'
  · have hX2' : (y.toNat : ℤ) < ((X ^ 2 : ℕ) : ℤ) := by exact_mod_cast hX2
    rw [hcast] at hX2'
    exact hX2'.le

private theorem harmonicLaw_weight_summable (X W : ℕ) (f : ℤ → ℝ) :
    Summable (fun y => harmonicLaw X W y * f y) := by
  apply summable_of_hasFiniteSupport
  apply (harmonicLaw_support_finite X W).subset
  intro y hy
  change harmonicLaw X W y * f y ≠ 0 at hy
  change harmonicLaw X W y ≠ 0
  intro hzero
  simp [hzero] at hy

private theorem harmonicNormalizer_nonneg (X W : ℕ) :
    0 ≤ harmonicNormalizer X W := by
  unfold harmonicNormalizer
  apply Finset.sum_nonneg
  intro n hn
  positivity

theorem harmonicLaw_nonneg (X W : ℕ) (y : ℤ) : 0 ≤ harmonicLaw X W y := by
  unfold harmonicLaw
  split_ifs with h
  · exact div_nonneg (by norm_num)
      (mul_nonneg (by positivity) (harmonicNormalizer_nonneg X W))
  · simp

theorem Emu_mono {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    {f g : ℤ → ℝ} (hfg : ∀ y, f y ≤ g y) :
    Emu A N i f ≤ Emu A N i g := by
  unfold Emu
  exact Summable.tsum_le_tsum
    (fun y => mul_le_mul_of_nonneg_left (hfg y)
      (harmonicLaw_nonneg (A.X N i) (primorial (N + 1)) y))
    (harmonicLaw_weight_summable (A.X N i) (primorial (N + 1)) f)
    (harmonicLaw_weight_summable (A.X N i) (primorial (N + 1)) g)

theorem Emu_mul_left {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (c : ℝ) (f : ℤ → ℝ) :
    Emu A N i (fun y => c * f y) = c * Emu A N i f := by
  unfold Emu
  calc
    (∑' y, mu A N i y * (c * f y)) =
        ∑' y, c * (mu A N i y * f y) := by
          apply tsum_congr
          intro y
          ring
    _ = c * ∑' y, mu A N i y * f y :=
      (harmonicLaw_weight_summable (A.X N i) (primorial (N + 1)) f).tsum_mul_left c

theorem Emu_add {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (f g : ℤ → ℝ) :
    Emu A N i (fun y => f y + g y) = Emu A N i f + Emu A N i g := by
  unfold Emu
  have hf := harmonicLaw_weight_summable (A.X N i) (primorial (N + 1)) f
  have hg := harmonicLaw_weight_summable (A.X N i) (primorial (N + 1)) g
  calc
    (∑' y, mu A N i y * (f y + g y)) =
        (∑' y, (mu A N i y * f y + mu A N i y * g y)) := by
          apply tsum_congr
          intro y
          ring
    _ = (∑' y, mu A N i y * f y) + ∑' y, mu A N i y * g y :=
      Summable.tsum_add hf hg

theorem Emu_nonneg {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    {f : ℤ → ℝ} (hf : ∀ y, 0 ≤ f y) :
    0 ≤ Emu A N i f := by
  have h := Emu_mono A N i (f := fun _ => 0) (g := f) (fun y => hf y)
  simpa [Emu] using h

private theorem harmonicNatLaw_nonneg (X W n : ℕ) :
    0 ≤ harmonicNatLaw X W n := by
  unfold harmonicNatLaw
  split_ifs with h
  · exact div_nonneg (by norm_num)
      (mul_nonneg (by positivity) (harmonicNormalizer_nonneg X W))
  · simp

private theorem momentHarmonicNatLaw_tsum_eq_one (X W : ℕ) (hX : 0 < X)
    (hH : 0 < harmonicNormalizer X W) :
    ∑' n : ℕ, harmonicNatLaw X W n = 1 := by
  let S := momentHarmonicNatSupport X W
  have hzero : ∀ n ∉ S, harmonicNatLaw X W n = 0 := by
    intro n hn
    exact momentHarmonicNatLaw_zero_of_not_mem X W n (by simpa [S] using hn)
  rw [tsum_eq_sum (s := S) hzero]
  calc
    (∑ n ∈ S, harmonicNatLaw X W n) =
        ∑ n ∈ S, (1 / (n : ℝ)) / harmonicNormalizer X W := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnrange := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hX hnrange.1
      have hvalid : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W :=
        ⟨hnrange.1, hnrange.2, (Finset.mem_filter.mp hn).2⟩
      rw [show harmonicNatLaw X W n =
        1 / ((n : ℝ) * harmonicNormalizer X W) by
          simp [harmonicNatLaw, hvalid.1, hvalid.2.1, hvalid.2.2]]
      field_simp [ne_of_gt hnpos, ne_of_gt hH]
    _ = (∑ n ∈ S, 1 / (n : ℝ)) / harmonicNormalizer X W := by
      rw [Finset.sum_div]
    _ = 1 := by
      rw [show (∑ n ∈ S, 1 / (n : ℝ)) = harmonicNormalizer X W by
        simp [harmonicNormalizer, S, momentHarmonicNatSupport]]
      exact div_self (ne_of_gt hH)

private theorem momentHarmonicNatTupleLaw_tsum_eq_one {ι : Type*} [Fintype ι]
    (W : ℕ) (X : ι → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W) :
    ∑' t : ι → ℕ, ∏ i, harmonicNatLaw (X i) W (t i) = 1 := by
  classical
  let S : ι → Finset ℕ := fun i => momentHarmonicNatSupport (X i) W
  let T : Finset (∀ i, ℕ) := Fintype.piFinset S
  have hzero : ∀ t ∉ T, ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    intro t ht
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro h
      exact ht (Fintype.mem_piFinset.mpr h)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (momentHarmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi))
  have hfactor :
      (∑ t ∈ T, ∏ i, harmonicNatLaw (X i) W (t i)) =
        ∏ i, ∑ n ∈ S i, harmonicNatLaw (X i) W n := by
    simpa [T] using (Finset.prod_univ_sum S
      (fun i n => harmonicNatLaw (X i) W n)).symm
  have hlocal (i : ι) :
      (∑ n ∈ S i, harmonicNatLaw (X i) W n) = 1 := by
    have hzeroI : ∀ n ∉ S i, harmonicNatLaw (X i) W n = 0 := by
      intro n hn
      exact momentHarmonicNatLaw_zero_of_not_mem (X i) W n (by simpa [S] using hn)
    calc
      _ = ∑' n : ℕ, harmonicNatLaw (X i) W n :=
        (tsum_eq_sum (s := S i) hzeroI).symm
      _ = 1 := momentHarmonicNatLaw_tsum_eq_one (X i) W (hX i) (hH i)
  calc
    _ = ∑ t ∈ T, ∏ i, harmonicNatLaw (X i) W (t i) :=
      tsum_eq_sum (s := T) hzero
    _ = ∏ i, ∑ n ∈ S i, harmonicNatLaw (X i) W n := hfactor
    _ = 1 := by simp_rw [hlocal]; simp

private theorem momentTailSplit_weight_factor {K : ℕ} (A : Parameters K) (N : ℕ)
    (B : Block K) (t : Fin K → ℕ) :
    (∏ j : Fin K, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
      (∏ j ∈ B.2.val, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) *
      ∏ j ∈ (Finset.univ : Finset (Fin K)) \ B.2.val,
        harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
  classical
  let C : Finset (Fin K) := Finset.univ \ B.2.val
  have hdisj : Disjoint B.2.val C := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext j
    simp [C]
  have hunion : B.2.val ∪ C = Finset.univ := by
    ext j
    simp [C]
  calc
    _ = ∏ j ∈ (Finset.univ : Finset (Fin K)),
          harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by simp
    _ = ∏ j ∈ B.2.val ∪ C,
          harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by rw [← hunion]
    _ = _ := Finset.prod_union hdisj

private theorem momentTailSplit_product {K : ℕ} (B : Block K) (t : Fin K → ℕ) :
    (∏ j ∈ B.2.val, t j) =
      ∏ j ∈ B.2.val.attach, t j.1 := by
  classical
  rw [Finset.prod_attach]

private theorem momentTailSplit_product_fintype {K : ℕ} (B : Block K) (t : Fin K → ℕ) :
    (∏ j ∈ B.2.val, t j) =
      ∏ j : MomentTailIndex K B, (momentTailSplitEquiv B t).1 j := by
  calc
    _ = ∏ j ∈ B.2.val.attach, t j.1 := momentTailSplit_product B t
    _ = ∏ j : MomentTailIndex K B, (momentTailSplitEquiv B t).1 j := by
      simpa [momentTailSplitEquiv, Equiv.piEquivPiSubtypeProd] using
        momentTailAttachProduct_eq_fintype B.2.val (fun j => t j.1)

private theorem momentTailSplit_weight_factor_fintype {K : ℕ} (A : Parameters K) (N : ℕ)
    (B : Block K) (t : Fin K → ℕ) :
    (∏ j : Fin K, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
      (∏ j : MomentTailIndex K B,
        harmonicNatLaw (A.X N j.1) (primorial (N + 1))
          ((momentTailSplitEquiv B t).1 j)) *
      ∏ j : MomentTailComplementIndex K B,
        harmonicNatLaw (A.X N j.1) (primorial (N + 1))
          ((momentTailSplitEquiv B t).2 j) := by
  let C : Finset (Fin K) := Finset.univ \ B.2.val
  have htail :
      (∏ j ∈ B.2.val, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
        ∏ j : MomentTailIndex K B,
          harmonicNatLaw (A.X N j.1) (primorial (N + 1))
            ((momentTailSplitEquiv B t).1 j) := by
    calc
      _ = ∏ j ∈ B.2.val.attach,
            harmonicNatLaw (A.X N j.1) (primorial (N + 1)) (t j.1) := by
              exact (Finset.prod_attach B.2.val
                (fun j => harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j))).symm
      _ = _ := by
            simpa [momentTailSplitEquiv, Equiv.piEquivPiSubtypeProd] using
              momentTailAttachProduct_eq_fintype B.2.val
                (fun j => harmonicNatLaw (A.X N j.1) (primorial (N + 1)) (t j.1))
  have hcomp :
      (∏ j ∈ C, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
        ∏ j : MomentTailComplementIndex K B,
          harmonicNatLaw (A.X N j.1) (primorial (N + 1))
            ((momentTailSplitEquiv B t).2 j) := by
    calc
      _ = ∏ j ∈ C.attach,
            harmonicNatLaw (A.X N j.1) (primorial (N + 1)) (t j.1) := by
              exact (Finset.prod_attach C
                (fun j => harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j))).symm
      _ = _ := by
            simpa [C, momentTailSplitEquiv, momentTailComplementEquiv,
              Equiv.piEquivPiSubtypeProd] using
              momentTailAttachProduct_eq_fintype C
                (fun j => harmonicNatLaw (A.X N j.1) (primorial (N + 1)) (t j.1))
  calc
    _ = (∏ j ∈ B.2.val, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) *
          ∏ j ∈ C, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) :=
      momentTailSplit_weight_factor A N B t
    _ = _ := by rw [htail, hcomp]

private theorem momentTailAttachProduct_eq_fintype {α : Type*} (s : Finset α)
    (f : {x // x ∈ s} → ℝ) :
    (∏ x ∈ s.attach, f x) = ∏ x : {x // x ∈ s}, f x := by
  rw [← Finset.univ_eq_attach s]

private theorem momentTailProductLaw_eq_subtypeLaw {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (N : ℕ) (B : Block K) (σ : ℕ) :
    parameterTailProductLaw MS.core.parameters N B.2.val σ =
      ∑' t : MomentTailIndex K B → ℕ,
        (if (∏ j, t j) = σ then (1 : ℝ) else 0) *
          ∏ j, harmonicNatLaw (MS.core.parameters.X N j.1)
            (primorial (N + 1)) (t j) := by
  classical
  let Tail := MomentTailIndex K B
  let Comp := MomentTailComplementIndex K B
  let A : Parameters K := MS.core.parameters
  let wt : Tail → ℕ → ℝ := fun j n =>
    harmonicNatLaw (A.X N j.1) (primorial (N + 1)) n
  let wc : Comp → ℕ → ℝ := fun j n =>
    harmonicNatLaw (A.X N j.1) (primorial (N + 1)) n
  let St : Finset (Tail → ℕ) := Fintype.piFinset fun j =>
    momentHarmonicNatSupport (A.X N j.1) (primorial (N + 1))
  let Sc : Finset (Comp → ℕ) := Fintype.piFinset fun j =>
    momentHarmonicNatSupport (A.X N j.1) (primorial (N + 1))
  have hX (j : Fin K) : 0 < A.X N j := A.Xpos N j
  have hnorm (j : Fin K) : 0 < harmonicNormalizer (A.X N j) (primorial (N + 1)) := by
    have hW : 0 < primorial (N + 1) := primorial_pos _
    have hcut : 4 * primorial (N + 1) ≤ A.X N j := MS.gapStage.valid_raw_cutoffs N j
    have h := OAI.RawHarmonicProbability.mass_pos (A.X N j) (primorial (N + 1)) hW hcut
    simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, one_div, Nat.coprime_comm] using h
  have hcompNorm : ∑' c : Comp → ℕ, ∏ j, wc j (c j) = 1 := by
    exact momentHarmonicNatTupleLaw_tsum_eq_one (ι := Comp) (primorial (N + 1))
      (fun j => A.X N j.1) (fun j => hX j.1) (fun j => hnorm j.1)
  have hcompZero : ∀ c ∉ Sc, ∏ j, wc j (c j) = 0 := by
    intro c hc
    have hnot : ¬ ∀ j, c j ∈ momentHarmonicNatSupport (A.X N j.1) (primorial (N + 1)) := by
      intro hall
      exact hc (Fintype.mem_piFinset.mpr hall)
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (momentHarmonicNatLaw_zero_of_not_mem _ _ _ (by simpa using hj))
  have hcompSum : ∑ c ∈ Sc, ∏ j, wc j (c j) = 1 := by
    calc
      _ = ∑' c : Comp → ℕ, ∏ j, wc j (c j) :=
        (tsum_eq_sum (s := Sc) hcompZero).symm
      _ = 1 := hcompNorm
  rw [parameterTailProductLaw]
  rw [← (momentTailSplitEquiv B).symm.tsum_eq (fun t : Fin K → ℕ =>
    (if (∏ j ∈ B.2.val, t j) = σ then (1 : ℝ) else 0) *
      ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j))]
  have hsplit (tc : (Tail → ℕ) × (Comp → ℕ)) :
      (if (∏ j ∈ B.2.val, ((momentTailSplitEquiv B).symm tc) j) = σ
        then (1 : ℝ) else 0) *
        ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1))
          (((momentTailSplitEquiv B).symm tc) j) =
      ((if (∏ j : Tail, tc.1 j) = σ then (1 : ℝ) else 0) *
        (∏ j : Tail, wt j (tc.1 j))) *
        ∏ j : Comp, wc j (tc.2 j) := by
    have hback : momentTailSplitEquiv B ((momentTailSplitEquiv B).symm tc) = tc :=
      Equiv.apply_symm_apply _ _
    have hprod := momentTailSplit_product_fintype B ((momentTailSplitEquiv B).symm tc)
    have hweight := momentTailSplit_weight_factor_fintype A N B
      ((momentTailSplitEquiv B).symm tc)
    rw [hback] at hprod hweight
    rw [hprod, hweight]
    simp [Tail, Comp, wt, wc]
    ring
  simp_rw [hsplit]
  have hpairZero : ∀ tc ∉ St ×ˢ Sc,
      ((if (∏ j : Tail, tc.1 j) = σ then (1 : ℝ) else 0) *
        (∏ j : Tail, wt j (tc.1 j))) *
        ∏ j : Comp, wc j (tc.2 j) = 0 := by
    intro tc htc
    have hnot : ¬ (tc.1 ∈ St ∧ tc.2 ∈ Sc) := by simpa using htc
    rcases not_and_or.mp hnot with ht | hc
    · have hz : ∏ j : Tail, wt j (tc.1 j) = 0 := by
        have hnot' : ¬ ∀ j : Tail, tc.1 j ∈ momentHarmonicNatSupport
            (A.X N j.1) (primorial (N + 1)) := by
          intro hall
          exact ht (Fintype.mem_piFinset.mpr hall)
        obtain ⟨j, hj⟩ := not_forall.mp hnot'
        exact Finset.prod_eq_zero (Finset.mem_univ j)
          (momentHarmonicNatLaw_zero_of_not_mem _ _ _ (by simpa [wt] using hj))
      simp [hz]
    · have hz : ∏ j : Comp, wc j (tc.2 j) = 0 := by
        have hnot' : ¬ ∀ j : Comp, tc.2 j ∈ momentHarmonicNatSupport
            (A.X N j.1) (primorial (N + 1)) := by
          intro hall
          exact hc (Fintype.mem_piFinset.mpr hall)
        obtain ⟨j, hj⟩ := not_forall.mp hnot'
        exact Finset.prod_eq_zero (Finset.mem_univ j)
          (momentHarmonicNatLaw_zero_of_not_mem _ _ _ (by simpa [wc] using hj))
      simp [hz]
  rw [tsum_eq_sum (s := St ×ˢ Sc) hpairZero, Finset.sum_product]
  have htailZero (t : Tail → ℕ) (ht : t ∉ St) :
      (if (∏ j : Tail, t j) = σ then (1 : ℝ) else 0) *
        ∏ j : Tail, wt j (t j) = 0 := by
    have hnot : ¬ ∀ j : Tail, t j ∈ momentHarmonicNatSupport
        (A.X N j.1) (primorial (N + 1)) := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    have hz := momentHarmonicNatLaw_zero_of_not_mem _ _ _ (by simpa [wt] using hj)
    by_cases hσ : (∏ j : Tail, t j) = σ
    · have hprod : ∏ j' : Tail, wt j' (t j') = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simpa [wt] using hz)
      simp [hσ, hprod]
    · simp [hσ]
  have htailLaw :
      ∑ t ∈ St,
        (if (∏ j : Tail, t j) = σ then (1 : ℝ) else 0) *
          ∏ j : Tail, wt j (t j) =
        ∑' t : Tail → ℕ,
          (if (∏ j : Tail, t j) = σ then (1 : ℝ) else 0) *
            ∏ j : Tail, wt j (t j) := by
    symm
    exact tsum_eq_sum (s := St) htailZero
  calc
    _ = ∑ t ∈ St,
          (if (∏ j : Tail, t j) = σ then (1 : ℝ) else 0) *
            ∏ j : Tail, wt j (t j) := by
          apply Finset.sum_congr rfl
          intro t ht
          simp only [Prod.fst, Prod.snd]
          rw [← Finset.mul_sum, hcompSum, mul_one]
    _ = _ := htailLaw

private theorem momentTailProductLaw_eq_divisorTemplateLaw {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (N : ℕ) (B : Block K) (σ : ℕ) :
    parameterTailProductLaw MS.core.parameters N B.2.val σ =
      divisorTemplateLaw MS.core.parameters N (momentTailDivisorTemplate B) σ := by
  classical
  let A : Parameters K := MS.core.parameters
  let Tail := MomentTailIndex K B
  let e := momentTailTupleEquiv B
  rw [momentTailProductLaw_eq_subtypeLaw MS N B σ]
  have hprodNat (x : Fin (Fintype.card Tail) → ℕ) :
      (∏ j : Tail, (e x) j) = ∏ i, x i := by
    symm
    exact Fintype.prod_equiv (momentTailEnum B)
      (fun i => x i) (fun j : Tail => (e x) j)
      (by intro i; simp [e, momentTailTupleEquiv])
  have hprodWeight (x : Fin (Fintype.card Tail) → ℕ) :
      (∏ j : Tail, harmonicNatLaw (A.X N j.1) (primorial (N + 1)) ((e x) j)) =
        ∏ i, harmonicNatLaw (A.X N (momentTailEnum B i).1) (primorial (N + 1)) (x i) := by
    symm
    exact Fintype.prod_equiv (momentTailEnum B)
      (fun i => harmonicNatLaw (A.X N (momentTailEnum B i).1) (primorial (N + 1)) (x i))
      (fun j : Tail => harmonicNatLaw (A.X N j.1) (primorial (N + 1)) ((e x) j))
      (by intro i; simp [e, momentTailTupleEquiv])
  calc
    _ = ∑' x : Fin (Fintype.card Tail) → ℕ,
          (if (∏ j : Tail, (e x) j) = σ then (1 : ℝ) else 0) *
            ∏ j : Tail, harmonicNatLaw (A.X N j.1) (primorial (N + 1)) ((e x) j) :=
      (e.tsum_eq (fun t : Tail → ℕ =>
        (if (∏ j, t j) = σ then (1 : ℝ) else 0) *
          ∏ j, harmonicNatLaw (A.X N j.1) (primorial (N + 1)) (t j))).symm
    _ = harmonicProductLaw (primorial (N + 1))
          (fun i => A.X N (momentTailEnum B i).1) σ := by
      unfold harmonicProductLaw
      apply tsum_congr
      intro x
      rw [hprodNat, hprodWeight]
    _ = divisorTemplateLaw MS.core.parameters N (momentTailDivisorTemplate B) σ := by
      rfl

private theorem momentHarmonicLaw_tsum_eq_one (X W : ℕ) (hX : 0 < X)
    (hH : 0 < harmonicNormalizer X W) :
    ∑' y : ℤ, harmonicLaw X W y = 1 := by
  classical
  let S := momentHarmonicNatSupport X W
  let SI := S.image (fun n : ℕ => (n : ℤ))
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro m n h
    exact Int.ofNat.inj h
  have hzero : ∀ y ∉ SI, harmonicLaw X W y = 0 := by
    intro y hy
    by_cases hcond : 0 ≤ y ∧ X ≤ y.toNat ∧ y.toNat < X ^ 2 ∧
        Nat.Coprime y.toNat W
    · have hcast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hcond.1
      have hS : y.toNat ∈ S := by
        dsimp [S, momentHarmonicNatSupport]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨hcond.2.1, hcond.2.2.1⟩, hcond.2.2.2⟩
      exact False.elim (hy (Finset.mem_image.mpr ⟨y.toNat, hS, hcast⟩))
    · simp [harmonicLaw, hcond]
  rw [tsum_eq_sum (s := SI) hzero]
  calc
    (∑ y ∈ SI, harmonicLaw X W y) =
        ∑ n ∈ S, harmonicLaw X W (n : ℤ) := by
          rw [Finset.sum_image (fun a ha b hb h => hinj h)]
    _ = ∑ n ∈ S, harmonicNatLaw X W n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnS : n ∈ momentHarmonicNatSupport X W := by simpa [S] using hn
      have hfilter := Finset.mem_filter.mp hnS
      have hbounds := Finset.mem_Ico.mp hfilter.1
      have htoNat : ((n : ℤ).toNat) = n := by simp
      simp [harmonicLaw, harmonicNatLaw, htoNat,
        hbounds.1, hbounds.2, hfilter.2]
    _ = 1 := by
      have htotal := momentHarmonicNatLaw_tsum_eq_one X W hX hH
      rw [tsum_eq_sum (s := S)
        (fun n hn => momentHarmonicNatLaw_zero_of_not_mem X W n (by simpa [S] using hn))]
        at htotal
      exact htotal

private theorem uniformIntegerIntervalLaw_tsum_eq_one (L : ℕ) (hL : 0 < L) :
    ∑' y : ℤ, uniformIntegerIntervalLaw 0 L y = 1 := by
  classical
  let S : Finset ℤ := Finset.Ico 0 (L : ℤ)
  have hzero : ∀ y ∉ S, uniformIntegerIntervalLaw 0 L y = 0 := by
    intro y hy
    have hnot : ¬ (0 ≤ y ∧ y < (L : ℤ)) := by
      simpa [S, Finset.mem_Ico] using hy
    simp [uniformIntegerIntervalLaw, hnot]
  rw [tsum_eq_sum (s := S) hzero]
  have hcardZ : ((S.card : ℕ) : ℤ) = (L : ℤ) := by
    dsimp [S]
    rw [Int.card_Ico_of_le (0 : ℤ) (L : ℤ) (by exact_mod_cast hL.le)]
    simp
  have hcard : S.card = L := by exact_mod_cast hcardZ
  have hsum : ∑ y ∈ S, uniformIntegerIntervalLaw 0 L y =
      ∑ _y ∈ S, (1 / (L : ℝ)) := by
    apply Finset.sum_congr rfl
    intro y hy
    have hy' : 0 ≤ y ∧ y < (L : ℤ) := Finset.mem_Ico.mp (by simpa [S] using hy)
    simp [uniformIntegerIntervalLaw, hy']
  rw [hsum]
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    (∑ _y ∈ S, (1 / (L : ℝ))) = (S.card : ℝ) * (1 / (L : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by rw [hcard]; field_simp [ne_of_gt hLreal]

private noncomputable def momentBaseRegular {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ) : Prop :=
  0 < harmonicNormalizer (MS.core.parameters.X N B.1) (primorial (N + 1)) ∧
    ∀ k : Fin b, 0 < T.length (corrScales MS) l J0 N
      (fun j => p ((momentPrimeEnum b T.q).symm (k, j)))

private noncomputable def momentBaseCoordinateLaw {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (i : MomentBaseIndex b T.d) (z : ℤ) : ℝ :=
  match i with
  | .inl _ => harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1)) z
  | .inr (k, (j, side)) =>
      uniformIntegerIntervalLaw 0
        (T.length (corrScales MS) l J0 N
          (fun j => p ((momentPrimeEnum b T.q).symm (k, j)))) z

private noncomputable def momentBaseMass {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (x : Fin (Fintype.card (MomentBaseIndex b T.d)) → ℤ) : ℝ := by
  classical
  exact if h : momentBaseRegular MS B l T J0 N b p then
    ∏ j, momentBaseCoordinateLaw MS B l T J0 N b p
      (momentBaseEnum b T.d j) (x j)
  else if x = 0 then 1 else 0

private noncomputable def momentBaseWindow {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ) : Finset ℤ :=
  Finset.Icc 0
    (((MS.core.parameters.X N B.1) ^ 2 +
      ∑ k : Fin b, T.length (corrScales MS) l J0 N
        (fun j => p ((momentPrimeEnum b T.q).symm (k, j))) : ℕ) : ℤ)

private theorem momentBaseCoordinateLaw_zero_outside {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (hreg : momentBaseRegular MS B l T J0 N b p)
    (i : MomentBaseIndex b T.d) (z : ℤ)
    (hz : z ∉ momentBaseWindow MS B l T J0 N b p) :
    momentBaseCoordinateLaw MS B l T J0 N b p i z = 0 := by
  classical
  by_contra hnotzero
  cases i with
  | inl _ =>
      have hcond : 0 ≤ z ∧ MS.core.parameters.X N B.1 ≤ z.toNat ∧
          z.toNat < (MS.core.parameters.X N B.1) ^ 2 ∧
          Nat.Coprime z.toNat (primorial (N + 1)) := by
        by_contra hbad
        apply hnotzero
        simp [momentBaseCoordinateLaw, harmonicLaw, hbad]
      have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hcond.1
      have hzmem : z ∈ momentBaseWindow MS B l T J0 N b p := by
        apply Finset.mem_Icc.mpr
        constructor
        · exact hcond.1
        · have hle : z.toNat ≤ (MS.core.parameters.X N B.1) ^ 2 := hcond.2.2.1.le
          have hle' : (z.toNat : ℤ) ≤ ((MS.core.parameters.X N B.1) ^ 2 : ℤ) := by
            exact_mod_cast hle
          have hsum : ((MS.core.parameters.X N B.1) ^ 2 : ℤ) ≤
              ((MS.core.parameters.X N B.1) ^ 2 +
                ∑ k : Fin b, T.length (corrScales MS) l J0 N
                  (fun j => p ((momentPrimeEnum b T.q).symm (k, j))) : ℕ) := by
            exact_mod_cast Nat.le_add_right _ _
          rw [← hcast]
          exact le_trans hle' hsum
      exact hz hzmem
  | inr idx =>
      rcases idx with ⟨k, ⟨j, side⟩⟩
      have hcond : 0 ≤ z ∧ z <
          (T.length (corrScales MS) l J0 N
            (fun j => p ((momentPrimeEnum b T.q).symm (k, j))) : ℕ) := by
        by_contra hbad
        apply hnotzero
        simp [momentBaseCoordinateLaw, uniformIntegerIntervalLaw, hbad]
      have hLle : T.length (corrScales MS) l J0 N
          (fun j => p ((momentPrimeEnum b T.q).symm (k, j))) ≤
            MS.core.parameters.X N B.1 ^ 2 +
              ∑ k' : Fin b, T.length (corrScales MS) l J0 N
                (fun j => p ((momentPrimeEnum b T.q).symm (k', j))) := by
        have hsum := Finset.single_le_sum
          (s := Finset.univ) (f := fun k' : Fin b =>
            T.length (corrScales MS) l J0 N
              (fun j => p ((momentPrimeEnum b T.q).symm (k', j))))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        exact le_trans hsum (Nat.le_add_left _ _)
      have hzmem : z ∈ momentBaseWindow MS B l T J0 N b p := by
        apply Finset.mem_Icc.mpr
        constructor
        · exact hcond.1
        · have hLleZ :
              ((T.length (corrScales MS) l J0 N
                (fun j => p ((momentPrimeEnum b T.q).symm (k, j))) : ℕ) : ℤ) ≤
                ((MS.core.parameters.X N B.1) ^ 2 +
                  ∑ k' : Fin b, T.length (corrScales MS) l J0 N
                    (fun j => p ((momentPrimeEnum b T.q).symm (k', j))) : ℕ) := by
            exact_mod_cast hLle
          exact le_trans hcond.2.le hLleZ
      exact hz hzmem

private theorem momentBaseCoordinateLaw_tsum_eq_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (hreg : momentBaseRegular MS B l T J0 N b p)
    (i : MomentBaseIndex b T.d) :
    ∑' z : ℤ, momentBaseCoordinateLaw MS B l T J0 N b p i z = 1 := by
  classical
  rcases hreg with ⟨hnorm, hlen⟩
  cases i with
  | inl _ =>
      simpa [momentBaseCoordinateLaw] using
        momentHarmonicLaw_tsum_eq_one (MS.core.parameters.X N B.1)
          (primorial (N + 1)) (MS.core.parameters.Xpos N B.1) hnorm
  | inr idx =>
      rcases idx with ⟨k, ⟨j, side⟩⟩
      simpa [momentBaseCoordinateLaw] using
        uniformIntegerIntervalLaw_tsum_eq_one
          (T.length (corrScales MS) l J0 N
            (fun j => p ((momentPrimeEnum b T.q).symm (k, j)))) (hlen k)

private theorem momentBaseMass_zero_outside {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (x : Fin (Fintype.card (MomentBaseIndex b T.d)) → ℤ)
    (hx : x ∉ Fintype.piFinset (fun _ : Fin (Fintype.card (MomentBaseIndex b T.d)) =>
      momentBaseWindow MS B l T J0 N b p)) :
    momentBaseMass MS B l T J0 N b p x = 0 := by
  classical
  by_cases hreg : momentBaseRegular MS B l T J0 N b p
  · have hx' : ¬ ∀ j : Fin (Fintype.card (MomentBaseIndex b T.d)),
        x j ∈ momentBaseWindow MS B l T J0 N b p := by
      simpa only [Fintype.mem_piFinset] using hx
    obtain ⟨j, hj⟩ := not_forall.mp hx'
    have hcoord := momentBaseCoordinateLaw_zero_outside MS B l T J0 N b p
      hreg (momentBaseEnum b T.d j) (x j) hj
    have hprod :
        ∏ j : Fin (Fintype.card (MomentBaseIndex b T.d)),
            momentBaseCoordinateLaw MS B l T J0 N b p
              (momentBaseEnum b T.d j) (x j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hcoord
    simpa [momentBaseMass, hreg] using hprod
  · by_cases hx0 : x = 0
    · subst x
      have hzeroMem : (0 : Fin (Fintype.card (MomentBaseIndex b T.d)) → ℤ) ∈
          Fintype.piFinset (fun _ : Fin (Fintype.card (MomentBaseIndex b T.d)) =>
            momentBaseWindow MS B l T J0 N b p) := by
        rw [Fintype.mem_piFinset]
        intro j
        apply Finset.mem_Icc.mpr
        constructor
        · norm_num
        · have hU : (0 : ℕ) ≤ MS.core.parameters.X N B.1 ^ 2 +
              ∑ k : Fin b, T.length (corrScales MS) l J0 N
                (fun j => p ((momentPrimeEnum b T.q).symm (k, j))) := Nat.zero_le _
          change (0 : ℤ) ≤ ((MS.core.parameters.X N B.1 ^ 2 +
            ∑ k : Fin b, T.length (corrScales MS) l J0 N
              (fun j => p ((momentPrimeEnum b T.q).symm (k, j))) : ℕ) : ℤ)
          exact_mod_cast hU
      exact False.elim (hx hzeroMem)
    · simp [momentBaseMass, hreg, hx0]

private theorem momentBaseMass_tsum_eq_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ) :
    ∑' x : Fin (Fintype.card (MomentBaseIndex b T.d)) → ℤ,
      momentBaseMass MS B l T J0 N b p x = 1 := by
  classical
  by_cases hreg : momentBaseRegular MS B l T J0 N b p
  · let win := momentBaseWindow MS B l T J0 N b p
    let S := Fintype.piFinset (fun _ : Fin (Fintype.card (MomentBaseIndex b T.d)) => win)
    have hzero : ∀ x ∉ S, momentBaseMass MS B l T J0 N b p x = 0 := by
      intro x hx
      apply momentBaseMass_zero_outside MS B l T J0 N b p x
      simpa [S, win] using hx
    have hfactor :
        (∑ x ∈ S, ∏ j : Fin (Fintype.card (MomentBaseIndex b T.d)),
          momentBaseCoordinateLaw MS B l T J0 N b p
            (momentBaseEnum b T.d j) (x j)) =
          ∏ j : Fin (Fintype.card (MomentBaseIndex b T.d)),
            ∑ z ∈ win, momentBaseCoordinateLaw MS B l T J0 N b p
              (momentBaseEnum b T.d j) z := by
      simpa [S] using
        (Finset.sum_prod_piFinset win
          (fun j z => momentBaseCoordinateLaw MS B l T J0 N b p
            (momentBaseEnum b T.d j) z))
    have hlocal (j : Fin (Fintype.card (MomentBaseIndex b T.d))) :
        (∑ z ∈ win, momentBaseCoordinateLaw MS B l T J0 N b p
          (momentBaseEnum b T.d j) z) = 1 := by
      have hzeroCoord : ∀ z : ℤ, z ∉ win →
          momentBaseCoordinateLaw MS B l T J0 N b p
            (momentBaseEnum b T.d j) z = 0 := by
        intro z hz
        exact momentBaseCoordinateLaw_zero_outside MS B l T J0 N b p hreg
          (momentBaseEnum b T.d j) z (by simpa [win] using hz)
      have hsum :
          (∑' z : ℤ, momentBaseCoordinateLaw MS B l T J0 N b p
            (momentBaseEnum b T.d j) z) =
          ∑ z ∈ win, momentBaseCoordinateLaw MS B l T J0 N b p
            (momentBaseEnum b T.d j) z :=
        tsum_eq_sum (s := win) hzeroCoord
      calc
        _ = ∑' z : ℤ, momentBaseCoordinateLaw MS B l T J0 N b p
              (momentBaseEnum b T.d j) z := hsum.symm
        _ = 1 := momentBaseCoordinateLaw_tsum_eq_one MS B l T J0 N b p hreg
          (momentBaseEnum b T.d j)
    calc
      _ = ∑ x ∈ S, ∏ j : Fin (Fintype.card (MomentBaseIndex b T.d)),
            momentBaseCoordinateLaw MS B l T J0 N b p
              (momentBaseEnum b T.d j) (x j) := by
            rw [tsum_eq_sum (s := S) hzero]
            simp [momentBaseMass, hreg]
      _ = ∏ j : Fin (Fintype.card (MomentBaseIndex b T.d)),
            ∑ z ∈ win, momentBaseCoordinateLaw MS B l T J0 N b p
              (momentBaseEnum b T.d j) z := hfactor
      _ = 1 := by simp_rw [hlocal]; simp
  · simp [momentBaseMass, hreg]

private theorem momentBaseMass_nonneg {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (x : Fin (Fintype.card (MomentBaseIndex b T.d)) → ℤ) :
    0 ≤ momentBaseMass MS B l T J0 N b p x := by
  classical
  by_cases hreg : momentBaseRegular MS B l T J0 N b p
  · have hreg' := hreg
    rcases hreg with ⟨hnorm, hlen⟩
    simp only [momentBaseMass, dif_pos hreg']
    apply Finset.prod_nonneg
    intro j hj
    cases hidx : momentBaseEnum b T.d j with
    | inl i =>
        simpa [momentBaseCoordinateLaw, hidx] using
          harmonicLaw_nonneg (MS.core.parameters.X N B.1) (primorial (N + 1)) (x j)
    | inr idx =>
        rcases idx with ⟨k, ⟨j', side⟩⟩
        simp only [momentBaseCoordinateLaw]
        have hL := hlen k
        unfold uniformIntegerIntervalLaw
        split_ifs <;> positivity
  · by_cases hx : x = 0 <;> simp [momentBaseMass, hreg, hx]

private noncomputable def momentBaseCoordinateResidueLaw {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (MomentBaseIndex b T.d))) (r : Fin modulus) : ℝ :=
  ∑' z : ℤ,
    momentBaseCoordinateLaw MS B l T J0 N b p (momentBaseEnum b T.d i) z *
      (if integerResidue modulus hmod z = r then 1 else 0)

private theorem momentBaseCoordinateLaw_nonneg {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (i : MomentBaseIndex b T.d) (z : ℤ) :
    0 ≤ momentBaseCoordinateLaw MS B l T J0 N b p i z := by
  cases i with
  | inl _ => exact harmonicLaw_nonneg _ _ _
  | inr idx =>
      rcases idx with ⟨k, ⟨j, side⟩⟩
      simp only [momentBaseCoordinateLaw, uniformIntegerIntervalLaw]
      split_ifs <;> positivity

private theorem momentBaseResidueLaw_eq_product {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (hreg : momentBaseRegular MS B l T J0 N b p)
    (modulus : ℕ) (hmod : 0 < modulus) (r :
      Fin (Fintype.card (MomentBaseIndex b T.d)) → Fin modulus) :
    baseResidueLaw modulus hmod (momentBaseMass MS B l T J0 N b p) r =
      ∏ i, momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i (r i) := by
  classical
  let d := Fintype.card (MomentBaseIndex b T.d)
  let win := momentBaseWindow MS B l T J0 N b p
  let S : Finset (Fin d → ℤ) := Fintype.piFinset fun _ : Fin d => win
  let f : Fin d → ℤ → ℝ := fun i z =>
    momentBaseCoordinateLaw MS B l T J0 N b p (momentBaseEnum b T.d i) z
  have hbaseZero : ∀ x ∉ S, momentBaseMass MS B l T J0 N b p x = 0 := by
    intro x hx
    apply momentBaseMass_zero_outside MS B l T J0 N b p x
    simpa [S, d] using hx
  have hcoordZero (i : Fin d) (z : ℤ) (hz : z ∉ win) : f i z = 0 := by
    exact momentBaseCoordinateLaw_zero_outside MS B l T J0 N b p hreg
      (momentBaseEnum b T.d i) z (by simpa [win] using hz)
  have hindicator (x : Fin d → ℤ) :
      (if (fun i => integerResidue modulus hmod (x i)) = r then (1 : ℝ) else 0) =
        ∏ i, (if integerResidue modulus hmod (x i) = r i then (1 : ℝ) else 0) := by
    by_cases heq : (fun i => integerResidue modulus hmod (x i)) = r
    · have hone :
          ∏ i : Fin d, (if integerResidue modulus hmod (x i) = r i then (1 : ℝ) else 0) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hpoint := congrFun heq i
        simp [hpoint]
      simp [heq, hone]
    · obtain ⟨i, hi⟩ : ∃ i, integerResidue modulus hmod (x i) ≠ r i := by
        by_contra hnone
        push_neg at hnone
        exact heq (funext hnone)
      have hzero :
          ∏ j : Fin d, (if integerResidue modulus hmod (x j) = r j then (1 : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
      simp [heq, hzero]
  have hlocal (i : Fin d) (a : Fin modulus) :
      (∑ z ∈ win, f i z *
        (if integerResidue modulus hmod z = a then (1 : ℝ) else 0)) =
        momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i a := by
    have hzero : ∀ z : ℤ, z ∉ win →
        f i z * (if integerResidue modulus hmod z = a then (1 : ℝ) else 0) = 0 := by
      intro z hz
      rw [hcoordZero i z hz]
      simp
    symm
    exact tsum_eq_sum (s := win) hzero
  calc
    _ = ∑ x ∈ S,
          momentBaseMass MS B l T J0 N b p x *
            (if (fun i => integerResidue modulus hmod (x i)) = r then (1 : ℝ) else 0) := by
          unfold baseResidueLaw
          exact tsum_eq_sum (s := S) (by
            intro x hx
            rw [hbaseZero x hx]
            simp)
    _ = ∑ x ∈ S, ∏ i : Fin d,
          f i (x i) * (if integerResidue modulus hmod (x i) = r i then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hmass : momentBaseMass MS B l T J0 N b p x = ∏ i : Fin d, f i (x i) := by
            simp [momentBaseMass, momentBaseCoordinateLaw, hreg, f, d]
          rw [hmass, hindicator, ← Finset.prod_mul_distrib]
    _ = ∏ i : Fin d, ∑ z ∈ win,
          f i z * (if integerResidue modulus hmod z = r i then (1 : ℝ) else 0) := by
          simpa [S] using (Finset.sum_prod_piFinset win
            (fun i z => f i z *
              (if integerResidue modulus hmod z = r i then (1 : ℝ) else 0)))
    _ = ∏ i, momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i (r i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hlocal i (r i)

private theorem momentBaseCoordinateResidueLaw_nonneg {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (MomentBaseIndex b T.d))) (r : Fin modulus) :
    0 ≤ momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i r := by
  unfold momentBaseCoordinateResidueLaw
  apply tsum_nonneg
  intro z
  exact mul_nonneg
    (momentBaseCoordinateLaw_nonneg MS B l T J0 N b p (momentBaseEnum b T.d i) z)
    (by split_ifs <;> positivity)

private theorem momentBaseCoordinateResidueLaw_sum_eq_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (hreg : momentBaseRegular MS B l T J0 N b p)
    (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (MomentBaseIndex b T.d))) :
    ∑ r : Fin modulus,
      momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i r = 1 := by
  classical
  let win := momentBaseWindow MS B l T J0 N b p
  let coord := momentBaseCoordinateLaw MS B l T J0 N b p (momentBaseEnum b T.d i)
  have hcoordZero (z : ℤ) (hz : z ∉ win) : coord z = 0 := by
    exact momentBaseCoordinateLaw_zero_outside MS B l T J0 N b p hreg
      (momentBaseEnum b T.d i) z (by simpa [win] using hz)
  have htermZero (r : Fin modulus) (z : ℤ) (hz : z ∉ win) :
      coord z * (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) = 0 := by
    rw [hcoordZero z hz]
    simp
  have hsum (r : Fin modulus) :
      momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i r =
        ∑ z ∈ win, coord z * (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) := by
    unfold momentBaseCoordinateResidueLaw
    exact tsum_eq_sum (s := win) (fun z hz => htermZero r z hz)
  have hpart (z : ℤ) :
      ∑ r : Fin modulus, (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) = 1 := by
    simp
  have htotal : ∑ z ∈ win, coord z = 1 := by
    have hzeroLaw : ∀ z : ℤ, z ∉ win → coord z = 0 := hcoordZero
    calc
      _ = ∑' z : ℤ, coord z := (tsum_eq_sum (s := win) hzeroLaw).symm
      _ = 1 := momentBaseCoordinateLaw_tsum_eq_one MS B l T J0 N b p hreg
        (momentBaseEnum b T.d i)
  calc
    _ = ∑ r : Fin modulus, ∑ z ∈ win,
          coord z * (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hsum r
    _ = ∑ z ∈ win, coord z := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro z hz
          rw [← Finset.mul_sum, hpart, mul_one]
    _ = 1 := htotal

private theorem uniformResidueLaw_sum_eq_one {modulus : ℕ} (hmod : 0 < modulus) :
    ∑ r : Fin modulus, uniformResidueLaw modulus r = 1 := by
  unfold uniformResidueLaw
  rw [Finset.sum_const, Finset.card_fin]
  simp only [nsmul_eq_mul]
  have hmodReal : (0 : ℝ) < modulus := by exact_mod_cast hmod
  field_simp [ne_of_gt hmodReal]

private theorem momentBaseResidueL1_le_coordinate_errors {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (hreg : momentBaseRegular MS B l T J0 N b p)
    (modulus : ℕ) (hmod : 0 < modulus)
    (δ : Fin (Fintype.card (MomentBaseIndex b T.d)) → ℝ)
    (hδ : ∀ i, finiteL1
      (momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i)
      (uniformResidueLaw modulus) ≤ δ i) :
    finiteL1
      (baseResidueLaw modulus hmod (momentBaseMass MS B l T J0 N b p))
      (uniformBaseResidueLaw modulus (Fintype.card (MomentBaseIndex b T.d))) ≤
      ∑ i, δ i := by
  classical
  let d := Fintype.card (MomentBaseIndex b T.d)
  let μ : Fin d → Fin modulus → ℝ := fun i r =>
    momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i r
  let ν : Fin d → Fin modulus → ℝ := fun _ r => uniformResidueLaw modulus r
  have hμsum (i : Fin d) : ∑ r : Fin modulus, |μ i r| = 1 := by
    have hnonneg (r : Fin modulus) : 0 ≤ μ i r := by
      exact momentBaseCoordinateResidueLaw_nonneg MS B l T J0 N b p modulus hmod i r
    calc
      _ = ∑ r : Fin modulus, μ i r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [abs_of_nonneg (hnonneg r)]
      _ = 1 := momentBaseCoordinateResidueLaw_sum_eq_one MS B l T J0 N b p hreg
        modulus hmod i
  have hνsum (i : Fin d) : ∑ r : Fin modulus, |ν i r| = 1 := by
    have hnonneg (r : Fin modulus) : 0 ≤ ν i r := by
      dsimp [ν]
      unfold uniformResidueLaw
      positivity
    calc
      _ = ∑ r : Fin modulus, ν i r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [abs_of_nonneg (hnonneg r)]
      _ = 1 := by
        dsimp [ν]
        exact uniformResidueLaw_sum_eq_one hmod
  have hUniform (r : Fin d → Fin modulus) :
      uniformBaseResidueLaw modulus d r = ∏ i, ν i (r i) := by
    simp [uniformBaseResidueLaw, uniformResidueLaw, ν, d, div_pow]
  have hmain := finite_product_l1_telescoping μ ν
  have hprodBound :
      finiteL1 (fun r : Fin d → Fin modulus => ∏ i, μ i (r i))
        (fun r => ∏ i, ν i (r i)) ≤
        ∑ i, finiteL1 (μ i) (ν i) := by
    calc
      _ ≤ ∑ i, finiteL1 (μ i) (ν i) *
          ∏ j ∈ Finset.univ.erase i,
            max (∑ a, |μ j a|) (∑ a, |ν j a|) := hmain
      _ = ∑ i, finiteL1 (μ i) (ν i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp_rw [hμsum, hνsum]
        simp
  have hmeasure :
      baseResidueLaw modulus hmod (momentBaseMass MS B l T J0 N b p) =
        fun r : Fin d → Fin modulus => ∏ i, μ i (r i) := by
    funext r
    exact momentBaseResidueLaw_eq_product MS B l T J0 N b p hreg modulus hmod r
  have huniform :
      uniformBaseResidueLaw modulus d =
        fun r : Fin d → Fin modulus => ∏ i, ν i (r i) := by
    funext r
    exact hUniform r
  calc
    _ = finiteL1 (fun r : Fin d → Fin modulus => ∏ i, μ i (r i))
          (fun r => ∏ i, ν i (r i)) := by
          rw [hmeasure, huniform]
    _ ≤ ∑ i, finiteL1 (μ i) (ν i) := hprodBound
    _ ≤ ∑ i, δ i := Finset.sum_le_sum fun i hi => by
          simpa [μ, ν] using hδ i

private theorem integerResidue_eq_toNat_mod {modulus : ℕ} (hmod : 0 < modulus)
    (z : ℤ) (hz : 0 ≤ z) :
    integerResidue modulus hmod z = ⟨z.toNat % modulus, Nat.mod_lt _ hmod⟩ := by
  apply Fin.ext
  simp only [integerResidue]
  have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
  have hmodEq : z % (modulus : ℤ) = (z.toNat : ℤ) % (modulus : ℤ) :=
    congrArg (fun n : ℤ => n % (modulus : ℤ)) hcast.symm
  rw [hmodEq, ← Int.natCast_mod, Int.toNat_natCast]

private theorem integerResidue_eq_iff {modulus : ℕ} (hmod : 0 < modulus)
    (z : ℤ) (hz : 0 ≤ z) (r : Fin modulus) :
    integerResidue modulus hmod z = r ↔ z.toNat % modulus = r.val := by
  rw [integerResidue_eq_toNat_mod hmod z hz]
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    exact Fin.ext h

private theorem momentPivotCoordinateResidueLaw_eq_harmonic {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (MomentBaseIndex b T.d)))
    (hi : momentBaseEnum b T.d i = Sum.inl ()) (r : Fin modulus) :
    momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i r =
      harmonicResidueLaw
        (harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))) modulus r := by
  classical
  unfold momentBaseCoordinateResidueLaw harmonicResidueLaw
  apply tsum_congr
  intro z
  have hcoord :
      momentBaseCoordinateLaw MS B l T J0 N b p (momentBaseEnum b T.d i) z =
        harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1)) z := by
    rw [hi]
    rfl
  rw [hcoord]
  by_cases hz : 0 ≤ z
  · by_cases hres : z.toNat % modulus = r.val
    · have hres' := (integerResidue_eq_iff hmod z hz r).mpr hres
      simp [hz, hres, hres']
    · have hres' : integerResidue modulus hmod z ≠ r := by
        intro h
        exact hres ((integerResidue_eq_iff hmod z hz r).mp h)
      simp [hz, hres, hres']
  · simp [hz, harmonicLaw]

private theorem momentPivotSamplingHypotheses {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (N : ℕ) :
    0 < primorial (N + 1) ∧ 2 ≤ MS.core.parameters.X N B.1 ∧
      Real.log (MS.core.parameters.X N B.1) >
        (primorial (N + 1) : ℝ) / MS.core.parameters.X N B.1 := by
  let W := primorial (N + 1)
  let X := MS.core.parameters.X N B.1
  have hW : 0 < W := primorial_pos _
  have hWle : 1 ≤ W := Nat.one_le_iff_ne_zero.mpr hW.ne'
  have hcut : 4 * W ≤ X := MS.gapStage.valid_raw_cutoffs N B.1
  have hXtwo : 2 ≤ X := by omega
  have hXfour : 4 ≤ X := by omega
  have hXreal : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXfour
  have hWreal : (1 : ℝ) ≤ W := by exact_mod_cast hWle
  have hcutReal : 4 * (W : ℝ) ≤ (X : ℝ) := by exact_mod_cast hcut
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hWover : (W : ℝ) / X ≤ 1 / 4 := by
    apply (div_le_iff₀ hXpos).2
    linarith
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).2
    exact lt_trans Real.exp_one_lt_three (by norm_num)
  have hlogX : Real.log 4 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) hXreal
  refine ⟨hW, hXtwo, ?_⟩
  change (W : ℝ) / (X : ℝ) < Real.log (X : ℝ)
  linarith

private theorem momentHarmonicPivotResidue_l1_bound {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (N modulus : ℕ)
    (hmod : 0 < modulus) (hcop : Nat.Coprime modulus (primorial (N + 1))) :
    finiteL1
      (harmonicResidueLaw
        (harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))) modulus)
      (uniformResidueLaw modulus) ≤
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) modulus := by
  obtain ⟨hW, hX, hlog⟩ := momentPivotSamplingHypotheses MS B N
  have hsampling := lem_sampling
    (MS.core.parameters.X N B.1) (primorial (N + 1)) hW hX hlog
  exact hsampling.1.residue_total_mass hX hlog modulus hcop hmod

private theorem momentPivotCoordinateResidue_l1_bound {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (MomentBaseIndex b T.d)))
    (hi : momentBaseEnum b T.d i = Sum.inl ())
    (hcop : Nat.Coprime modulus (primorial (N + 1))) :
    finiteL1
      (momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i)
      (uniformResidueLaw modulus) ≤
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) modulus := by
  have hEq : (fun r : Fin modulus =>
      momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i r) =
      fun r => harmonicResidueLaw
        (harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))) modulus r := by
    funext r
    exact momentPivotCoordinateResidueLaw_eq_harmonic
      MS B l T J0 N b p modulus hmod i hi r
  calc
    _ = finiteL1 (fun r : Fin modulus => harmonicResidueLaw
          (harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))) modulus r)
          (uniformResidueLaw modulus) := by
        unfold finiteL1
        apply Finset.sum_congr rfl
        intro r hr
        rw [congrFun hEq r]
    _ ≤ harmonicResidueError
          (MS.core.parameters.X N B.1) (primorial (N + 1)) modulus :=
        momentHarmonicPivotResidue_l1_bound MS B N modulus hmod hcop

private theorem uniformIntegerIntervalResidueLaw_eq_nat {L modulus : ℕ}
    (hL : 0 < L) (hmod : 0 < modulus) (r : Fin modulus) :
    (∑' z : ℤ, uniformIntegerIntervalLaw 0 L z *
      (if integerResidue modulus hmod z = r then (1 : ℝ) else 0)) =
      ∑ n ∈ Finset.range L,
        if n % modulus = r.val then 1 / (L : ℝ) else 0 := by
  classical
  let I : Finset ℤ := Finset.Ico 0 (L : ℤ)
  have hzero (z : ℤ) (hz : z ∉ I) :
      uniformIntegerIntervalLaw 0 L z *
        (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) = 0 := by
    have hnot : ¬ (0 ≤ z ∧ z < (L : ℤ)) := by
      simpa [I, Finset.mem_Ico] using hz
    simp [uniformIntegerIntervalLaw, hnot]
  have hsum :
      (∑' z : ℤ, uniformIntegerIntervalLaw 0 L z *
        (if integerResidue modulus hmod z = r then (1 : ℝ) else 0)) =
      ∑ z ∈ I, uniformIntegerIntervalLaw 0 L z *
        (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) := by
    exact tsum_eq_sum (s := I) (fun z hz => hzero z hz)
  calc
    _ = ∑ z ∈ I, uniformIntegerIntervalLaw 0 L z *
          (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) := hsum
    _ = ∑ n ∈ Finset.range L,
          if n % modulus = r.val then 1 / (L : ℝ) else 0 := by
          apply Finset.sum_bij (s := I) (t := Finset.range L)
            (f := fun z : ℤ => uniformIntegerIntervalLaw 0 L z *
              (if integerResidue modulus hmod z = r then (1 : ℝ) else 0))
            (g := fun n : ℕ =>
              if n % modulus = r.val then 1 / (L : ℝ) else 0)
            (fun z hz => z.toNat)
          · intro z hz
            rcases Finset.mem_Ico.mp (by simpa [I] using hz) with ⟨hz0, hzL⟩
            have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
            have hlt : z.toNat < L := by
              have hltZ : (z.toNat : ℤ) < (L : ℤ) := by rw [hzcast]; exact hzL
              exact_mod_cast hltZ
            exact Finset.mem_range.mpr hlt
          · intro z hz y hy hEq
            rcases Finset.mem_Ico.mp (by simpa [I] using hz) with ⟨hz0, hzL⟩
            rcases Finset.mem_Ico.mp (by simpa [I] using hy) with ⟨hy0, hyL⟩
            calc
              z = (z.toNat : ℤ) := (Int.toNat_of_nonneg hz0).symm
              _ = (y.toNat : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hEq
              _ = y := Int.toNat_of_nonneg hy0
          · intro n hn
            refine ⟨(n : ℤ), ?_, ?_⟩
            · apply Finset.mem_Ico.mpr
              constructor
              · norm_num
              · exact_mod_cast Finset.mem_range.mp hn
            · simp
          · intro z hz
            rcases Finset.mem_Ico.mp (by simpa [I] using hz) with ⟨hz0, hzL⟩
            have hres := integerResidue_eq_toNat_mod hmod z hz0
            have hcond :
                (integerResidue modulus hmod z = r) ↔ z.toNat % modulus = r.val := by
              rw [hres]
              constructor
              · intro hEq
                exact congrArg Fin.val hEq
              · intro hval
                exact Fin.ext hval
            by_cases h : z.toNat % modulus = r.val
            · have hr : integerResidue modulus hmod z = r := hcond.mpr h
              simp [uniformIntegerIntervalLaw, hz0, hzL, h, hr]
            · have hr : integerResidue modulus hmod z ≠ r := fun hr => h (hcond.mp hr)
              simp [uniformIntegerIntervalLaw, hz0, hzL, h, hr]

private theorem momentShiftCoordinateResidue_l1_bound {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 N b : ℕ)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (hreg : momentBaseRegular MS B l T J0 N b p)
    (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (MomentBaseIndex b T.d)))
    (k : Fin b) (j : Fin T.d) (side : Fin 2)
    (hi : momentBaseEnum b T.d i = Sum.inr (k, (j, side))) :
    finiteL1
      (momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i)
      (uniformResidueLaw modulus) ≤
      2 * (modulus : ℝ) /
        T.length (corrScales MS) l J0 N
          (fun t => p ((momentPrimeEnum b T.q).symm (k, t))) := by
  classical
  let L := T.length (corrScales MS) l J0 N
    (fun t => p ((momentPrimeEnum b T.q).symm (k, t)))
  have hIco : Finset.Ico 0 (0 + L) = Finset.range L := by
    ext n
    simp
  have hL : 0 < L := hreg.2 k
  have hEq : (fun r : Fin modulus =>
      momentBaseCoordinateResidueLaw MS B l T J0 N b p modulus hmod i r) =
      fun r => ∑ n ∈ Finset.range L,
        if n % modulus = r.val then 1 / (L : ℝ) else 0 := by
    funext r
    unfold momentBaseCoordinateResidueLaw
    simp only [momentBaseCoordinateLaw, hi]
    exact uniformIntegerIntervalResidueLaw_eq_nat hL hmod r
  calc
    _ = finiteL1 (fun r : Fin modulus => ∑ n ∈ Finset.range L,
          if n % modulus = r.val then 1 / (L : ℝ) else 0) (uniformResidueLaw modulus) := by
          unfold finiteL1
          apply Finset.sum_congr rfl
          intro r hr
          rw [congrFun hEq r]
    _ = finiteL1 (fun r : Fin modulus => ∑ n ∈ Finset.Ico 0 (0 + L),
          if n % modulus = r.val then 1 / (L : ℝ) else 0) (uniformResidueLaw modulus) := by
          unfold finiteL1
          apply Finset.sum_congr rfl
          intro r hr
          rw [hIco]
    _ ≤ 2 * (modulus : ℝ) / L := by
          simpa [Nat.zero_add, hIco] using
            (uniform_interval_sampling_bounds 0 L modulus hL hmod)

private theorem harmonicResidueError_mono {X W k K : ℕ} (hk : k ≤ K)
    (hden : 0 < (X : ℝ) * (Real.log X - (W : ℝ) / X)) :
    harmonicResidueError X W k ≤ harmonicResidueError X W K := by
  unfold harmonicResidueError
  apply div_le_div_of_nonneg_right _ hden.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Nat.add_le_add_right hk 1

private noncomputable def momentBaseEpsilonBase {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 b N : ℕ) : ℝ := by
  let V := masterScaleV MS.core.parameters N l
  let rows := Fintype.card (MomentRowIndex b T.d)
  let base := Fintype.card (MomentBaseIndex b T.d)
  let kbound := V ^ rows
  let lengthFloor := momentShiftLengthLower MS l T J0 N
  exact (base : ℝ) *
    (harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) kbound +
      2 * (kbound : ℝ) / (max 1 lengthFloor : ℝ))

private theorem momentBaseResidue_uniform_bound {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hgap : ValidGap B l) (T : CubeTemplate) (J0 b N : ℕ) (hJ0 : 0 < J0)
    (p : Fin (Fintype.card (MomentPrimeIndex b T.q)) → ℕ)
    (hreg : momentBaseRegular MS B l T J0 N b p)
    (hgood : ∀ k : Fin b,
      T.Good (corrScales MS) l N
        (fun j => p ((momentPrimeEnum b T.q).symm (k, j))))
    (active : Finset (Fin (Fintype.card (MomentRowIndex b T.d))))
    (σ : Fin (Fintype.card (MomentRowIndex b T.d)) → ℕ)
    (hσ : ∀ u, divisorTemplateLaw MS.core.parameters N
      (momentDivisorFamily B active u) (σ u) ≠ 0) :
    finiteL1
      (baseResidueLaw (∏ u, σ u) (by
        have hs (u : Fin (Fintype.card (MomentRowIndex b T.d))) : 0 < σ u := by
          have hh := momentDivisorFamily_support_specs MS B l hgap.1 active u N (σ u) (hσ u)
          exact lt_of_lt_of_le Nat.zero_lt_one hh.1
        exact Finset.prod_pos fun u _ => hs u)
        (momentBaseMass MS B l T J0 N b p))
      (uniformBaseResidueLaw (∏ u, σ u)
        (Fintype.card (MomentBaseIndex b T.d))) ≤
      momentBaseEpsilonBase MS B l T J0 b N := by
  classical
  let rows := Fintype.card (MomentRowIndex b T.d)
  let base := Fintype.card (MomentBaseIndex b T.d)
  let V := masterScaleV MS.core.parameters N l
  let Kmod := ∏ u : Fin rows, σ u
  let Kbound := V ^ rows
  let lengthFloor := momentShiftLengthLower MS l T J0 N
  let pivotErr := harmonicResidueError
    (MS.core.parameters.X N B.1) (primorial (N + 1)) Kbound
  let shiftErr := 2 * (Kbound : ℝ) / (max 1 lengthFloor : ℝ)
  have hVone : 1 ≤ V := by dsimp [V, masterScaleV]; omega
  have hspec (u : Fin rows) : 1 ≤ σ u ∧ σ u ≤ V := by
    exact momentDivisorFamily_support_specs MS B l hgap.1 active u N (σ u) (hσ u)
  have hKpos : 0 < Kmod := by
    dsimp [Kmod]
    apply Finset.prod_pos
    intro u hu
    exact lt_of_lt_of_le Nat.zero_lt_one (hspec u).1
  have hKcop : Nat.Coprime Kmod (primorial (N + 1)) := by
    dsimp [Kmod]
    rw [Nat.coprime_fintype_prod_left_iff]
    intro u
    exact momentDivisorFamily_support_coprime MS B active u N (σ u) (hσ u)
  have hKle : Kmod ≤ Kbound := by
    dsimp [Kmod, Kbound, V]
    calc
      ∏ u : Fin rows, σ u ≤ ∏ _u : Fin rows, masterScaleV MS.core.parameters N l :=
        Finset.prod_le_prod fun u hu => (hspec u).2
      _ = masterScaleV MS.core.parameters N l ^ rows := by simp
  have hSampling := momentHarmonicPivotResidue_l1_bound MS B N Kmod hKpos hKcop
  obtain ⟨hW, hX, hlog⟩ := momentPivotSamplingHypotheses MS B N
  have hXpos : (0 : ℝ) < MS.core.parameters.X N B.1 := by exact_mod_cast (by omega : 0 < MS.core.parameters.X N B.1)
  have hDenPos : 0 < (MS.core.parameters.X N B.1 : ℝ) *
      (Real.log (MS.core.parameters.X N B.1) - (primorial (N + 1) : ℝ) /
        MS.core.parameters.X N B.1) := mul_pos hXpos (sub_pos.mpr hlog)
  have hPivotNonneg : 0 ≤ pivotErr := by
    dsimp [pivotErr, harmonicResidueError]
    exact div_nonneg (by positivity) hDenPos.le
  have hShiftNonneg : 0 ≤ shiftErr := by dsimp [shiftErr]; positivity
  have hδ (i : Fin base) :
      finiteL1
        (momentBaseCoordinateResidueLaw MS B l T J0 N b p Kmod hKpos i)
        (uniformResidueLaw Kmod) ≤ pivotErr + shiftErr := by
    cases hi : momentBaseEnum b T.d i with
    | inl u =>
        have hp := momentPivotCoordinateResidue_l1_bound
          MS B l T J0 N b p Kmod hKpos i hi hKcop
        exact le_trans (hp.trans (harmonicResidueError_mono hKle hDenPos))
          (le_add_of_nonneg_right hShiftNonneg)
    | inr idx =>
        rcases idx with ⟨k, ⟨j, side⟩⟩
        let pk : Fin T.q → ℕ := fun t => p ((momentPrimeEnum b T.q).symm (k, t))
        have hInt := momentShiftCoordinateResidue_l1_bound
          MS B l T J0 N b p hreg Kmod hKpos i k j side hi
        have hlow := momentShiftLength_lower MS l T J0 N hJ0 pk (hgood k)
        have hlength : max 1 lengthFloor ≤
            T.length (corrScales MS) l J0 N pk := by
          exact (Nat.max_le).2 ⟨Nat.succ_le_iff.mpr (hreg.2 k), hlow⟩
        have hInterval :
            finiteL1
              (momentBaseCoordinateResidueLaw MS B l T J0 N b p Kmod hKpos i)
              (uniformResidueLaw Kmod) ≤ shiftErr := by
          dsimp [shiftErr]
          calc
            _ ≤ 2 * (Kmod : ℝ) /
                  (T.length (corrScales MS) l J0 N pk : ℝ) := hInt
            _ ≤ 2 * (Kbound : ℝ) /
                  (T.length (corrScales MS) l J0 N pk : ℝ) := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                exact_mod_cast (Nat.mul_le_mul_left 2 hKle)
            _ ≤ 2 * (Kbound : ℝ) / (max 1 lengthFloor : ℝ) := by
                apply div_le_div_of_nonneg_left (by positivity)
                  (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 lengthFloor)))
                exact_mod_cast hlength
        exact le_trans hInterval (le_add_of_nonneg_left hPivotNonneg)
  have hresidue := momentBaseResidueL1_le_coordinate_errors
    MS B l T J0 N b p hreg Kmod hKpos (fun _ => pivotErr + shiftErr) hδ
  calc
    _ ≤ ∑ _i : Fin base, (pivotErr + shiftErr) := hresidue
    _ = (base : ℝ) * (pivotErr + shiftErr) := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
    _ = momentBaseEpsilonBase MS B l T J0 b N := by
          simp [momentBaseEpsilonBase, rows, base, V, Kbound, lengthFloor, pivotErr, shiftErr]

private theorem momentPivotLogDen_ge_half {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (N : ℕ) :
    (1 / 2 : ℝ) ≤ Real.log (MS.core.parameters.X N B.1 : ℝ) -
      (primorial (N + 1) : ℝ) / MS.core.parameters.X N B.1 := by
  let W := primorial (N + 1)
  let X := MS.core.parameters.X N B.1
  have hW : 0 < W := primorial_pos _
  have hWle : 1 ≤ W := Nat.one_le_iff_ne_zero.mpr hW.ne'
  have hcut : 4 * W ≤ X := MS.gapStage.valid_raw_cutoffs N B.1
  have hXfour : 4 ≤ X := by omega
  have hXreal : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXfour
  have hWreal : (1 : ℝ) ≤ W := by exact_mod_cast hWle
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hcutReal : 4 * (W : ℝ) ≤ (X : ℝ) := by exact_mod_cast hcut
  have hWover : (W : ℝ) / X ≤ 1 / 4 := by
    apply (div_le_iff₀ hXpos).2
    linarith
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).2
    exact lt_trans Real.exp_one_lt_three (by norm_num)
  have hlogX : Real.log 4 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) hXreal
  change (1 / 2 : ℝ) ≤ Real.log (X : ℝ) - (W : ℝ) / X
  linarith

private theorem momentPivotResidueError_superPolynomial {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hgap : ValidGap B l) (T : CubeTemplate) (b : ℕ) :
    SuperPolynomialSmall
      (fun N => harmonicResidueError (MS.core.parameters.X N B.1)
        (primorial (N + 1)) ((masterScaleV MS.core.parameters N l) ^
          Fintype.card (MomentRowIndex b T.d)))
      (fun N => (masterScaleV MS.core.parameters N l : ℝ)) := by
  intro C hC
  let rows := Fintype.card (MomentRowIndex b T.d)
  let G : ℕ → ℕ := fun N => momentGapScale MS l N
  let S : ℕ → ℝ := fun N => (G N : ℝ)
  let V : ℕ → ℕ := fun N => masterScaleV MS.core.parameters N l
  let Aexp : ℝ := ((rows + 1 : ℕ) : ℝ) + C
  have hAexp : 0 < Aexp := by dsimp [Aexp]; positivity
  have hS_tendsto : Tendsto S atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (momentGapScale_tendsto MS l)
  have hSpos (N : ℕ) : 0 < S N := by
    have hNat : 0 < G N := by
      dsimp [G, momentGapScale]
      have hV : 2 ≤ masterScaleV MS.core.parameters N l := by
        dsimp [masterScaleV]
        omega
      omega
    change (0 : ℝ) < (G N : ℝ)
    exact_mod_cast hNat
  have hXpos (N : ℕ) :
      (0 : ℝ) < (MS.core.parameters.X N B.1 : ℝ) := by
    exact_mod_cast MS.core.parameters.Xpos N B.1
  have hWleV (N : ℕ) : primorial (N + 1) ≤ V N := by
    dsimp [V]
    exact (MS.core.parameters.Wle N).trans (by dsimp [masterScaleV]; omega)
  have hVleS (N : ℕ) : (V N : ℝ) ≤ S N := by
    dsimp [V, S, momentGapScale]
    exact_mod_cast Nat.le_add_left (masterScaleV MS.core.parameters N l)
      ((MS.primeStage.pool N l).upper)
  have hXratio := momentPivotCutoff_dominates_gap_scale MS B l hgap
    (Aexp + 1) (by linarith)
  have hXlower : ∀ᶠ N : ℕ in atTop,
      S N ^ (Aexp + 1) ≤ (MS.core.parameters.X N B.1 : ℝ) := by
    filter_upwards [hXratio.eventually_ge_atTop (1 : ℝ)] with N hN
    have hmul := (le_div_iff₀ (Real.rpow_pos_of_pos (hSpos N) (Aexp + 1))).1 hN
    simpa using hmul
  have hErrBound (N : ℕ) :
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) (V N ^ rows) ≤
        4 * (V N : ℝ) ^ (rows + 1) /
          (MS.core.parameters.X N B.1 : ℝ) := by
    have hVone : 1 ≤ V N := by dsimp [V, masterScaleV]; omega
    have hKone : 1 ≤ V N ^ rows := one_le_pow₀ hVone
    have hKplus : V N ^ rows + 1 ≤ 2 * V N ^ rows := by omega
    have hNum : primorial (N + 1) * (V N ^ rows + 1) ≤ 2 * V N ^ (rows + 1) := by
      calc
        primorial (N + 1) * (V N ^ rows + 1) ≤ V N * (2 * V N ^ rows) :=
          Nat.mul_le_mul (hWleV N) hKplus
        _ = 2 * V N ^ (rows + 1) := by rw [pow_succ]; ring
    have hXpos : (0 : ℝ) < (MS.core.parameters.X N B.1 : ℝ) := by
      exact_mod_cast MS.core.parameters.Xpos N B.1
    have hDen := momentPivotLogDen_ge_half MS B N
    calc
      _ = ((primorial (N + 1) : ℝ) * ((V N ^ rows + 1 : ℕ) : ℝ)) /
          ((MS.core.parameters.X N B.1 : ℝ) *
            (Real.log (MS.core.parameters.X N B.1 : ℝ) -
              (primorial (N + 1) : ℝ) / MS.core.parameters.X N B.1)) := rfl
      _ ≤ ((primorial (N + 1) : ℝ) * ((V N ^ rows + 1 : ℕ) : ℝ)) /
          ((MS.core.parameters.X N B.1 : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hDen, hXpos])
      _ = 2 * ((primorial (N + 1) : ℝ) * ((V N ^ rows + 1 : ℕ) : ℝ)) /
            (MS.core.parameters.X N B.1 : ℝ) := by
              field_simp [ne_of_gt hXpos] <;> ring
      _ ≤ 4 * (V N : ℝ) ^ (rows + 1) /
          (MS.core.parameters.X N B.1 : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hNum' : 2 * (primorial (N + 1) * (V N ^ rows + 1)) ≤
            4 * V N ^ (rows + 1) := by
          calc
            _ ≤ 2 * (2 * V N ^ (rows + 1)) := Nat.mul_le_mul_left 2 hNum
            _ = _ := by ring
        exact_mod_cast hNum'
  have hSmallBound : ∀ᶠ N : ℕ in atTop,
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) (V N ^ rows) *
          (V N : ℝ) ^ C ≤ 4 / S N := by
    filter_upwards [hXlower] with N hXN
    have hVbase : 1 ≤ (V N : ℝ) := by exact_mod_cast (show 1 ≤ V N from by dsimp [V, masterScaleV]; omega)
    have hVrow : (V N : ℝ) ^ (rows + 1) ≤ S N ^ ((rows + 1 : ℕ) : ℝ) := by
      have hVle : V N ≤ momentGapScale MS l N := by
        dsimp [V, momentGapScale]
        omega
      have hcast := (Real.rpow_natCast (V N : ℝ) (rows + 1)).symm
      rw [hcast]
      have hVleReal : (V N : ℝ) ≤ S N := by
        change (V N : ℝ) ≤ (momentGapScale MS l N : ℝ)
        exact_mod_cast hVle
      exact Real.rpow_le_rpow (by positivity) hVleReal (by positivity)
    have hVC : (V N : ℝ) ^ C ≤ S N ^ C :=
      Real.rpow_le_rpow (by positivity) (hVleS N) hC.le
    have hProd : (V N : ℝ) ^ (rows + 1) * (V N : ℝ) ^ C ≤ S N ^ Aexp := by
      calc
        _ ≤ S N ^ ((rows + 1 : ℕ) : ℝ) * S N ^ C :=
          mul_le_mul hVrow hVC (by positivity) (by positivity)
        _ = S N ^ Aexp := by
          calc
            _ = S N ^ ((rows + 1 : ℕ) : ℝ) * S N ^ C := by rfl
            _ = S N ^ (((rows + 1 : ℕ) : ℝ) + C) :=
              (Real.rpow_add (hSpos N) _ _).symm
            _ = S N ^ Aexp := by rfl
    have hratio : S N ^ Aexp / (MS.core.parameters.X N B.1 : ℝ) ≤ 1 / S N := by
      apply (div_le_div_iff₀ (hXpos N) (hSpos N)).2
      calc
        S N ^ Aexp * S N = S N ^ Aexp * S N ^ (1 : ℝ) := by simp
        _ = S N ^ (Aexp + 1) := (Real.rpow_add (hSpos N) Aexp 1).symm
        _ ≤ (MS.core.parameters.X N B.1 : ℝ) := hXN
        _ = 1 * (MS.core.parameters.X N B.1 : ℝ) := by ring
    calc
      _ ≤ (4 * (V N : ℝ) ^ (rows + 1) /
            (MS.core.parameters.X N B.1 : ℝ)) * (V N : ℝ) ^ C :=
        mul_le_mul_of_nonneg_right (hErrBound N) (by positivity)
      _ = 4 * ((V N : ℝ) ^ (rows + 1) * (V N : ℝ) ^ C) /
            (MS.core.parameters.X N B.1 : ℝ) := by ring
      _ ≤ 4 * (S N ^ Aexp /
            (MS.core.parameters.X N B.1 : ℝ)) := by
        calc
          _ = (4 * ((V N : ℝ) ^ (rows + 1) * (V N : ℝ) ^ C)) /
                (MS.core.parameters.X N B.1 : ℝ) := by ring
          _ ≤ (4 * S N ^ Aexp) /
                (MS.core.parameters.X N B.1 : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hProd (by norm_num)) (by positivity)
          _ = _ := by ring
      _ ≤ 4 / S N := by
        have := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4)
        simpa [div_eq_mul_inv, mul_assoc] using this
  have hSreal := tendsto_inv_atTop_zero.comp hS_tendsto
  have hTop : Tendsto (fun N : ℕ => 4 / S N) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hSreal
  have hErrNonneg (N : ℕ) :
      0 ≤ harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) (V N ^ rows) *
        (V N : ℝ) ^ C := by
    have hXposN : (0 : ℝ) < MS.core.parameters.X N B.1 := by
      exact_mod_cast MS.core.parameters.Xpos N B.1
    have hdenN : 0 < (MS.core.parameters.X N B.1 : ℝ) *
        (Real.log (MS.core.parameters.X N B.1 : ℝ) -
          (primorial (N + 1) : ℝ) / MS.core.parameters.X N B.1) :=
      mul_pos hXposN (by linarith [momentPivotLogDen_ge_half MS B N])
    have hVnonneg : 0 ≤ (V N : ℝ) := by positivity
    unfold harmonicResidueError
    exact mul_nonneg (div_nonneg (by positivity) hdenN.le)
      (Real.rpow_nonneg hVnonneg C)
  exact squeeze_zero' (Eventually.of_forall hErrNonneg) hSmallBound hTop

private theorem momentShiftResidueError_superPolynomial {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (T : CubeTemplate)
    (J0 : ℕ) (hJ0 : 0 < J0) (b : ℕ) :
    SuperPolynomialSmall
      (fun N => 2 * ((masterScaleV MS.core.parameters N l) ^
        Fintype.card (MomentRowIndex b T.d) : ℝ) /
        (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ))
      (fun N => (masterScaleV MS.core.parameters N l : ℝ)) := by
  intro C hC
  let rows := Fintype.card (MomentRowIndex b T.d)
  let G : ℕ → ℕ := fun N => momentGapScale MS l N
  let S : ℕ → ℝ := fun N => (G N : ℝ)
  let V : ℕ → ℕ := fun N => masterScaleV MS.core.parameters N l
  let Aexp : ℝ := (rows : ℝ) + C
  let m : ℕ := Nat.ceil Aexp + 1
  have hApos : 0 < Aexp := by dsimp [Aexp]; positivity
  have hm : Aexp + 1 ≤ (m : ℝ) := by
    dsimp [m]
    have hceil := Nat.le_ceil Aexp
    norm_num at hceil ⊢
    linarith
  have hS : Tendsto S atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (momentGapScale_tendsto MS l)
  have hSpos (N : ℕ) : 0 < S N := by
    have hNat : 0 < G N := by
      dsimp [G, momentGapScale]
      have hV : 2 ≤ masterScaleV MS.core.parameters N l := by
        dsimp [masterScaleV]
        omega
      omega
    change (0 : ℝ) < (G N : ℝ)
    exact_mod_cast hNat
  have hSone (N : ℕ) : 1 ≤ S N := by
    have hNat : 1 ≤ G N := by
      dsimp [G, momentGapScale]
      have hV : 2 ≤ masterScaleV MS.core.parameters N l := by
        dsimp [masterScaleV]
        omega
      omega
    change (1 : ℝ) ≤ (G N : ℝ)
    exact_mod_cast hNat
  have hVleS (N : ℕ) : (V N : ℝ) ≤ S N := by
    change (V N : ℝ) ≤ (momentGapScale MS l N : ℝ)
    have hNat : V N ≤ momentGapScale MS l N := by
      dsimp [V, momentGapScale]
      omega
    exact_mod_cast hNat
  have hVrealPos (N : ℕ) : 0 < (V N : ℝ) := by
    have hVpos : 0 < V N := by dsimp [V, masterScaleV]; omega
    exact_mod_cast hVpos
  have hFloorLower : ∀ᶠ N : ℕ in atTop,
      S N ^ (m : ℝ) ≤ (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ) := by
    have hfloor := momentShiftLengthLower_ge_pow MS l T J0 hJ0 m
    filter_upwards [hfloor] with N hN
    have hcast : ((G N) ^ m : ℝ) = S N ^ (m : ℝ) := by
      dsimp [S]
      exact (Real.rpow_natCast (G N : ℝ) m).symm
    rw [← hcast]
    exact_mod_cast le_trans hN (Nat.le_max_right 1 _)
  have hSmallBound : ∀ᶠ N : ℕ in atTop,
      (2 * ((V N) ^ rows : ℝ) /
        (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ)) * (V N : ℝ) ^ C ≤
        2 / S N := by
    filter_upwards [hFloorLower] with N hfloor
    have hVrow : (V N : ℝ) ^ rows ≤ S N ^ (rows : ℝ) := by
      have hNat : V N ^ rows ≤ momentGapScale MS l N ^ rows := by
        exact Nat.pow_le_pow_left (by
          dsimp [V, momentGapScale]
          omega) rows
      have hcast := (Real.rpow_natCast (V N : ℝ) rows).symm
      rw [hcast]
      exact Real.rpow_le_rpow (by positivity) (hVleS N) (by positivity)
    have hVC : (V N : ℝ) ^ C ≤ S N ^ C :=
      Real.rpow_le_rpow (by positivity) (hVleS N) hC.le
    have hProd : (V N : ℝ) ^ rows * (V N : ℝ) ^ C ≤ S N ^ Aexp := by
      calc
        _ ≤ S N ^ (rows : ℝ) * S N ^ C :=
          mul_le_mul hVrow hVC (by positivity) (by positivity)
        _ = S N ^ Aexp := by
          calc
            _ = S N ^ (rows : ℝ) * S N ^ C := by rfl
            _ = S N ^ ((rows : ℝ) + C) :=
              (Real.rpow_add (hSpos N) _ _).symm
            _ = S N ^ Aexp := by rfl
    have hDenPos : 0 < (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _))
    have hRatio : S N ^ Aexp /
        (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ) ≤ 1 / S N := by
      apply (div_le_div_iff₀ hDenPos (hSpos N)).2
      calc
        S N ^ Aexp * S N = S N ^ (Aexp + 1) := by
          calc
            _ = S N ^ Aexp * S N ^ (1 : ℝ) := by simp
            _ = _ := (Real.rpow_add (hSpos N) Aexp 1).symm
        _ ≤ S N ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le (hSone N) hm
        _ ≤ (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ) := hfloor
        _ = 1 * (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ) := by ring
    calc
      _ = 2 * (((V N : ℝ) ^ rows * (V N : ℝ) ^ C) /
          (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ)) := by ring
      _ ≤ 2 * (S N ^ Aexp /
          (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hProd (by positivity)) (by norm_num)
      _ ≤ 2 / S N := by
        have := mul_le_mul_of_nonneg_left hRatio (by norm_num : (0 : ℝ) ≤ 2)
        simpa [div_eq_mul_inv, mul_assoc] using this
  have hInv := tendsto_inv_atTop_zero.comp hS
  have hTop : Tendsto (fun N : ℕ => 2 / S N) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hInv
  have hErrNonneg (N : ℕ) :
      0 ≤ (2 * ((V N) ^ rows : ℝ) /
        (max 1 (momentShiftLengthLower MS l T J0 N) : ℝ)) * (V N : ℝ) ^ C := by
    positivity
  exact squeeze_zero' (Eventually.of_forall hErrNonneg) hSmallBound hTop

theorem parameterTailProductLaw_nonneg {n : ℕ} (A : Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (σ : ℕ) :
    0 ≤ parameterTailProductLaw A N T σ := by
  unfold parameterTailProductLaw
  apply tsum_nonneg
  intro t
  have hprod : 0 ≤ ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) :=
    Finset.prod_nonneg fun j _ => harmonicNatLaw_nonneg _ _ _
  by_cases hσ : (∏ j ∈ T, t j) = σ
  · simpa [hσ] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hprod
  · simp [hσ]

theorem nu_nonneg {n : ℕ} (A : Parameters n) (N : ℕ) (B : Block n) (y : ℤ) :
    0 ≤ nu A N B y := by
  unfold nu nuB
  apply tsum_nonneg
  intro σ
  have htail := parameterTailProductLaw_nonneg A N B.2.val σ
  by_cases hdiv : (σ : ℤ) ∣ y
  · simpa [hdiv] using
      mul_nonneg (mul_nonneg htail (by positivity)) (by norm_num : (0 : ℝ) ≤ 1)
  · simp [hdiv]

theorem abs_sub_one_le_add_one {x : ℝ} (hx : 0 ≤ x) :
    |x - 1| ≤ 1 + x := by
  rw [abs_le]
  constructor <;> linarith

noncomputable def emuSupport {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n) : Finset ℤ :=
  (harmonicLaw_support_finite (A.X N i) (primorial (N + 1))).toFinset

theorem Emu_eq_sum_support {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (f : ℤ → ℝ) :
    Emu A N i f = ∑ y ∈ emuSupport A N i, mu A N i y * f y := by
  classical
  unfold Emu
  rw [tsum_eq_sum (s := emuSupport A N i)]
  intro y hy
  have hzero : mu A N i y = 0 := by
    by_contra hne
    have hmem : y ∈ Function.support (mu A N i) := by
      change mu A N i y ≠ 0
      exact hne
    exact hy ((harmonicLaw_support_finite (A.X N i) (primorial (N + 1))).mem_toFinset.mpr hmem)
  simp [hzero]

theorem Emu_finset_sum {ι : Type*} {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (s : Finset ι) (F : ι → ℤ → ℝ) :
    Emu A N i (fun y => ∑ k ∈ s, F k y) =
      ∑ k ∈ s, Emu A N i (F k) := by
  classical
  rw [Emu_eq_sum_support]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Emu_eq_sum_support]

theorem Emu_abs_le {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n) (f : ℤ → ℝ) :
    |Emu A N i f| ≤ Emu A N i (fun y => |f y|) := by
  classical
  calc
    |Emu A N i f| =
        |∑ y ∈ emuSupport A N i, mu A N i y * f y| := by
          rw [Emu_eq_sum_support]
    _ ≤ ∑ y ∈ emuSupport A N i, |mu A N i y * f y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y ∈ emuSupport A N i, mu A N i y * |f y| := by
      apply Finset.sum_congr rfl
      intro y hy
      have hμ : 0 ≤ mu A N i y := by
        simpa [mu] using harmonicLaw_nonneg (A.X N i) (primorial (N + 1)) y
      rw [abs_mul, abs_of_nonneg hμ]
    _ = Emu A N i (fun y => |f y|) :=
      (Emu_eq_sum_support A N i (fun y => |f y|)).symm

theorem Emu_weighted_cauchy {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (w f g : ℤ → ℝ) (hw : ∀ y, 0 ≤ w y) :
    |Emu A N i (fun y => w y * f y * g y)| ^ 2 ≤
      Emu A N i (fun y => w y * f y ^ 2) *
        Emu A N i (fun y => w y * g y ^ 2) := by
  classical
  let s := emuSupport A N i
  let mass : ℤ → ℝ := fun y => mu A N i y * w y
  let u : ℤ → ℝ := fun y => Real.sqrt (mass y) * f y
  let v : ℤ → ℝ := fun y => Real.sqrt (mass y) * g y
  have hmass (y : ℤ) : 0 ≤ mass y :=
    mul_nonneg (harmonicLaw_nonneg (A.X N i) (primorial (N + 1)) y) (hw y)
  have hsumuv :
      (∑ y ∈ s, u y * v y) = Emu A N i (fun y => w y * f y * g y) := by
    change (∑ y ∈ emuSupport A N i, u y * v y) =
      Emu A N i (fun y => w y * f y * g y)
    rw [Emu_eq_sum_support]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [u, v, mass]
    calc
      Real.sqrt (mu A N i y * w y) * f y *
          (Real.sqrt (mu A N i y * w y) * g y) =
          (Real.sqrt (mu A N i y * w y) ^ 2) * (f y * g y) := by ring
      _ = (mu A N i y * w y) * (f y * g y) := by rw [Real.sq_sqrt (hmass y)]
      _ = mu A N i y * (w y * f y * g y) := by ring
  have hsumu :
      (∑ y ∈ s, u y ^ 2) = Emu A N i (fun y => w y * f y ^ 2) := by
    change (∑ y ∈ emuSupport A N i, u y ^ 2) =
      Emu A N i (fun y => w y * f y ^ 2)
    rw [Emu_eq_sum_support]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [u, mass]
    rw [mul_pow, Real.sq_sqrt (hmass y)]
    ring
  have hsumv :
      (∑ y ∈ s, v y ^ 2) = Emu A N i (fun y => w y * g y ^ 2) := by
    change (∑ y ∈ emuSupport A N i, v y ^ 2) =
      Emu A N i (fun y => w y * g y ^ 2)
    rw [Emu_eq_sum_support]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [v, mass]
    rw [mul_pow, Real.sq_sqrt (hmass y)]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s u v
  rw [hsumuv, hsumu, hsumv] at hcs
  simpa only [sq_abs] using hcs

-- Adapted from OpenAI openai/math (Apache-2.0), OAI/MeasureTheory/Falconer/Estimates/FiniteHolder.lean.
theorem finite_holder_equal {ι α : Type*} (I : Finset ι) (B : Finset α)
    (hI : I.Nonempty) (f : ι → α → ℝ)
    (hf : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ f i x) :
    (∑ x ∈ B, ∏ i ∈ I, (f i x) ^ (1 / (I.card : ℝ))) ≤
      ∏ i ∈ I, (∑ x ∈ B, f i x) ^ (1 / (I.card : ℝ)) := by
  classical
  let p : ℝ := 1 / (I.card : ℝ)
  let M : ι → ℝ := fun i => ∑ x ∈ B, f i x
  have hcard : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  have hp : 0 < p := one_div_pos.mpr hcard
  have hweights : ∑ _i ∈ I, p = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, p]
    exact mul_one_div_cancel hcard.ne'
  have hMnonneg : ∀ i ∈ I, 0 ≤ M i := by
    intro i hi
    dsimp [M]
    exact Finset.sum_nonneg fun x hx => hf i hi x hx
  by_cases hM : ∀ i ∈ I, 0 < M i
  · let g : ι → α → ℝ := fun i x => f i x / M i
    have hg : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ g i x := by
      intro i hi x hx
      exact div_nonneg (hf i hi x hx) (hMnonneg i hi)
    have hgsum : ∀ i ∈ I, ∑ x ∈ B, g i x = 1 := by
      intro i hi
      simp only [g, ← Finset.sum_div, M]
      exact div_self (hM i hi).ne'
    have hmean : ∀ x ∈ B, ∏ i ∈ I, (g i x) ^ p ≤ ∑ i ∈ I, p * g i x := by
      intro x hx
      exact Real.geom_mean_le_arith_mean_weighted I (fun _ => p) (fun i => g i x)
        (fun _ _ => hp.le) hweights (fun i hi => hg i hi x hx)
    have hsum : ∑ x ∈ B, ∏ i ∈ I, (g i x) ^ p ≤ 1 := by
      calc
        _ ≤ ∑ x ∈ B, ∑ i ∈ I, p * g i x := Finset.sum_le_sum hmean
        _ = ∑ i ∈ I, p * (∑ x ∈ B, g i x) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
        _ = 1 := by
          calc
            _ = ∑ i ∈ I, p := Finset.sum_congr rfl fun i hi => by rw [hgsum i hi, mul_one]
            _ = 1 := hweights
    have hprod : ∀ x ∈ B,
        (∏ i ∈ I, (f i x) ^ p) =
          (∏ i ∈ I, (M i) ^ p) * (∏ i ∈ I, (g i x) ^ p) := by
      intro x hx
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      change (f i x) ^ p = (M i) ^ p * (f i x / M i) ^ p
      rw [Real.div_rpow (hf i hi x hx) (hMnonneg i hi)]
      have hne : (M i) ^ p ≠ 0 := (Real.rpow_pos_of_pos (hM i hi) _).ne'
      field_simp
    change (∑ x ∈ B, ∏ i ∈ I, (f i x) ^ p) ≤
      ∏ i ∈ I, (M i) ^ p
    calc
      _ = (∏ i ∈ I, (M i) ^ p) * (∑ x ∈ B, ∏ i ∈ I, (g i x) ^ p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hprod
      _ ≤ (∏ i ∈ I, (M i) ^ p) * 1 :=
        mul_le_mul_of_nonneg_left hsum
          (Finset.prod_nonneg fun i hi => Real.rpow_nonneg (hMnonneg i hi) _)
      _ = _ := mul_one _
  · push Not at hM
    obtain ⟨i, hi, hMi⟩ := hM
    have hzero : M i = 0 := le_antisymm hMi (hMnonneg i hi)
    have hrow : ∀ x ∈ B, f i x = 0 := by
      intro x hx
      apply le_antisymm _ (hf i hi x hx)
      calc
        f i x ≤ ∑ y ∈ B, f i y := Finset.single_le_sum (fun y hy => hf i hi y hy) hx
        _ = 0 := hzero
    have hleft : ∑ x ∈ B, ∏ j ∈ I, (f j x) ^ p = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply Finset.prod_eq_zero hi
      rw [hrow x hx, Real.zero_rpow hp.ne']
    change (∑ x ∈ B, ∏ i ∈ I, (f i x) ^ p) ≤ ∏ i ∈ I, (M i) ^ p
    rw [hleft]
    exact Finset.prod_nonneg fun j hj => Real.rpow_nonneg (hMnonneg j hj) _

theorem finite_holder_weighted {ι α : Type*} (I : Finset ι) (B : Finset α)
    (hI : I.Nonempty) (weight : α → ℝ) (f : ι → α → ℝ)
    (hw : ∀ x ∈ B, 0 ≤ weight x) :
    (∑ x ∈ B, weight x * ∏ i ∈ I, |f i x|) ≤
      ∏ i ∈ I, (∑ x ∈ B, weight x * |f i x| ^ I.card) ^
        (1 / (I.card : ℝ)) := by
  classical
  let p : ℝ := 1 / (I.card : ℝ)
  have hcard : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  have hpNat : (I.card : ℝ) * p = 1 := by
    dsimp [p]
    exact mul_one_div_cancel hcard.ne'
  have hp : p * (I.card : ℝ) = 1 := by rw [mul_comm, hpNat]
  have hpow (z : ℝ) (hz : 0 ≤ z) :
      (z ^ I.card) ^ p = z := by
    dsimp [p]
    rw [← Real.rpow_natCast_mul hz, hpNat, Real.rpow_one]
  have hweight_pow_eq (x : α) (hx : 0 ≤ weight x) :
      (weight x ^ p) ^ (I.card : ℝ) = weight x ^ (p * (I.card : ℝ)) :=
    (Real.rpow_mul hx p (I.card : ℝ)).symm
  have hweight_pow (x : α) (hx : 0 ≤ weight x) :
      (∏ _i ∈ I, (weight x) ^ p) = weight x := by
    rw [Finset.prod_const]
    rw [← Real.rpow_natCast, hweight_pow_eq x hx, hp, Real.rpow_one]
  let F : ι → α → ℝ := fun i x => weight x * |f i x| ^ I.card
  have hF : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ F i x := by
    intro i hi x hx
    dsimp [F]
    exact mul_nonneg (hw x hx) (pow_nonneg (abs_nonneg _) _)
  have hmain :=
    finite_holder_equal I B hI F hF
  have hterm (x : α) (hx : x ∈ B) :
      (∏ i ∈ I, (F i x) ^ p) = weight x * ∏ i ∈ I, |f i x| := by
    dsimp [F]
    calc
      ∏ i ∈ I, (weight x * |f i x| ^ I.card) ^ p =
          (∏ i ∈ I, (weight x) ^ p) *
            ∏ i ∈ I, (|f i x| ^ I.card) ^ p := by
        calc
          _ = ∏ i ∈ I, (weight x) ^ p * (|f i x| ^ I.card) ^ p := by
            apply Finset.prod_congr rfl
            intro i hi
            exact Real.mul_rpow (hw x hx) (pow_nonneg (abs_nonneg _) _)
          _ = (∏ i ∈ I, (weight x) ^ p) *
              ∏ i ∈ I, (|f i x| ^ I.card) ^ p := by
            rw [Finset.prod_mul_distrib]
      _ = weight x * ∏ i ∈ I, |f i x| := by
        rw [hweight_pow x (hw x hx)]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        exact hpow _ (abs_nonneg _)
  change (∑ x ∈ B, weight x * ∏ i ∈ I, |f i x|) ≤
      ∏ i ∈ I, (∑ x ∈ B, weight x * |f i x| ^ I.card) ^ p
  calc
    _ = ∑ x ∈ B, ∏ i ∈ I, (F i x) ^ p := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hterm x hx]
    _ ≤ ∏ i ∈ I, (∑ x ∈ B, F i x) ^ p := hmain

theorem Emu_weighted_holder {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    {n : ℕ} (A : Parameters n) (N : ℕ) (pivot : Fin n) (w : ℤ → ℝ)
    (f : ι → ℤ → ℝ) (hw : ∀ y, 0 ≤ w y) :
    Emu A N pivot (fun y => w y * ∏ i ∈ I, |f i y|) ≤
      ∏ i ∈ I,
        Emu A N pivot (fun y => w y * |f i y| ^ I.card) ^
          (1 / (I.card : ℝ)) := by
  classical
  let s := emuSupport A N pivot
  let mass : ℤ → ℝ := fun y => mu A N pivot y * w y
  have hmass (y : ℤ) : 0 ≤ mass y :=
    mul_nonneg (harmonicLaw_nonneg (A.X N pivot) (primorial (N + 1)) y) (hw y)
  have h :=
    finite_holder_weighted I s hI mass f (fun y _ => hmass y)
  have hleft :
      (∑ y ∈ s, mass y * ∏ i ∈ I, |f i y|) =
        Emu A N pivot (fun y => w y * ∏ i ∈ I, |f i y|) := by
    change (∑ y ∈ emuSupport A N pivot, mass y * ∏ i ∈ I, |f i y|) = _
    rw [Emu_eq_sum_support]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [mass]
    ring
  have hright (i : ι) :
      (∑ y ∈ s, mass y * |f i y| ^ I.card) =
        Emu A N pivot (fun y => w y * |f i y| ^ I.card) := by
    change (∑ y ∈ emuSupport A N pivot, mass y * |f i y| ^ I.card) = _
    rw [Emu_eq_sum_support]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [mass]
    ring
  calc
    Emu A N pivot (fun y => w y * ∏ i ∈ I, |f i y|) =
        ∑ y ∈ s, mass y * ∏ i ∈ I, |f i y| := hleft.symm
    _ ≤
        ∏ i ∈ I, (∑ y ∈ s, mass y * |f i y| ^ I.card) ^
          (1 / (I.card : ℝ)) := h
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hright i]

theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      ∑ i ∈ s, |f i - g i| *
        ∏ j ∈ s, (if j = i then (1 : ℝ) else max (|f j|) (|g j|)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    let M : ι → ℝ := fun j => max (|f j|) (|g j|)
    have hM_nonneg : ∀ j, 0 ≤ M j := fun j => le_trans (abs_nonneg _) (le_max_left _ _)
    have hprodF : |∏ i ∈ s, f i| ≤ ∏ i ∈ s, M i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun i hi => abs_nonneg _)
        (fun i hi => le_max_left _ _)
    have hprodG : |∏ i ∈ s, g i| ≤ ∏ i ∈ s, M i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun i hi => abs_nonneg _)
        (fun i hi => le_max_right _ _)
    have htermA :
        |f a - g a| * ∏ j ∈ insert a s, (if j = a then (1 : ℝ) else M j) =
          |f a - g a| * ∏ j ∈ s, M j := by
      rw [Finset.prod_insert ha]
      have hprod : ∏ j ∈ s, (if j = a then (1 : ℝ) else M j) =
          ∏ j ∈ s, M j := by
        apply Finset.prod_congr rfl
        intro j hj
        have hja : j ≠ a := by
          intro h
          apply ha
          simpa [h] using hj
        simp [hja]
      rw [if_pos (show a = a by rfl), one_mul, hprod]
    have htermI (i : ι) (hi : i ∈ s) :
        ∏ j ∈ insert a s, (if j = i then (1 : ℝ) else M j) =
          M a * ∏ j ∈ s, (if j = i then (1 : ℝ) else M j) := by
      have hia : a ≠ i := by
        intro h
        subst i
        exact ha hi
      rw [Finset.prod_insert ha]
      simp [hia]
    have hsum :
        ∑ i ∈ insert a s, |f i - g i| *
            ∏ j ∈ insert a s, (if j = i then (1 : ℝ) else M j) =
          |f a - g a| * ∏ j ∈ s, M j +
            M a * ∑ i ∈ s, |f i - g i| *
              ∏ j ∈ s, (if j = i then (1 : ℝ) else M j) := by
      rw [Finset.sum_insert ha, htermA]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [htermI i hi]
      ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    calc
      |f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i| =
          |(f a - g a) * (∏ i ∈ s, f i) +
            g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by
              congr 1
              ring
      _ ≤ |f a - g a| * |∏ i ∈ s, f i| +
            |g a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
              simpa only [abs_mul] using abs_add_le
                ((f a - g a) * (∏ i ∈ s, f i))
                (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
      _ ≤ |f a - g a| * ∏ i ∈ s, M i +
            M a * ∑ i ∈ s, |f i - g i| *
              ∏ j ∈ s, (if j = i then (1 : ℝ) else M j) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hprodF (abs_nonneg _))
                (mul_le_mul (le_max_right (|f a|) (|g a|)) ih
                  (abs_nonneg _) (hM_nonneg a))
      _ = ∑ i ∈ insert a s, |f i - g i| *
            ∏ j ∈ insert a s, (if j = i then (1 : ℝ) else M j) := by
              simpa [M] using hsum.symm

theorem prod_ite_singleton {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (i : ι) (hi : i ∈ s) (a : ℝ) :
    (∏ j ∈ s, (if j = i then a else (1 : ℝ))) = a := by
  have hrest : ∏ j ∈ s.erase i, (if j = i then a else (1 : ℝ)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]
  rw [← Finset.prod_erase_mul s (fun j => if j = i then a else (1 : ℝ)) hi, hrest]
  simp [hi]

theorem prod_ite_factorization {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (i : ι) (hi : i ∈ s) (a : ℝ) (f : ι → ℝ) :
    (∏ j ∈ s, (if j = i then a else f j)) =
      a * ∏ j ∈ s, (if j = i then (1 : ℝ) else f j) := by
  calc
    (∏ j ∈ s, if j = i then a else f j) =
        ∏ j ∈ s, (if j = i then a else (1 : ℝ)) * (if j = i then (1 : ℝ) else f j) := by
          apply Finset.prod_congr rfl
          intro j hj
          by_cases hji : j = i <;> simp [hji]
    _ = (∏ j ∈ s, if j = i then a else 1) *
          ∏ j ∈ s, if j = i then 1 else f j := by
      rw [Finset.prod_mul_distrib]
    _ = a * ∏ j ∈ s, if j = i then 1 else f j := by
          rw [prod_ite_singleton s i hi a]

end Prediction

end HindmanSumsProducts
