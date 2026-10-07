import HindmanSumsProducts.Arithmetic.MasterScales

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section

private lemma a_rough3_log2_iff_dyadic (p j : ℕ) (hp : p ≠ 0) :
    Nat.log2 p = j ↔ 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) := by
  constructor
  · intro h
    subst j
    constructor
    · simpa [Nat.log2_eq_log_two] using (Nat.pow_log_le_self 2 hp)
    · exact Nat.lt_log2_self
  · intro h
    rw [Nat.log2_eq_log_two]
    exact Nat.log_eq_of_pow_le_of_lt_pow h.1 (by simpa [Nat.pow_succ] using h.2)

private lemma a_rough3_dyadic_fiber_eq {lo hi a b j : ℕ}
    (hlo : lo = 2 ^ a) (hhi : hi = 2 ^ b) (haj : a ≤ j) (hjb : j < b) :
    (Finset.Ico lo hi).filter (fun p => Nat.log2 p = j) =
      Finset.Ico (2 ^ j) (2 ^ (j + 1)) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hlo_p, hp_hi⟩, hlog⟩
    have hp0 : p ≠ 0 := by
      intro hp
      subst p
      have hpos : 0 < lo := by rw [hlo]; positivity
      omega
    have hbin := (a_rough3_log2_iff_dyadic p j hp0).1 hlog
    exact hbin
  · intro hp
    have hp0 : p ≠ 0 := by
      intro hp0
      subst p
      simp at hp
    have hlog := (a_rough3_log2_iff_dyadic p j hp0).2 hp
    constructor
    · constructor
      · rw [hlo]
        exact (pow_le_pow_right' (a := 2) (by omega) haj).trans hp.1
      · rw [hhi]
        have hj1b : j + 1 ≤ b := by omega
        exact hp.2.trans_le (pow_le_pow_right' (a := 2) (by omega) hj1b)
    · exact hlog

private lemma a_rough3_level_mem {lo hi a b p : ℕ}
    (hlo : lo = 2 ^ a) (hhi : hi = 2 ^ b)
    (hp : p ∈ Finset.Ico lo hi) (hprime : p.Prime) :
    Nat.log2 p ∈ Finset.Ico a b := by
  have hp0 : p ≠ 0 := hprime.ne_zero
  have hp' := Finset.mem_Ico.mp hp
  simp only [Finset.mem_Ico]
  constructor
  · rw [Nat.log2_eq_log_two]
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hp0).2 (by simpa [hlo] using hp'.1)
  · rw [Nat.log2_eq_log_two]
    exact (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hp0).2 (by simpa [hhi] using hp'.2)

lemma a_rough3_primePoolMass_dyadic_sum {lo hi a b : ℕ}
    (hlo : lo = 2 ^ a) (hhi : hi = 2 ^ b) :
    primePoolMass lo hi =
      ∑ j ∈ Finset.Ico a b, primePoolMass (2 ^ j) (2 ^ (j + 1)) := by
  have hlevel (p : ℕ) (hp : p ∈ Finset.Ico lo hi) (hprime : p.Prime) :
      Nat.log2 p ∈ Finset.Ico a b := by
    exact a_rough3_level_mem hlo hhi hp hprime
  unfold primePoolMass
  rw [Finset.sum_filter]
  calc
    (∑ p ∈ Finset.Ico lo hi, if p.Prime then 1 / (p : ℝ) else 0) =
        ∑ j ∈ Finset.Ico a b,
          ∑ p ∈ (Finset.Ico lo hi).filter (fun p => Nat.log2 p = j),
            if p.Prime then 1 / (p : ℝ) else 0 := by
      symm
      rw [Finset.sum_fiberwise_eq_sum_filter]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hprime : p.Prime
      · simp [hlevel p hp hprime]
      · simp [hprime]
    _ = ∑ j ∈ Finset.Ico a b,
          ∑ p ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
            if p.Prime then 1 / (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      rw [a_rough3_dyadic_fiber_eq hlo hhi hj'.1 hj'.2]
    _ = ∑ j ∈ Finset.Ico a b, primePoolMass (2 ^ j) (2 ^ (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold primePoolMass
      rw [Finset.sum_filter]

private lemma a_rough3_primePoolLaw_dyadic_mix {lo hi a b : ℕ}
    (hlo : lo = 2 ^ a) (hhi : hi = 2 ^ b)
    (hmass : 0 < primePoolMass lo hi)
    (hbin : ∀ j ∈ Finset.Ico a b,
      0 < primePoolMass (2 ^ j) (2 ^ (j + 1))) (p : ℕ) :
    primePoolLaw lo hi p =
      ∑ j ∈ Finset.Ico a b,
        (primePoolMass (2 ^ j) (2 ^ (j + 1)) / primePoolMass lo hi) *
          primePoolLaw (2 ^ j) (2 ^ (j + 1)) p := by
  classical
  by_cases hmem : lo ≤ p ∧ p < hi ∧ p.Prime
  · have hp0 : p ≠ 0 := hmem.2.2.ne_zero
    have hlogmem : Nat.log2 p ∈ Finset.Ico a b :=
      a_rough3_level_mem hlo hhi (Finset.mem_Ico.mpr ⟨hmem.1, hmem.2.1⟩) hmem.2.2
    have hsum :
        (∑ j ∈ Finset.Ico a b,
          (primePoolMass (2 ^ j) (2 ^ (j + 1)) / primePoolMass lo hi) *
            primePoolLaw (2 ^ j) (2 ^ (j + 1)) p) =
          (primePoolMass (2 ^ Nat.log2 p) (2 ^ (Nat.log2 p + 1)) / primePoolMass lo hi) *
            primePoolLaw (2 ^ Nat.log2 p) (2 ^ (Nat.log2 p + 1)) p := by
      refine Finset.sum_eq_single (s := Finset.Ico a b)
        (f := fun j => (primePoolMass (2 ^ j) (2 ^ (j + 1)) / primePoolMass lo hi) *
          primePoolLaw (2 ^ j) (2 ^ (j + 1)) p) (Nat.log2 p) ?_ ?_
      · intro j hj hjne
        have hnot : ¬ (2 ^ j ≤ p ∧ p < 2 ^ (j + 1)) := by
          intro hb
          exact hjne ((a_rough3_log2_iff_dyadic p j hp0).2 hb).symm
        have hnot' : ¬ (2 ^ j ≤ p ∧ p < 2 ^ (j + 1) ∧ p.Prime) := by
          intro h
          exact hnot ⟨h.1, h.2.1⟩
        simp [primePoolLaw, hnot']
      · intro h
        exact (h hlogmem).elim
    rw [show primePoolLaw lo hi p = (1 / (p : ℝ)) / primePoolMass lo hi by
      simp [primePoolLaw, hmem]]
    rw [hsum]
    have hcomponent :
        primePoolLaw (2 ^ Nat.log2 p) (2 ^ (Nat.log2 p + 1)) p =
          (1 / (p : ℝ)) / primePoolMass (2 ^ Nat.log2 p) (2 ^ (Nat.log2 p + 1)) := by
      unfold primePoolLaw
      rw [if_pos (show 2 ^ Nat.log2 p ≤ p ∧ p < 2 ^ (Nat.log2 p + 1) ∧ p.Prime from
        ⟨(a_rough3_log2_iff_dyadic p (Nat.log2 p) hp0).1 rfl |>.1,
          (a_rough3_log2_iff_dyadic p (Nat.log2 p) hp0).1 rfl |>.2, hmem.2.2⟩)]
    rw [hcomponent]
    have hbinpos := hbin (Nat.log2 p) hlogmem
    have hpoolne : primePoolMass lo hi ≠ 0 := ne_of_gt hmass
    have hbinne : primePoolMass (2 ^ Nat.log2 p) (2 ^ (Nat.log2 p + 1)) ≠ 0 :=
      ne_of_gt hbinpos
    field_simp [hpoolne, hbinne]
  · rw [primePoolLaw, if_neg hmem]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hcomponent_zero :
        primePoolLaw (2 ^ j) (2 ^ (j + 1)) p = 0 := by
      unfold primePoolLaw
      split_ifs with h
      · have hglobal : lo ≤ p ∧ p < hi ∧ p.Prime := by
          have hlow : lo ≤ 2 ^ j := by
            simpa [hlo] using (pow_le_pow_right' (a := 2) (by omega) hj'.1)
          have hup : 2 ^ (j + 1) ≤ hi := by
            simpa [hhi] using
              (pow_le_pow_right' (a := 2) (by omega) (by omega : j + 1 ≤ b))
          exact ⟨le_trans hlow h.1, lt_of_lt_of_le h.2.1 hup, h.2.2⟩
        exact (hmem hglobal).elim
      · rfl
    simp [hcomponent_zero]

def a_rough3_dyadicLower {m : ℕ} (j : Fin m → ℕ) : Fin m → ℕ :=
  fun i => 2 ^ (j i)

def a_rough3_dyadicUpper {m : ℕ} (j : Fin m → ℕ) : Fin m → ℕ :=
  fun i => 2 ^ (j i + 1)

private def a_rough3_scaleWeight {m : ℕ} (lo hi a b : Fin m → ℕ)
    (j : Fin m → ℕ) : ℝ :=
  ∏ i, (primePoolMass (2 ^ (j i)) (2 ^ (j i + 1)) /
    primePoolMass (lo i) (hi i))

private def a_rough3_tupleSupport {m : ℕ} (lo hi : Fin m → ℕ) :
    Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

def a_rough3_scaleSupport {m : ℕ} (a b : Fin m → ℕ) :
    Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (a i) (b i))

private lemma a_rough3_primePoolMass_nonneg (lo hi : ℕ) :
    0 ≤ primePoolMass lo hi := by
  unfold primePoolMass
  apply Finset.sum_nonneg
  intro p hp
  exact one_div_nonneg.mpr (Nat.cast_nonneg p)

lemma a_rough3_roughPart_eq_one_of_natAbs_le {w : ℕ} {z : ℤ}
    (h : z.natAbs ≤ w) : roughPart w z = 1 := by
  unfold roughPart
  apply Finset.prod_eq_one
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpRange := Finset.mem_range.mp hp'.1
  have hpLarge := hp'.2.2
  omega

private lemma a_rough3_independentPrimePoolMass_zero_outside {m : ℕ}
    (lo hi : Fin m → ℕ) (x : Fin m → ℕ)
    (hx : x ∉ a_rough3_tupleSupport lo hi) :
    independentPrimePoolMass lo hi x = 0 := by
  classical
  have hnotall : ¬ ∀ i : Fin m, x i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hx
    simpa [a_rough3_tupleSupport] using hall
  obtain ⟨i, hi'⟩ := not_forall.mp hnotall
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi' (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private lemma a_rough3_pairProbability_eq_finset {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (sF : Finset (Fin kF → ℕ)) (sG : Finset (Fin kG → ℕ))
    (hF : ∀ x, x ∉ sF → independentPrimePoolMass loF hiF x = 0)
    (hG : ∀ y, y ∉ sG → independentPrimePoolMass loG hiG y = 0)
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) :
    independentPrimePairProbability loF hiF loG hiG E =
      ∑ x ∈ sF, ∑ y ∈ sG,
        independentPrimePoolMass loF hiF x *
          (independentPrimePoolMass loG hiG y *
            @ite ℝ (E x y) (Classical.propDecidable (E x y)) 1 0) := by
  classical
  unfold independentPrimePairProbability
  rw [tsum_eq_sum (s := sF)]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [tsum_eq_sum (s := sG)]
    · rw [Finset.mul_sum]
    · intro y hy
      rw [hG y hy]
      simp
  · intro x hx
    rw [hF x hx]
    simp

private lemma a_rough3_dyadicTupleSupport_subset {m : ℕ}
    (lo hi a b : Fin m → ℕ)
    (hlo : ∀ i, lo i = 2 ^ (a i)) (hhi : ∀ i, hi i = 2 ^ (b i))
    (j : Fin m → ℕ) (hj : j ∈ a_rough3_scaleSupport a b) :
    a_rough3_tupleSupport (a_rough3_dyadicLower j) (a_rough3_dyadicUpper j) ⊆
      a_rough3_tupleSupport lo hi := by
  intro x hx
  have hjall : ∀ i, j i ∈ Finset.Ico (a i) (b i) := by
    simpa [a_rough3_scaleSupport] using hj
  have hxall : ∀ i, x i ∈
      Finset.Ico (2 ^ (j i)) (2 ^ (j i + 1)) := by
    simpa [a_rough3_tupleSupport, a_rough3_dyadicLower, a_rough3_dyadicUpper] using hx
  have hfull : ∀ i, x i ∈ Finset.Ico (lo i) (hi i) := by
    intro i
    have hji := Finset.mem_Ico.mp (hjall i)
    have hxi := Finset.mem_Ico.mp (hxall i)
    have hlow : lo i ≤ 2 ^ (j i) := by
      simpa [hlo i] using (pow_le_pow_right' (a := 2) (by omega) hji.1)
    have hupp : 2 ^ (j i + 1) ≤ hi i := by
      have hjib : j i + 1 ≤ b i := by omega
      simpa [hhi i] using (pow_le_pow_right' (a := 2) (by omega) hjib)
    exact Finset.mem_Ico.mpr ⟨le_trans hlow hxi.1,
      lt_of_lt_of_le hxi.2 hupp⟩
  simpa [a_rough3_tupleSupport] using hfull

private lemma a_rough3_independentPrimePoolMass_dyadic_mix {m : ℕ}
    (lo hi a b : Fin m → ℕ)
    (hlo : ∀ i, lo i = 2 ^ (a i)) (hhi : ∀ i, hi i = 2 ^ (b i))
    (hmass : ∀ i, 0 < primePoolMass (lo i) (hi i))
    (hbin : ∀ i j, j ∈ Finset.Ico (a i) (b i) →
      0 < primePoolMass (2 ^ j) (2 ^ (j + 1)))
    (x : Fin m → ℕ) :
    independentPrimePoolMass lo hi x =
      ∑ j ∈ Fintype.piFinset (fun i => Finset.Ico (a i) (b i)),
        a_rough3_scaleWeight lo hi a b j *
          independentPrimePoolMass (a_rough3_dyadicLower j) (a_rough3_dyadicUpper j) x := by
  classical
  have hlaw (i : Fin m) :
      primePoolLaw (lo i) (hi i) (x i) =
        ∑ j ∈ Finset.Ico (a i) (b i),
          (primePoolMass (2 ^ j) (2 ^ (j + 1)) /
            primePoolMass (lo i) (hi i)) *
            primePoolLaw (2 ^ j) (2 ^ (j + 1)) (x i) :=
    a_rough3_primePoolLaw_dyadic_mix (hlo i) (hhi i) (hmass i) (hbin i) (x i)
  unfold independentPrimePoolMass
  calc
    (∏ i, primePoolLaw (lo i) (hi i) (x i)) =
        ∏ i, ∑ j ∈ Finset.Ico (a i) (b i),
          (primePoolMass (2 ^ j) (2 ^ (j + 1)) /
            primePoolMass (lo i) (hi i)) *
            primePoolLaw (2 ^ j) (2 ^ (j + 1)) (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hlaw i
    _ = ∑ j ∈ Fintype.piFinset (fun i => Finset.Ico (a i) (b i)),
          ∏ i, (primePoolMass (2 ^ (j i)) (2 ^ (j i + 1)) /
            primePoolMass (lo i) (hi i)) *
            primePoolLaw (2 ^ (j i)) (2 ^ (j i + 1)) (x i) := by
      exact Finset.prod_univ_sum
        (t := fun i => Finset.Ico (a i) (b i))
        (f := fun i j =>
          (primePoolMass (2 ^ j) (2 ^ (j + 1)) / primePoolMass (lo i) (hi i)) *
            primePoolLaw (2 ^ j) (2 ^ (j + 1)) (x i))
    _ = ∑ j ∈ Fintype.piFinset (fun i => Finset.Ico (a i) (b i)),
          a_rough3_scaleWeight lo hi a b j *
            independentPrimePoolMass (a_rough3_dyadicLower j)
              (a_rough3_dyadicUpper j) x := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.prod_mul_distrib]
      rfl

private lemma a_rough3_independentPrimePairProbability_dyadic_mix
    {kF kG : ℕ}
    (loF hiF aF bF : Fin kF → ℕ) (loG hiG aG bG : Fin kG → ℕ)
    (hloF : ∀ i, loF i = 2 ^ (aF i)) (hhiF : ∀ i, hiF i = 2 ^ (bF i))
    (hloG : ∀ i, loG i = 2 ^ (aG i)) (hhiG : ∀ i, hiG i = 2 ^ (bG i))
    (hmassF : ∀ i, 0 < primePoolMass (loF i) (hiF i))
    (hmassG : ∀ i, 0 < primePoolMass (loG i) (hiG i))
    (hbinF : ∀ i j, j ∈ Finset.Ico (aF i) (bF i) →
      0 < primePoolMass (2 ^ j) (2 ^ (j + 1)))
    (hbinG : ∀ i j, j ∈ Finset.Ico (aG i) (bG i) →
      0 < primePoolMass (2 ^ j) (2 ^ (j + 1)))
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) :
    independentPrimePairProbability loF hiF loG hiG E =
      ∑ yF ∈ a_rough3_scaleSupport aF bF,
        ∑ yG ∈ a_rough3_scaleSupport aG bG,
          (a_rough3_scaleWeight loF hiF aF bF yF *
            a_rough3_scaleWeight loG hiG aG bG yG) *
            independentPrimePairProbability
              (a_rough3_dyadicLower yF) (a_rough3_dyadicUpper yF)
              (a_rough3_dyadicLower yG) (a_rough3_dyadicUpper yG) E := by
  classical
  let sF := a_rough3_tupleSupport loF hiF
  let sG := a_rough3_tupleSupport loG hiG
  let tF := a_rough3_scaleSupport aF bF
  let tG := a_rough3_scaleSupport aG bG
  have hmassMixF (x : Fin kF → ℕ) :=
    a_rough3_independentPrimePoolMass_dyadic_mix loF hiF aF bF hloF hhiF
      hmassF hbinF x
  have hmassMixG (y : Fin kG → ℕ) :=
    a_rough3_independentPrimePoolMass_dyadic_mix loG hiG aG bG hloG hhiG
      hmassG hbinG y
  have hfull : independentPrimePairProbability loF hiF loG hiG E =
      ∑ x ∈ sF, ∑ y ∈ sG,
        independentPrimePoolMass loF hiF x *
          (independentPrimePoolMass loG hiG y * if E x y then 1 else 0) := by
    apply a_rough3_pairProbability_eq_finset loF hiF loG hiG sF sG
    · intro x hx
      exact a_rough3_independentPrimePoolMass_zero_outside loF hiF x (by simpa [sF] using hx)
    · intro y hy
      exact a_rough3_independentPrimePoolMass_zero_outside loG hiG y (by simpa [sG] using hy)
  calc
    independentPrimePairProbability loF hiF loG hiG E = _ := hfull
    _ = ∑ x ∈ sF, ∑ y ∈ sG,
          ∑ yF ∈ tF, ∑ yG ∈ tG,
            (a_rough3_scaleWeight loF hiF aF bF yF *
              a_rough3_scaleWeight loG hiG aG bG yG) *
              (independentPrimePoolMass (a_rough3_dyadicLower yF)
                (a_rough3_dyadicUpper yF) x *
                (independentPrimePoolMass (a_rough3_dyadicLower yG)
                  (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      have hsumG :
          (∑ yG ∈ Fintype.piFinset (fun i => Finset.Ico (aG i) (bG i)),
            a_rough3_scaleWeight loG hiG aG bG yG *
              independentPrimePoolMass (a_rough3_dyadicLower yG)
                (a_rough3_dyadicUpper yG) y) *
              (if E x y then 1 else 0) =
            ∑ yG ∈ Fintype.piFinset (fun i => Finset.Ico (aG i) (bG i)),
              (a_rough3_scaleWeight loG hiG aG bG yG *
                independentPrimePoolMass (a_rough3_dyadicLower yG)
                  (a_rough3_dyadicUpper yG) y) * (if E x y then 1 else 0) := by
        rw [Finset.sum_mul]
      rw [hmassMixF x, hmassMixG y, hsumG, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro yF hyF
      apply Finset.sum_congr rfl
      intro yG hyG
      ring
    _ = ∑ yF ∈ tF, ∑ yG ∈ tG, ∑ x ∈ sF, ∑ y ∈ sG,
          (a_rough3_scaleWeight loF hiF aF bF yF *
            a_rough3_scaleWeight loG hiG aG bG yG) *
            (independentPrimePoolMass (a_rough3_dyadicLower yF)
              (a_rough3_dyadicUpper yF) x *
              (independentPrimePoolMass (a_rough3_dyadicLower yG)
                (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0)) := by
      calc
        _ = ∑ x ∈ sF, ∑ yF ∈ tF, ∑ y ∈ sG, ∑ yG ∈ tG,
              (a_rough3_scaleWeight loF hiF aF bF yF *
                a_rough3_scaleWeight loG hiG aG bG yG) *
                (independentPrimePoolMass (a_rough3_dyadicLower yF)
                  (a_rough3_dyadicUpper yF) x *
                  (independentPrimePoolMass (a_rough3_dyadicLower yG)
                    (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_comm]
        _ = ∑ yF ∈ tF, ∑ x ∈ sF, ∑ y ∈ sG, ∑ yG ∈ tG,
              (a_rough3_scaleWeight loF hiF aF bF yF *
                a_rough3_scaleWeight loG hiG aG bG yG) *
                (independentPrimePoolMass (a_rough3_dyadicLower yF)
                  (a_rough3_dyadicUpper yF) x *
                  (independentPrimePoolMass (a_rough3_dyadicLower yG)
                    (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0)) := by
              rw [Finset.sum_comm]
        _ = ∑ yF ∈ tF, ∑ x ∈ sF, ∑ yG ∈ tG, ∑ y ∈ sG,
              (a_rough3_scaleWeight loF hiF aF bF yF *
                a_rough3_scaleWeight loG hiG aG bG yG) *
                (independentPrimePoolMass (a_rough3_dyadicLower yF)
                  (a_rough3_dyadicUpper yF) x *
                  (independentPrimePoolMass (a_rough3_dyadicLower yG)
                    (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro yF hyF
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_comm]
        _ = ∑ yF ∈ tF, ∑ yG ∈ tG, ∑ x ∈ sF, ∑ y ∈ sG,
              (a_rough3_scaleWeight loF hiF aF bF yF *
                a_rough3_scaleWeight loG hiG aG bG yG) *
                (independentPrimePoolMass (a_rough3_dyadicLower yF)
                  (a_rough3_dyadicUpper yF) x *
                  (independentPrimePoolMass (a_rough3_dyadicLower yG)
                    (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro yF hyF
              rw [Finset.sum_comm]
    _ = ∑ yF ∈ tF, ∑ yG ∈ tG,
          (a_rough3_scaleWeight loF hiF aF bF yF *
            a_rough3_scaleWeight loG hiG aG bG yG) *
            independentPrimePairProbability
              (a_rough3_dyadicLower yF) (a_rough3_dyadicUpper yF)
              (a_rough3_dyadicLower yG) (a_rough3_dyadicUpper yG) E := by
      apply Finset.sum_congr rfl
      intro yF hyF
      apply Finset.sum_congr rfl
      intro yG hyG
      have hsubF := a_rough3_dyadicTupleSupport_subset loF hiF aF bF hloF hhiF yF
        (by simpa [tF] using hyF)
      have hsubG := a_rough3_dyadicTupleSupport_subset loG hiG aG bG hloG hhiG yG
        (by simpa [tG] using hyG)
      have hfinite := a_rough3_pairProbability_eq_finset
        (a_rough3_dyadicLower yF) (a_rough3_dyadicUpper yF)
        (a_rough3_dyadicLower yG) (a_rough3_dyadicUpper yG) sF sG
        (fun x hx => a_rough3_independentPrimePoolMass_zero_outside
          (a_rough3_dyadicLower yF) (a_rough3_dyadicUpper yF) x
          (by intro hx'; exact hx (hsubF hx')))
        (fun y hy => a_rough3_independentPrimePoolMass_zero_outside
          (a_rough3_dyadicLower yG) (a_rough3_dyadicUpper yG) y
          (by intro hy'; exact hy (hsubG hy')))
        E
      rw [hfinite]
      calc
          (∑ x ∈ sF, ∑ y ∈ sG,
              (a_rough3_scaleWeight loF hiF aF bF yF *
                a_rough3_scaleWeight loG hiG aG bG yG) *
                (independentPrimePoolMass (a_rough3_dyadicLower yF)
                  (a_rough3_dyadicUpper yF) x *
                  (independentPrimePoolMass (a_rough3_dyadicLower yG)
                    (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0))) =
              (a_rough3_scaleWeight loF hiF aF bF yF *
                a_rough3_scaleWeight loG hiG aG bG yG) *
                ∑ x ∈ sF, ∑ y ∈ sG,
                  independentPrimePoolMass (a_rough3_dyadicLower yF)
                    (a_rough3_dyadicUpper yF) x *
                    (independentPrimePoolMass (a_rough3_dyadicLower yG)
                      (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0) := by
            calc
              _ = ∑ x ∈ sF,
                    (a_rough3_scaleWeight loF hiF aF bF yF *
                      a_rough3_scaleWeight loG hiG aG bG yG) *
                      ∑ y ∈ sG,
                        independentPrimePoolMass (a_rough3_dyadicLower yF)
                          (a_rough3_dyadicUpper yF) x *
                          (independentPrimePoolMass (a_rough3_dyadicLower yG)
                            (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [Finset.mul_sum]
              _ = (a_rough3_scaleWeight loF hiF aF bF yF *
                    a_rough3_scaleWeight loG hiG aG bG yG) *
                    ∑ x ∈ sF, ∑ y ∈ sG,
                      independentPrimePoolMass (a_rough3_dyadicLower yF)
                        (a_rough3_dyadicUpper yF) x *
                        (independentPrimePoolMass (a_rough3_dyadicLower yG)
                          (a_rough3_dyadicUpper yG) y * if E x y then 1 else 0) := by
                  rw [Finset.mul_sum]

private lemma a_rough3_scaleWeight_sum_one {m : ℕ}
    (lo hi a b : Fin m → ℕ)
    (hlo : ∀ i, lo i = 2 ^ (a i)) (hhi : ∀ i, hi i = 2 ^ (b i))
    (hmass : ∀ i, 0 < primePoolMass (lo i) (hi i)) :
    ∑ j ∈ a_rough3_scaleSupport a b, a_rough3_scaleWeight lo hi a b j = 1 := by
  classical
  have hcoord (i : Fin m) :
      ∑ j ∈ Finset.Ico (a i) (b i),
        primePoolMass (2 ^ j) (2 ^ (j + 1)) / primePoolMass (lo i) (hi i) = 1 := by
    calc
      _ = (∑ j ∈ Finset.Ico (a i) (b i),
            primePoolMass (2 ^ j) (2 ^ (j + 1))) / primePoolMass (lo i) (hi i) := by
          rw [Finset.sum_div]
      _ = primePoolMass (lo i) (hi i) / primePoolMass (lo i) (hi i) := by
          rw [← a_rough3_primePoolMass_dyadic_sum (hlo i) (hhi i)]
      _ = 1 := div_self (ne_of_gt (hmass i))
  calc
    _ = ∏ i, ∑ j ∈ Finset.Ico (a i) (b i),
          primePoolMass (2 ^ j) (2 ^ (j + 1)) / primePoolMass (lo i) (hi i) := by
      simpa [a_rough3_scaleSupport, a_rough3_scaleWeight] using
        (Finset.prod_univ_sum
          (t := fun i : Fin m => Finset.Ico (a i) (b i))
          (f := fun i j =>
            primePoolMass (2 ^ j) (2 ^ (j + 1)) / primePoolMass (lo i) (hi i))).symm
    _ = 1 := by simp [hcoord]

private lemma a_rough3_scaleWeight_nonneg {m : ℕ}
    (lo hi a b : Fin m → ℕ)
    (hmass : ∀ i, 0 < primePoolMass (lo i) (hi i))
    (j : Fin m → ℕ) : 0 ≤ a_rough3_scaleWeight lo hi a b j := by
  unfold a_rough3_scaleWeight
  apply Finset.prod_nonneg
  intro i hi'
  exact div_nonneg (a_rough3_primePoolMass_nonneg _ _) (hmass i).le

private lemma a_rough3_sum_weight_products_mul {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β)
    (f : α → ℝ) (g : β → ℝ) (B : ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, (f x * g y) * B) =
      (∑ x ∈ s, f x) * (∑ y ∈ t, g y) * B := by
  calc
    _ = ∑ x ∈ s, f x * ((∑ y ∈ t, g y) * B) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        _ = (∑ y ∈ t, f x * g y) * B := by rw [Finset.sum_mul]
        _ = (f x * (∑ y ∈ t, g y)) * B := by rw [Finset.mul_sum]
        _ = _ := by ring
    _ = (∑ x ∈ s, f x) * ((∑ y ∈ t, g y) * B) := by
      exact (Finset.sum_mul s f ((∑ y ∈ t, g y) * B)).symm
    _ = _ := by ring

lemma a_rough3_independentPrimePairProbability_dyadic_bound
    {kF kG : ℕ}
    (loF hiF aF bF : Fin kF → ℕ) (loG hiG aG bG : Fin kG → ℕ)
    (hloF : ∀ i, loF i = 2 ^ (aF i)) (hhiF : ∀ i, hiF i = 2 ^ (bF i))
    (hloG : ∀ i, loG i = 2 ^ (aG i)) (hhiG : ∀ i, hiG i = 2 ^ (bG i))
    (hmassF : ∀ i, 0 < primePoolMass (loF i) (hiF i))
    (hmassG : ∀ i, 0 < primePoolMass (loG i) (hiG i))
    (hbinF : ∀ i j, j ∈ Finset.Ico (aF i) (bF i) →
      0 < primePoolMass (2 ^ j) (2 ^ (j + 1)))
    (hbinG : ∀ i j, j ∈ Finset.Ico (aG i) (bG i) →
      0 < primePoolMass (2 ^ j) (2 ^ (j + 1)))
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) (B : ℝ)
    (hB : 0 ≤ B)
    (hdyad : ∀ yF ∈ a_rough3_scaleSupport aF bF,
      ∀ yG ∈ a_rough3_scaleSupport aG bG,
        independentPrimePairProbability
          (a_rough3_dyadicLower yF) (a_rough3_dyadicUpper yF)
          (a_rough3_dyadicLower yG) (a_rough3_dyadicUpper yG) E ≤ B) :
    independentPrimePairProbability loF hiF loG hiG E ≤ B := by
  classical
  rw [a_rough3_independentPrimePairProbability_dyadic_mix
    loF hiF aF bF loG hiG aG bG hloF hhiF hloG hhiG
    hmassF hmassG hbinF hbinG E]
  calc
    _ ≤ ∑ yF ∈ a_rough3_scaleSupport aF bF,
          ∑ yG ∈ a_rough3_scaleSupport aG bG,
            (a_rough3_scaleWeight loF hiF aF bF yF *
              a_rough3_scaleWeight loG hiG aG bG yG) * B := by
      apply Finset.sum_le_sum
      intro yF hyF
      apply Finset.sum_le_sum
      intro yG hyG
      have hwF := a_rough3_scaleWeight_nonneg loF hiF aF bF hmassF yF
      have hwG := a_rough3_scaleWeight_nonneg loG hiG aG bG hmassG yG
      exact mul_le_mul_of_nonneg_left (hdyad yF hyF yG hyG)
        (mul_nonneg hwF hwG)
    _ = (∑ yF ∈ a_rough3_scaleSupport aF bF,
          a_rough3_scaleWeight loF hiF aF bF yF) *
        (∑ yG ∈ a_rough3_scaleSupport aG bG,
          a_rough3_scaleWeight loG hiG aG bG yG) * B := by
      exact a_rough3_sum_weight_products_mul
        (a_rough3_scaleSupport aF bF) (a_rough3_scaleSupport aG bG)
        (a_rough3_scaleWeight loF hiF aF bF)
        (a_rough3_scaleWeight loG hiG aG bG) B
    _ = B := by
      rw [a_rough3_scaleWeight_sum_one loF hiF aF bF hloF hhiF hmassF,
        a_rough3_scaleWeight_sum_one loG hiG aG bG hloG hhiG hmassG]
      ring

def a_rough3_endpointSet {kF kG : ℕ}
    (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) : Finset ℕ :=
  Finset.univ.image YF ∪ Finset.univ.image YG

noncomputable def a_rough3_endpointMinimum {kF kG : ℕ}
    (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) : ℕ :=
  if h : (a_rough3_endpointSet YF YG).Nonempty then
    (a_rough3_endpointSet YF YG).min' h
  else 1

lemma a_rough3_endpointMinimum_mono {kF kG : ℕ}
    (XF YF : Fin kF → ℕ) (XG YG : Fin kG → ℕ)
    (hF : ∀ i, XF i ≤ YF i) (hG : ∀ j, XG j ≤ YG j)
    (hX : (a_rough3_endpointSet XF XG).Nonempty)
    (hY : (a_rough3_endpointSet YF YG).Nonempty) :
    a_rough3_endpointMinimum XF XG ≤ a_rough3_endpointMinimum YF YG := by
  classical
  unfold a_rough3_endpointMinimum
  rw [dif_pos hX, dif_pos hY, Finset.le_min'_iff]
  intro z hz
  rcases Finset.mem_union.mp hz with hzF | hzG
  · rcases Finset.mem_image.mp hzF with ⟨i, -, rfl⟩
    calc
      (a_rough3_endpointSet XF XG).min' hX ≤ XF i :=
        Finset.min'_le _ _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      _ ≤ YF i := hF i
  · rcases Finset.mem_image.mp hzG with ⟨j, -, rfl⟩
    calc
      (a_rough3_endpointSet XF XG).min' hX ≤ XG j :=
        Finset.min'_le _ _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
      _ ≤ YG j := hG j

lemma a_rough3_endpointMinimum_tendsto {kF kG : ℕ}
    (XF : ℕ → Fin kF → ℕ) (XG : ℕ → Fin kG → ℕ)
    (hF : ∀ i, Tendsto (fun N => XF N i) atTop atTop)
    (hG : ∀ j, Tendsto (fun N => XG N j) atTop atTop)
    (hdim : Nonempty (Fin kF) ∨ Nonempty (Fin kG)) :
    Tendsto (fun N => a_rough3_endpointMinimum (XF N) (XG N)) atTop atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro b
  have hevF : ∀ᶠ N in atTop, ∀ i, b ≤ XF N i := by
    rw [Filter.eventually_all]
    intro i
    exact (hF i).eventually_ge_atTop b
  have hevG : ∀ᶠ N in atTop, ∀ j, b ≤ XG N j := by
    rw [Filter.eventually_all]
    intro j
    exact (hG j).eventually_ge_atTop b
  have hne (N : ℕ) : (a_rough3_endpointSet (XF N) (XG N)).Nonempty := by
    rcases hdim with hFdim | hGdim
    · obtain ⟨i⟩ := hFdim
      refine ⟨XF N i, ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · obtain ⟨j⟩ := hGdim
      refine ⟨XG N j, ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  filter_upwards [hevF, hevG] with N hNF hNG
  unfold a_rough3_endpointMinimum
  rw [dif_pos (hne N), Finset.le_min'_iff]
  intro z hz
  rcases Finset.mem_union.mp hz with hzF | hzG
  · rcases Finset.mem_image.mp hzF with ⟨i, -, rfl⟩
    exact hNF i
  · rcases Finset.mem_image.mp hzG with ⟨j, -, rfl⟩
    exact hNG j

end
end HindmanSumsProducts
