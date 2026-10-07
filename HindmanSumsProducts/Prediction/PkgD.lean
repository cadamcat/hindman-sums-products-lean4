import HindmanSumsProducts.Prediction.Outside
import OAI.Combinatorics.SumProduct.Alignment.RawHarmonic01

/-! Helper lemmas for §5 (part S5-D). -/

namespace HindmanSumsProducts

namespace Prediction

open OAI.DyadicHarmonicBoundary
open Filter
open scoped Topology

-- The arithmetic boundary estimate we will apply after dilating the pivot law by a tail product.
theorem raw_boundary_bound (X W t H R : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X)
    (ht : 0 < t) (hH : 0 < H) (hR : R ≤ X) :
    badMass X (X ^ 2) W t H R / mass X (X ^ 2) W ≤
      168 * (t : ℝ) * (R + W + 1) / H + 112 * ((R : ℝ) + W + 1) / X :=
  raw_bad_bound X W t H R hW hX ht hH hR

/-- Moving a root by at most `width` leaves its `R`-interval unchanged away from both ends. -/
theorem ediv_stable_of_interior (R width : ℕ) (hR : 0 < R) (y z : ℤ)
    (hz : |z| ≤ width) (hlo : (width : ℤ) < y % (R : ℤ))
    (hhi : y % (R : ℤ) + (width : ℤ) < R) :
    (y + z) / (R : ℤ) = y / (R : ℤ) := by
  have hRz : (R : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  let q : ℤ := y / (R : ℤ)
  let r : ℤ := y % (R : ℤ)
  have hdecomp : r + (R : ℤ) * q = y := by
    dsimp [q, r]
    simpa [mul_comm] using Int.emod_add_mul_ediv y (R : ℤ)
  have hzlo : -(width : ℤ) ≤ z := (abs_le.mp hz).1
  have hzhi : z ≤ (width : ℤ) := (abs_le.mp hz).2
  have hrlo : 0 ≤ r + z := by dsimp [r]; omega
  have hrhi : r + z < (R : ℤ) := by dsimp [r]; omega
  have hdecomp' : (r + z) + (R : ℤ) * q = y + z := by rw [← hdecomp]; ring
  have hRpos : (0 : ℤ) < (R : ℤ) := by exact_mod_cast hR
  have hRabs : |(R : ℤ)| = (R : ℤ) := abs_of_pos hRpos
  have h := (Int.ediv_emod_unique'' hRz).2 ⟨hdecomp', hrlo, by rw [hRabs]; exact hrhi⟩
  dsimp [q] at h
  exact h.1

/-- Adding a multiple of `M` preserves the residue and advances the progression index. -/
theorem residue_and_progression_shift (M : ℕ) (hM : 0 < M) (y e : ℤ) :
    (y + (M : ℤ) * e) % (M : ℤ) = y % (M : ℤ) ∧
      ((y + (M : ℤ) * e) - (y + (M : ℤ) * e) % (M : ℤ)) / (M : ℤ) =
        (y - y % (M : ℤ)) / (M : ℤ) + e := by
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  constructor
  · simp [Int.add_emod, Int.mul_emod]
  · have hmod : (y + (M : ℤ) * e) % (M : ℤ) = y % (M : ℤ) := by
      simp [Int.add_emod, Int.mul_emod]
    rw [hmod]
    have hnum : y + (M : ℤ) * e - y % (M : ℤ) =
        (y - y % (M : ℤ)) + (M : ℤ) * e := by ring
    rw [hnum, Int.add_mul_ediv_left _ e hMz]

/-- A boundary strip for `σ p` is contained in the raw bad set with a slightly larger
integer radius. The strict `+1` handles roots exactly at the lower edge of a strip. -/
theorem strip_mul_subset_rawBad (H width σ p R : ℕ) (hH : 0 < H)
    (hσ : 0 < σ) (hp : R ≤ p) (hwidth : width < σ * R)
    (hstrip : (σ * p) % H ≤ width ∨ H ≤ (σ * p) % H + width) :
    σ * (p - R) / H ≠ σ * (p + R) / H := by
  intro hbad
  let a := σ * (p - R)
  let b := σ * (p + R)
  let y := σ * p
  let g := σ * R
  have ha : a + g = y := by
    dsimp [a, g, y]
    rw [Nat.mul_sub_left_distrib, Nat.sub_add_cancel (Nat.mul_le_mul_left σ hp)]
  have hb : y + g = b := by
    dsimp [b, g, y]
    rw [Nat.mul_add]
  have haq : a / H = b / H := by simpa [a, b] using hbad
  let q := a / H
  have haq' : a / H = q := rfl
  have hbq : b / H = q := by simpa [q] using haq.symm
  have hlo : q * H ≤ a := by simpa [q] using Nat.div_mul_le_self a H
  have hhi : b ≤ q * H + H - 1 := by
    have h := (Nat.div_eq_iff hH).mp hbq
    omega
  have hylo : q * H ≤ y := by omega
  have hyhi : y ≤ q * H + H - 1 := by omega
  have hyq : y / H = q := (Nat.div_eq_iff hH).mpr ⟨hylo, hyhi⟩
  have hdivmod : H * (y / H) + y % H = y := Nat.div_add_mod y H
  rw [hyq] at hdivmod
  have hdivmod' : q * H + y % H = y := by simpa [Nat.mul_comm] using hdivmod
  have hmod : y % H = y - q * H := by omega
  have hgap : g ≤ y % H := by rw [hmod]; omega
  have hupper : y % H + g < H := by rw [hmod]; omega
  have hnotlow : ¬ y % H ≤ width := by omega
  have hnothigh : ¬ H ≤ y % H + width := by omega
  exact hstrip.elim hnotlow hnothigh

def harmonicNatSupport (X W : ℕ) : Finset ℕ :=
  (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)

theorem harmonicNatLaw_zero_of_not_mem (X W n : ℕ)
    (hn : n ∉ harmonicNatSupport X W) : harmonicNatLaw X W n = 0 := by
  have hnot : ¬ (X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W) := by
    intro h
    apply hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
  simp [harmonicNatLaw, hnot]

theorem harmonicNormalizer_pos (X W : ℕ) (hW : 0 < W) (hX : 4 * W ≤ X) :
    0 < harmonicNormalizer X W := by
  have h := OAI.RawHarmonicProbability.mass_pos X W hW hX
  simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
    Finset.sum_filter, one_div, Nat.coprime_comm] using h

theorem harmonicNatLaw_tsum_one (X W : ℕ) (hX : 0 < X)
    (hNorm : 0 < harmonicNormalizer X W) :
    ∑' n : ℕ, harmonicNatLaw X W n = 1 := by
  let S := harmonicNatSupport X W
  have hzero : ∀ n ∉ S, harmonicNatLaw X W n = 0 := by
    intro n hn
    exact harmonicNatLaw_zero_of_not_mem X W n (by simpa [S] using hn)
  rw [tsum_eq_sum (s := S) hzero]
  calc
    (∑ n ∈ S, harmonicNatLaw X W n) =
        ∑ n ∈ S, (1 / (n : ℝ)) / harmonicNormalizer X W := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnrange : X ≤ n ∧ n < X ^ 2 := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le hX hnrange.1
      have hnvalid : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W :=
        ⟨hnrange.1, hnrange.2, (Finset.mem_filter.mp hn).2⟩
      rw [harmonicNatLaw, if_pos hnvalid]
      field_simp [ne_of_gt hnpos, ne_of_gt hNorm]
    _ = (∑ n ∈ S, 1 / (n : ℝ)) / harmonicNormalizer X W := by rw [Finset.sum_div]
    _ = 1 := by
      rw [show (∑ n ∈ S, 1 / (n : ℝ)) = harmonicNormalizer X W by
        simp [harmonicNormalizer, S, harmonicNatSupport]]
      exact div_self (ne_of_gt hNorm)

theorem harmonicNatTupleLaw_tsum_one {k : ℕ} (W : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hNorm : ∀ i, 0 < harmonicNormalizer (X i) W) :
    ∑' t : Fin k → ℕ, ∏ i, harmonicNatLaw (X i) W (t i) = 1 := by
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  have hzero (t : Fin k → ℕ) (ht : t ∉ T) :
      ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 :=
      harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  rw [tsum_eq_sum (s := T) hzero]
  have hsum (i : Fin k) :
      ∑ n ∈ S i, harmonicNatLaw (X i) W n = 1 := by
    have htotal := harmonicNatLaw_tsum_one (X i) W (hX i) (hNorm i)
    rw [tsum_eq_sum (s := S i) (fun n hn =>
      harmonicNatLaw_zero_of_not_mem (X i) W n (by simpa [S] using hn))] at htotal
    exact htotal
  calc
    (∑ t ∈ T, ∏ i, harmonicNatLaw (X i) W (t i)) =
        ∏ i, ∑ n ∈ S i, harmonicNatLaw (X i) W n := by
      simpa [T] using (Finset.prod_univ_sum S
        (fun i n => harmonicNatLaw (X i) W n)).symm
    _ = 1 := by simp [hsum]

theorem parameterTailProductLaw_tsum_one {n : ℕ} (A : Parameters n)
    (N : ℕ) (Tails : Finset (Fin n)) (hX : ∀ i, 0 < A.X N i)
    (hNorm : ∀ i, 0 < harmonicNormalizer (A.X N i) (primorial (N + 1))) :
    ∑' σ : ℕ, parameterTailProductLaw A N Tails σ = 1 := by
  let S : Fin n → Finset ℕ := fun i => harmonicNatSupport (A.X N i) (primorial (N + 1))
  let Tuples : Finset (Fin n → ℕ) := Fintype.piFinset S
  let prodTail : (Fin n → ℕ) → ℕ := fun t => ∏ j ∈ Tails, t j
  let weight : (Fin n → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (A.X N i)
    (primorial (N + 1)) (t i)
  have hweight_zero (t : Fin n → ℕ) (ht : t ∉ Tuples) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (A.X N i) (primorial (N + 1)) (t i) = 0 :=
      harmonicNatLaw_zero_of_not_mem (A.X N i) (primorial (N + 1)) (t i)
        (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hterm_zero_out (σ : ℕ) (t : Fin n → ℕ) (ht : t ∉ Tuples) :
      (if prodTail t = σ then 1 else 0) * weight t = 0 := by
    simp [hweight_zero t ht]
  have hLawZero (σ : ℕ) (hσ : σ ∉ Tuples.image prodTail) :
      parameterTailProductLaw A N Tails σ = 0 := by
    unfold parameterTailProductLaw
    rw [tsum_eq_sum (s := Tuples) (hterm_zero_out σ)]
    apply Finset.sum_eq_zero
    intro t ht
    have hp : prodTail t ≠ σ := by
      intro heq
      apply hσ
      exact Finset.mem_image.mpr ⟨t, ht, heq⟩
    simp [hp]
  have hLawEq (σ : ℕ) : parameterTailProductLaw A N Tails σ =
      ∑ t ∈ Tuples, (if prodTail t = σ then 1 else 0) * weight t := by
    unfold parameterTailProductLaw
    rw [tsum_eq_sum (s := Tuples) (hterm_zero_out σ)]
  have htuple : ∑ t ∈ Tuples, weight t = 1 := by
    have h := harmonicNatTupleLaw_tsum_one (primorial (N + 1)) (A.X N) hX hNorm
    have hzero : ∀ t ∉ Tuples, weight t = 0 := hweight_zero
    simpa [weight, Tuples] using (tsum_eq_sum (s := Tuples) hzero).symm.trans h
  rw [tsum_eq_sum (s := Tuples.image prodTail) hLawZero]
  calc
    (∑ σ ∈ Tuples.image prodTail, parameterTailProductLaw A N Tails σ) =
        ∑ σ ∈ Tuples.image prodTail,
          ∑ t ∈ Tuples, (if prodTail t = σ then 1 else 0) * weight t := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact hLawEq σ
    _ = ∑ t ∈ Tuples, weight t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      have hin : prodTail t ∈ Tuples.image prodTail :=
        Finset.mem_image.mpr ⟨t, ht, rfl⟩
      simp [Finset.sum_ite_eq', hin]
    _ = 1 := htuple

theorem parameterTailProductLaw_support {n : ℕ} (A : Parameters n)
    (N : ℕ) (Tails : Finset (Fin n)) (σ : ℕ)
    (hMass : parameterTailProductLaw A N Tails σ ≠ 0) :
    ∃ t : Fin n → ℕ,
      (∀ i, t i ∈ harmonicNatSupport (A.X N i) (primorial (N + 1))) ∧
      (∏ j ∈ Tails, t j) = σ := by
  let S : Fin n → Finset ℕ := fun i => harmonicNatSupport (A.X N i) (primorial (N + 1))
  let Tuples : Finset (Fin n → ℕ) := Fintype.piFinset S
  let prodTail : (Fin n → ℕ) → ℕ := fun t => ∏ j ∈ Tails, t j
  let weight : (Fin n → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (A.X N i)
    (primorial (N + 1)) (t i)
  have hweight_zero (t : Fin n → ℕ) (ht : t ∉ Tuples) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (A.X N i) (primorial (N + 1)) (t i) = 0 :=
      harmonicNatLaw_zero_of_not_mem (A.X N i) (primorial (N + 1)) (t i)
        (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hterm_zero_out (t : Fin n → ℕ) (ht : t ∉ Tuples) :
      (if prodTail t = σ then 1 else 0) * weight t = 0 := by
    simp [hweight_zero t ht]
  have hLawZero (hσ : σ ∉ Tuples.image prodTail) :
      parameterTailProductLaw A N Tails σ = 0 := by
    unfold parameterTailProductLaw
    rw [tsum_eq_sum (s := Tuples) (fun t ht => hterm_zero_out t ht)]
    apply Finset.sum_eq_zero
    intro t ht
    have hp : prodTail t ≠ σ := by
      intro heq
      apply hσ
      exact Finset.mem_image.mpr ⟨t, ht, heq⟩
    simp [hp]
  have himage : σ ∈ Tuples.image prodTail := by
    by_contra hnot
    exact hMass (hLawZero hnot)
  obtain ⟨t, ht, hprod⟩ := Finset.mem_image.mp himage
  refine ⟨t, ?_, hprod⟩
  intro i
  exact (Fintype.mem_piFinset.mp (by simpa [Tuples] using ht) i)

theorem parameterTailProductLaw_support_properties {n : ℕ} (A : Parameters n)
    (N : ℕ) (Tails : Finset (Fin n)) (σ : ℕ)
    (hMass : parameterTailProductLaw A N Tails σ ≠ 0)
    (hX : ∀ i, 0 < A.X N i) :
    0 < σ ∧ Nat.Coprime σ (primorial (N + 1)) ∧
      σ ≤ ∏ j ∈ Tails, (A.X N j) ^ 2 := by
  obtain ⟨t, ht, hprod⟩ := parameterTailProductLaw_support A N Tails σ hMass
  have htlo (j : Fin n) (hj : j ∈ Tails) : A.X N j ≤ t j := by
    have hs := Finset.mem_filter.mp (ht j)
    exact (Finset.mem_Ico.mp hs.1).1
  have hthi (j : Fin n) (hj : j ∈ Tails) : t j < (A.X N j) ^ 2 := by
    have hs := Finset.mem_filter.mp (ht j)
    exact (Finset.mem_Ico.mp hs.1).2
  have hpositive : 0 < ∏ j ∈ Tails, t j := by
    apply Finset.prod_pos
    intro j hj
    exact Nat.zero_lt_of_lt (lt_of_lt_of_le (hX j) (htlo j hj))
  have hcop : Nat.Coprime (∏ j ∈ Tails, t j) (primorial (N + 1)) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro j hj
    exact (Finset.mem_filter.mp (ht j)).2
  have hprod_le : (∏ j ∈ Tails, t j) ≤ ∏ j ∈ Tails, (A.X N j) ^ 2 := by
    apply Finset.prod_le_prod
    · intro j hj
      exact (hthi j hj).le
  exact ⟨by simpa [hprod] using hpositive, by simpa [hprod] using hcop,
    by simpa [hprod] using hprod_le⟩

theorem tailProductLaw_cutoff_bound {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (l : Fin K) (hl : ValidGap B l) (N σ : ℕ)
    (hMass : parameterTailProductLaw MS.core.parameters N B.2.val σ ≠ 0) :
    0 < σ ∧ Nat.Coprime σ (primorial (N + 1)) ∧
      σ ≤ masterScaleV MS.core.parameters N l := by
  let A := MS.core.parameters
  let J : Finset (Fin K) := Finset.univ.filter (fun j => j < l)
  have hprop := parameterTailProductLaw_support_properties A N B.2.val σ hMass
    (fun j => A.Xpos N j)
  have hsub : B.2.val ⊆ J := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl.1 j hj⟩
  have hXone (j : Fin K) : 1 ≤ A.X N j :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (A.Xpos N j))
  have hprodle : (∏ j ∈ B.2.val, (A.X N j) ^ 2) ≤
      ∏ j ∈ J, (A.X N j) ^ 2 := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun j _ => Nat.zero_le _)
    intro j hj hjnot
    exact Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero 2 (Nat.ne_of_gt (A.Xpos N j)))
  have hfull : (∏ j ∈ J, (A.X N j) ^ 2) =
      (∏ j ∈ J, A.X N j) ^ 2 := by
    dsimp [J]
    rw [← Finset.prod_pow]
  have hprodV : (∏ j ∈ J, A.X N j) ^ 2 ≤ masterScaleV A N l := by
    rw [← hfull]
    dsimp [J, masterScaleV]
    omega
  refine ⟨hprop.1, hprop.2.1, ?_⟩
  calc
    σ ≤ ∏ j ∈ B.2.val, (A.X N j) ^ 2 := hprop.2.2
    _ ≤ ∏ j ∈ J, (A.X N j) ^ 2 := hprodle
    _ = (∏ j ∈ J, A.X N j) ^ 2 := hfull
    _ ≤ masterScaleV A N l := hprodV

def harmonicIntSupport (X W : ℕ) : Finset ℤ :=
  (harmonicNatSupport X W).image (fun n : ℕ => (n : ℤ))

theorem pkgD_harmonicLaw_zero_of_not_mem (X W : ℕ) (y : ℤ)
    (hy : y ∉ harmonicIntSupport X W) : harmonicLaw X W y = 0 := by
  by_cases h : 0 ≤ y ∧ X ≤ y.toNat ∧ y.toNat < X ^ 2 ∧ Nat.Coprime y.toNat W
  · have hyNat : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg h.1
    have hyMem : y ∈ harmonicIntSupport X W := by
      rw [← hyNat]
      exact Finset.mem_image.mpr ⟨y.toNat,
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩, rfl⟩
    exact (hy hyMem).elim
  · simp [harmonicLaw, h]

theorem harmonicLaw_nat_eq (X W n : ℕ)
    (hn : n ∈ harmonicNatSupport X W) :
    harmonicLaw X W (n : ℤ) = harmonicNatLaw X W n := by
  have hn' := Finset.mem_filter.mp hn
  have hIco := Finset.mem_Ico.mp hn'.1
  simp [harmonicLaw, harmonicNatLaw, hIco.1, hIco.2, hn'.2]

theorem Emu_eq_harmonicNat_sum {n : ℕ} (A : Parameters n) (N : ℕ)
    (i : Fin n) (f : ℤ → ℝ) :
    Emu A N i f =
      ∑ y ∈ harmonicNatSupport (A.X N i) (primorial (N + 1)),
        harmonicNatLaw (A.X N i) (primorial (N + 1)) y * f (y : ℤ) := by
  let S := harmonicNatSupport (A.X N i) (primorial (N + 1))
  let T := harmonicIntSupport (A.X N i) (primorial (N + 1))
  unfold Emu
  change (∑' y : ℤ, harmonicLaw (A.X N i) (primorial (N + 1)) y * f y) = _
  rw [tsum_eq_sum (s := T) (fun y hy => by
    rw [pkgD_harmonicLaw_zero_of_not_mem _ _ y (by simpa [T] using hy)]
    simp)]
  change (∑ y ∈ S.image (fun y : ℕ => (y : ℤ)),
    harmonicLaw (A.X N i) (primorial (N + 1)) y * f y) = _
  calc
    _ = ∑ y ∈ S, harmonicLaw (A.X N i) (primorial (N + 1)) (y : ℤ) * f (y : ℤ) :=
      (Finset.sum_image (s := S)
        (f := fun y : ℤ => harmonicLaw (A.X N i) (primorial (N + 1)) y * f y)
        (g := fun y : ℕ => (y : ℤ))
        (by intro y hy z hz heq; exact Int.ofNat.inj heq))
    _ = ∑ y ∈ S, harmonicNatLaw (A.X N i) (primorial (N + 1)) y * f (y : ℤ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [harmonicLaw_nat_eq _ _ y hy]

theorem finite_pairing_l1_bound (S : Finset ℤ) (μ ν f : ℤ → ℝ)
    (hμ : ∀ y ∉ S, μ y = 0) (hν : ∀ y ∉ S, ν y = 0)
    (hf : ∀ y, |f y| ≤ 1) :
    |(∑' y, μ y * f y) - (∑' y, ν y * f y)| ≤ arithmeticL1 μ ν := by
  have hμsum : ∑' y, μ y * f y = ∑ y ∈ S, μ y * f y :=
    tsum_eq_sum (s := S) (fun y hy => by simp [hμ y hy])
  have hνsum : ∑' y, ν y * f y = ∑ y ∈ S, ν y * f y :=
    tsum_eq_sum (s := S) (fun y hy => by simp [hν y hy])
  have hL1 : arithmeticL1 μ ν = ∑ y ∈ S, |μ y - ν y| := by
    unfold arithmeticL1
    exact tsum_eq_sum (s := S) (fun y hy => by simp [hμ y hy, hν y hy])
  rw [hμsum, hνsum, hL1]
  calc
    |(∑ y ∈ S, μ y * f y) - ∑ y ∈ S, ν y * f y| =
        |∑ y ∈ S, (μ y - ν y) * f y| := by
      apply congrArg abs
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ ≤ ∑ y ∈ S, |(μ y - ν y) * f y| := by
      simpa [Real.norm_eq_abs] using (norm_sum_le S (fun y : ℤ => (μ y - ν y) * f y))
    _ ≤ ∑ y ∈ S, |μ y - ν y| := Finset.sum_le_sum fun y hy => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hf y)

theorem dilatedLaw_pairing (μ : ℤ → ℝ) (σ : ℕ) (hσ : 0 < σ)
    (S : Finset ℤ) (hμ : ∀ y ∉ S, μ y = 0) (f : ℤ → ℝ) :
    (∑' y, dilatedLaw μ σ y * f y) =
      ∑' z, μ z * f ((σ : ℤ) * z) := by
  let e : ℤ → ℤ := fun z => (σ : ℤ) * z
  let T := S.image e
  have hσz : (σ : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hσ)
  have hzero (y : ℤ) (hy : y ∉ T) : dilatedLaw μ σ y * f y = 0 := by
    by_cases hm : y % (σ : ℤ) = 0
    · have hdvd : (σ : ℤ) ∣ y := Int.dvd_of_emod_eq_zero hm
      let z := y / (σ : ℤ)
      have hmul : (σ : ℤ) * z = y := by
        dsimp [z]
        exact Int.mul_ediv_cancel_of_dvd hdvd
      have hz : z ∉ S := by
        intro hzS
        apply hy
        exact Finset.mem_image.mpr ⟨z, hzS, hmul⟩
      simp [dilatedLaw, hm, z, hμ (y / (σ : ℤ)) hz]
    · simp [dilatedLaw, hm]
  rw [tsum_eq_sum (s := T) (fun y hy => hzero y hy)]
  have hinj : Set.InjOn e (↑S : Set ℤ) := by
    intro x hx y hy hxy
    exact (mul_left_cancel₀ hσz hxy)
  rw [Finset.sum_image hinj]
  have hfinite : ∑ z ∈ S, μ z * f (e z) = ∑' z, μ z * f (e z) := by
    symm
    exact tsum_eq_sum (s := S) (fun z hz => by simp [hμ z hz])
  rw [← hfinite]
  apply Finset.sum_congr rfl
  intro z hz
  simp [dilatedLaw, e, Int.mul_ediv_cancel_left _ hσz]

theorem harmonicLaw_tsum_eq_natSum (X W : ℕ) (f : ℤ → ℝ) :
    (∑' y : ℤ, harmonicLaw X W y * f y) =
      ∑ y ∈ harmonicNatSupport X W, harmonicNatLaw X W y * f (y : ℤ) := by
  let S := harmonicNatSupport X W
  let T := harmonicIntSupport X W
  rw [tsum_eq_sum (s := T) (fun y hy => by
    rw [pkgD_harmonicLaw_zero_of_not_mem X W y (by simpa [T] using hy)]
    simp)]
  change (∑ y ∈ S.image (fun y : ℕ => (y : ℤ)),
    harmonicLaw X W y * f y) = _
  calc
    _ = ∑ y ∈ S, harmonicLaw X W (y : ℤ) * f (y : ℤ) :=
      (Finset.sum_image (s := S) (f := fun y : ℤ => harmonicLaw X W y * f y)
        (g := fun y : ℕ => (y : ℤ))
        (by intro y hy z hz heq; exact Int.ofNat.inj heq))
    _ = ∑ y ∈ harmonicNatSupport X W, harmonicNatLaw X W y * f (y : ℤ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [harmonicLaw_nat_eq X W y hy]

theorem harmonicNormalizer_eq_dyadicMass (X W : ℕ) :
    harmonicNormalizer X W = OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W := by
  simp [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
    Finset.sum_filter, one_div, Nat.coprime_comm]

theorem harmonic_event_rawBad_bound (X W H σ R : ℕ)
    (hW : 0 < W) (hX : 4 * W ≤ X) (hH : 0 < H) (hR : R ≤ X)
    (f : ℤ → ℝ) (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (hbad : ∀ p : ℕ, f (p : ℤ) ≠ 0 →
      σ * (p - R) / H ≠ σ * (p + R) / H) :
    (∑' y : ℤ, harmonicLaw X W y * f y) ≤
      OAI.DyadicHarmonicBoundary.badMass X (X ^ 2) W σ H R /
        OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W := by
  have hNorm : 0 < harmonicNormalizer X W := harmonicNormalizer_pos X W hW hX
  rw [harmonicLaw_tsum_eq_natSum]
  have hterm (p : ℕ) (hp : p ∈ harmonicNatSupport X W) :
      harmonicNatLaw X W p * f (p : ℤ) ≤
        (if Nat.Coprime p W ∧ σ * (p - R) / H ≠ σ * (p + R) / H
          then 1 / (p : ℝ) else 0) / harmonicNormalizer X W := by
    have hp' := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hp'.1
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le (by omega : 0 < X) hpIco.1
    by_cases hf : f (p : ℤ) = 0
    · simp [hf]
      positivity
    · have hb := hbad p hf
      have hμ : harmonicNatLaw X W p =
          (1 / (p : ℝ)) / harmonicNormalizer X W := by
        rw [harmonicNatLaw, if_pos ⟨hpIco.1, hpIco.2, hp'.2⟩]
        field_simp [ne_of_gt hpR, ne_of_gt hNorm]
      rw [hμ]
      have hfp : 0 ≤ f (p : ℤ) := hf0 _
      calc
        (1 / (p : ℝ) / harmonicNormalizer X W) * f (p : ℤ) ≤
            (1 / (p : ℝ)) / harmonicNormalizer X W := by
              have hnonneg : 0 ≤ (1 / (p : ℝ)) / harmonicNormalizer X W := by positivity
              nlinarith [hf1 (p : ℤ)]
        _ = (if Nat.Coprime p W ∧ σ * (p - R) / H ≠ σ * (p + R) / H
              then 1 / (p : ℝ) else 0) / harmonicNormalizer X W := by
              rw [if_pos ⟨hp'.2, hb⟩]
  calc
    _ ≤ ∑ p ∈ harmonicNatSupport X W,
          (if Nat.Coprime p W ∧ σ * (p - R) / H ≠ σ * (p + R) / H
            then 1 / (p : ℝ) else 0) / harmonicNormalizer X W :=
      Finset.sum_le_sum fun p hp => hterm p hp
    _ = (∑ p ∈ harmonicNatSupport X W,
          if Nat.Coprime p W ∧ σ * (p - R) / H ≠ σ * (p + R) / H
            then 1 / (p : ℝ) else 0) / harmonicNormalizer X W := by
      rw [Finset.sum_div]
    _ = (∑ p ∈ Finset.Ico X (X ^ 2),
          if Nat.Coprime p W ∧ σ * (p - R) / H ≠ σ * (p + R) / H
            then 1 / (p : ℝ) else 0) / harmonicNormalizer X W := by
      congr 1
      change (∑ p ∈ (Finset.Ico X (X ^ 2)).filter (fun p => Nat.Coprime p W),
        if Nat.Coprime p W ∧ σ * (p - R) / H ≠ σ * (p + R) / H
          then 1 / (p : ℝ) else 0) = _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hc : Nat.Coprime p W <;> simp [hc]
    _ = OAI.DyadicHarmonicBoundary.badMass X (X ^ 2) W σ H R /
          harmonicNormalizer X W := by
      congr 1
      unfold OAI.DyadicHarmonicBoundary.badMass
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hc : W.Coprime p <;> simp [hc, Nat.coprime_comm]
    _ = OAI.DyadicHarmonicBoundary.badMass X (X ^ 2) W σ H R /
          OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W := by
      rw [harmonicNormalizer_eq_dyadicMass]

theorem pivotDilationError_tendsto {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (i : Fin n) :
    Tendsto (fun N => harmonicDilationUniformError (A.X N i) (primorial (N + 1))
      (masterScaleV A N i)) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, masterScaleV A N i ≤ A.X N i) := by
  let P : ℕ → ℕ := fun N => OAI.SourceAdmissible.previous (A.X N) i
  let S : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N) P N
  let V : ℕ → ℕ := fun N => masterScaleV A N i
  have hVle : ∀ N, (V N : ℝ) ≤ (S N) ^ 2 := by
    intro N
    have hprod :
        (∏ j ∈ Finset.univ.filter (fun j : Fin n => j < i), (A.X N j) ^ 2) =
          (P N) ^ 2 := by
      dsimp [P, OAI.SourceAdmissible.previous]
      rw [← Finset.prod_pow]
    have hveq : (V N : ℝ) = 2 + (A.M N : ℝ) + (P N : ℝ) ^ 2 := by
      dsimp [V, masterScaleV]
      rw [hprod]
      push_cast
      rfl
    have hseq : S N = 2 + (A.M N : ℝ) + (P N : ℝ) := by
      rfl
    rw [hveq, hseq]
    have hm : 0 ≤ (A.M N : ℝ) := by positivity
    have hp : 0 ≤ (P N : ℝ) := by positivity
    nlinarith [sq_nonneg (A.M N : ℝ), sq_nonneg (P N : ℝ)]
  have hSpos : ∀ N, 0 < S N := by
    intro N
    rw [show S N = 2 + (A.M N : ℝ) + (P N : ℝ) by rfl]
    positivity
  have hdom2 : Tendsto (fun N => (A.H N i : ℝ) / (S N) ^ (2 : ℕ)) atTop atTop := by
    have h := A.Hdom i 2 (by norm_num)
    simpa [S, P, OAI.AdmissibleMicrocellBoundary.earlierScale, Real.rpow_natCast] using h
  have hdom8 : Tendsto (fun N => (A.H N i : ℝ) / (S N) ^ (8 : ℕ)) atTop atTop := by
    have h := A.Hdom i 8 (by norm_num)
    simpa [S, P, OAI.AdmissibleMicrocellBoundary.earlierScale, Real.rpow_natCast] using h
  have hlogH : Tendsto (fun N => Real.log (A.X N i : ℝ) / (A.H N i : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using A.Xdom i 1 (by norm_num)
  have hXatTop : Tendsto (fun N => (A.X N i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (A.Xtendsto i)
  have hInvX : Tendsto (fun N => ((A.X N i : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hXatTop
  have hRad : Tendsto (fun N => (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) /
      (A.X N i : ℝ)) atTop (𝓝 0) :=
    OAI.MicrocellScale.endpoint_rate
      (Filter.Eventually.of_forall (fun _ => by norm_num))
      (Filter.Eventually.of_forall (fun N => A.Hpos N i)) hlogH
  have hRoot : Tendsto (fun N => Real.sqrt (A.H N i : ℝ) / (A.X N i : ℝ))
      atTop (𝓝 0) := by
    have hupper : ∀ᶠ N in atTop,
        Real.sqrt (A.H N i : ℝ) / (A.X N i : ℝ) ≤
          (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) / (A.X N i : ℝ) +
            ((A.X N i : ℝ))⁻¹ := by
      filter_upwards with N
      have hgt := OAI.MicrocellScale.radius_gt 1 (A.H N i) (by norm_num)
      have hXpos : (0 : ℝ) < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
      have hgt' : Real.sqrt (A.H N i : ℝ) - 1 <
          (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) := by simpa using hgt
      have hnum : Real.sqrt (A.H N i : ℝ) ≤
          (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) + 1 := by linarith
      calc
        Real.sqrt (A.H N i : ℝ) / (A.X N i : ℝ) ≤
            ((OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) + 1) / (A.X N i : ℝ) :=
          div_le_div_of_nonneg_right hnum hXpos.le
        _ = (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) / (A.X N i : ℝ) +
            1 / (A.X N i : ℝ) := by rw [add_div]
        _ = (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) / (A.X N i : ℝ) +
            ((A.X N i : ℝ))⁻¹ := by rw [one_div]
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (Real.sqrt_nonneg _) (by positivity)))
      hupper (by simpa using hRad.add hInvX)
  have hV4 : ∀ᶠ N in atTop, (V N : ℝ) ^ 4 ≤ (A.H N i : ℝ) := by
    filter_upwards [hdom8.eventually_ge_atTop 1] with N hN
    have hS8 : (S N) ^ 8 ≤ (A.H N i : ℝ) := by
      simpa only [one_mul] using (le_div_iff₀ (pow_pos (hSpos N) 8)).mp hN
    have hV4S8 : (V N : ℝ) ^ 4 ≤ (S N) ^ 8 := by
      calc
        _ ≤ ((S N) ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) (hVle N) 4
        _ = (S N) ^ 8 := by rw [← pow_mul]
    exact hV4S8.trans hS8
  have hVsqrt : ∀ᶠ N in atTop, (V N : ℝ) ^ 2 ≤ Real.sqrt (A.H N i : ℝ) := by
    filter_upwards [hV4] with N hN
    have hsq : (Real.sqrt (A.H N i : ℝ)) ^ 2 = (A.H N i : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hsqle : ((V N : ℝ) ^ 2) ^ 2 ≤ (Real.sqrt (A.H N i : ℝ)) ^ 2 := by
      nlinarith [hN, hsq]
    exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsqle
  have hVoverH : Tendsto (fun N => (V N : ℝ) / (A.H N i : ℝ)) atTop (𝓝 0) := by
    have hInvDom : Tendsto (fun N => ((A.H N i : ℝ) / (S N) ^ 2)⁻¹)
        atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hdom2
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
      ?_ hInvDom
    filter_upwards with N
    have hHpos : (0 : ℝ) < (A.H N i : ℝ) := by exact_mod_cast A.Hpos N i
    have hSsq : 0 < (S N) ^ 2 := pow_pos (hSpos N) 2
    calc
      (V N : ℝ) / (A.H N i : ℝ) ≤ (S N) ^ 2 / (A.H N i : ℝ) :=
        div_le_div_of_nonneg_right (hVle N) hHpos.le
      _ = ((A.H N i : ℝ) / (S N) ^ 2)⁻¹ := by field_simp
  have hVoverLog : Tendsto (fun N => (V N : ℝ) / Real.log (A.X N i : ℝ))
      atTop (𝓝 0) := by
    have hXone : ∀ N, (1 : ℝ) ≤ (A.X N i : ℝ) := by
      intro N
      have hNat : 1 ≤ A.X N i := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (A.Xpos N i))
      exact_mod_cast hNat
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity)
        (Real.log_nonneg (hXone N))))
      ?_ hVoverH
    filter_upwards [hlogH.eventually_ge_atTop 1] with N hN
    have hHpos : (0 : ℝ) < (A.H N i : ℝ) := by exact_mod_cast A.Hpos N i
    have hHleLog : (A.H N i : ℝ) ≤ Real.log (A.X N i : ℝ) := by
      simpa only [one_mul] using (le_div_iff₀ hHpos).mp hN
    exact div_le_div_of_nonneg_left (by positivity) hHpos hHleLog
  have hWKoverX : Tendsto (fun N => (primorial (N + 1) : ℝ) * (V N : ℝ) /
      (A.X N i : ℝ)) atTop (𝓝 0) := by
    have hupper : ∀ᶠ N in atTop,
        (primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ) ≤
          Real.sqrt (A.H N i : ℝ) / (A.X N i : ℝ) := by
      filter_upwards [hVsqrt] with N hN
      have hWleV : (primorial (N + 1) : ℝ) ≤ (V N : ℝ) := by
        have hNat : primorial (N + 1) ≤ masterScaleV A N i :=
          (A.Wle N).trans (by unfold masterScaleV; omega)
        exact_mod_cast hNat
      have hVnonneg : 0 ≤ (V N : ℝ) := by positivity
      have hVminusW : 0 ≤ (V N : ℝ) - (primorial (N + 1) : ℝ) := sub_nonneg.mpr hWleV
      have hprod : (primorial (N + 1) : ℝ) * (V N : ℝ) ≤ (V N : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hVnonneg hVminusW]
      exact div_le_div_of_nonneg_right (hprod.trans hN) (by positivity)
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
      hupper hRoot
  have hErr : Tendsto
      (fun N => harmonicDilationUniformError (A.X N i) (primorial (N + 1)) (V N))
      atTop (𝓝 0) := by
    have hLogLarge : ∀ᶠ N in atTop, 2 ≤ Real.log (A.X N i : ℝ) := by
      filter_upwards [hlogH.eventually_ge_atTop 2] with N hN
      have hHge : (1 : ℝ) ≤ A.H N i := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (A.Hpos N i)))
      have hmul := (le_div_iff₀ (show (0 : ℝ) < (A.H N i : ℝ) by positivity)).mp hN
      nlinarith
    have hWoverX : Tendsto (fun N => (primorial (N + 1) : ℝ) / (A.X N i : ℝ))
        atTop (𝓝 0) := by
      apply squeeze_zero'
        (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
        ?_ hWKoverX
      filter_upwards with N
      have hVpos : 1 ≤ V N := by dsimp [V, masterScaleV]; omega
      have hXpos : 0 < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
      have hWnonneg : 0 ≤ (primorial (N + 1) : ℝ) := by positivity
      have hVposR : (1 : ℝ) ≤ (V N : ℝ) := by exact_mod_cast hVpos
      have hWle : (primorial (N + 1) : ℝ) ≤
          (primorial (N + 1) : ℝ) * (V N : ℝ) := by
        calc
          _ = (primorial (N + 1) : ℝ) * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hVposR hWnonneg
      exact div_le_div_of_nonneg_right hWle hXpos.le
    have hDen : ∀ᶠ N in atTop,
        (Real.log (A.X N i : ℝ) - (primorial (N + 1) : ℝ) / (A.X N i : ℝ)) ≥
          Real.log (A.X N i : ℝ) / 2 := by
      filter_upwards [hLogLarge, hWoverX.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with N hL hW
      linarith
    have hNum : Tendsto (fun N => 4 * (V N : ℝ) / Real.log (A.X N i : ℝ) +
        4 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N => 4 * (V N : ℝ) / Real.log (A.X N i : ℝ))
          atTop (𝓝 0) := by
        simpa [div_eq_mul_inv, mul_assoc] using Filter.Tendsto.const_mul 4 hVoverLog
      simpa only [mul_zero, zero_add] using h1.add (Filter.Tendsto.const_mul 4 hWKoverX)
    have hErrNonneg : ∀ᶠ N in atTop,
        0 ≤ harmonicDilationUniformError (A.X N i) (primorial (N + 1)) (V N) := by
      filter_upwards [hDen, hLogLarge] with N hden hlog
      unfold harmonicDilationUniformError
      apply div_nonneg
      · have hXpos : 0 < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
        have hVposNat : 1 ≤ V N := by dsimp [V, masterScaleV]; omega
        have hVpos : (1 : ℝ) ≤ V N := by exact_mod_cast hVposNat
        positivity
      · linarith
    apply squeeze_zero'
      hErrNonneg ?_ hNum
    filter_upwards [hDen, hLogLarge] with N hden hlog
    unfold harmonicDilationUniformError
    have hXpos : 0 < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
    have hVposNat : 1 ≤ V N := by dsimp [V, masterScaleV]; omega
    have hVpos : (1 : ℝ) ≤ V N := by exact_mod_cast hVposNat
    have hlogV : Real.log (V N : ℝ) ≤ (V N : ℝ) := Real.log_le_self (by positivity)
    have hWnonneg : 0 ≤ (primorial (N + 1) : ℝ) := by positivity
    have hnum : 2 * Real.log (V N : ℝ) + (primorial (N + 1) : ℝ) * (V N : ℝ) /
        (A.X N i : ℝ) * (1 + 1 / (A.X N i : ℝ)) ≤
          2 * (V N : ℝ) + 2 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ)) := by
      have hxNat : 1 ≤ A.X N i :=
        Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (A.Xpos N i))
      have hxlarge : (1 : ℝ) ≤ (A.X N i : ℝ) := by exact_mod_cast hxNat
      have hxinv : 1 / (A.X N i : ℝ) ≤ 1 := by
        exact (div_le_iff₀ hXpos).2 (by nlinarith)
      have hterm : 0 ≤ (primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ) := by positivity
      have hfac : 1 + 1 / (A.X N i : ℝ) ≤ 2 := by linarith
      have hprod := mul_le_mul_of_nonneg_left hfac hterm
      nlinarith [hlogV, hprod]
    have hdenpos : 0 < Real.log (A.X N i : ℝ) / 2 := by positivity
    calc
      _ ≤ (2 * (V N : ℝ) + 2 * ((primorial (N + 1) : ℝ) * (V N : ℝ) /
          (A.X N i : ℝ))) / (Real.log (A.X N i : ℝ) / 2) := by
        have hdenpos : 0 < Real.log (A.X N i : ℝ) -
            (primorial (N + 1) : ℝ) / (A.X N i : ℝ) := by linarith [hlog]
        have hnumNonneg : 0 ≤ 2 * (V N : ℝ) +
            2 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ)) := by positivity
        calc
          _ ≤ (2 * (V N : ℝ) + 2 * ((primorial (N + 1) : ℝ) * (V N : ℝ) /
              (A.X N i : ℝ))) / (Real.log (A.X N i : ℝ) -
                (primorial (N + 1) : ℝ) / (A.X N i : ℝ)) :=
            div_le_div_of_nonneg_right hnum hdenpos.le
          _ ≤ _ := div_le_div_of_nonneg_left hnumNonneg
            (by positivity : 0 < Real.log (A.X N i : ℝ) / 2) hden
      _ = 4 * (V N : ℝ) / Real.log (A.X N i : ℝ) +
          4 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ)) /
            Real.log (A.X N i : ℝ) := by field_simp; ring
      _ ≤ 4 * (V N : ℝ) / Real.log (A.X N i : ℝ) +
          4 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ)) := by
        have hR : 1 ≤ Real.log (A.X N i : ℝ) := by linarith
        have hterm : 0 ≤ (primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ) := by positivity
        have hsmall := div_le_self hterm hR
        have hsmall4 := mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 4)
        have heq : 4 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ)) /
            Real.log (A.X N i : ℝ) = 4 * (((primorial (N + 1) : ℝ) * (V N : ℝ) /
              (A.X N i : ℝ)) / Real.log (A.X N i : ℝ)) := by ring
        rw [heq]
        calc
          _ = 4 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ) /
              Real.log (A.X N i : ℝ)) + 4 * (V N : ℝ) / Real.log (A.X N i : ℝ) := by ring
          _ ≤ 4 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ)) +
              4 * (V N : ℝ) / Real.log (A.X N i : ℝ) := by
            calc
              _ = 4 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ) /
                  Real.log (A.X N i : ℝ)) + 4 * (V N : ℝ) / Real.log (A.X N i : ℝ) := rfl
              _ ≤ 4 * ((primorial (N + 1) : ℝ) * (V N : ℝ) / (A.X N i : ℝ)) +
                  4 * (V N : ℝ) / Real.log (A.X N i : ℝ) := by nlinarith [hsmall4]
          _ = _ := by ring
  have hVoverX : Tendsto (fun N => (V N : ℝ) / (A.X N i : ℝ)) atTop (𝓝 0) := by
    have hupper : ∀ᶠ N in atTop,
        (V N : ℝ) / (A.X N i : ℝ) ≤ Real.sqrt (A.H N i : ℝ) / (A.X N i : ℝ) := by
      filter_upwards [hVsqrt] with N hN
      have hVpos : 1 ≤ V N := by dsimp [V, masterScaleV]; omega
      have hVposR : (1 : ℝ) ≤ (V N : ℝ) := by exact_mod_cast hVpos
      have hVle : (V N : ℝ) ≤ (V N : ℝ) ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_right (hVle.trans hN) (by positivity)
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
      hupper hRoot
  have hVleX : ∀ᶠ N in atTop, V N ≤ A.X N i := by
    filter_upwards [hVoverX.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with N hN
    have hXpos : (0 : ℝ) < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
    have hlt : (V N : ℝ) < (A.X N i : ℝ) := by
      simpa only [one_mul] using (div_lt_iff₀ hXpos).mp hN
    exact_mod_cast hlt.le
  exact ⟨by simpa [V] using hErr, by simpa [V] using hVleX⟩

theorem earlierGapOverPivot_tendsto {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (l i : Fin n) (hli : l < i) :
    Tendsto (fun N => (A.H N l : ℝ) / (A.X N i : ℝ)) atTop (𝓝 0) := by
  let P : ℕ → ℕ := fun N => OAI.SourceAdmissible.previous (A.X N) i
  let S : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N) P N
  have hSpos (N : ℕ) : 0 < S N := by
    rw [show S N = 2 + (A.M N : ℝ) + (P N : ℝ) by rfl]
    positivity
  have hdom2 : Tendsto (fun N => (A.H N i : ℝ) / (S N) ^ (2 : ℕ)) atTop atTop := by
    simpa [S, P, OAI.AdmissibleMicrocellBoundary.earlierScale, Real.rpow_natCast] using
      A.Hdom i 2 (by norm_num)
  have hSsqrt : ∀ᶠ N in atTop, S N ≤ Real.sqrt (A.H N i : ℝ) := by
    filter_upwards [hdom2.eventually_ge_atTop 1] with N hN
    have hH : (S N) ^ 2 ≤ (A.H N i : ℝ) := by
      simpa only [one_mul] using (le_div_iff₀ (pow_pos (hSpos N) 2)).mp hN
    have hsq : (Real.sqrt (A.H N i : ℝ)) ^ 2 = (A.H N i : ℝ) :=
      Real.sq_sqrt (by positivity)
    apply (sq_le_sq₀ (le_of_lt (hSpos N)) (Real.sqrt_nonneg _)).mp
    nlinarith
  have hlogL : Tendsto (fun N => Real.log (A.X N l : ℝ) / (A.H N l : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using A.Xdom l 1 (by norm_num)
  have hHleP : ∀ᶠ N in atTop, A.H N l ≤ P N := by
    filter_upwards [hlogL.eventually_ge_atTop 1] with N hN
    have hHpos : (0 : ℝ) < (A.H N l : ℝ) := by exact_mod_cast A.Hpos N l
    have hHleLog : (A.H N l : ℝ) ≤ Real.log (A.X N l : ℝ) := by
      simpa only [one_mul] using (le_div_iff₀ hHpos).mp hN
    have hXpos : (0 : ℝ) ≤ (A.X N l : ℝ) := by positivity
    have hlogle : Real.log (A.X N l : ℝ) ≤ (A.X N l : ℝ) := Real.log_le_self hXpos
    have hXleP : A.X N l ≤ P N := by
      dsimp [P, OAI.SourceAdmissible.previous]
      apply Finset.single_le_prod
      · intro j hj
        exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (A.Xpos N j))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli⟩
    have hHlePReal : (A.H N l : ℝ) ≤ (P N : ℝ) :=
      hHleLog.trans (hlogle.trans (by exact_mod_cast hXleP))
    exact_mod_cast hHlePReal
  have hXatTop : Tendsto (fun N => (A.X N i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (A.Xtendsto i)
  have hInvX : Tendsto (fun N => ((A.X N i : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hXatTop
  have hlogI : Tendsto (fun N => Real.log (A.X N i : ℝ) / (A.H N i : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using A.Xdom i 1 (by norm_num)
  have hRad : Tendsto (fun N => (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) /
      (A.X N i : ℝ)) atTop (𝓝 0) :=
    OAI.MicrocellScale.endpoint_rate
      (Filter.Eventually.of_forall (fun _ => by norm_num))
      (Filter.Eventually.of_forall (fun N => A.Hpos N i)) hlogI
  have hRoot : Tendsto (fun N => Real.sqrt (A.H N i : ℝ) / (A.X N i : ℝ))
      atTop (𝓝 0) := by
    have hupper : ∀ᶠ N in atTop,
        Real.sqrt (A.H N i : ℝ) / (A.X N i : ℝ) ≤
          (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) / (A.X N i : ℝ) +
            ((A.X N i : ℝ))⁻¹ := by
      filter_upwards with N
      have hgt := OAI.MicrocellScale.radius_gt 1 (A.H N i) (by norm_num)
      have hXpos : (0 : ℝ) < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
      have hgt' : Real.sqrt (A.H N i : ℝ) - 1 <
          (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) := by simpa using hgt
      have hnum : Real.sqrt (A.H N i : ℝ) ≤
          (OAI.MicrocellScale.radius 1 (A.H N i) : ℝ) + 1 := by linarith
      simpa [add_div, one_div] using div_le_div_of_nonneg_right hnum hXpos.le
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (Real.sqrt_nonneg _) (by positivity)))
      hupper (by simpa using hRad.add hInvX)
  have hupper : ∀ᶠ N in atTop, (A.H N l : ℝ) / (A.X N i : ℝ) ≤
      Real.sqrt (A.H N i : ℝ) / (A.X N i : ℝ) := by
    filter_upwards [hHleP, hSsqrt] with N hHL hS
    have hPleS : (P N : ℝ) ≤ S N := by
      dsimp [S, OAI.AdmissibleMicrocellBoundary.earlierScale]
      have hMnonneg : 0 ≤ (A.M N : ℝ) := by positivity
      nlinarith
    have hXpos : (0 : ℝ) < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
    have hHLR : (A.H N l : ℝ) ≤ (P N : ℝ) := by exact_mod_cast hHL
    exact div_le_div_of_nonneg_right (hHLR.trans (hPleS.trans hS)) hXpos.le
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
    hupper hRoot

theorem Emu_eq_harmonicInt_sum {n : ℕ} (A : Parameters n) (N : ℕ)
    (i : Fin n) (f : ℤ → ℝ) :
    Emu A N i f =
      ∑ y ∈ harmonicIntSupport (A.X N i) (primorial (N + 1)),
        harmonicLaw (A.X N i) (primorial (N + 1)) y * f y := by
  change (∑' y : ℤ, harmonicLaw (A.X N i) (primorial (N + 1)) y * f y) = _
  rw [tsum_eq_sum (s := harmonicIntSupport (A.X N i) (primorial (N + 1)))
    (fun y hy => by
      rw [pkgD_harmonicLaw_zero_of_not_mem _ _ y hy]
      simp)]

theorem parameterTailProductLaw_zero_of_gt {n : ℕ} (A : Parameters n)
    (N : ℕ) (Tails : Finset (Fin n)) (σ : ℕ)
    (hbound : (∏ j ∈ Tails, (A.X N j) ^ 2) < σ) :
    parameterTailProductLaw A N Tails σ = 0 := by
  by_contra hzero
  have hnonzero : parameterTailProductLaw A N Tails σ ≠ 0 := hzero
  obtain ⟨_, _, hσle⟩ := parameterTailProductLaw_support_properties A N Tails σ hnonzero
    (fun j => A.Xpos N j)
  omega

theorem nuWeightedPairing_eq {n : ℕ} (A : Parameters n) (N : ℕ)
    (B : Block n) (f : ℤ → ℝ) :
    Emu A N B.1 (fun y => nu A N B y * f y) =
      ∑' σ : ℕ, parameterTailProductLaw A N B.2.val σ *
        (∑' y : ℤ, dilationReference (harmonicLaw (A.X N B.1) (primorial (N + 1))) σ y * f y) := by
  let μ : ℤ → ℝ := harmonicLaw (A.X N B.1) (primorial (N + 1))
  let Tails : Finset (Fin n) := (B.2).val
  let Tail : ℕ → ℝ := parameterTailProductLaw A N Tails
  let Sy : Finset ℤ := harmonicIntSupport (A.X N B.1) (primorial (N + 1))
  let bound : ℕ := ∏ j ∈ Tails, (A.X N j) ^ 2
  let Sσ : Finset ℕ := Finset.range (bound + 1)
  have hμzero : ∀ y ∉ Sy, μ y = 0 := by
    intro y hy
    exact pkgD_harmonicLaw_zero_of_not_mem _ _ y (by simpa [Sy, μ] using hy)
  have htailzero : ∀ σ ∉ Sσ, Tail σ = 0 := by
    intro σ hσ
    apply parameterTailProductLaw_zero_of_gt A N Tails σ _
    have hnot : ¬ σ < bound + 1 := by simpa [Sσ, Finset.mem_range] using hσ
    change (∏ j ∈ Tails, (A.X N j) ^ 2) < σ
    omega
  have hrefzero (σ : ℕ) (y : ℤ) (hy : y ∉ Sy) :
      dilationReference μ σ y = 0 := by
    simp [dilationReference, μ, hμzero y (by simpa [Sy] using hy)]
  have hpoint (y : ℤ) :
      (∑ σ ∈ Sσ, Tail σ * dilationReference μ σ y) =
        nu A N B y * μ y := by
    have h := block_product_weight_average_is_nu A N B y
    rw [tsum_eq_sum (s := Sσ) (fun σ hσ => by
      have htail0 : parameterTailProductLaw A N (B.2).val σ = 0 := by
        simpa [Tail, Tails] using htailzero σ hσ
      simp [htail0])] at h
    simpa [Tail, Tails, Sy, μ, nu, weightedPivotMass] using h
  have hInner (σ : ℕ) :
      (∑ y ∈ Sy, dilationReference μ σ y * f y) =
        ∑' y : ℤ, dilationReference μ σ y * f y := by
    symm
    exact tsum_eq_sum (s := Sy) (fun y hy => by simp [hrefzero σ y hy])
  have hOuter :
      (∑' σ : ℕ, Tail σ * (∑' y : ℤ, dilationReference μ σ y * f y)) =
        ∑ σ ∈ Sσ, Tail σ * (∑ y ∈ Sy, dilationReference μ σ y * f y) := by
    rw [tsum_eq_sum (s := Sσ) (fun σ hσ => by
      have htail0 : parameterTailProductLaw A N (B.2).val σ = 0 := by
        simpa [Tail, Tails] using htailzero σ hσ
      simp [Tail, Tails, htail0])]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [← hInner σ]
  calc
    Emu A N B.1 (fun y => nu A N B y * f y) =
        ∑ y ∈ Sy, μ y * (nu A N B y * f y) := by
      rw [Emu_eq_harmonicInt_sum]
    _ = ∑ y ∈ Sy, (∑ σ ∈ Sσ, Tail σ * dilationReference μ σ y) * f y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hpoint y]
      ring
    _ = ∑ σ ∈ Sσ, Tail σ * (∑ y ∈ Sy, dilationReference μ σ y * f y) := by
      calc
        _ = ∑ y ∈ Sy, ∑ σ ∈ Sσ, (Tail σ * dilationReference μ σ y) * f y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.sum_mul]
        _ = ∑ σ ∈ Sσ, ∑ y ∈ Sy, (Tail σ * dilationReference μ σ y) * f y :=
          Finset.sum_comm
        _ = ∑ σ ∈ Sσ, Tail σ * (∑ y ∈ Sy, dilationReference μ σ y * f y) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = ∑' σ : ℕ, Tail σ * (∑' y : ℤ, dilationReference μ σ y * f y) := hOuter.symm

/-- Local copy of the endpoint strip predicate, kept here so the analytic helpers do not import
`Results.lean` (which imports this package). -/
def pkgDBoundaryStrip (H width : ℕ) (y : ℤ) : Prop :=
  y % (H : ℤ) ≤ (width : ℤ) ∨ (H : ℤ) ≤ y % (H : ℤ) + (width : ℤ)

/-- Indicator of `pkgDBoundaryStrip`. -/
noncomputable def pkgDBoundaryIndicator (H width : ℕ) (y : ℤ) : ℝ :=
  by
    classical
    exact if pkgDBoundaryStrip H width y then 1 else 0

theorem pkgD_harmonicNatLaw_nonneg (X W n : ℕ) (hNorm : 0 < harmonicNormalizer X W) :
    0 ≤ harmonicNatLaw X W n := by
  unfold harmonicNatLaw
  split_ifs with h
  · apply div_nonneg
    · positivity
    · apply mul_nonneg
      · positivity
      · exact hNorm.le
  · positivity

theorem pkgD_parameterTailProductLaw_nonneg {n : ℕ} (A : Parameters n)
    (N : ℕ) (Tails : Finset (Fin n))
    (hNorm : ∀ i, 0 < harmonicNormalizer (A.X N i) (primorial (N + 1)))
    (σ : ℕ) : 0 ≤ parameterTailProductLaw A N Tails σ := by
  unfold parameterTailProductLaw
  apply tsum_nonneg
  intro t
  apply mul_nonneg
  · positivity
  · apply Finset.prod_nonneg
    intro i hi
    exact pkgD_harmonicNatLaw_nonneg (A.X N i) (primorial (N + 1)) (t i) (hNorm i)

theorem pkgD_nu_nonneg {n : ℕ} (A : Parameters n) (N : ℕ) (B : Block n)
    (hNorm : ∀ i, 0 < harmonicNormalizer (A.X N i) (primorial (N + 1))) (y : ℤ) :
    0 ≤ nu A N B y := by
  unfold nu nuB
  apply tsum_nonneg
  intro σ
  have htail := pkgD_parameterTailProductLaw_nonneg A N B.2.val hNorm σ
  by_cases hd : (σ : ℤ) ∣ y
  · simp [hd]
    positivity
  · simp [hd]

/-- Pairing against a bounded function changes by at most the L1 distance between the pushed
law and its unnormalized dilation reference. -/
theorem dilationReference_pairing_l1 (X W σ : ℕ) (hσ : 0 < σ)
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    |(∑' y : ℤ, dilationReference (harmonicLaw X W) σ y * f y) -
      (∑' y : ℤ, dilatedLaw (harmonicLaw X W) σ y * f y)| ≤
        arithmeticL1 (dilatedLaw (harmonicLaw X W) σ)
          (dilationReference (harmonicLaw X W) σ) := by
  let S : Finset ℤ := harmonicIntSupport X W ∪
    (harmonicIntSupport X W).image (fun z => (σ : ℤ) * z)
  have hμzero : ∀ z ∉ harmonicIntSupport X W, harmonicLaw X W z = 0 := by
    intro z hz
    exact pkgD_harmonicLaw_zero_of_not_mem X W z hz
  have hrefzero : ∀ y ∉ S, dilationReference (harmonicLaw X W) σ y = 0 := by
    intro y hy
    have hyμ : y ∉ harmonicIntSupport X W := by
      intro hmem
      exact hy (Finset.mem_union.mpr (Or.inl hmem))
    simp [dilationReference, hμzero y hyμ]
  have hdilzero : ∀ y ∉ S, dilatedLaw (harmonicLaw X W) σ y = 0 := by
    intro y hy
    have hyimage : y ∉ (harmonicIntSupport X W).image (fun z => (σ : ℤ) * z) := by
      intro hmem
      exact hy (Finset.mem_union.mpr (Or.inr hmem))
    by_cases hm : y % (σ : ℤ) = 0
    · have hdvd : (σ : ℤ) ∣ y := Int.dvd_of_emod_eq_zero hm
      let z : ℤ := y / (σ : ℤ)
      have hmul : (σ : ℤ) * z = y := by
        dsimp [z]
        exact Int.mul_ediv_cancel_of_dvd hdvd
      have hz : z ∉ harmonicIntSupport X W := by
        intro hz
        apply hyimage
        exact Finset.mem_image.mpr ⟨z, hz, hmul⟩
      simp [dilatedLaw, hm, z, hμzero z hz]
    · simp [dilatedLaw, hm]
  have hl1 := finite_pairing_l1_bound S
    (dilationReference (harmonicLaw X W) σ)
    (dilatedLaw (harmonicLaw X W) σ) f hrefzero hdilzero hf
  calc
    _ ≤ arithmeticL1 (dilationReference (harmonicLaw X W) σ)
        (dilatedLaw (harmonicLaw X W) σ) := hl1
    _ = arithmeticL1 (dilatedLaw (harmonicLaw X W) σ)
        (dilationReference (harmonicLaw X W) σ) := by
      unfold arithmeticL1
      apply tsum_congr
      intro y
      rw [abs_sub_comm]

theorem harmonicNormalizer_nonneg_of_Xpos (X W : ℕ) (hX : 0 < X) :
    0 ≤ harmonicNormalizer X W := by
  unfold harmonicNormalizer
  apply Finset.sum_nonneg
  intro n hn
  have hrange := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le hX hrange.1
  exact div_nonneg (by positivity) (le_of_lt hnpos)

theorem harmonicLaw_nonneg_of_Xpos (X W : ℕ) (hX : 0 < X) (y : ℤ) :
    0 ≤ harmonicLaw X W y := by
  unfold harmonicLaw
  split_ifs with h
  · apply div_nonneg
    · positivity
    · exact mul_nonneg (by positivity) (harmonicNormalizer_nonneg_of_Xpos X W hX)
  · positivity

theorem pivotNu_nonneg_eventually {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm) (B : Block K) :
    ∀ᶠ N in atTop, ∀ y, 0 ≤ nu MS.core.parameters N B y := by
  classical
  let A := MS.core.parameters
  have hXall : ∀ᶠ N in atTop, ∀ j : Fin K,
      j ∈ (Finset.univ : Finset (Fin K)) → 4 * primorial (N + 1) ≤ A.X N j := by
    apply (eventually_all_finset (Finset.univ : Finset (Fin K))).2
    intro j hj
    exact A.eventual_X j
  filter_upwards [hXall] with N hXN y
  apply pkgD_nu_nonneg A N B
  intro j
  exact harmonicNormalizer_pos (A.X N j) (primorial (N + 1)) (primorial_pos _)
    (hXN j (Finset.mem_univ j))

theorem pkgD_Emu_add {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (f g : ℤ → ℝ) :
    Emu A N i (fun y => f y + g y) = Emu A N i f + Emu A N i g := by
  rw [Emu_eq_harmonicNat_sum, Emu_eq_harmonicNat_sum, Emu_eq_harmonicNat_sum]
  calc
    _ = ∑ y ∈ harmonicNatSupport (A.X N i) (primorial (N + 1)),
        (harmonicNatLaw (A.X N i) (primorial (N + 1)) y * f (y : ℤ) +
          harmonicNatLaw (A.X N i) (primorial (N + 1)) y * g (y : ℤ)) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = _ := Finset.sum_add_distrib

theorem Emu_const_mul {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (c : ℝ) (f : ℤ → ℝ) :
    Emu A N i (fun y => c * f y) = c * Emu A N i f := by
  rw [Emu_eq_harmonicNat_sum, Emu_eq_harmonicNat_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem Emu_const_add_mul {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (w f : ℤ → ℝ) (a b : ℝ) :
    Emu A N i (fun y => w y * (a + b * f y)) =
      a * Emu A N i w + b * Emu A N i (fun y => w y * f y) := by
  calc
    Emu A N i (fun y => w y * (a + b * f y)) =
        Emu A N i (fun y => a * w y + b * (w y * f y)) := by
          congr 1
          funext y
          ring
    _ = Emu A N i (fun y => a * w y) +
        Emu A N i (fun y => b * (w y * f y)) := pkgD_Emu_add A N i _ _
    _ = a * Emu A N i w + b * Emu A N i (fun y => w y * f y) := by
      rw [Emu_const_mul, Emu_const_mul]

theorem Emu_sum_pairing {n m : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (g : ℤ → ℝ) (coeff : Fin m → ℝ) (f : Fin m → ℤ → ℝ) :
    Emu A N i (fun y => g y * ∑ t, coeff t * f t y) =
      ∑ t, coeff t * Emu A N i (fun y => g y * f t y) := by
  rw [Emu_eq_harmonicNat_sum]
  let S := harmonicNatSupport (A.X N i) (primorial (N + 1))
  calc
    (∑ y ∈ S, harmonicNatLaw (A.X N i) (primorial (N + 1)) y *
        (g (y : ℤ) * ∑ t, coeff t * f t (y : ℤ))) =
      ∑ y ∈ S, ∑ t, coeff t *
        (harmonicNatLaw (A.X N i) (primorial (N + 1)) y *
          (g (y : ℤ) * f t (y : ℤ))) := by
        apply Finset.sum_congr rfl
        intro y hy
        calc
          _ = harmonicNatLaw (A.X N i) (primorial (N + 1)) y * g (y : ℤ) *
              ∑ t, coeff t * f t (y : ℤ) := by ring
          _ = ∑ t, (harmonicNatLaw (A.X N i) (primorial (N + 1)) y * g (y : ℤ)) *
              (coeff t * f t (y : ℤ)) := by rw [Finset.mul_sum]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro t ht
            ring
    _ = ∑ t, ∑ y ∈ S, coeff t *
        (harmonicNatLaw (A.X N i) (primorial (N + 1)) y *
          (g (y : ℤ) * f t (y : ℤ))) := Finset.sum_comm
    _ = ∑ t, coeff t * ∑ y ∈ S,
        harmonicNatLaw (A.X N i) (primorial (N + 1)) y *
          (g (y : ℤ) * f t (y : ℤ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mul_sum]
    _ = ∑ t, coeff t * Emu A N i (fun y => g y * f t y) := by
        apply Finset.sum_congr rfl
        intro t ht
        congr 1
        simpa [S] using
          (Emu_eq_harmonicNat_sum A N i (fun y => g y * f t y)).symm

theorem Emu_abs_bound_by_weight {n : ℕ} (A : Parameters n) (N : ℕ) (i : Fin n)
    (f g : ℤ → ℝ) (hμ : ∀ y, 0 ≤ harmonicLaw (A.X N i) (primorial (N + 1)) y)
    (hfg : ∀ y, |f y| ≤ g y) :
    |Emu A N i f| ≤ Emu A N i g := by
  rw [Emu_eq_harmonicNat_sum, Emu_eq_harmonicNat_sum]
  calc
    |∑ y ∈ harmonicNatSupport (A.X N i) (primorial (N + 1)),
        harmonicNatLaw (A.X N i) (primorial (N + 1)) y * f (y : ℤ)|
        = ‖∑ y ∈ harmonicNatSupport (A.X N i) (primorial (N + 1)),
          harmonicNatLaw (A.X N i) (primorial (N + 1)) y * f (y : ℤ)‖ := by
            rw [Real.norm_eq_abs]
    _ ≤ ∑ y ∈ harmonicNatSupport (A.X N i) (primorial (N + 1)),
          |harmonicNatLaw (A.X N i) (primorial (N + 1)) y * f (y : ℤ)| := by
            simpa [Real.norm_eq_abs] using
              (norm_sum_le (harmonicNatSupport (A.X N i) (primorial (N + 1)) : Finset ℕ)
                (fun y : ℕ => harmonicNatLaw (A.X N i) (primorial (N + 1)) y * f (y : ℤ)))
    _ ≤ ∑ y ∈ harmonicNatSupport (A.X N i) (primorial (N + 1)),
          harmonicNatLaw (A.X N i) (primorial (N + 1)) y * g (y : ℤ) := by
      apply Finset.sum_le_sum
      intro y hy
      have hμy : 0 ≤ harmonicNatLaw (A.X N i) (primorial (N + 1)) y := by
        rw [← harmonicLaw_nat_eq _ _ y hy]
        exact hμ (y : ℤ)
      rw [abs_mul, abs_of_nonneg hμy]
      exact mul_le_mul_of_nonneg_left (hfg (y : ℤ)) hμy

theorem extraTemplate_allowed {K sl s : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (h1 : (1 : IntegerPolynomial sl) ∈ Dm) :
    Allowed Dm (extraTemplate s) := by
  classical
  let ι : Fin 0 ↪ Fin sl := ⟨Fin.elim0, by intro i j hij; exact Fin.elim0 i⟩
  refine ⟨ι, ?_⟩
  intro P hP
  change P ∈ ({1} : Finset (IntegerPolynomial 0)) at hP
  have hP1 : P = 1 := Finset.mem_singleton.mp hP
  subst P
  change MvPolynomial.rename (ι : Fin 0 → Fin sl) (1 : IntegerPolynomial 0) ∈ Dm
  rw [← MvPolynomial.C_1, MvPolynomial.rename_C, MvPolynomial.C_1]
  exact h1

theorem tsum_finZero_real (f : (Fin 0 → ℕ) → ℝ) :
    ∑' p : Fin 0 → ℕ, f p = f (fun i => Fin.elim0 i) := by
  classical
  let p₀ : Fin 0 → ℕ := fun i => Fin.elim0 i
  apply tsum_eq_single p₀
  intro p hp
  have hpeq : p = p₀ := by
    funext i
    exact Fin.elim0 i
  exact (hp hpeq).elim

def emptyNatTuple {q : ℕ} (hq : q = 0) : Fin q → ℕ :=
  fun i => Fin.elim0 (Fin.cast hq i)

theorem tsum_emptyNatTuple_real {q : ℕ} (hq : q = 0)
    (f : (Fin q → ℕ) → ℝ) :
    ∑' p : Fin q → ℕ, f p = f (emptyNatTuple hq) := by
  classical
  apply tsum_eq_single (emptyNatTuple hq)
  intro p hp
  have hpeq : p = emptyNatTuple hq := by
    funext i
    exact Fin.elim0 (Fin.cast hq i)
  exact (hp hpeq).elim

theorem extraTemplate_good {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (s : ℕ) (l : Fin K) (N : ℕ) (p : Fin (extraTemplate s).q → ℕ) :
    (extraTemplate s).Good (corrScales MS) l N p := by
  classical
  change GoodTuple (corrScales MS) l N {1} (1 : IntegerPolynomial 0) p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i j hij
    exact Fin.elim0 i
  · intro P hP
    have hP1 : P = 1 := by simpa using hP
    subst P
    simp [evalIntegerPolynomial]
  · intro π hπ hπN hdiv
    have hdiv' : ((π ^ ((corrScales MS).primeStage.e0 N) : ℕ) : ℤ) ∣ 1 := by
      simpa [evalIntegerPolynomial] using hdiv
    have he0 : 1 ≤ (corrScales MS).primeStage.e0 N := (corrScales MS).primeStage.e0_pos N
    have hpow : 2 ≤ π ^ ((corrScales MS).primeStage.e0 N) := by
      calc
        2 ≤ π := hπ.two_le
        _ = π ^ 1 := by simp
        _ ≤ π ^ ((corrScales MS).primeStage.e0 N) :=
          Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hπ.two_le) he0
    have hdvd : π ^ ((corrScales MS).primeStage.e0 N) ∣ 1 :=
      Int.natCast_dvd_natCast.mp hdiv'
    have hle : π ^ ((corrScales MS).primeStage.e0 N) ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
    omega

noncomputable def extraTemplateEmptyTuple (s : ℕ) : Fin (extraTemplate s).q → ℕ :=
  emptyNatTuple (by rfl)

theorem independentPrimePoolMass_finZero (lo hi : Fin 0 → ℕ) (p : Fin 0 → ℕ) :
    independentPrimePoolMass lo hi p = 1 := by
  simp [independentPrimePoolMass]

theorem extraTemplate_goodSlotProbability_eq_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (s : ℕ) (l : Fin K) (N : ℕ) :
    gapSlotProbability (corrScales MS) l N ((extraTemplate s).Good (corrScales MS) l N) = 1 := by
  have hgood (p : Fin (extraTemplate s).q → ℕ) := extraTemplate_good MS s l N p
  unfold gapSlotProbability independentPrimePoolProbability
  rw [tsum_emptyNatTuple_real (by rfl)]
  have hgood0 := hgood (emptyNatTuple (by rfl))
  have hmass : independentPrimePoolMass
      (fun _ : Fin (extraTemplate s).q => ((corrScales MS).primeStage.pool N l).lower)
      (fun _ : Fin (extraTemplate s).q => ((corrScales MS).primeStage.pool N l).upper)
      (emptyNatTuple (by rfl)) = 1 := by
    change independentPrimePoolMass
      (fun _ : Fin 0 => ((corrScales MS).primeStage.pool N l).lower)
      (fun _ : Fin 0 => ((corrScales MS).primeStage.pool N l).upper)
      (emptyNatTuple (rfl)) = 1
    exact independentPrimePoolMass_finZero _ _ _
  rw [if_pos hgood0]
  rw [hmass]
  norm_num

theorem extraTemplate_goodSlotAverage_eq {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (s : ℕ) (l : Fin K) (N : ℕ) (F : (Fin (extraTemplate s).q → ℕ) → ℝ) :
    goodSlotAverage (corrScales MS) l N ((extraTemplate s).Good (corrScales MS) l N) F =
      F (extraTemplateEmptyTuple s) := by
  have hgood (p : Fin (extraTemplate s).q → ℕ) := extraTemplate_good MS s l N p
  unfold goodSlotAverage
  rw [extraTemplate_goodSlotProbability_eq_one]
  rw [tsum_emptyNatTuple_real (by rfl)]
  have hgood0 := hgood (emptyNatTuple (by rfl))
  have hmass : gapSlotMass (corrScales MS) l N
      (emptyNatTuple (by rfl)) = 1 := by
    unfold gapSlotMass
    change independentPrimePoolMass
      (fun _ : Fin 0 => ((corrScales MS).primeStage.pool N l).lower)
      (fun _ : Fin 0 => ((corrScales MS).primeStage.pool N l).upper)
      (emptyNatTuple (rfl)) = 1
    exact independentPrimePoolMass_finZero _ _ _
  rw [if_pos hgood0]
  simp only [extraTemplate] at hmass ⊢
  rw [hmass]
  simp [gapSlotMass, independentPrimePoolMass, extraTemplateEmptyTuple, emptyNatTuple]
  rfl

theorem extraTemplate_dualTest_eq {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (s : ℕ) (l : Fin K) (J0 N : ℕ)
    (I : DualInput MS B (extraTemplate s) N) (y : ℤ) :
    dualTest MS B (extraTemplate s) l J0 N I y =
      I.e (extraTemplateEmptyTuple s) * shiftAverage (Fin (extraTemplate s).d)
        ((extraTemplate s).length (corrScales MS) l J0 N (extraTemplateEmptyTuple s)) (fun u =>
          ∏ ω ∈ (Finset.univ : Finset (Finset (Fin (extraTemplate s).d))).erase ∅,
            I.g ω (extraTemplateEmptyTuple s)
              (y + ((extraTemplate s).modulus (corrScales MS) N (extraTemplateEmptyTuple s) : ℤ) *
                ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))) := by
  unfold dualTest
  rw [extraTemplate_goodSlotAverage_eq]

theorem shiftAverage_abs_le_one {d L : ℕ} (hd : 0 < d)
    (F : (Fin d → Fin 2 → ℕ) → ℝ) (hF : ∀ u, |F u| ≤ 1) :
    |shiftAverage (Fin d) L F| ≤ 1 := by
  classical
  let U : Finset (Fin d → Fin 2 → ℕ) :=
    Fintype.piFinset (fun _ : Fin d =>
      Fintype.piFinset (fun _ : Fin 2 => Finset.range L))
  by_cases hL : L = 0
  · subst L
    have hU : U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have hu' : u ∈ Fintype.piFinset (fun _ : Fin d =>
          Fintype.piFinset (fun _ : Fin 2 => Finset.range 0)) := by
        simpa [U] using hu
      have huOuter := Fintype.mem_piFinset.mp hu'
      let j : Fin d := ⟨0, hd⟩
      have huInner := Fintype.mem_piFinset.mp (huOuter j)
      have hlt := Finset.mem_range.mp (huInner (0 : Fin 2))
      omega
    unfold shiftAverage
    rw [show Fintype.piFinset (fun _ : Fin d =>
        Fintype.piFinset (fun _ : Fin 2 => Finset.range 0)) = U by rfl, hU]
    have hexp : 0 < 2 * Fintype.card (Fin d) := by
      simp [Fintype.card_fin]
      omega
    simp [hexp.ne']
  · have hLpos : 0 < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hL
    have hinner :
        (Fintype.piFinset (fun _ : Fin 2 => Finset.range L)).card = L ^ 2 := by
      simp
    have hcard : U.card = L ^ (2 * Fintype.card (Fin d)) := by
      calc
        U.card = (L ^ 2) ^ d := by simp [U, hinner]
        _ = L ^ (2 * Fintype.card (Fin d)) := by
          rw [Fintype.card_fin, ← pow_mul]
    have hcardR : (U.card : ℝ) = (L : ℝ) ^ (2 * Fintype.card (Fin d)) := by
      exact_mod_cast hcard
    have hden : 0 < (U.card : ℝ) := by
      rw [hcardR]
      apply pow_pos hLpos
    have hsumAbs :
        |∑ u ∈ U, F u| ≤ ∑ u ∈ U, |F u| := by
      simpa [Real.norm_eq_abs] using (norm_sum_le U F)
    have hsumBound : |∑ u ∈ U, F u| ≤ (U.card : ℝ) := by
      calc
        |∑ u ∈ U, F u| ≤ ∑ u ∈ U, |F u| := hsumAbs
        _ ≤ ∑ u ∈ U, 1 := Finset.sum_le_sum fun u hu => hF u
        _ = (U.card : ℝ) := by simp
    unfold shiftAverage
    rw [show Fintype.piFinset (fun _ : Fin d =>
        Fintype.piFinset (fun _ : Fin 2 => Finset.range L)) = U by rfl, ← hcardR]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hden.le)]
    calc
      (U.card : ℝ)⁻¹ * |∑ u ∈ U, F u| ≤ (U.card : ℝ)⁻¹ * (U.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsumBound (inv_nonneg.mpr hden.le)
      _ = 1 := by field_simp [ne_of_gt hden]

theorem shiftAverage_sub_const_abs_le {d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (F : (Fin d → Fin 2 → ℕ) → ℝ) (c δ : ℝ)
    (hF : ∀ u, |F u - c| ≤ δ) :
    |shiftAverage (Fin d) L F - c| ≤ δ := by
  classical
  let U : Finset (Fin d → Fin 2 → ℕ) :=
    Fintype.piFinset (fun _ : Fin d =>
      Fintype.piFinset (fun _ : Fin 2 => Finset.range L))
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
  have hinner :
      (Fintype.piFinset (fun _ : Fin 2 => Finset.range L)).card = L ^ 2 := by
    simp
  have hcard : U.card = L ^ (2 * Fintype.card (Fin d)) := by
    calc
      U.card = (L ^ 2) ^ d := by simp [U, hinner]
      _ = L ^ (2 * Fintype.card (Fin d)) := by
        rw [Fintype.card_fin, ← pow_mul]
  have hcardR : (U.card : ℝ) = (L : ℝ) ^ (2 * Fintype.card (Fin d)) := by
    exact_mod_cast hcard
  have hden : 0 < (U.card : ℝ) := by
    rw [hcardR]
    exact pow_pos hLpos _
  have hsumSub :
      (∑ u ∈ U, (F u - c)) = (∑ u ∈ U, F u) - c * (U.card : ℝ) := by
    simp [Finset.sum_sub_distrib]
    ring
  have havgEq :
      (U.card : ℝ)⁻¹ * (∑ u ∈ U, F u) - c =
        (U.card : ℝ)⁻¹ * (∑ u ∈ U, (F u - c)) := by
    rw [hsumSub]
    field_simp [ne_of_gt hden]
  have hsumBound :
      |∑ u ∈ U, (F u - c)| ≤ (U.card : ℝ) * δ := by
    calc
      |∑ u ∈ U, (F u - c)| ≤ ∑ u ∈ U, |F u - c| := by
        simpa [Real.norm_eq_abs] using
          (norm_sum_le U (fun u => F u - c))
      _ ≤ ∑ u ∈ U, δ := Finset.sum_le_sum fun u _ => hF u
      _ = (U.card : ℝ) * δ := by simp
  unfold shiftAverage
  rw [show Fintype.piFinset (fun _ : Fin d =>
      Fintype.piFinset (fun _ : Fin 2 => Finset.range L)) = U by rfl, ← hcardR]
  rw [havgEq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hden.le)]
  calc
    (U.card : ℝ)⁻¹ * |∑ u ∈ U, (F u - c)| ≤
        (U.card : ℝ)⁻¹ * ((U.card : ℝ) * δ) :=
      mul_le_mul_of_nonneg_left hsumBound (inv_nonneg.mpr hden.le)
    _ = δ := by field_simp [ne_of_gt hden]

theorem extraDualTest_abs_le_one {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (s : ℕ) (l : Fin K) (J0 N : ℕ)
    (I : DualInput MS B (extraTemplate s) N)
    (he : ∀ p, I.e p = 1) (hg : ∀ ω p y, |I.g ω p y| ≤ 1) (y : ℤ) :
    |dualTest MS B (extraTemplate s) l J0 N I y| ≤ 1 := by
  have hd : 0 < (extraTemplate s).d := by simp [extraTemplate]
  rw [extraTemplate_dualTest_eq]
  rw [he (extraTemplateEmptyTuple s)]
  simp only [one_mul]
  apply shiftAverage_abs_le_one hd
  intro u
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro ω hω
    exact abs_nonneg _
  · intro ω hω
    exact hg ω (extraTemplateEmptyTuple s)
      (y + ((extraTemplate s).modulus (corrScales MS) N (extraTemplateEmptyTuple s) : ℤ) *
        ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))

theorem pivotSamplingEventually {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (i : Fin K) :
    ∀ᶠ N in atTop,
      2 ≤ MS.core.parameters.X N i ∧
        Real.log (MS.core.parameters.X N i : ℝ) >
          (primorial (N + 1) : ℝ) / (MS.core.parameters.X N i : ℝ) := by
  let A := MS.core.parameters
  have hXreal : Tendsto (fun N => (A.X N i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (A.Xtendsto i)
  have hlog : Tendsto (fun N => Real.log (A.X N i : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hXreal
  filter_upwards [hlog.eventually_ge_atTop 1] with N hlogN
  have hraw : 4 * primorial (N + 1) ≤ A.X N i := MS.gapStage.valid_raw_cutoffs N i
  have hWpos : 0 < primorial (N + 1) := primorial_pos _
  have hXpos : 0 < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
  have hWratio : (primorial (N + 1) : ℝ) / (A.X N i : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hXpos).2
    have hrawR : 4 * (primorial (N + 1) : ℝ) ≤ (A.X N i : ℝ) := by exact_mod_cast hraw
    nlinarith
  have hX2 : 2 ≤ A.X N i := by omega
  exact ⟨hX2, by linarith⟩

theorem harmonicDilationUniformError_mono (X W k V : ℕ) (hX : 0 < X)
    (hk : 1 ≤ k) (hkv : k ≤ V) (hden : 0 < Real.log (X : ℝ) - (W : ℝ) / X) :
    harmonicDilationUniformError X W k ≤ harmonicDilationUniformError X W V := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (le_trans hk hkv))
  have hkvR : (k : ℝ) ≤ (V : ℝ) := by exact_mod_cast hkv
  have hlog : Real.log (k : ℝ) ≤ Real.log (V : ℝ) := Real.log_le_log hkpos hkvR
  have hmul : (W : ℝ) * (k : ℝ) ≤ (W : ℝ) * (V : ℝ) :=
    mul_le_mul_of_nonneg_left hkvR (by positivity)
  have hfrac : (W : ℝ) * (k : ℝ) / X ≤ (W : ℝ) * (V : ℝ) / X :=
    div_le_div_of_nonneg_right hmul (by positivity)
  have hterm :
      (W : ℝ) * (k : ℝ) / X * (1 + 1 / X) ≤
        (W : ℝ) * (V : ℝ) / X * (1 + 1 / X) :=
    mul_le_mul_of_nonneg_right hfrac (by positivity)
  unfold harmonicDilationUniformError
  apply div_le_div_of_nonneg_right
  · nlinarith
  · exact hden.le

theorem boundaryRadiusProperties (width σ : ℕ) (hσ : 0 < σ) :
    width < σ * (width / σ + 1) ∧ width / σ + 1 ≤ width + 1 := by
  have hdecomp : width % σ + σ * (width / σ) = width := Nat.mod_add_div _ _
  have hmod : width % σ < σ := Nat.mod_lt _ hσ
  constructor
  · rw [Nat.mul_add, Nat.mul_one]
    omega
  · have hdiv : width / σ ≤ width := Nat.div_le_self _ _
    omega

theorem boundarySigmaSumBound (width W σ V : ℕ) (hσ : 0 < σ) (hσV : σ ≤ V) :
    σ * (width / σ + 1 + W + 1) ≤ width + V * (W + 2) ∧
      width / σ + 1 + W + 1 ≤ width + W + 2 := by
  have hrad := boundaryRadiusProperties width σ hσ
  have hquot : σ * (width / σ) ≤ width := by
    simpa [Nat.mul_comm] using (Nat.div_mul_le_self width σ)
  have hσR : σ * (width / σ + 1) ≤ width + σ := by
    calc
      σ * (width / σ + 1) = σ * (width / σ) + σ := by rw [Nat.mul_add]; simp
      _ ≤ width + σ := Nat.add_le_add_right hquot σ
  constructor
  · calc
      σ * (width / σ + 1 + W + 1) =
          σ * (width / σ + 1) + σ * (W + 1) := by ring
      _ ≤ width + σ + σ * (W + 1) := Nat.add_le_add_right hσR _
      _ = width + σ * (W + 2) := by ring
      _ ≤ width + V * (W + 2) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right (W + 2) hσV) width
  · omega

/-- A strip under a dilation is contained in the raw arithmetic bad set. The support guard
makes the radius bound valid whenever the indicator is nonzero. -/
theorem harmonicDilation_boundary_raw_bound (X W H width σ : ℕ)
    (hW : 0 < W) (hX : 4 * W ≤ X) (hH : 0 < H) (hσ : 0 < σ)
    (hRle : width / σ + 1 ≤ X) :
    (∑' y : ℤ, dilatedLaw (harmonicLaw X W) σ y * pkgDBoundaryIndicator H width y) ≤
      168 * (σ : ℝ) * ((width / σ + 1 + W + 1 : ℕ) : ℝ) / H +
        112 * ((width / σ + 1 + W + 1 : ℕ) : ℝ) / X := by
  classical
  let R : ℕ := width / σ + 1
  let S : Finset ℤ := harmonicIntSupport X W
  let f : ℤ → ℝ := fun z =>
    if z ∈ S then pkgDBoundaryIndicator H width ((σ : ℤ) * z) else 0
  have hμzero : ∀ z ∉ S, harmonicLaw X W z = 0 := by
    intro z hz
    exact pkgD_harmonicLaw_zero_of_not_mem X W z (by simpa [S] using hz)
  have hf0 : ∀ z, 0 ≤ f z := by
    intro z
    by_cases hz : z ∈ S
    · simp [f, hz, pkgDBoundaryIndicator]
      split_ifs <;> norm_num
    · simp [f, hz]
  have hf1 : ∀ z, f z ≤ 1 := by
    intro z
    by_cases hz : z ∈ S
    · simp [f, hz, pkgDBoundaryIndicator]
      split_ifs <;> norm_num
    · simp [f, hz]
  have hwidth := boundaryRadiusProperties width σ hσ
  have hbad : ∀ p : ℕ, f (p : ℤ) ≠ 0 →
      σ * (p - R) / H ≠ σ * (p + R) / H := by
    intro p hp
    have hpInt : (p : ℤ) ∈ S := by
      by_contra hnot
      have hfzero : f (p : ℤ) = 0 := by simp [f, hnot]
      exact hp hfzero
    have hpSupport : p ∈ harmonicNatSupport X W := by
      have himage : (p : ℤ) ∈ (harmonicNatSupport X W).image (fun q : ℕ => (q : ℤ)) := by
        simpa only [S, harmonicIntSupport] using hpInt
      obtain ⟨q, hq, hcast⟩ := Finset.mem_image.mp himage
      have hqp : q = p := Int.ofNat.inj hcast
      simpa [hqp] using hq
    have hpIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hpSupport).1
    have hRp : R ≤ p := hRle.trans hpIco.1
    have hindicator : pkgDBoundaryIndicator H width ((σ : ℤ) * (p : ℤ)) ≠ 0 := by
      have heq : f (p : ℤ) = pkgDBoundaryIndicator H width ((σ : ℤ) * (p : ℤ)) := by
        dsimp [f]
        rw [if_pos hpInt]
      rw [heq] at hp
      exact hp
    have hstrip : pkgDBoundaryStrip H width ((σ : ℤ) * (p : ℤ)) := by
      by_contra hnot
      simp [pkgDBoundaryIndicator, hnot] at hindicator
    have hstripNat : (σ * p) % H ≤ width ∨ H ≤ (σ * p) % H + width := by
      have hstripCast :
          ((σ * p % H : ℕ) : ℤ) ≤ (width : ℤ) ∨
            (H : ℤ) ≤ ((σ * p % H : ℕ) : ℤ) + (width : ℤ) := by
        simpa [pkgDBoundaryStrip, Int.natCast_mul, Int.natCast_emod] using hstrip
      exact_mod_cast hstripCast
    exact strip_mul_subset_rawBad H width σ p R hH hσ hRp hwidth.1 hstripNat
  have hraw := harmonic_event_rawBad_bound X W H σ R hW hX hH hRle f hf0 hf1 hbad
  have hpair := dilatedLaw_pairing (harmonicLaw X W) σ hσ S hμzero
    (pkgDBoundaryIndicator H width)
  have hreduce :
      (∑' z : ℤ, harmonicLaw X W z *
        pkgDBoundaryIndicator H width ((σ : ℤ) * z)) =
      (∑' z : ℤ, harmonicLaw X W z * f z) := by
    rw [harmonicLaw_tsum_eq_natSum X W
      (fun z => pkgDBoundaryIndicator H width ((σ : ℤ) * z)),
      harmonicLaw_tsum_eq_natSum X W f]
    apply Finset.sum_congr rfl
    intro p hp
    have hpInt : (p : ℤ) ∈ S := by
      change (p : ℤ) ∈ S
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    simp [f, hpInt, Int.natCast_mul]
  have hOAI := raw_boundary_bound X W σ H R hW hX hσ hH hRle
  calc
    _ = ∑' z : ℤ, harmonicLaw X W z *
        pkgDBoundaryIndicator H width ((σ : ℤ) * z) := hpair
    _ = ∑' z : ℤ, harmonicLaw X W z * f z := hreduce
    _ ≤ OAI.DyadicHarmonicBoundary.badMass X (X ^ 2) W σ H R /
        OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W := hraw
    _ ≤ _ := by simpa [R] using hOAI

theorem harmonicReference_boundary_le (X W H width σ V : ℕ)
    (hW : 0 < W) (hX : 4 * W ≤ X) (hXpos : 0 < X) (hX2 : 2 ≤ X)
    (hlog : Real.log (X : ℝ) > (W : ℝ) / X) (hH : 0 < H)
    (hσ : 0 < σ) (hσV : σ ≤ V) (hVX : V ≤ X)
    (hcop : Nat.Coprime σ W) (hRle : width / σ + 1 ≤ X) :
    (∑' y : ℤ, dilationReference (harmonicLaw X W) σ y * pkgDBoundaryIndicator H width y) ≤
        168 * (σ : ℝ) * ((width / σ + 1 + W + 1 : ℕ) : ℝ) / H +
          112 * ((width / σ + 1 + W + 1 : ℕ) : ℝ) / X +
            harmonicDilationUniformError X W V := by
  let b : ℤ → ℝ := pkgDBoundaryIndicator H width
  let refPair : ℝ := ∑' y : ℤ,
    dilationReference (harmonicLaw X W) σ y * b y
  let dilPair : ℝ := ∑' y : ℤ, dilatedLaw (harmonicLaw X W) σ y * b y
  have hb : ∀ y, |b y| ≤ 1 := by
    intro y
    classical
    unfold b pkgDBoundaryIndicator
    split_ifs <;> norm_num
  have hL1 := dilationReference_pairing_l1 X W σ hσ b hb
  have hsamp := sampling_pointwise_claim X W hW hX2 hlog
  have hDilation := hsamp.dilation hX2 hlog σ
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hσ)) (le_trans hσV hVX) hcop
  have hden : 0 < Real.log (X : ℝ) - (W : ℝ) / X := by linarith
  have hmono := harmonicDilationUniformError_mono X W σ V hXpos
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hσ)) hσV hden
  have hdiff : |refPair - dilPair| ≤ harmonicDilationUniformError X W V := by
    dsimp [refPair, dilPair, b]
    exact hL1.trans (hDilation.1.trans hmono)
  have hraw := harmonicDilation_boundary_raw_bound X W H width σ hW hX hH hσ hRle
  have hupper : refPair ≤ dilPair + harmonicDilationUniformError X W V := by
    have hle := le_abs_self (refPair - dilPair)
    linarith [hdiff]
  calc
    _ = refPair := rfl
    _ ≤ dilPair + harmonicDilationUniformError X W V := hupper
    _ ≤ 168 * (σ : ℝ) * ((width / σ + 1 + W + 1 : ℕ) : ℝ) / H +
          112 * ((width / σ + 1 + W + 1 : ℕ) : ℝ) / X +
            harmonicDilationUniformError X W V := by
          exact add_le_add hraw le_rfl

theorem harmonicResidueError_le_two_dilation (X W σ V : ℕ)
    (hX : 0 < X) (hV : 1 ≤ V) (hσV : σ ≤ V)
    (hden : 0 < Real.log (X : ℝ) - (W : ℝ) / X) :
    harmonicResidueError X W σ ≤ 2 * harmonicDilationUniformError X W V := by
  have hVreal : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hσplus : (σ : ℝ) + 1 ≤ 2 * (V : ℝ) := by
    have hσreal : (σ : ℝ) ≤ (V : ℝ) := by exact_mod_cast hσV
    exact_mod_cast (show σ + 1 ≤ 2 * V by omega)
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hWnonneg : 0 ≤ (W : ℝ) := by positivity
  have hnumResidue :
      (W : ℝ) * ((σ + 1 : ℕ) : ℝ) / X ≤ 2 * ((W : ℝ) * (V : ℝ) / X) := by
    have hprod := mul_le_mul_of_nonneg_left hσplus hWnonneg
    have hdiv := div_le_div_of_nonneg_right hprod (by positivity : 0 ≤ (X : ℝ))
    calc
      _ ≤ (W : ℝ) * (2 * (V : ℝ)) / X := by simpa using hdiv
      _ = 2 * ((W : ℝ) * (V : ℝ) / X) := by ring
  have hlogV : 0 ≤ Real.log (V : ℝ) := Real.log_nonneg hVreal
  have hterm : 0 ≤ (W : ℝ) * (V : ℝ) / X := by positivity
  have hinvX : 0 ≤ 1 / (X : ℝ) := by positivity
  have hfac : 1 ≤ 1 + 1 / (X : ℝ) := by linarith
  have hnumDilation :
      (W : ℝ) * (V : ℝ) / X ≤
        2 * Real.log (V : ℝ) + (W : ℝ) * (V : ℝ) / X * (1 + 1 / (X : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hfac hterm
    nlinarith
  have hnum :
      (W : ℝ) * ((σ + 1 : ℕ) : ℝ) / X ≤
        2 * (2 * Real.log (V : ℝ) + (W : ℝ) * (V : ℝ) / X * (1 + 1 / (X : ℝ))) := by
    nlinarith [hnumResidue, hnumDilation]
  have hresEq : harmonicResidueError X W σ =
      ((W : ℝ) * ((σ + 1 : ℕ) : ℝ) / X) /
        (Real.log (X : ℝ) - (W : ℝ) / X) := by
    unfold harmonicResidueError
    push_cast
    field_simp [ne_of_gt hXreal, ne_of_gt hden]
  rw [hresEq]
  unfold harmonicDilationUniformError
  have h := div_le_div_of_nonneg_right hnum hden.le
  convert h using 1 <;> ring

theorem masterScaleV_mono {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (i j : Fin n) (hij : i ≤ j) :
    masterScaleV A N i ≤ masterScaleV A N j := by
  let I : Finset (Fin n) := Finset.univ.filter (fun k => k < i)
  let J : Finset (Fin n) := Finset.univ.filter (fun k => k < j)
  have hsub : I ⊆ J := by
    intro k hk
    change k ∈ Finset.univ.filter (fun x : Fin n => x < i) at hk
    have hki : k < i := (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hki hij⟩
  have hprod : (∏ k ∈ I, (A.X N k) ^ 2) ≤ ∏ k ∈ J, (A.X N k) ^ 2 := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun k _ => Nat.zero_le _)
    intro k hk hknot
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.ne_of_gt (A.Xpos N k)))
  unfold masterScaleV
  dsimp [I, J] at hprod ⊢
  exact Nat.add_le_add_left hprod (2 + A.M N)

theorem pivotEmu_one_plus_nu_le_three {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (l : Fin K) (hl : ValidGap B l) :
    ∀ᶠ N in atTop,
      Emu MS.core.parameters N B.1 (fun y => 1 + nu MS.core.parameters N B y) ≤ 3 := by
  classical
  let A := MS.core.parameters
  let Tail : ℕ → ℕ → ℝ := fun N σ => parameterTailProductLaw A N B.2.val σ
  let Ref : ℕ → ℕ → ℝ := fun N σ =>
    ∑' y : ℤ, dilationReference
      (harmonicLaw (A.X N B.1) (primorial (N + 1))) σ y * 1
  let V : ℕ → ℕ := fun N => masterScaleV A N B.1
  let Bound : ℕ → ℕ := fun N => ∏ j ∈ B.2.val, (A.X N j) ^ 2
  let Sig : ℕ → Finset ℕ := fun N => Finset.range (Bound N + 1)
  have hNorm (N : ℕ) (j : Fin K) :
      0 < harmonicNormalizer (A.X N j) (primorial (N + 1)) :=
    harmonicNormalizer_pos (A.X N j) (primorial (N + 1)) (primorial_pos _)
      (MS.gapStage.valid_raw_cutoffs N j)
  have hTailZero (N σ : ℕ) (hσ : σ ∉ Sig N) : Tail N σ = 0 := by
    apply parameterTailProductLaw_zero_of_gt A N B.2.val σ
    have hnot : ¬ σ < Bound N + 1 := by
      simpa [Sig, Finset.mem_range] using hσ
    change (∏ j ∈ B.2.val, (A.X N j) ^ 2) < σ
    dsimp [Bound] at hnot ⊢
    omega
  have hTailNonneg (N σ : ℕ) : 0 ≤ Tail N σ := by
    dsimp [Tail]
    exact pkgD_parameterTailProductLaw_nonneg A N B.2.val (fun j => hNorm N j) σ
  have hTailSum (N : ℕ) : ∑ σ ∈ Sig N, Tail N σ = 1 := by
    have htotal := parameterTailProductLaw_tsum_one A N B.2.val
      (fun j => A.Xpos N j) (fun j => hNorm N j)
    rw [tsum_eq_sum (s := Sig N) (fun σ hσ => by
      have hz := hTailZero N σ hσ
      simpa [Tail] using hz)] at htotal
    simpa [Tail] using htotal
  have hMuOne (N : ℕ) : Emu A N B.1 (fun _ => 1) = 1 := by
    have hNatSum :
        (∑ n ∈ harmonicNatSupport (A.X N B.1) (primorial (N + 1)),
          harmonicNatLaw (A.X N B.1) (primorial (N + 1)) n) = 1 := by
      have h := harmonicNatLaw_tsum_one (A.X N B.1) (primorial (N + 1))
        (A.Xpos N B.1) (hNorm N B.1)
      rw [tsum_eq_sum
        (s := harmonicNatSupport (A.X N B.1) (primorial (N + 1)))
        (fun n hn => harmonicNatLaw_zero_of_not_mem (A.X N B.1)
          (primorial (N + 1)) n hn)] at h
      exact h
    rw [Emu_eq_harmonicNat_sum]
    simpa using hNatSum
  have hRefBound (N : ℕ) (hX2 : 2 ≤ A.X N B.1)
      (hlog : Real.log (A.X N B.1 : ℝ) >
        (primorial (N + 1) : ℝ) / (A.X N B.1 : ℝ))
      (hVX : V N ≤ A.X N B.1) (σ : ℕ) (hMass : Tail N σ ≠ 0) :
      Ref N σ ≤ 1 + 2 * harmonicDilationUniformError (A.X N B.1)
        (primorial (N + 1)) (V N) := by
    have hcut := tailProductLaw_cutoff_bound MS B l hl N σ (by simpa [Tail] using hMass)
    rcases hcut with ⟨hσpos, hcop, hσV⟩
    have hσV' : σ ≤ V N := by
      exact hσV.trans (masterScaleV_mono A N l B.1 (le_of_lt hl.2))
    have hσone : 1 ≤ σ := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hσpos)
    have hσX : σ ≤ A.X N B.1 := hσV'.trans hVX
    have hsamp := sampling_pointwise_claim (A.X N B.1) (primorial (N + 1))
      (primorial_pos _) hX2 hlog
    have hD := hsamp.dilation hX2 hlog σ hσone hσX hcop
    have hden : 0 < Real.log (A.X N B.1 : ℝ) -
        (primorial (N + 1) : ℝ) / (A.X N B.1 : ℝ) := by linarith
    have hVone : 1 ≤ V N := by
      dsimp [V, masterScaleV]
      omega
    have hres := harmonicResidueError_le_two_dilation
      (A.X N B.1) (primorial (N + 1)) σ (V N) (A.Xpos N B.1)
      hVone hσV' hden
    have hRefErr : |Ref N σ - 1| ≤
        harmonicResidueError (A.X N B.1) (primorial (N + 1)) σ := by
      simpa [Ref] using hD.2
    have hle := le_abs_self (Ref N σ - 1)
    linarith
  have hNuPair (N : ℕ) :
      Emu A N B.1 (fun y => nu A N B y) =
        ∑' σ : ℕ, Tail N σ * Ref N σ := by
    have h := nuWeightedPairing_eq A N B (fun _ : ℤ => (1 : ℝ))
    simpa [Tail, Ref] using h
  have hOuter (N : ℕ) :
      (∑' σ : ℕ, Tail N σ * Ref N σ) =
        ∑ σ ∈ Sig N, Tail N σ * Ref N σ := by
    rw [tsum_eq_sum (s := Sig N) (fun σ hσ => by
      have hz := hTailZero N σ hσ
      simp [Tail, hz])]
  have hNuBound (N : ℕ) (hX2 : 2 ≤ A.X N B.1)
      (hlog : Real.log (A.X N B.1 : ℝ) >
        (primorial (N + 1) : ℝ) / (A.X N B.1 : ℝ))
      (hVX : V N ≤ A.X N B.1) :
      Emu A N B.1 (fun y => nu A N B y) ≤
        1 + 2 * harmonicDilationUniformError (A.X N B.1)
          (primorial (N + 1)) (V N) := by
    rw [hNuPair, hOuter]
    calc
      (∑ σ ∈ Sig N, Tail N σ * Ref N σ) ≤
          ∑ σ ∈ Sig N, Tail N σ *
            (1 + 2 * harmonicDilationUniformError (A.X N B.1)
              (primorial (N + 1)) (V N)) := by
        apply Finset.sum_le_sum
        intro σ hσ
        by_cases hzero : Tail N σ = 0
        · simp [hzero]
        · exact mul_le_mul_of_nonneg_left
            (hRefBound N hX2 hlog hVX σ hzero) (hTailNonneg N σ)
      _ = (∑ σ ∈ Sig N, Tail N σ) *
          (1 + 2 * harmonicDilationUniformError (A.X N B.1)
            (primorial (N + 1)) (V N)) := by rw [Finset.sum_mul]
      _ = 1 + 2 * harmonicDilationUniformError (A.X N B.1)
          (primorial (N + 1)) (V N) := by rw [hTailSum N]; ring
  have hError : ∀ᶠ N in atTop,
      harmonicDilationUniformError (A.X N B.1) (primorial (N + 1)) (V N) ≤ 1 / 2 := by
    have h := (pivotDilationError_tendsto A B.1).1
    filter_upwards [h.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hN
    exact hN.le
  have hVle : ∀ᶠ N in atTop, V N ≤ A.X N B.1 := (pivotDilationError_tendsto A B.1).2
  filter_upwards [pivotSamplingEventually MS B.1, hVle, hError]
    with N ⟨hX2, hlog⟩ hVX hE
  have hmean := hNuBound N hX2 hlog hVX
  rw [pkgD_Emu_add, hMuOne N]
  linarith

theorem masterScaleV_le_earlierScale_sq {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (i : Fin n) :
    (masterScaleV A N i : ℝ) ≤
      (OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N)
        (fun N => OAI.SourceAdmissible.previous (A.X N) i) N) ^ 2 := by
  let P : ℕ → ℕ := fun N => OAI.SourceAdmissible.previous (A.X N) i
  let S : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N) P N
  have hprod :
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => j < i), (A.X N j) ^ 2) = (P N) ^ 2 := by
    dsimp [P, OAI.SourceAdmissible.previous]
    rw [← Finset.prod_pow]
  have hV : (masterScaleV A N i : ℝ) = 2 + (A.M N : ℝ) + (P N : ℝ) ^ 2 := by
    dsimp [masterScaleV]
    rw [hprod]
    push_cast
    rfl
  have hS : S N = 2 + (A.M N : ℝ) + (P N : ℝ) := rfl
  change (masterScaleV A N i : ℝ) ≤ S N ^ 2
  rw [hV, hS]
  have hM : 0 ≤ (A.M N : ℝ) := by positivity
  have hP : 0 ≤ (P N : ℝ) := by positivity
  nlinarith [sq_nonneg (A.M N : ℝ), sq_nonneg (P N : ℝ)]

theorem earlierScalePow_over_H_tendsto {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (i : Fin n) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N =>
      (OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N)
        (fun N => OAI.SourceAdmissible.previous (A.X N) i) N) ^ k /
        (A.H N i : ℝ)) atTop (𝓝 0) := by
  let S : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N)
      (fun N => OAI.SourceAdmissible.previous (A.X N) i) N
  have hSpos (N : ℕ) : 0 < S N := by
    rw [show S N = 2 + (A.M N : ℝ) +
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) by rfl]
    positivity
  have hHpos (N : ℕ) : 0 < (A.H N i : ℝ) := by exact_mod_cast A.Hpos N i
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hdom : Tendsto (fun N => (A.H N i : ℝ) / (S N) ^ k) atTop atTop := by
    simpa [S, OAI.AdmissibleMicrocellBoundary.earlierScale,
      OAI.SourceAdmissible.previous, Real.rpow_natCast] using A.Hdom i (k : ℝ) hkR
  have hinv : Tendsto (fun N => ((A.H N i : ℝ) / (S N) ^ k)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hdom
  apply hinv.congr'
  filter_upwards with N
  have hpow : (S N) ^ k ≠ 0 := ne_of_gt (pow_pos (hSpos N) k)
  change ((A.H N i : ℝ) / (S N) ^ k)⁻¹ = (S N) ^ k / (A.H N i : ℝ)
  field_simp [hpow, ne_of_gt (hHpos N)]

theorem earlierScale_le_H_eventually {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (i : Fin n) :
    ∀ᶠ N in atTop,
      OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N)
        (fun N => OAI.SourceAdmissible.previous (A.X N) i) N ≤ (A.H N i : ℝ) := by
  let S : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N)
      (fun N => OAI.SourceAdmissible.previous (A.X N) i) N
  have hSpos (N : ℕ) : 0 < S N := by
    rw [show S N = 2 + (A.M N : ℝ) +
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) by rfl]
    positivity
  have hdom : Tendsto (fun N => (A.H N i : ℝ) / S N) atTop atTop := by
    simpa [S, OAI.AdmissibleMicrocellBoundary.earlierScale,
      OAI.SourceAdmissible.previous, Real.rpow_natCast] using A.Hdom i (1 : ℝ) (by norm_num)
  filter_upwards [hdom.eventually_ge_atTop 1] with N hN
  change S N ≤ (A.H N i : ℝ)
  simpa using (le_div_iff₀ (hSpos N)).1 hN

theorem gapScale_multiple_le_eventually {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (i : Fin n) (q : ℕ) :
    ∀ᶠ N in atTop, q * A.M N ≤ A.H N i := by
  let S : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N)
      (fun N => OAI.SourceAdmissible.previous (A.X N) i) N
  have hSpos (N : ℕ) : 0 < S N := by
    rw [show S N = 2 + (A.M N : ℝ) +
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) by rfl]
    positivity
  have hMleS (N : ℕ) : (A.M N : ℝ) ≤ S N := by
    rw [show S N = 2 + (A.M N : ℝ) +
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) by rfl]
    have hP : 0 ≤ (OAI.SourceAdmissible.previous (A.X N) i : ℝ) := Nat.cast_nonneg _
    linarith
  have hdom : Tendsto (fun N => (A.H N i : ℝ) / S N) atTop atTop := by
    simpa [S, OAI.AdmissibleMicrocellBoundary.earlierScale,
      OAI.SourceAdmissible.previous, Real.rpow_natCast] using
      A.Hdom i (1 : ℝ) (by norm_num)
  filter_upwards [hdom.eventually_gt_atTop (q : ℝ)] with N hN
  have hratio : (q : ℝ) * S N < (A.H N i : ℝ) :=
    (lt_div_iff₀ (hSpos N)).1 hN
  have hmul : (q : ℝ) * (A.M N : ℝ) ≤ (q : ℝ) * S N :=
    mul_le_mul_of_nonneg_left (hMleS N) (by positivity)
  have hreal : (q : ℝ) * (A.M N : ℝ) ≤ (A.H N i : ℝ) := hmul.trans hratio.le
  have hcast : ((q * A.M N : ℕ) : ℝ) ≤ (A.H N i : ℝ) := by
    simpa [Nat.cast_mul] using hreal
  exact_mod_cast hcast

theorem weighted_boundary_aux (s : ℕ) :
    ∃ C : ℝ, ∀ {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
      (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K), ValidGap B l →
      ∀ J0 : ℕ, 0 < J0 → ∀ ε > 0, ∀ᶠ N in atTop,
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          pkgDBoundaryIndicator (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J0) y) ≤ C / J0 + ε := by
  classical
  let d : ℕ := s + 1
  refine ⟨1000 * (d : ℝ), ?_⟩
  intro K sl As Dm MS B l hl J0 hJ0 ε hε
  let A := MS.core.parameters
  let W : ℕ → ℕ := fun N => primorial (N + 1)
  let H : ℕ → ℕ := fun N => A.H N l
  let X : ℕ → ℕ := fun N => A.X N B.1
  let Width : ℕ → ℕ := fun N => d * H N / J0
  let Vtail : ℕ → ℕ := fun N => masterScaleV A N l
  let Vpivot : ℕ → ℕ := fun N => masterScaleV A N B.1
  let Scale : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale (fun N => A.M N)
      (fun N => OAI.SourceAdmissible.previous (A.X N) l) N
  let Err : ℕ → ℝ := fun N =>
    168 * ((W N + 2 : ℕ) : ℝ) / (H N : ℝ) +
      168 * ((Vtail N * (W N + 2) : ℕ) : ℝ) / (H N : ℝ) +
      224 * ((Width N + W N + 2 : ℕ) : ℝ) / (X N : ℝ) +
      harmonicDilationUniformError (X N) (W N) (Vpivot N)
  let BaseRaw : ℕ → ℝ := fun N =>
    168 * ((Width N + W N + 2 : ℕ) : ℝ) / (H N : ℝ) +
      112 * ((Width N + W N + 2 : ℕ) : ℝ) / (X N : ℝ)
  let TailRaw : ℕ → ℝ := fun N =>
    168 * (Width N : ℝ) / (H N : ℝ) +
      168 * (Vtail N : ℝ) * ((W N + 2 : ℕ) : ℝ) / (H N : ℝ) +
      112 * ((Width N + W N + 2 : ℕ) : ℝ) / (X N : ℝ) +
      harmonicDilationUniformError (X N) (W N) (Vpivot N)
  have hJ0real : 0 < (J0 : ℝ) := by exact_mod_cast hJ0
  have hwidthRatio (N : ℕ) :
    (Width N : ℝ) / (H N : ℝ) ≤ (d : ℝ) / J0 := by
    have hnat : Width N * J0 ≤ d * H N := by
      dsimp [Width, H]
      exact Nat.div_mul_le_self (d * A.H N l) J0
    rw [div_le_div_iff₀ (by exact_mod_cast A.Hpos N l) hJ0real]
    exact_mod_cast hnat
  have hGap : Tendsto (fun N => (H N : ℝ) / (X N : ℝ)) atTop (𝓝 0) := by
    simpa [H, X] using earlierGapOverPivot_tendsto A l B.1 hl.2
  have hSone (N : ℕ) : 1 ≤ Scale N := by
    change 1 ≤ (2 : ℝ) + (A.M N : ℝ) +
      (OAI.SourceAdmissible.previous (A.X N) l : ℝ)
    have hM : 0 ≤ (A.M N : ℝ) := Nat.cast_nonneg _
    have hp : 0 ≤ (OAI.SourceAdmissible.previous (A.X N) l : ℝ) := Nat.cast_nonneg _
    linarith
  have hWplusScale (N : ℕ) : ((W N + 2 : ℕ) : ℝ) ≤ Scale N := by
    have hNat : primorial (N + 1) + 2 ≤
        2 + A.M N + OAI.SourceAdmissible.previous (A.X N) l := by
      have hW := A.Wle N
      omega
    change ((primorial (N + 1) + 2 : ℕ) : ℝ) ≤
      2 + (A.M N : ℝ) + (OAI.SourceAdmissible.previous (A.X N) l : ℝ)
    exact_mod_cast hNat
  have hScale2 : Tendsto (fun N => Scale N ^ 2 / (H N : ℝ)) atTop (𝓝 0) := by
    simpa [Scale, H] using earlierScalePow_over_H_tendsto A l 2 (by norm_num)
  have hScale4 : Tendsto (fun N => Scale N ^ 4 / (H N : ℝ)) atTop (𝓝 0) := by
    simpa [Scale, H] using earlierScalePow_over_H_tendsto A l 4 (by norm_num)
  have hScaleOverH : Tendsto (fun N => Scale N / (H N : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun N => by
        apply div_nonneg
        · exact le_of_lt (lt_of_lt_of_le (by norm_num) (hSone N))
        · exact le_of_lt (by exact_mod_cast A.Hpos N l)))
      ?_ hScale2
    filter_upwards with N
    have hSq : Scale N ≤ Scale N ^ 2 := by nlinarith [hSone N]
    exact div_le_div_of_nonneg_right hSq (by positivity)
  have hWplusOverH : Tendsto (fun N => (W N + 2 : ℕ) / (H N : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
      ?_ hScaleOverH
    filter_upwards with N
    exact div_le_div_of_nonneg_right (hWplusScale N) (by positivity)
  have hVtailOverH : Tendsto (fun N =>
      (Vtail N * (W N + 2 : ℕ) : ℕ) / (H N : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
      ?_ hScale4
    filter_upwards with N
    have hV : (Vtail N : ℝ) ≤ Scale N ^ 2 := by
      simpa [Vtail, Scale] using masterScaleV_le_earlierScale_sq A N l
    have hprod := mul_le_mul hV (hWplusScale N)
      (by positivity : 0 ≤ ((W N + 2 : ℕ) : ℝ)) (by positivity : 0 ≤ Scale N ^ 2)
    have hS3 : Scale N ^ 3 ≤ Scale N ^ 4 := by
      have hS3nonneg : 0 ≤ Scale N ^ 3 :=
        pow_nonneg (le_trans (by norm_num) (hSone N)) 3
      calc
        Scale N ^ 3 = Scale N ^ 3 * 1 := by ring
        _ ≤ Scale N ^ 3 * Scale N :=
          mul_le_mul_of_nonneg_left (hSone N) hS3nonneg
        _ = Scale N ^ 4 := by ring
    have hnum : (Vtail N : ℝ) * ((W N + 2 : ℕ) : ℝ) ≤ Scale N ^ 4 := by
      calc
        _ ≤ Scale N ^ 2 * Scale N := hprod
        _ = Scale N ^ 3 := by ring
        _ ≤ Scale N ^ 4 := hS3
    have hnumCast : ((Vtail N * (W N + 2 : ℕ) : ℕ) : ℝ) ≤ Scale N ^ 4 := by
      simpa [Nat.cast_mul] using hnum
    exact div_le_div_of_nonneg_right hnumCast (by
      exact le_of_lt (by exact_mod_cast A.Hpos N l))
  have hScaleLeH := earlierScale_le_H_eventually A l
  have hWplusOverX : Tendsto (fun N => (W N + 2 : ℕ) / (X N : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
      ?_ hGap
    filter_upwards [hScaleLeH] with N hSH
    have hnum : ((W N + 2 : ℕ) : ℝ) ≤ (H N : ℝ) :=
      (hWplusScale N).trans hSH
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hWidthOverX : Tendsto (fun N => (Width N : ℝ) / (X N : ℝ))
      atTop (𝓝 0) := by
    have hupper : ∀ᶠ N in atTop,
        (Width N : ℝ) / (X N : ℝ) ≤ ((d : ℝ) / J0) * ((H N : ℝ) / (X N : ℝ)) := by
      filter_upwards with N
      have hratio := hwidthRatio N
      have hHnonneg : 0 ≤ (H N : ℝ) := Nat.cast_nonneg _
      have hXnonneg : 0 ≤ (X N : ℝ) := Nat.cast_nonneg _
      have hfactor : 0 ≤ (H N : ℝ) / (X N : ℝ) :=
        div_nonneg hHnonneg hXnonneg
      have hmul := mul_le_mul_of_nonneg_right hratio hfactor
      have hHneq : (H N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast A.Hpos N l)
      have hXneq : (X N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast A.Xpos N B.1)
      have heq : (Width N : ℝ) / (X N : ℝ) =
          ((Width N : ℝ) / (H N : ℝ)) * ((H N : ℝ) / (X N : ℝ)) := by
        field_simp [hHneq, hXneq]
      rw [heq]
      simpa [mul_assoc] using hmul
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun N => div_nonneg (by positivity) (by positivity)))
      hupper (by simpa [mul_zero] using
        Filter.Tendsto.const_mul ((d : ℝ) / J0) hGap)
  have hSumOverX : Tendsto (fun N => (Width N + W N + 2 : ℕ) / (X N : ℝ))
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun N => (Width N : ℝ) / (X N : ℝ) +
        ((W N + 2 : ℕ) : ℝ) / (X N : ℝ)) atTop (𝓝 0) :=
      by simpa using hWidthOverX.add hWplusOverX
    apply hsum.congr'
    filter_upwards with N
    push_cast
    ring
  have hDHoverX : Tendsto (fun N => (d * H N : ℕ) / (X N : ℝ))
      atTop (𝓝 0) := by
    have h := Filter.Tendsto.const_mul (d : ℝ) hGap
    simpa [Nat.cast_mul, div_eq_mul_inv, mul_assoc] using h
  have hWidthX : ∀ᶠ N in atTop, Width N + 1 ≤ X N := by
    filter_upwards [hDHoverX.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
      pivotSamplingEventually MS B.1] with N hsmall hSampling
    have hXpos : 0 < (X N : ℝ) := by exact_mod_cast A.Xpos N B.1
    have hX2 : (2 : ℝ) ≤ (X N : ℝ) := by exact_mod_cast hSampling.1
    have hinv : 1 / (X N : ℝ) ≤ 1 / 2 := by
      apply (div_le_div_iff₀ hXpos (by norm_num : (0 : ℝ) < 2)).2
      nlinarith
    have hsmall' : (d : ℝ) * (H N : ℝ) / (X N : ℝ) < 1 / 2 := by
      simpa only [Nat.cast_mul] using hsmall
    have hsumParts : (d : ℝ) * (H N : ℝ) / (X N : ℝ) +
        1 / (X N : ℝ) < 1 := by
      linarith [hsmall', hinv]
    have hsum : ((d * H N + 1 : ℕ) : ℝ) / (X N : ℝ) ≤ 1 := by
      rw [Nat.cast_add, Nat.cast_mul, add_div, Nat.cast_one]
      exact hsumParts.le
    have hNat : d * H N + 1 ≤ X N := by
      have hReal := (div_le_iff₀ hXpos).1 hsum
      have hReal' : ((d * H N + 1 : ℕ) : ℝ) ≤ (X N : ℝ) := by simpa using hReal
      exact_mod_cast hReal'
    have hWidthLe : Width N + 1 ≤ d * H N + 1 := by
      dsimp [Width, d]
      exact Nat.add_le_add_right (Nat.div_le_self _ _) 1
    exact hWidthLe.trans hNat
  have hErrTendsto : Tendsto Err atTop (𝓝 0) := by
    have h1 := Filter.Tendsto.const_mul (168 : ℝ) hWplusOverH
    have h2 := Filter.Tendsto.const_mul (168 : ℝ) hVtailOverH
    have h3 := Filter.Tendsto.const_mul (224 : ℝ) hSumOverX
    have h4 := (pivotDilationError_tendsto A B.1).1
    simpa [Err, div_eq_mul_inv, add_assoc, mul_assoc, mul_left_comm, mul_comm] using
      h1.add (h2.add (h3.add h4))
  have hErrSmall : ∀ᶠ N in atTop, Err N ≤ ε := by
    filter_upwards [hErrTendsto.eventually_lt_const hε] with N hN
    exact hN.le
  have hPivotScale := pivotDilationError_tendsto A B.1
  have hPivotSampling := pivotSamplingEventually MS B.1
  let Tail : ℕ → ℕ → ℝ := fun N σ => parameterTailProductLaw A N B.2.val σ
  let RefB : ℕ → ℕ → ℝ := fun N σ =>
    ∑' y : ℤ, dilationReference (harmonicLaw (X N) (W N)) σ y *
      pkgDBoundaryIndicator (H N) (Width N) y
  let Bound : ℕ → ℕ := fun N => ∏ j ∈ B.2.val, (A.X N j) ^ 2
  let Sig : ℕ → Finset ℕ := fun N => Finset.range (Bound N + 1)
  have hNorm (N : ℕ) (j : Fin K) :
      0 < harmonicNormalizer (A.X N j) (W N) :=
    harmonicNormalizer_pos (A.X N j) (W N) (primorial_pos _)
      (MS.gapStage.valid_raw_cutoffs N j)
  have hTailZero (N σ : ℕ) (hσ : σ ∉ Sig N) : Tail N σ = 0 := by
    apply parameterTailProductLaw_zero_of_gt A N B.2.val σ
    have hnot : ¬ σ < Bound N + 1 := by simpa [Sig, Finset.mem_range] using hσ
    change (∏ j ∈ B.2.val, (A.X N j) ^ 2) < σ
    dsimp [Bound] at hnot ⊢
    omega
  have hTailNonneg (N σ : ℕ) : 0 ≤ Tail N σ := by
    dsimp [Tail]
    exact pkgD_parameterTailProductLaw_nonneg A N B.2.val (fun j => hNorm N j) σ
  have hTailSum (N : ℕ) : ∑ σ ∈ Sig N, Tail N σ = 1 := by
    have htotal := parameterTailProductLaw_tsum_one A N B.2.val
      (fun j => A.Xpos N j) (fun j => hNorm N j)
    rw [tsum_eq_sum (s := Sig N) (fun σ hσ => by
      have hz := hTailZero N σ hσ
      simpa [Tail] using hz)] at htotal
    simpa [Tail] using htotal
  have hBase (N : ℕ) (hWidthX : Width N + 1 ≤ X N) :
      Emu A N B.1 (pkgDBoundaryIndicator (H N) (Width N)) ≤ BaseRaw N := by
    have hraw := harmonicDilation_boundary_raw_bound (X N) (W N) (H N) (Width N) 1
      (primorial_pos _) (MS.gapStage.valid_raw_cutoffs N B.1) (A.Hpos N l) (by norm_num)
      (by simpa [Nat.div_one] using hWidthX)
    have hnat : Width N / 1 + 1 + W N + 1 = Width N + W N + 2 := by
      simp [Nat.div_one]
      omega
    rw [hnat] at hraw
    simpa [Emu, mu, dilatedLaw, BaseRaw, W, H, X, Width, Nat.div_one,
      Int.emod_one, Int.ediv_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      add_assoc, add_left_comm, add_comm] using hraw
  have hNuPair (N : ℕ) :
      Emu A N B.1 (fun y => nu A N B y * pkgDBoundaryIndicator (H N) (Width N) y) =
        ∑' σ : ℕ, Tail N σ * RefB N σ := by
    simpa [Tail, RefB, H, W, X] using
      nuWeightedPairing_eq A N B (pkgDBoundaryIndicator (H N) (Width N))
  have hOuter (N : ℕ) :
      (∑' σ : ℕ, Tail N σ * RefB N σ) =
        ∑ σ ∈ Sig N, Tail N σ * RefB N σ := by
    rw [tsum_eq_sum (s := Sig N) (fun σ hσ => by
      have hz := hTailZero N σ hσ
      simp [Tail, hz])]
  have hNuBound (N : ℕ) (hX2 : 2 ≤ X N)
      (hlog : Real.log (X N : ℝ) > (W N : ℝ) / (X N : ℝ))
      (hWidthX : Width N + 1 ≤ X N) (hVpivot : Vpivot N ≤ X N) :
      Emu A N B.1 (fun y => nu A N B y * pkgDBoundaryIndicator (H N) (Width N) y) ≤
        TailRaw N := by
    rw [hNuPair, hOuter]
    have hInnerBound (σ : ℕ) (hMass : Tail N σ ≠ 0) : RefB N σ ≤ TailRaw N := by
      have hcut := tailProductLaw_cutoff_bound MS B l hl N σ (by simpa [Tail] using hMass)
      rcases hcut with ⟨hσpos, hcop, hσVtail⟩
      have hσVpivot : σ ≤ Vpivot N :=
        hσVtail.trans (masterScaleV_mono A N l B.1 (le_of_lt hl.2))
      have hRle : Width N / σ + 1 ≤ X N := by
        exact (boundaryRadiusProperties (Width N) σ hσpos).2 |>.trans hWidthX
      have hRef := harmonicReference_boundary_le (X N) (W N) (H N) (Width N) σ
        (Vpivot N) (primorial_pos _) (MS.gapStage.valid_raw_cutoffs N B.1)
        (A.Xpos N B.1) hX2 hlog (A.Hpos N l) hσpos hσVpivot hVpivot hcop hRle
      have hsum := boundarySigmaSumBound (Width N) (W N) σ (Vtail N) hσpos hσVtail
      have hprod1 : (σ : ℝ) * ((Width N / σ + 1 + W N + 1 : ℕ) : ℝ) ≤
          ((Width N + Vtail N * (W N + 2) : ℕ) : ℝ) := by exact_mod_cast hsum.1
      have hprod2 : ((Width N / σ + 1 + W N + 1 : ℕ) : ℝ) ≤
          ((Width N + W N + 2 : ℕ) : ℝ) := by exact_mod_cast hsum.2
      have hterm1 :
          168 * (σ : ℝ) * ((Width N / σ + 1 + W N + 1 : ℕ) : ℝ) / (H N : ℝ) ≤
            168 * ((Width N + Vtail N * (W N + 2) : ℕ) : ℝ) / (H N : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hprod1 (by norm_num : (0 : ℝ) ≤ 168)
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith
      have hterm2 :
          112 * ((Width N / σ + 1 + W N + 1 : ℕ) : ℝ) / (X N : ℝ) ≤
            112 * ((Width N + W N + 2 : ℕ) : ℝ) / (X N : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hprod2 (by norm_num : (0 : ℝ) ≤ 112)
        exact div_le_div_of_nonneg_right hmul (by positivity)
      calc
        RefB N σ ≤
            168 * (σ : ℝ) * ((Width N / σ + 1 + W N + 1 : ℕ) : ℝ) / (H N : ℝ) +
              112 * ((Width N / σ + 1 + W N + 1 : ℕ) : ℝ) / (X N : ℝ) +
                harmonicDilationUniformError (X N) (W N) (Vpivot N) := by
          simpa [RefB, H, W, X] using hRef
        _ ≤ 168 * ((Width N + Vtail N * (W N + 2) : ℕ) : ℝ) / (H N : ℝ) +
              112 * ((Width N + W N + 2 : ℕ) : ℝ) / (X N : ℝ) +
                harmonicDilationUniformError (X N) (W N) (Vpivot N) :=
          add_le_add (add_le_add hterm1 hterm2) le_rfl
        _ = TailRaw N := by
          dsimp [TailRaw]
          push_cast
          ring
    calc
      (∑ σ ∈ Sig N, Tail N σ * RefB N σ) ≤
          ∑ σ ∈ Sig N, Tail N σ * TailRaw N := by
        apply Finset.sum_le_sum
        intro σ hσ
        by_cases hzero : Tail N σ = 0
        · simp [hzero]
        · exact mul_le_mul_of_nonneg_left (hInnerBound σ hzero) (hTailNonneg N σ)
      _ = (∑ σ ∈ Sig N, Tail N σ) * TailRaw N := by rw [Finset.sum_mul]
      _ = TailRaw N := by rw [hTailSum N]; ring
  have hsplit (N : ℕ) :
      Emu A N B.1 (fun y => (1 + nu A N B y) * pkgDBoundaryIndicator (H N) (Width N) y) =
        Emu A N B.1 (pkgDBoundaryIndicator (H N) (Width N)) +
          Emu A N B.1 (fun y => nu A N B y * pkgDBoundaryIndicator (H N) (Width N) y) := by
    calc
      _ = Emu A N B.1 (fun y => pkgDBoundaryIndicator (H N) (Width N) y +
          nu A N B y * pkgDBoundaryIndicator (H N) (Width N) y) := by
            congr 1
            funext y
            ring
      _ = _ := pkgD_Emu_add A N B.1 _ _
  have hTotalBound (N : ℕ) (hX2 : 2 ≤ X N)
      (hlog : Real.log (X N : ℝ) > (W N : ℝ) / (X N : ℝ))
      (hWidthX : Width N + 1 ≤ X N) (hVpivot : Vpivot N ≤ X N) :
      Emu A N B.1 (fun y => (1 + nu A N B y) * pkgDBoundaryIndicator (H N) (Width N) y) ≤
        336 * (d : ℝ) / J0 + Err N := by
    rw [hsplit N]
    have hBaseBound := hBase N hWidthX
    have hTailBound := hNuBound N hX2 hlog hWidthX hVpivot
    have hBaseExpand : BaseRaw N =
        168 * (Width N : ℝ) / (H N : ℝ) +
          168 * ((W N + 2 : ℕ) : ℝ) / (H N : ℝ) +
          112 * (Width N : ℝ) / (X N : ℝ) +
          112 * ((W N + 2 : ℕ) : ℝ) / (X N : ℝ) := by
      dsimp [BaseRaw]
      push_cast
      ring
    have hsumIdentity : BaseRaw N + TailRaw N =
        336 * (Width N : ℝ) / (H N : ℝ) + Err N := by
      dsimp [BaseRaw, TailRaw, Err]
      push_cast
      ring
    have hWidthTerm : 336 * (Width N : ℝ) / (H N : ℝ) ≤
        336 * (d : ℝ) / J0 := by
      calc
        336 * (Width N : ℝ) / (H N : ℝ) =
            336 * ((Width N : ℝ) / (H N : ℝ)) := by ring
        _ ≤ 336 * ((d : ℝ) / J0) :=
          mul_le_mul_of_nonneg_left (hwidthRatio N) (by norm_num)
        _ = 336 * (d : ℝ) / J0 := by ring
    calc
      _ ≤ BaseRaw N + TailRaw N := add_le_add hBaseBound hTailBound
      _ = 336 * (Width N : ℝ) / (H N : ℝ) + Err N := hsumIdentity
      _ ≤ 336 * (d : ℝ) / J0 + Err N := add_le_add_left hWidthTerm (Err N)
  have hErrTendsto : Tendsto Err atTop (𝓝 0) := by
    have h1 := Filter.Tendsto.const_mul (168 : ℝ) hWplusOverH
    have h2 := Filter.Tendsto.const_mul (168 : ℝ) hVtailOverH
    have h3 := Filter.Tendsto.const_mul (224 : ℝ) hSumOverX
    have h4 := (pivotDilationError_tendsto A B.1).1
    have h1' : Tendsto (fun N =>
        168 * ((W N + 2 : ℕ) : ℝ) / (H N : ℝ)) atTop (𝓝 0) := by
      convert h1 using 1 <;> ext N <;> push_cast <;> ring
    have h2' : Tendsto (fun N =>
        168 * ((Vtail N * (W N + 2) : ℕ) : ℝ) / (H N : ℝ)) atTop (𝓝 0) := by
      convert h2 using 1 <;> ext N <;> push_cast <;> ring
    have h3' : Tendsto (fun N =>
        224 * ((Width N + W N + 2 : ℕ) : ℝ) / (X N : ℝ)) atTop (𝓝 0) := by
      convert h3 using 1 <;> ext N <;> push_cast <;> ring
    simpa [Err, X, W, Vpivot, add_assoc] using h1'.add (h2'.add (h3'.add h4))
  have hErrSmall : ∀ᶠ N in atTop, Err N ≤ ε := by
    filter_upwards [hErrTendsto.eventually_lt_const hε] with N hN
    exact hN.le
  have hVlePivot : ∀ᶠ N in atTop, Vpivot N ≤ X N := by
    simpa [Vpivot, X] using (pivotDilationError_tendsto A B.1).2
  filter_upwards [pivotSamplingEventually MS B.1, hWidthX, hVlePivot, hErrSmall]
    with N ⟨hX2, hlog⟩ hWidthXN hVP hErrN
  have hTotal := hTotalBound N hX2 hlog hWidthXN hVP
  have hCoeff : 336 * (d : ℝ) / J0 ≤ 1000 * (d : ℝ) / J0 := by
    have hd : 0 ≤ (d : ℝ) / J0 := by positivity
    have hconst : (336 : ℝ) ≤ 1000 := by norm_num
    have hmul := mul_le_mul_of_nonneg_right hconst hd
    calc
      336 * (d : ℝ) / J0 = 336 * ((d : ℝ) / J0) := by ring
      _ ≤ 1000 * ((d : ℝ) / J0) := hmul
      _ = 1000 * (d : ℝ) / J0 := by ring
  have hCoeffErr := add_le_add_left hCoeff (Err N)
  have hErrFinal := add_le_add_right hErrN (1000 * (d : ℝ) / J0)
  exact hTotal.trans (hCoeffErr.trans hErrFinal)

end Prediction

end HindmanSumsProducts
